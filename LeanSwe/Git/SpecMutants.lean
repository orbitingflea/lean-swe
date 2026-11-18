import Core.NondetTest
import LeanSwe.Git.Types
import LeanSwe.Git.Model
import LeanSwe.Git.SpecTests

/-! Compile-time negative specification mutants for `LeanSwe.Git`. -/

namespace LeanSwe.Git

open Core (NondetTest)
open Core.NondetTest
open LeanSwe.Git.Model

example : cleanGitEnv #[("GIT_DIR", "/bad"), ("HOME", "/var/u")] #[("GIT_TERMINAL_PROMPT", some "1"), ("GIT_AUTHOR_NAME", some "A"), ("FOO", some "bar")] =
    #[("GIT_DIR", none),
      ("GIT_TERMINAL_PROMPT", some "0"), ("GIT_CONFIG_COUNT", some "1"),
      ("GIT_CONFIG_KEY_0", some "safe.bareRepository"), ("GIT_CONFIG_VALUE_0", some "all"),
      ("GIT_AUTHOR_NAME", some "A"), ("FOO", some "bar")] := by
  cbv

example : parsePorcelainStatusZ "R  dest.txt\x00src.txt\x00".toUTF8 =
    .ok #[{ indexStatus := some .renamed, worktreeStatus := none, path := "dest.txt", origPath := some "src.txt" }] := by
  cbv

example : parseDiffNameStatusZ "R100\x00src.txt\x00dest.txt\x00".toUTF8 =
    .ok #[{ kind := .renamed 100, path := "dest.txt", origPath := some "src.txt" }] := by
  cbv

example : isValidRepoState
    { rootPath := "/repo"
      commits := [
        { id := mkSyntheticCommitId 0, parents := [] },
        { id := mkSyntheticCommitId 1, parents := [mkSyntheticCommitId 0] },
        { id := mkSyntheticCommitId 2, parents := [mkSyntheticCommitId 0] }
      ]
      branches := [
        ({ raw := "main" }, mkSyntheticCommitId 1),
        ({ raw := "feat" }, mkSyntheticCommitId 2)
      ]
      worktrees := [
        { path := "/repo", head := .attached { raw := "main" } (some (mkSyntheticCommitId 1)) }
      ] } = true := by
  cbv

example : mergeBase?
    { rootPath := "/repo"
      commits := [
        { id := mkSyntheticCommitId 0, parents := [] },
        { id := mkSyntheticCommitId 1, parents := [mkSyntheticCommitId 0] },
        { id := mkSyntheticCommitId 2, parents := [mkSyntheticCommitId 0] }
      ]
      branches := []
      worktrees := [{ path := "/repo", head := .detached (mkSyntheticCommitId 1) }] }
    (mkSyntheticCommitId 1) (mkSyntheticCommitId 2) = some (mkSyntheticCommitId 0) := by
  cbv

private def stubGitApi : GitApiM (StateM RepoState) :=
  let stubErr : GitError := { kind := .commandFailed, message := "stub" }
  { isRepo := fun _ s => (.ok true, s)
    repoRoot := fun p s => (.ok p, s)
    commonDir := fun p s => (.ok (p ++ "/.git"), s)
    headCommit? := fun _ s =>
      match s.worktrees.head? with
      | some w => (.ok (headCommitOfSlot w.head), s)
      | none => (.ok none, s)
    headBranch? := fun _ s =>
      match s.worktrees.head? with
      | some w =>
        match w.head with
        | .attached b _ => (.ok (some b), s)
        | .detached _ => (.ok none, s)
      | none => (.ok none, s)
    headState := fun _ s => (.error stubErr, s)
    revParseCommit := fun _ _ s => (.error { kind := .invalidRef, message := "unborn" }, s)
    isAncestor := fun _ _ _ s => (.ok false, s)
    mergeBase? := fun _ _ _ s => (.ok none, s)
    status := fun _ s => (.ok #[], s)
    diffNameStatus := fun _ _ _ _ s => (.ok #[], s)
    listWorktrees := fun _ s => (.ok #[], s)
    showFile? := fun _ _ _ s => (.ok none, s)
    init := fun path _ b? s =>
      (.ok (), { s with
        rootPath := path
        worktrees := [{ path := path, head := .attached (b?.getD { raw := "main" }) none }] })
    clone := fun _ _ _ s => (.ok (), s)
    add := fun _ _ _ s => (.ok (), s)
    commit := fun _ _ s => (.error { kind := .nothingToCommit, message := "nothing to commit" }, s)
    createBranch := fun _ _ _ _ s => (.ok (), s)
    deleteBranch := fun _ _ _ s => (.ok (), s)
    checkout := fun _ _ _ s => (.error { kind := .dirtyWorktree, message := "dirty" }, s)
    switch := fun _ _ _ _ _ s => (.ok (), s)
    reset := fun _ _ _ s => (.ok (), s)
    fetch := fun _ _ _ _ s => (.ok (), s)
    worktreeAdd := fun _ _ s => (.error { kind := .branchInUse, message := "in use" }, s)
    worktreeRemove := fun _ _ _ s => (.ok (), s)
    withWorktree := fun _ _ _ s => (.error stubErr, s) }

private def stubRawMkApi (ops : RawGitOpsM (StateM GitCliMockState)) :
    GitApiM (StateM GitCliMockState) :=
  let stubErr : GitError := { kind := .commandFailed, message := "stub" }
  { isRepo := fun _ => pure (.ok false)
    repoRoot := fun _ => pure (.error stubErr)
    commonDir := fun _ => pure (.error stubErr)
    headCommit? := fun _ => pure (.error stubErr)
    headBranch? := fun _ => pure (.error stubErr)
    headState := fun _ => pure (.error stubErr)
    revParseCommit := fun _ _ => pure (.error stubErr)
    isAncestor := fun _ _ _ => pure (.error stubErr)
    mergeBase? := fun _ _ _ => pure (.error stubErr)
    status := fun _ => pure (.error stubErr)
    diffNameStatus := fun _ _ _ _ => pure (.error stubErr)
    listWorktrees := fun _ => pure (.error stubErr)
    showFile? := fun _ _ _ => pure (.error stubErr)
    init := fun _ _ _ => pure (.error stubErr)
    clone := fun _ _ _ => pure (.error stubErr)
    add := fun _ _ _ => pure (.error stubErr)
    commit := fun _ _ => do
      let _ ← ops.execGit #[] { args := #["commit"] }
      pure (.error stubErr)
    createBranch := fun _ _ _ _ => pure (.error stubErr)
    deleteBranch := fun _ _ _ => pure (.error stubErr)
    checkout := fun _ _ _ => pure (.error stubErr)
    switch := fun _ _ _ _ _ => pure (.error stubErr)
    reset := fun _ _ _ => pure (.error stubErr)
    fetch := fun _ _ _ _ => pure (.error stubErr)
    worktreeAdd := fun _ _ => pure (.error stubErr)
    worktreeRemove := fun _ _ _ => pure (.error stubErr)
    withWorktree := fun _ _ _ => pure (.error stubErr) }

example : ¬ Core.AllPass (test_git_cleanGitEnv_stripsInheritedGitKeys fun _ extra => extra) := by
  intro h
  have h0 := h #[("GIT_DIR", "/bad")] #[]
  simp [bind, assert] at h0
  have h1 := h0.1
  revert h1
  decide

example : ¬ Core.AllPass (test_git_cleanGitEnv_preservesValidNonGitExtra fun _ _ => #[]) := by
  intro h
  have h0 := h #[] "FOO" (some "bar") (by decide) (by decide) (by decide)
  simp [assert] at h0

example : ¬ Core.AllPass (test_git_mkCommitId_validatesHexLengthAndChars fun s => .ok { hex := s }) := by
  intro h
  have h0 := h "bad"
  simp [assert] at h0
  exact absurd h0 (by decide)

example : ¬ Core.AllPass (test_git_mkRefName_rejectsUnsafeRefs fun s => .ok { raw := s }) := by
  intro h
  have h0 := h "-rf" (Or.inr (Or.inl rfl))
  simp [assert] at h0

example : ¬ Core.AllPass (test_git_parsePorcelainStatusZ_framingAndEmpty fun _ => .ok #[]) := by
  intro h
  dsimp [test_git_parsePorcelainStatusZ_framingAndEmpty, Core.AllPass, bind, assert] at h
  rcases h.2.1 with ⟨e, he, _⟩
  cases he

example : ¬ Core.AllPass (test_git_parsePorcelainStatusZ_renameDestFirst fun _ =>
    .ok #[{ indexStatus := some .renamed, worktreeStatus := none, path := "src.txt", origPath := some "dest.txt" }]) := by
  intro h
  have h0 := h "src.txt" "dest.txt" (by cbv) (by cbv)
  simp [assert] at h0

example : ¬ Core.AllPass (test_git_parseDiffNameStatusZ_renameSourceFirst fun _ =>
    .ok #[{ kind := .renamed 100, path := "src.txt", origPath := some "dest.txt" }]) := by
  intro h
  have h0 := h "src.txt" "dest.txt" (by cbv) (by cbv)
  simp [assert] at h0

example : ¬ Core.AllPass (test_git_parseWorktreeListPorcelain_bareUnbornLocked fun _ => .ok #[]) := by
  intro h
  have h1 := h.1
  cases h1

example : ¬ Core.AllPass (test_git_model_isAncestor_reflexiveAndGuarded fun _ _ _ => false) := by
  intro h
  dsimp [test_git_model_isAncestor_reflexiveAndGuarded, Core.AllPass, bind, assert] at h
  let c0 : CommitId := { hex := "0000000000000000000000000000000000000000" }
  let s : RepoState := {
    rootPath := "/repo"
    commits := [{ id := c0, parents := [] }]
    worktrees := [{ path := "/repo", head := .detached c0 }]
  }
  have hHas : hasCommit s c0 = true := by cbv
  have h0 := h s c0 c0
  simp [hHas] at h0

example : ¬ Core.AllPass (test_git_model_isAncestor_transitiveAndMergeBaseValid
    (fun s a b => a == b || (parentsOf s b).contains a)
    (fun _ _ _ => none)) := by
  intro h
  dsimp [test_git_model_isAncestor_transitiveAndMergeBaseValid, Core.AllPass, bind, assert] at h
  let c0 : CommitId := { hex := "0000000000000000000000000000000000000000" }
  let c1 : CommitId := { hex := "0000000000000000000000000000000000000001" }
  let c2 : CommitId := { hex := "0000000000000000000000000000000000000002" }
  let s : RepoState := {
    rootPath := "/repo"
    commits := [
      { id := c0, parents := [] },
      { id := c1, parents := [c0] },
      { id := c2, parents := [c1] }
    ]
    worktrees := [{ path := "/repo", head := .detached c2 }]
  }
  have hValid : ValidRepoState s := by cbv
  have h0 := (h s c0 c1 c2 hValid).1
  cbv at h0

example : ¬ Core.AllPass (test_git_api_unbornHead_behavior
    { stubGitApi with revParseCommit := fun _ _ s => (.error { kind := .notARepo, message := "bad" }, s) }) := by
  intro h
  let s0 : RepoState := { rootPath := "/repo" }
  have h0 := h s0 "/repo" { raw := "main" } (by decide) rfl
  simp [stubGitApi, StateT.run, bind, assert] at h0

example : ¬ Core.AllPass (test_git_api_commit_emptyVsAllowEmpty
    { stubGitApi with
      commit := fun _ _ s => (.error { kind := .commandFailed, message := "wrong" }, s) }) := by
  intro h
  let c0 : CommitId := { hex := "0000000000000000000000000000000000000000" }
  let b : RefName := { raw := "main" }
  let wt : WorktreeSlot := { path := "/repo", head := .attached b (some c0) }
  let s0 : RepoState := {
    rootPath := "/repo"
    commits := [{ id := c0, parents := [] }]
    branches := [(b, c0)]
    worktrees := [wt]
  }
  have hValid : ValidRepoState s0 := by cbv
  have h0 := h s0 wt hValid ⟨rfl, rfl, rfl, rfl⟩
  simp [bind, StateT.run, assert] at h0

example : ¬ Core.AllPass (test_git_api_worktreeAdd_branchInUseRejected
    { stubGitApi with
      worktreeAdd := fun _ _ s => (.ok (), s) }) := by
  intro h
  let c0 : CommitId := { hex := "0000000000000000000000000000000000000000" }
  let b : RefName := { raw := "main" }
  let wt : WorktreeSlot := { path := "/repo", head := .attached b (some c0) }
  let s0 : RepoState := {
    rootPath := "/repo"
    commits := [{ id := c0, parents := [] }]
    branches := [(b, c0)]
    worktrees := [wt]
  }
  have hValid : ValidRepoState s0 := by cbv
  have h0 := h s0 wt b c0 "/wt2" hValid ⟨rfl, rfl⟩ ⟨by decide, by decide⟩ (by decide)
  simp [StateT.run, assert] at h0

example : ¬ Core.AllPass (test_git_api_checkout_dirtyWorktreeRejected
    { stubGitApi with
      checkout := fun _ _ _ s => (.ok (), s) }) := by
  intro h
  let c0 : CommitId := { hex := "0000000000000000000000000000000000000000" }
  let b : RefName := { raw := "main" }
  let wt : WorktreeSlot := {
    path := "/repo"
    head := .attached b (some c0)
    unstaged := [("a.txt", some "dirty")]
  }
  let s0 : RepoState := {
    rootPath := "/repo"
    commits := [{ id := c0, parents := [] }]
    branches := [(b, c0)]
    worktrees := [wt]
  }
  have hValid : ValidRepoState s0 := by cbv
  have h0 := h s0 wt b c0 hValid ⟨rfl, rfl, rfl⟩ (List.Mem.head _)
  simp [StateT.run, assert] at h0

example : ¬ Core.AllPass (test_git_api_withWorktree_cleanupAndErrorPrecedence stubRawMkApi) := by
  intro h
  have h0 := h "/repo" "/wt" true true ⟨by decide, by decide⟩
  dsimp [test_git_api_withWorktree_cleanupAndErrorPrecedence, stubRawMkApi, mockRawOps,
    StateT.run, bind, StateT.bind, pure, StateT.pure, assert] at h0
  cases h0.1

example : ¬ Core.AllPass (test_git_raw_mkApi_isolationAndGuards stubRawMkApi) := by
  intro h
  dsimp [test_git_raw_mkApi_isolationAndGuards, stubRawMkApi, mockRawOps, Core.AllPass,
    StateT.run, bind, StateT.bind, pure, StateT.pure, assert] at h
  rcases h with ⟨⟨e, he, hkind⟩, _⟩
  cases he
  cases hkind

example : ¬ Core.AllPass (test_git_status_parsesRealOutput fun _ => .ok #[]) := by
  intro h
  dsimp [test_git_status_parsesRealOutput, Core.AllPass, assert] at h
  have hlen := congrArg Array.size (Except.ok.inj h.1)
  simp at hlen

example : ¬ Core.AllPass (test_git_worktreeList_parsesRealOutput fun _ => .ok #[]) := by
  intro h
  dsimp [test_git_worktreeList_parsesRealOutput, Core.AllPass, assert] at h
  have hlen := congrArg Array.size (Except.ok.inj h.1)
  simp at hlen

end LeanSwe.Git
