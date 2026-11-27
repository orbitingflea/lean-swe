import Core.NondetTest
import LeanSwe.Git.Types
import LeanSwe.Git.Model
import LeanSwe.Git.SpecTests

/-! Compile-time negative specification mutants for `LeanSwe.Git`. -/

namespace LeanSwe.Git

open Core (NondetTest)
open Core.NondetTest
open LeanSwe.Git.Model

example : cleanGitEnv #[("GIT_DIR", "/bad"), ("HOME", "/var/u")]
      #[("GIT_TERMINAL_PROMPT", some "1"), ("GIT_AUTHOR_NAME", some "A"), ("FOO", some "bar")] =
    #[("GIT_DIR", none)] ++ defaultGitSafetyEnv.toArray ++
      #[("GIT_AUTHOR_NAME", some "A"), ("FOO", some "bar")] := by
  cbv

example : parsePorcelainStatusZ "R  dest.txt\x00src.txt\x00".toUTF8 =
    .ok #[{ indexStatus := some .renamed, worktreeStatus := none, path := "dest.txt", origPath := some "src.txt" }] := by
  cbv

example : parseDiffNameStatusZ "R100\x00src.txt\x00dest.txt\x00".toUTF8 =
    .ok #[{ kind := .renamed 100, path := "dest.txt", origPath := some "src.txt" }] := by
  cbv

example : isValidRepoInstance
    { commonDir := "/repo/.git".toUTF8
      commits := [
        { id := mkSyntheticCommitId 0, parents := [] },
        { id := mkSyntheticCommitId 1, parents := [mkSyntheticCommitId 0] },
        { id := mkSyntheticCommitId 2, parents := [mkSyntheticCommitId 0] }
      ]
      refs := [
        ("refs/heads/main", mkSyntheticCommitId 1),
        ("refs/heads/feat", mkSyntheticCommitId 2)
      ]
      worktrees := [
        { rootPath := "/repo".toUTF8, head := .symbolic { raw := "main" } }
      ] } = true := by
  cbv

example : mergeBase?
    { commonDir := "/repo/.git".toUTF8
      commits := [
        { id := mkSyntheticCommitId 0, parents := [] },
        { id := mkSyntheticCommitId 1, parents := [mkSyntheticCommitId 0] },
        { id := mkSyntheticCommitId 2, parents := [mkSyntheticCommitId 0] }
      ]
      refs := []
      worktrees := [{ rootPath := "/repo".toUTF8, head := .detached (mkSyntheticCommitId 1) }] }
    (mkSyntheticCommitId 1) (mkSyntheticCommitId 2) = some (mkSyntheticCommitId 0) := by
  cbv

private def stubGitApi : GitApiM (StateM GitRepoState) :=
  let stubErr : GitError := { kind := .commandFailed, message := "stub" }
  { isRepo := fun _ s => (.ok true, s)
    repoRoot := fun p s => (.ok p, s)
    commonDir := fun p s => (.ok (p ++ "/.git"), s)
    headCommit? := fun _ s =>
      match s.repos.head? with
      | some r =>
        match r.worktrees.head? with
        | some w => (.ok (headCommitOfSymbolic r w.head), s)
        | none => (.ok none, s)
      | none => (.ok none, s)
    headBranch? := fun _ s =>
      match s.repos.head? with
      | some r =>
        match r.worktrees.head? with
        | some w =>
          match w.head with
          | .symbolic b => (.ok (some b), s)
          | .detached _ => (.ok none, s)
        | none => (.ok none, s)
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
        repos := [{
          commonDir := (path ++ "/.git").toUTF8
          worktrees := [{ rootPath := path.toUTF8, head := .symbolic (b?.getD { raw := "main" }) }] }] })
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
  have h0 := h #[] "FOO" (some "bar") (by decide) (by decide) (by decide) (by decide)
  simp [assert] at h0

example : ¬ Core.AllPass (test_git_mkCommitId_validatesHexLengthAndChars fun s => .ok { hex := s }) := by
  intro h
  have h0 := h "bad"
  simp [assert] at h0
  exact absurd h0 (by decide)

example : ¬ Core.AllPass (test_git_mkRefName_rejectsUnsafeRefs fun s => .ok { raw := s }) := by
  intro h
  have h0 := h "-rf" (Or.inr (Or.inr (Or.inl rfl)))
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
  let s : RepoInstance := {
    commonDir := "/repo/.git".toUTF8
    commits := [{ id := c0, parents := [] }]
    worktrees := [{ rootPath := "/repo".toUTF8, head := .detached c0 }]
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
  let s : RepoInstance := {
    commonDir := "/repo/.git".toUTF8
    commits := [
      { id := c0, parents := [] },
      { id := c1, parents := [c0] },
      { id := c2, parents := [c1] }
    ]
    worktrees := [{ rootPath := "/repo".toUTF8, head := .detached c2 }]
  }
  have hValid : isValidRepoInstance s = true := by cbv
  have h0 := (h s c0 c1 c2 hValid).1
  cbv at h0

example : ¬ Core.AllPass (test_git_api_unbornHead_behavior
    { stubGitApi with revParseCommit := fun _ _ s => (.error { kind := .notARepo, message := "bad" }, s) }) := by
  intro h
  let s0 : GitRepoState := {}
  have h0 := h s0 "/repo" { raw := "main" } rfl rfl (by decide) rfl
  simp [stubGitApi, StateT.run, bind, assert] at h0

example : ¬ Core.AllPass (test_git_api_commit_emptyVsAllowEmpty
    { stubGitApi with
      commit := fun _ _ s => (.error { kind := .commandFailed, message := "wrong" }, s) }) := by
  intro h
  let c0 : CommitId := { hex := "0000000000000000000000000000000000000000" }
  let b : RefName := { raw := "main" }
  let wt : WorktreeSlot := { rootPath := "/repo".toUTF8, head := .symbolic b }
  let repo : RepoInstance := {
    commonDir := "/repo/.git".toUTF8
    commits := [{ id := c0, parents := [] }]
    refs := [("refs/heads/main", c0)]
    worktrees := [wt]
  }
  let s0 : GitRepoState := {
    vfs := .dir true true [("repo".toUTF8, .dir true true [])]
    repos := [repo]
  }
  have hValid : isValidGitRepoState s0 = true := by cbv
  have h0 := h s0 repo wt c0 b hValid ⟨rfl, rfl, rfl, rfl⟩ ⟨rfl, rfl⟩ ⟨rfl, rfl⟩ rfl
  simp [bind, StateT.run, assert] at h0

example : ¬ Core.AllPass (test_git_api_worktreeAdd_branchInUseRejected
    { stubGitApi with
      worktreeAdd := fun _ _ s => (.ok (), s) }) := by
  intro h
  let c0 : CommitId := { hex := "0000000000000000000000000000000000000000" }
  let b : RefName := { raw := "main" }
  let wt : WorktreeSlot := { rootPath := "/repo".toUTF8, head := .symbolic b }
  let repo : RepoInstance := {
    commonDir := "/repo/.git".toUTF8
    commits := [{ id := c0, parents := [] }]
    refs := [("refs/heads/main", c0)]
    worktrees := [wt]
  }
  let s0 : GitRepoState := {
    vfs := .dir true true [("repo".toUTF8, .dir true true [])]
    repos := [repo]
  }
  have hValid : isValidGitRepoState s0 = true := by cbv
  have h0 := h s0 repo wt b c0 hValid ⟨rfl, rfl, rfl, rfl⟩ ⟨rfl, rfl⟩ ⟨rfl, rfl⟩ (by decide)
  simp [StateT.run, assert] at h0

example : ¬ Core.AllPass (test_git_api_checkout_dirtyWorktreeRejected
    { stubGitApi with
      checkout := fun _ _ _ s => (.ok (), s) }) := by
  intro h
  let c0 : CommitId := { hex := "0000000000000000000000000000000000000000" }
  let c1 : CommitId := { hex := "0000000000000000000000000000000000000001" }
  let bMain : RefName := { raw := "main" }
  let bFeat : RefName := { raw := "feat" }
  let e0 : GitTreeEntry := { kind := .regular false, bytes := "v0".toUTF8 }
  let e1 : GitTreeEntry := { kind := .regular false, bytes := "v1".toUTF8 }
  let wt : WorktreeSlot := {
    rootPath := "/repo".toUTF8
    head := .symbolic bMain
    index := { entries := [("a.txt".toUTF8, e0)] }
  }
  let repo : RepoInstance := {
    commonDir := "/repo/.git".toUTF8
    commits := [
      { id := c0, parents := [], tree := [("a.txt".toUTF8, e0)] },
      { id := c1, parents := [c0], tree := [("a.txt".toUTF8, e1)] }
    ]
    refs := [("refs/heads/main", c0), ("refs/heads/feat", c1)]
    worktrees := [wt]
  }
  let s0 : GitRepoState := {
    vfs := .dir true true [("repo".toUTF8, .dir true true [("a.txt".toUTF8, .file false "dirty".toUTF8)])]
    repos := [repo]
  }
  have hValid : isValidGitRepoState s0 = true := by cbv
  have h0 := h s0 repo wt bMain bFeat c0 c1 hValid ⟨rfl, rfl, rfl, rfl⟩ ⟨rfl, rfl⟩
    ⟨rfl, rfl⟩ ⟨by decide, by decide⟩ rfl rfl rfl rfl
  simp [StateT.run, assert] at h0

example : ¬ Core.AllPass (test_git_api_withWorktree_cleanupAndErrorPrecedence stubRawMkApi) := by
  intro h
  have h0 := h "/repo" "/wt" true true ⟨by cbv, by cbv⟩
  dsimp [test_git_api_withWorktree_cleanupAndErrorPrecedence, stubRawMkApi, mockRawOps,
    StateT.run, bind, StateT.bind, pure, StateT.pure, assert] at h0
  omega

example : ¬ Core.AllPass (test_git_raw_mkApi_isolationAndGuards stubRawMkApi) := by
  intro h
  dsimp [test_git_raw_mkApi_isolationAndGuards, stubRawMkApi, mockRawOps, Core.AllPass,
    StateT.run, bind, StateT.bind, pure, StateT.pure, assert] at h
  rcases h with ⟨⟨e, he, hkind⟩, _⟩
  cases he
  cases hkind

example : ¬ Core.AllPass (test_git_raw_mkApi_queryAndParserDelegation stubRawMkApi) := by
  intro h
  dsimp [test_git_raw_mkApi_queryAndParserDelegation, stubRawMkApi, mockRawOps, Core.AllPass,
    StateT.run, bind, StateT.bind, pure, StateT.pure, assert] at h
  rcases h with ⟨⟨hrr, _⟩, _⟩
  cases hrr

example : ¬ Core.AllPass (test_git_raw_mkApi_mutationAndFlagDelegation stubRawMkApi) := by
  intro h
  dsimp [test_git_raw_mkApi_mutationAndFlagDelegation, stubRawMkApi, mockRawOps, Core.AllPass,
    StateT.run, bind, StateT.bind, pure, StateT.pure, assert] at h
  rcases h with ⟨⟨hir, _⟩, _⟩
  cases hir

example : ¬ Core.AllPass (test_git_raw_mkApi_extendedFlagAndCommitDelegation stubRawMkApi) := by
  intro h
  dsimp [test_git_raw_mkApi_extendedFlagAndCommitDelegation, stubRawMkApi, mockRawOps, Core.AllPass,
    StateT.run, bind, StateT.bind, pure, StateT.pure, assert] at h
  rcases h with ⟨⟨hcm, _⟩, _⟩
  cases hcm

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

example : ¬ Core.AllPass (test_git_api_resetDiffFetchDeleteAndSwitch_semantics stubGitApi) := by
  intro h
  dsimp [test_git_api_resetDiffFetchDeleteAndSwitch_semantics, stubGitApi, Core.AllPass,
    StateT.run, bind, StateT.bind, pure, StateT.pure, assert] at h
  rcases h with ⟨⟨_, _, hSoftSt⟩, _⟩
  have hlen := congrArg Array.size (Except.ok.inj hSoftSt)
  simp at hlen

example : ¬ Core.AllPass (test_git_raw_mkApi_forceAndShortShaGuards stubRawMkApi) := by
  intro h
  dsimp [test_git_raw_mkApi_forceAndShortShaGuards, stubRawMkApi, mockRawOps, Core.AllPass,
    StateT.run, bind, StateT.bind, pure, StateT.pure, assert] at h
  rcases h with ⟨⟨hsw, _⟩, _⟩
  cases hsw

example : ¬ Core.AllPass (test_git_raw_mkApi_secondaryShortShaAnd40HexWorktreeGuards stubRawMkApi) := by
  intro h
  dsimp [test_git_raw_mkApi_secondaryShortShaAnd40HexWorktreeGuards, stubRawMkApi, mockRawOps,
    Core.AllPass, StateT.run, bind, StateT.bind, pure, StateT.pure, assert] at h
  rcases h with ⟨⟨hok, _⟩, _⟩
  cases hok

end LeanSwe.Git
