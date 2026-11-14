import Core.NondetTest
import LeanSwe.Git.Types
import LeanSwe.Git.Model

namespace LeanSwe.Git

open Core (NondetTest)
open Core.NondetTest
open LeanSwe.Git.Model

/-- `cleanGitEnv` emits explicit `none` removals for every inherited `GIT_*` key and restricts surviving `GIT_*` entries to safety defaults or the author/committer allowlist. -/
def test_git_cleanGitEnv_stripsInheritedGitKeys
    {runner} [NondetTest runner]
    (sanitize : Array (String × String) → Array (String × Option String) → Array (String × Option String)) :
    runner Unit := do
  let inherited ← nondet (Array (String × String))
  let extra ← nondet (Array (String × Option String))
  let out := sanitize inherited extra
  let outList := out.toList
  NondetTest.assert (inherited.toList.all fun kv =>
    !isGitKey kv.1 || outList.contains (kv.1, none))
  NondetTest.assert (defaultGitSafetyEnv.all fun kv => outList.contains kv)
  NondetTest.assert (outList.all fun kv =>
    !isGitKey kv.1 || kv.2 == none || defaultGitSafetyEnv.contains kv || isAllowedExtraGitKey kv.1)

/-- `cleanGitEnv` preserves valid non-`GIT_*` extra environment entries. -/
def test_git_cleanGitEnv_preservesValidNonGitExtra
    {runner} [NondetTest runner]
    (sanitize : Array (String × String) → Array (String × Option String) → Array (String × Option String)) :
    runner Unit := do
  let inherited ← nondet (Array (String × String))
  let key ← nondet String
  let val ← nondet (Option String)
  assume (isValidEnvKey key = true)
  assume (isValidEnvVal? val = true)
  assume (isGitKey key = false)
  let out := sanitize inherited #[(key, val)]
  NondetTest.assert (out.toList.contains (key, val))

/-- `mkCommitId` accepts 40/64-char lowercase hex strings and rejects invalid hashes with `.invalidRef`. -/
def test_git_mkCommitId_validatesHexLengthAndChars
    {runner} [NondetTest runner] (buildId : String → Except GitError CommitId) : runner Unit := do
  let s ← nondet String
  match buildId s with
  | .ok cid =>
    NondetTest.assert (cid.hex = s ∧ isValidCommitIdStr s = true)
  | .error err =>
    NondetTest.assert (err.kind = .invalidRef ∧ err.message ≠ "" ∧ isValidCommitIdStr s = false)

/-- `mkRefName` rejects unsafe ref names (leading `'-'`, `".."`, `"@{"`, control chars, `.lock`) with `.invalidRef`. -/
def test_git_mkRefName_rejectsUnsafeRefs
    {runner} [NondetTest runner] (buildRef : String → Except GitError RefName) : runner Unit := do
  let s ← nondet String
  assume (s = "" ∨ s.toList.head? = some '-' ∨ s = "@" ∨ hasSubstrChars ['.', '.'] s.toList = true)
  match buildRef s with
  | .ok _ => NondetTest.assert False
  | .error err => NondetTest.assert (err.kind = .invalidRef ∧ err.message ≠ "")

/-- `parsePorcelainStatusZ` returns `#[]` on empty output and `.parseError` on unterminated or interior-empty records. -/
def test_git_parsePorcelainStatusZ_framingAndEmpty
    {runner} [NondetTest runner]
    (parseFn : ByteArray → Except GitError (Array StatusEntry)) : runner Unit := do
  let emptyRes := parseFn ByteArray.empty
  let badRes := parseFn " M a.txt".toUTF8
  NondetTest.assert (emptyRes = .ok #[])
  NondetTest.assert (∃ e, badRes = .error e ∧ e.kind = .parseError ∧ e.message ≠ "")

/-- `parsePorcelainStatusZ` binds `PATH1` to `path` (destination) and `PATH2` to `origPath` (source) for renames and copies. -/
def test_git_parsePorcelainStatusZ_renameDestFirst
    {runner} [NondetTest runner]
    (parseFn : ByteArray → Except GitError (Array StatusEntry)) : runner Unit := do
  let src ← nondet String
  let dst ← nondet String
  assume (src ≠ "" ∧ !hasNulChar src.toList)
  assume (dst ≠ "" ∧ !hasNulChar dst.toList)
  let payload := ("R  " ++ dst ++ "\x00" ++ src ++ "\x00").toUTF8
  match parseFn payload with
  | .error _ => NondetTest.assert False
  | .ok entries =>
    NondetTest.assert (entries = #[{
      indexStatus := some .renamed
      worktreeStatus := none
      path := dst
      origPath := some src
    }])

/-- `parseDiffNameStatusZ` binds `origPath` first and `path` second for `R<score>` / `C<score>` entries. -/
def test_git_parseDiffNameStatusZ_renameSourceFirst
    {runner} [NondetTest runner]
    (parseFn : ByteArray → Except GitError (Array DiffEntry)) : runner Unit := do
  let src ← nondet String
  let dst ← nondet String
  assume (src ≠ "" ∧ !hasNulChar src.toList)
  assume (dst ≠ "" ∧ !hasNulChar dst.toList)
  let payload := ("R095\x00" ++ src ++ "\x00" ++ dst ++ "\x00").toUTF8
  match parseFn payload with
  | .error _ => NondetTest.assert False
  | .ok entries =>
    NondetTest.assert (entries = #[{
      kind := .renamed 95
      path := dst
      origPath := some src
    }])

/-- `parseWorktreeListPorcelain` handles bare stanzas without `HEAD`, unborn `000...0` heads, and `locked`/`prunable` with or without reasons. -/
def test_git_parseWorktreeListPorcelain_bareUnbornLocked
    {runner} [NondetTest runner]
    (parseFn : ByteArray → Except GitError (Array WorktreeInfo)) : runner Unit := do
  let bareBytes := "worktree /tmp/bare.git\x00bare\x00\x00".toUTF8
  let unbornBytes :=
    ("worktree /tmp/wt\x00HEAD " ++ String.ofList (List.replicate 40 '0') ++
      "\x00branch refs/heads/main\x00locked\x00prunable gone\x00\x00").toUTF8
  NondetTest.assert (parseFn bareBytes = .ok #[{
    path := "/tmp/bare.git", head? := none, branch? := none, isBare := true
  }])
  NondetTest.assert (parseFn unbornBytes = .ok #[{
    path := "/tmp/wt"
    head? := none
    branch? := some { raw := "main" }
    isLocked := true
    lockReason := none
    isPrunable := true
    pruneReason := some "gone"
  }])

/-- `isAncestor` is reflexive on existing commits and `false` if either commit is absent from `RepoState`. -/
def test_git_model_isAncestor_reflexiveAndGuarded
    {runner} [NondetTest runner]
    (ancFn : RepoState → CommitId → CommitId → Bool) : runner Unit := do
  let s ← nondet RepoState
  let a ← nondet CommitId
  let b ← nondet CommitId
  if hasCommit s a then
    NondetTest.assert (ancFn s a a = true)
  else
    NondetTest.assert (ancFn s a b = false ∧ ancFn s b a = false)

/-- On any `ValidRepoState`, `isAncestor` is transitive and `mergeBase?` returns an ancestor of both inputs. -/
def test_git_model_isAncestor_transitiveAndMergeBaseValid
    {runner} [NondetTest runner]
    (ancFn : RepoState → CommitId → CommitId → Bool)
    (mbFn : RepoState → CommitId → CommitId → Option CommitId) : runner Unit := do
  let s ← nondet RepoState
  let a ← nondet CommitId
  let b ← nondet CommitId
  let c ← nondet CommitId
  assume (ValidRepoState s)
  if ancFn s a b && ancFn s b c then
    NondetTest.assert (ancFn s a c = true)
  match mbFn s a b with
  | none => pure ()
  | some m => NondetTest.assert (ancFn s m a = true ∧ ancFn s m b = true)

/-- Initializing a repo gives an unborn `HEAD` (`headCommit? = none`, `headBranch? = some branch`), and `revParseCommit "HEAD"` fails with `.invalidRef`. -/
def test_git_api_unbornHead_behavior
    {S : Type} {runner} [NondetTest runner]
    (api : GitApiM (StateM S)) : runner Unit := do
  let s₀ ← nondet S
  let path ← nondet String
  let branch ← nondet RefName
  assume (isValidPathArg path = true)
  let (initRes, s₁) := (api.init path false (some branch)).run s₀
  assume (initRes = .ok ())
  let (hcRes, _) := (api.headCommit? path).run s₁
  let (hbRes, _) := (api.headBranch? path).run s₁
  let (rpRes, _) := (api.revParseCommit path "HEAD").run s₁
  NondetTest.assert (hcRes = .ok none)
  NondetTest.assert (hbRes = .ok (some branch))
  NondetTest.assert (∃ e, rpRes = .error e ∧ e.kind = .invalidRef ∧ e.message ≠ "")

/-- `commit` fails with `.nothingToCommit` when nothing is staged and `allowEmpty = false`, and succeeds when `allowEmpty = true`. -/
def test_git_api_commit_emptyVsAllowEmpty
    {runner} [NondetTest runner] (api : GitApiM (StateM RepoState)) : runner Unit := do
  let s₀ ← nondet RepoState
  let wt ← nondet WorktreeSlot
  assume (ValidRepoState s₀)
  assume (s₀.worktrees = [wt] ∧ wt.isBare = false ∧ wt.staged = [] ∧ wt.conflicts = [])
  let (emptyRes, sEmpty) :=
    (api.commit wt.path { message := "empty", allowEmpty := false }).run s₀
  let (okRes, sOk) :=
    (api.commit wt.path { message := "allow", allowEmpty := true }).run s₀
  NondetTest.assert (∃ e, emptyRes = .error e ∧ e.kind = .nothingToCommit ∧ sEmpty = s₀)
  match okRes with
  | .error _ => NondetTest.assert False
  | .ok cid =>
    let (hcRes, _) := (api.headCommit? wt.path).run sOk
    NondetTest.assert (hcRes = .ok (some cid))

/-- `worktreeAdd` rejects checking out a branch already attached in another worktree with `.branchInUse`. -/
def test_git_api_worktreeAdd_branchInUseRejected
    {runner} [NondetTest runner] (api : GitApiM (StateM RepoState)) : runner Unit := do
  let s₀ ← nondet RepoState
  let mainWt ← nondet WorktreeSlot
  let b ← nondet RefName
  let c ← nondet CommitId
  let newWtPath ← nondet String
  assume (ValidRepoState s₀)
  assume (s₀.worktrees = [mainWt] ∧ mainWt.head = .attached b (some c))
  assume (isValidPathArg newWtPath = true ∧ newWtPath ≠ mainWt.path)
  let (res, s₁) :=
    (api.worktreeAdd mainWt.path { path := newWtPath, target? := some b.raw }).run s₀
  NondetTest.assert (∃ e, res = .error e ∧ e.kind = .branchInUse ∧ s₁ = s₀)

/-- `checkout` refuses dirty worktrees with `.dirtyWorktree` when `force = false`. -/
def test_git_api_checkout_dirtyWorktreeRejected
    {runner} [NondetTest runner] (api : GitApiM (StateM RepoState)) : runner Unit := do
  let s₀ ← nondet RepoState
  let mainWt ← nondet WorktreeSlot
  let b ← nondet RefName
  let c ← nondet CommitId
  assume (ValidRepoState s₀)
  assume (s₀.worktrees = [mainWt] ∧ !mainWt.isBare ∧ isWorktreeDirty mainWt = true)
  assume ((b, c) ∈ s₀.branches)
  let (res, s₁) := (api.checkout mainWt.path (.branch b) false).run s₀
  NondetTest.assert (∃ e, res = .error e ∧ e.kind = .dirtyWorktree ∧ s₁ = s₀)

/-- `withWorktree` runs cleanup on both `.ok` and `.error` action outcomes, preserving action errors over cleanup errors and surfacing cleanup errors only when action succeeded. -/
def test_git_api_withWorktree_cleanupAndErrorPrecedence
    {runner} [NondetTest runner]
    (mkApi : RawGitOpsM (StateM GitCliMockState) → GitApiM (StateM GitCliMockState)) :
    runner Unit := do
  let repoPath ← nondet String
  let wtPath ← nondet String
  let actOk ← nondet Bool
  let cleanOk ← nondet Bool
  assume (isValidPathArg repoPath = true ∧ isValidPathArg wtPath = true)
  let handlerFn : GitRawRequest → Nat → Except GitError GitRawOutput := fun _ idx =>
    if idx == 0 then
      .ok { exitCode := 0, stdout := ByteArray.empty, stderr := ByteArray.empty }
    else if cleanOk then
      .ok { exitCode := 0, stdout := ByteArray.empty, stderr := ByteArray.empty }
    else
      .ok { exitCode := 1, stdout := ByteArray.empty, stderr := "remove failed".toUTF8 }
  let st₀ : GitCliMockState := { handler := handlerFn }
  let api := mkApi mockRawOps
  let opts : WorktreeAddOptions := { path := wtPath, detach := true }
  let actErr : GitError := { kind := .invalidInput, message := "action failed" }
  let cleanAction : String → StateM GitCliMockState (Except GitError Nat) := fun _ =>
    if actOk then pure (.ok 42) else pure (.error actErr)
  let (res, st₁) := (api.withWorktree repoPath opts cleanAction).run st₀
  NondetTest.assert (st₁.callCount = 2)
  if actOk && cleanOk then
    NondetTest.assert (res = .ok 42)
  else if actOk && !cleanOk then
    NondetTest.assert (∃ e, res = .error e ∧ e.kind = .commandFailed)
  else
    NondetTest.assert (res = .error actErr)

/-- `Impl.mkApiM` strips inherited `GIT_*` keys on every call, classifies stdout-only `"nothing to commit"`, returns `none` for directories in `showFile?`, and blocks option injection. -/
def test_git_raw_mkApi_isolationAndGuards
    {runner} [NondetTest runner]
    (mkApi : RawGitOpsM (StateM GitCliMockState) → GitApiM (StateM GitCliMockState)) :
    runner Unit := do
  let st₀ : GitCliMockState :=
    { inheritedEnv := #[("GIT_DIR", "/evil/.git"), ("GIT_TERMINAL_PROMPT", "1"), ("PATH", "/usr/bin")]
      handler := fun req _ =>
        if req.args.toList.contains "commit" then
          .ok { exitCode := 1, stdout := "nothing to commit, working tree clean\n".toUTF8, stderr := ByteArray.empty }
        else if req.args.toList.contains "rev-parse" then
          .ok { exitCode := 0, stdout := (String.ofList (List.replicate 40 'a') ++ "\n").toUTF8, stderr := ByteArray.empty }
        else if req.args.toList.contains "cat-file" then
          .ok { exitCode := 0, stdout := "tree\n".toUTF8, stderr := ByteArray.empty }
        else
          .ok { exitCode := 0, stdout := ByteArray.empty, stderr := ByteArray.empty } }
  let api := mkApi mockRawOps
  let (cRes, stCommit) := (api.commit "/repo" { message := "msg" }).run st₀
  let (sRes, stShow) := (api.showFile? "/repo" "HEAD" "subdir").run st₀
  let (fRes, stFetch) := (api.fetch "/repo" "--upload-pack=evil" none false).run st₀
  let (aRes, stAdd) := (api.add "/repo" #[] false).run st₀
  let (colonRes, stColon) := (api.showFile? "/repo" "HEAD:etc/passwd" "a").run st₀
  NondetTest.assert (∃ e, cRes = .error e ∧ e.kind = .nothingToCommit)
  NondetTest.assert (stCommit.recordedEnvs.all fun env =>
    env.toList.contains ("GIT_DIR", none) ∧
    env.toList.contains ("GIT_TERMINAL_PROMPT", some "0") ∧
    env.toList.contains ("GIT_CONFIG_VALUE_0", some "all"))
  NondetTest.assert (sRes = .ok none ∧ stShow.callCount = 2)
  NondetTest.assert (∃ e, fRes = .error e ∧ e.kind = .invalidInput ∧ stFetch.callCount = 0)
  NondetTest.assert (∃ e, aRes = .error e ∧ e.kind = .invalidInput ∧ stAdd.callCount = 0)
  NondetTest.assert (∃ e, colonRes = .error e ∧ e.kind = .invalidInput ∧ stColon.callCount = 0)

/-- External trust boundary assumptions for real `git` CLI subprocesses (`>= 2.30`) grounded in `RuntimeTests.lean`. -/
structure EmpiricalAssumptions where
  /-- `git` CLI (`>= 2.30`) honors `GIT_TERMINAL_PROMPT=0` and `GIT_CONFIG_KEY_0=safe.bareRepository` / `all` when inherited `GIT_*` keys are unset. -/
  envIsolationRespected : Prop
  /-- `git status --porcelain=v1 -z` emits `XY PATH1\0` (and `XY PATH1\0PATH2\0` with destination first for `R`/`C`). -/
  porcelainStatusZFormat : Prop
  /-- `git diff --name-status -z` emits `OP\0PATH\0` (and `Rscore\0SRC\0DEST\0` with source first for `R`/`C`). -/
  diffNameStatusZFormat : Prop
  /-- `git worktree list --porcelain -z` emits `\0\0`-terminated stanzas (`bare` optionally omitting `HEAD`, `000...0` for unborn `HEAD`). -/
  worktreeListPorcelainFormat : Prop
  /-- `git merge-base a b` returns `none` iff `commonAncestors = []`, and otherwise returns some minimal common ancestor (matching `Model.mergeBase?` when the LCA is unique). -/
  mergeBaseMinimalCommonAncestor : Prop

/-- Empirical contract (grounded in `RuntimeTests.lean`): `parsePorcelainStatusZ` round-trips real `git status --porcelain=v1 -z` outputs including spaces and renames. -/
def empirical_git_status_parsesRealOutput
    {runner} [NondetTest runner]
    (parseFn : ByteArray → Except GitError (Array StatusEntry)) : runner Unit := do
  let raw := " M a b.txt\x00R  new name.txt\x00old name.txt\x00?? untrack.txt\x00".toUTF8
  NondetTest.assert (parseFn raw = .ok #[
    { indexStatus := none, worktreeStatus := some .modified, path := "a b.txt" },
    { indexStatus := some .renamed, worktreeStatus := none, path := "new name.txt", origPath := some "old name.txt" },
    { indexStatus := some .untracked, worktreeStatus := some .untracked, path := "untrack.txt" }
  ])

/-- Empirical contract (grounded in `RuntimeTests.lean`): `parseWorktreeListPorcelain` parses real `git worktree list --porcelain -z` stanzas. -/
def empirical_git_worktreeList_parsesRealOutput
    {runner} [NondetTest runner]
    (parseFn : ByteArray → Except GitError (Array WorktreeInfo)) : runner Unit := do
  let sha := String.ofList (List.replicate 40 'a')
  let raw := ("worktree /tmp/main\x00HEAD " ++ sha ++ "\x00branch refs/heads/main\x00\x00worktree /tmp/wt\x00HEAD " ++ sha ++ "\x00detached\x00\x00").toUTF8
  NondetTest.assert (parseFn raw = .ok #[
    { path := "/tmp/main", head? := some { hex := sha }, branch? := some { raw := "main" } },
    { path := "/tmp/wt", head? := some { hex := sha }, branch? := none, isDetached := true }
  ])

example : cleanGitEnv #[("GIT_DIR", "/bad"), ("HOME", "/home/u")] #[("GIT_TERMINAL_PROMPT", some "1"), ("GIT_AUTHOR_NAME", some "A"), ("FOO", some "bar")] =
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
  have h0 := h s0 wt b c0 "/wt2" hValid ⟨rfl, rfl⟩ ⟨by decide, by decide⟩
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

end LeanSwe.Git
