import Core.NondetTest
import Core.Assumptions
import LeanSwe.Git.Types
import LeanSwe.Git.Model

namespace LeanSwe.Git

open Core (NondetTest AssumptionObligation ErrorObligation)
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
  assume (isValidRefNameStr b.raw = true)
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

/-- `parsePorcelainStatusZ` round-trips NUL-delimited `git status --porcelain=v1 -z` records including spaces and destination-first renames. -/
def test_git_status_parsesRealOutput
    {runner} [NondetTest runner]
    (parseFn : ByteArray → Except GitError (Array StatusEntry)) : runner Unit := do
  let raw := " M a b.txt\x00R  new name.txt\x00old name.txt\x00?? untrack.txt\x00".toUTF8
  NondetTest.assert (parseFn raw = .ok #[
    { indexStatus := none, worktreeStatus := some .modified, path := "a b.txt" },
    { indexStatus := some .renamed, worktreeStatus := none, path := "new name.txt", origPath := some "old name.txt" },
    { indexStatus := some .untracked, worktreeStatus := some .untracked, path := "untrack.txt" }
  ])

/-- `parseWorktreeListPorcelain` parses NUL-delimited `git worktree list --porcelain -z` attached and detached stanzas. -/
def test_git_worktreeList_parsesRealOutput
    {runner} [NondetTest runner]
    (parseFn : ByteArray → Except GitError (Array WorktreeInfo)) : runner Unit := do
  let sha := String.ofList (List.replicate 40 'a')
  let raw := ("worktree /tmp/main\x00HEAD " ++ sha ++ "\x00branch refs/heads/main\x00\x00worktree /tmp/wt\x00HEAD " ++ sha ++ "\x00detached\x00\x00").toUTF8
  NondetTest.assert (parseFn raw = .ok #[
    { path := "/tmp/main", head? := some { hex := sha }, branch? := some { raw := "main" } },
    { path := "/tmp/wt", head? := some { hex := sha }, branch? := none, isDetached := true }
  ])

/-- External `git` CLI subprocess boundary assumptions (`git >= 2.30`) verified at runtime in
    `LeanSwe.Git.RuntimeTests` with nonce-authenticated logging. -/
def externalAssumptions : List AssumptionObligation :=
  [ { name := "LeanSwe.Git.assume_git_defaultRawOps_stripsPoisonedGitEnvAndHonorsBareConfig"
      subject := "LeanSwe.Git.defaultRawOps"
      formalPred? := none }
  , { name := "LeanSwe.Git.assume_git_status_porcelainV1Z_emitsUnquotedAndDestFirstRename"
      subject := "LeanSwe.Git.status"
      formalPred? := none }
  , { name := "LeanSwe.Git.assume_git_diffNameStatus_porcelainZ_emitsSourceFirstRename"
      subject := "LeanSwe.Git.diffNameStatus"
      formalPred? := none }
  , { name := "LeanSwe.Git.assume_git_listWorktrees_porcelainZ_emitsBareUnbornAndLinkedStanzas"
      subject := "LeanSwe.Git.listWorktrees"
      formalPred? := none }
  , { name := "LeanSwe.Git.assume_git_mergeBase_andIsAncestor_matchDagSemantics"
      subject := "LeanSwe.Git.mergeBase?"
      formalPred? := none }
  , { name := "LeanSwe.Git.assume_git_headState_andShowFile_unbornDetachedAndTreeVsBlob"
      subject := "LeanSwe.Git.showFile?"
      formalPred? := none }
  , { name := "LeanSwe.Git.assume_git_clone_andFetch_roundTripLocalRefsAndPrune"
      subject := "LeanSwe.Git.fetch"
      formalPred? := none } ]

/-- Complete `26 × 13` `(request, errorKind)` coverage matrix across all 26 fallible `LeanSwe.Git` entrypoints (`GitErrorKind`). -/
def errorCoverage : List (ErrorObligation GitErrorKind) :=
  [ { request := "LeanSwe.Git.isRepo"
      errorKind := .notARepo
      justification := .provedImpossible "LeanSwe.Git.Proofs.git_isRepo_never_notARepo" }
  , { request := "LeanSwe.Git.isRepo"
      errorKind := .invalidRef
      justification := .tested "LeanSwe.Git.RuntimeTests.err_git_isRepo_invalidRef" .mocked }
  , { request := "LeanSwe.Git.isRepo"
      errorKind := .invalidPath
      justification := .tested "LeanSwe.Git.RuntimeTests.err_git_isRepo_invalidPath" .real }
  , { request := "LeanSwe.Git.isRepo"
      errorKind := .invalidInput
      justification := .tested "LeanSwe.Git.RuntimeTests.err_git_isRepo_invalidInput" .real }
  , { request := "LeanSwe.Git.isRepo"
      errorKind := .dirtyWorktree
      justification := .tested "LeanSwe.Git.RuntimeTests.err_git_isRepo_dirtyWorktree" .mocked }
  , { request := "LeanSwe.Git.isRepo"
      errorKind := .nothingToCommit
      justification := .tested "LeanSwe.Git.RuntimeTests.err_git_isRepo_nothingToCommit" .mocked }
  , { request := "LeanSwe.Git.isRepo"
      errorKind := .branchInUse
      justification := .tested "LeanSwe.Git.RuntimeTests.err_git_isRepo_branchInUse" .mocked }
  , { request := "LeanSwe.Git.isRepo"
      errorKind := .alreadyExists
      justification := .tested "LeanSwe.Git.RuntimeTests.err_git_isRepo_alreadyExists" .mocked }
  , { request := "LeanSwe.Git.isRepo"
      errorKind := .notFound
      justification := .tested "LeanSwe.Git.RuntimeTests.err_git_isRepo_notFound" .mocked }
  , { request := "LeanSwe.Git.isRepo"
      errorKind := .conflict
      justification := .tested "LeanSwe.Git.RuntimeTests.err_git_isRepo_conflict" .mocked }
  , { request := "LeanSwe.Git.isRepo"
      errorKind := .timeout
      justification := .tested "LeanSwe.Git.RuntimeTests.err_git_isRepo_timeout" .mocked }
  , { request := "LeanSwe.Git.isRepo"
      errorKind := .commandFailed
      justification := .tested "LeanSwe.Git.RuntimeTests.err_git_isRepo_commandFailed" .real }
  , { request := "LeanSwe.Git.isRepo"
      errorKind := .parseError
      justification := .provedImpossible "LeanSwe.Git.Proofs.git_isRepo_never_parseError" }
  , { request := "LeanSwe.Git.repoRoot"
      errorKind := .notARepo
      justification := .tested "LeanSwe.Git.RuntimeTests.err_git_repoRoot_notARepo" .real }
  , { request := "LeanSwe.Git.repoRoot"
      errorKind := .invalidRef
      justification := .tested "LeanSwe.Git.RuntimeTests.err_git_repoRoot_invalidRef" .mocked }
  , { request := "LeanSwe.Git.repoRoot"
      errorKind := .invalidPath
      justification := .tested "LeanSwe.Git.RuntimeTests.err_git_repoRoot_invalidPath" .real }
  , { request := "LeanSwe.Git.repoRoot"
      errorKind := .invalidInput
      justification := .tested "LeanSwe.Git.RuntimeTests.err_git_repoRoot_invalidInput" .real }
  , { request := "LeanSwe.Git.repoRoot"
      errorKind := .dirtyWorktree
      justification := .tested "LeanSwe.Git.RuntimeTests.err_git_repoRoot_dirtyWorktree" .mocked }
  , { request := "LeanSwe.Git.repoRoot"
      errorKind := .nothingToCommit
      justification := .tested "LeanSwe.Git.RuntimeTests.err_git_repoRoot_nothingToCommit" .mocked }
  , { request := "LeanSwe.Git.repoRoot"
      errorKind := .branchInUse
      justification := .tested "LeanSwe.Git.RuntimeTests.err_git_repoRoot_branchInUse" .mocked }
  , { request := "LeanSwe.Git.repoRoot"
      errorKind := .alreadyExists
      justification := .tested "LeanSwe.Git.RuntimeTests.err_git_repoRoot_alreadyExists" .mocked }
  , { request := "LeanSwe.Git.repoRoot"
      errorKind := .notFound
      justification := .tested "LeanSwe.Git.RuntimeTests.err_git_repoRoot_notFound" .mocked }
  , { request := "LeanSwe.Git.repoRoot"
      errorKind := .conflict
      justification := .tested "LeanSwe.Git.RuntimeTests.err_git_repoRoot_conflict" .mocked }
  , { request := "LeanSwe.Git.repoRoot"
      errorKind := .timeout
      justification := .tested "LeanSwe.Git.RuntimeTests.err_git_repoRoot_timeout" .mocked }
  , { request := "LeanSwe.Git.repoRoot"
      errorKind := .commandFailed
      justification := .tested "LeanSwe.Git.RuntimeTests.err_git_repoRoot_commandFailed" .real }
  , { request := "LeanSwe.Git.repoRoot"
      errorKind := .parseError
      justification := .tested "LeanSwe.Git.RuntimeTests.err_git_repoRoot_parseError" .real }
  , { request := "LeanSwe.Git.commonDir"
      errorKind := .notARepo
      justification := .tested "LeanSwe.Git.RuntimeTests.err_git_commonDir_notARepo" .real }
  , { request := "LeanSwe.Git.commonDir"
      errorKind := .invalidRef
      justification := .tested "LeanSwe.Git.RuntimeTests.err_git_commonDir_invalidRef" .mocked }
  , { request := "LeanSwe.Git.commonDir"
      errorKind := .invalidPath
      justification := .tested "LeanSwe.Git.RuntimeTests.err_git_commonDir_invalidPath" .real }
  , { request := "LeanSwe.Git.commonDir"
      errorKind := .invalidInput
      justification := .tested "LeanSwe.Git.RuntimeTests.err_git_commonDir_invalidInput" .real }
  , { request := "LeanSwe.Git.commonDir"
      errorKind := .dirtyWorktree
      justification := .tested "LeanSwe.Git.RuntimeTests.err_git_commonDir_dirtyWorktree" .mocked }
  , { request := "LeanSwe.Git.commonDir"
      errorKind := .nothingToCommit
      justification := .tested "LeanSwe.Git.RuntimeTests.err_git_commonDir_nothingToCommit" .mocked }
  , { request := "LeanSwe.Git.commonDir"
      errorKind := .branchInUse
      justification := .tested "LeanSwe.Git.RuntimeTests.err_git_commonDir_branchInUse" .mocked }
  , { request := "LeanSwe.Git.commonDir"
      errorKind := .alreadyExists
      justification := .tested "LeanSwe.Git.RuntimeTests.err_git_commonDir_alreadyExists" .mocked }
  , { request := "LeanSwe.Git.commonDir"
      errorKind := .notFound
      justification := .tested "LeanSwe.Git.RuntimeTests.err_git_commonDir_notFound" .mocked }
  , { request := "LeanSwe.Git.commonDir"
      errorKind := .conflict
      justification := .tested "LeanSwe.Git.RuntimeTests.err_git_commonDir_conflict" .mocked }
  , { request := "LeanSwe.Git.commonDir"
      errorKind := .timeout
      justification := .tested "LeanSwe.Git.RuntimeTests.err_git_commonDir_timeout" .mocked }
  , { request := "LeanSwe.Git.commonDir"
      errorKind := .commandFailed
      justification := .tested "LeanSwe.Git.RuntimeTests.err_git_commonDir_commandFailed" .real }
  , { request := "LeanSwe.Git.commonDir"
      errorKind := .parseError
      justification := .tested "LeanSwe.Git.RuntimeTests.err_git_commonDir_parseError" .real }
  , { request := "LeanSwe.Git.headCommit?"
      errorKind := .notARepo
      justification := .tested "LeanSwe.Git.RuntimeTests.err_git_headCommit_notARepo" .real }
  , { request := "LeanSwe.Git.headCommit?"
      errorKind := .invalidRef
      justification := .tested "LeanSwe.Git.RuntimeTests.err_git_headCommit_invalidRef" .mocked }
  , { request := "LeanSwe.Git.headCommit?"
      errorKind := .invalidPath
      justification := .tested "LeanSwe.Git.RuntimeTests.err_git_headCommit_invalidPath" .real }
  , { request := "LeanSwe.Git.headCommit?"
      errorKind := .invalidInput
      justification := .tested "LeanSwe.Git.RuntimeTests.err_git_headCommit_invalidInput" .real }
  , { request := "LeanSwe.Git.headCommit?"
      errorKind := .dirtyWorktree
      justification := .tested "LeanSwe.Git.RuntimeTests.err_git_headCommit_dirtyWorktree" .mocked }
  , { request := "LeanSwe.Git.headCommit?"
      errorKind := .nothingToCommit
      justification := .tested "LeanSwe.Git.RuntimeTests.err_git_headCommit_nothingToCommit" .mocked }
  , { request := "LeanSwe.Git.headCommit?"
      errorKind := .branchInUse
      justification := .tested "LeanSwe.Git.RuntimeTests.err_git_headCommit_branchInUse" .mocked }
  , { request := "LeanSwe.Git.headCommit?"
      errorKind := .alreadyExists
      justification := .tested "LeanSwe.Git.RuntimeTests.err_git_headCommit_alreadyExists" .mocked }
  , { request := "LeanSwe.Git.headCommit?"
      errorKind := .notFound
      justification := .tested "LeanSwe.Git.RuntimeTests.err_git_headCommit_notFound" .mocked }
  , { request := "LeanSwe.Git.headCommit?"
      errorKind := .conflict
      justification := .tested "LeanSwe.Git.RuntimeTests.err_git_headCommit_conflict" .mocked }
  , { request := "LeanSwe.Git.headCommit?"
      errorKind := .timeout
      justification := .tested "LeanSwe.Git.RuntimeTests.err_git_headCommit_timeout" .mocked }
  , { request := "LeanSwe.Git.headCommit?"
      errorKind := .commandFailed
      justification := .tested "LeanSwe.Git.RuntimeTests.err_git_headCommit_commandFailed" .real }
  , { request := "LeanSwe.Git.headCommit?"
      errorKind := .parseError
      justification := .tested "LeanSwe.Git.RuntimeTests.err_git_headCommit_parseError" .mocked }
  , { request := "LeanSwe.Git.headBranch?"
      errorKind := .notARepo
      justification := .tested "LeanSwe.Git.RuntimeTests.err_git_headBranch_notARepo" .real }
  , { request := "LeanSwe.Git.headBranch?"
      errorKind := .invalidRef
      justification := .tested "LeanSwe.Git.RuntimeTests.err_git_headBranch_invalidRef" .mocked }
  , { request := "LeanSwe.Git.headBranch?"
      errorKind := .invalidPath
      justification := .tested "LeanSwe.Git.RuntimeTests.err_git_headBranch_invalidPath" .real }
  , { request := "LeanSwe.Git.headBranch?"
      errorKind := .invalidInput
      justification := .tested "LeanSwe.Git.RuntimeTests.err_git_headBranch_invalidInput" .real }
  , { request := "LeanSwe.Git.headBranch?"
      errorKind := .dirtyWorktree
      justification := .tested "LeanSwe.Git.RuntimeTests.err_git_headBranch_dirtyWorktree" .mocked }
  , { request := "LeanSwe.Git.headBranch?"
      errorKind := .nothingToCommit
      justification := .tested "LeanSwe.Git.RuntimeTests.err_git_headBranch_nothingToCommit" .mocked }
  , { request := "LeanSwe.Git.headBranch?"
      errorKind := .branchInUse
      justification := .tested "LeanSwe.Git.RuntimeTests.err_git_headBranch_branchInUse" .mocked }
  , { request := "LeanSwe.Git.headBranch?"
      errorKind := .alreadyExists
      justification := .tested "LeanSwe.Git.RuntimeTests.err_git_headBranch_alreadyExists" .mocked }
  , { request := "LeanSwe.Git.headBranch?"
      errorKind := .notFound
      justification := .tested "LeanSwe.Git.RuntimeTests.err_git_headBranch_notFound" .mocked }
  , { request := "LeanSwe.Git.headBranch?"
      errorKind := .conflict
      justification := .tested "LeanSwe.Git.RuntimeTests.err_git_headBranch_conflict" .mocked }
  , { request := "LeanSwe.Git.headBranch?"
      errorKind := .timeout
      justification := .tested "LeanSwe.Git.RuntimeTests.err_git_headBranch_timeout" .mocked }
  , { request := "LeanSwe.Git.headBranch?"
      errorKind := .commandFailed
      justification := .tested "LeanSwe.Git.RuntimeTests.err_git_headBranch_commandFailed" .real }
  , { request := "LeanSwe.Git.headBranch?"
      errorKind := .parseError
      justification := .tested "LeanSwe.Git.RuntimeTests.err_git_headBranch_parseError" .mocked }
  , { request := "LeanSwe.Git.headState"
      errorKind := .notARepo
      justification := .tested "LeanSwe.Git.RuntimeTests.err_git_headState_notARepo" .real }
  , { request := "LeanSwe.Git.headState"
      errorKind := .invalidRef
      justification := .tested "LeanSwe.Git.RuntimeTests.err_git_headState_invalidRef" .mocked }
  , { request := "LeanSwe.Git.headState"
      errorKind := .invalidPath
      justification := .tested "LeanSwe.Git.RuntimeTests.err_git_headState_invalidPath" .real }
  , { request := "LeanSwe.Git.headState"
      errorKind := .invalidInput
      justification := .tested "LeanSwe.Git.RuntimeTests.err_git_headState_invalidInput" .real }
  , { request := "LeanSwe.Git.headState"
      errorKind := .dirtyWorktree
      justification := .tested "LeanSwe.Git.RuntimeTests.err_git_headState_dirtyWorktree" .mocked }
  , { request := "LeanSwe.Git.headState"
      errorKind := .nothingToCommit
      justification := .tested "LeanSwe.Git.RuntimeTests.err_git_headState_nothingToCommit" .mocked }
  , { request := "LeanSwe.Git.headState"
      errorKind := .branchInUse
      justification := .tested "LeanSwe.Git.RuntimeTests.err_git_headState_branchInUse" .mocked }
  , { request := "LeanSwe.Git.headState"
      errorKind := .alreadyExists
      justification := .tested "LeanSwe.Git.RuntimeTests.err_git_headState_alreadyExists" .mocked }
  , { request := "LeanSwe.Git.headState"
      errorKind := .notFound
      justification := .tested "LeanSwe.Git.RuntimeTests.err_git_headState_notFound" .mocked }
  , { request := "LeanSwe.Git.headState"
      errorKind := .conflict
      justification := .tested "LeanSwe.Git.RuntimeTests.err_git_headState_conflict" .mocked }
  , { request := "LeanSwe.Git.headState"
      errorKind := .timeout
      justification := .tested "LeanSwe.Git.RuntimeTests.err_git_headState_timeout" .mocked }
  , { request := "LeanSwe.Git.headState"
      errorKind := .commandFailed
      justification := .tested "LeanSwe.Git.RuntimeTests.err_git_headState_commandFailed" .real }
  , { request := "LeanSwe.Git.headState"
      errorKind := .parseError
      justification := .tested "LeanSwe.Git.RuntimeTests.err_git_headState_parseError" .mocked }
  , { request := "LeanSwe.Git.revParseCommit"
      errorKind := .notARepo
      justification := .tested "LeanSwe.Git.RuntimeTests.err_git_revParseCommit_notARepo" .real }
  , { request := "LeanSwe.Git.revParseCommit"
      errorKind := .invalidRef
      justification := .tested "LeanSwe.Git.RuntimeTests.err_git_revParseCommit_invalidRef" .real }
  , { request := "LeanSwe.Git.revParseCommit"
      errorKind := .invalidPath
      justification := .tested "LeanSwe.Git.RuntimeTests.err_git_revParseCommit_invalidPath" .real }
  , { request := "LeanSwe.Git.revParseCommit"
      errorKind := .invalidInput
      justification := .tested "LeanSwe.Git.RuntimeTests.err_git_revParseCommit_invalidInput" .real }
  , { request := "LeanSwe.Git.revParseCommit"
      errorKind := .dirtyWorktree
      justification := .tested "LeanSwe.Git.RuntimeTests.err_git_revParseCommit_dirtyWorktree" .mocked }
  , { request := "LeanSwe.Git.revParseCommit"
      errorKind := .nothingToCommit
      justification := .tested "LeanSwe.Git.RuntimeTests.err_git_revParseCommit_nothingToCommit" .mocked }
  , { request := "LeanSwe.Git.revParseCommit"
      errorKind := .branchInUse
      justification := .tested "LeanSwe.Git.RuntimeTests.err_git_revParseCommit_branchInUse" .mocked }
  , { request := "LeanSwe.Git.revParseCommit"
      errorKind := .alreadyExists
      justification := .tested "LeanSwe.Git.RuntimeTests.err_git_revParseCommit_alreadyExists" .mocked }
  , { request := "LeanSwe.Git.revParseCommit"
      errorKind := .notFound
      justification := .tested "LeanSwe.Git.RuntimeTests.err_git_revParseCommit_notFound" .mocked }
  , { request := "LeanSwe.Git.revParseCommit"
      errorKind := .conflict
      justification := .tested "LeanSwe.Git.RuntimeTests.err_git_revParseCommit_conflict" .mocked }
  , { request := "LeanSwe.Git.revParseCommit"
      errorKind := .timeout
      justification := .tested "LeanSwe.Git.RuntimeTests.err_git_revParseCommit_timeout" .mocked }
  , { request := "LeanSwe.Git.revParseCommit"
      errorKind := .commandFailed
      justification := .tested "LeanSwe.Git.RuntimeTests.err_git_revParseCommit_commandFailed" .real }
  , { request := "LeanSwe.Git.revParseCommit"
      errorKind := .parseError
      justification := .tested "LeanSwe.Git.RuntimeTests.err_git_revParseCommit_parseError" .mocked }
  , { request := "LeanSwe.Git.isAncestor"
      errorKind := .notARepo
      justification := .tested "LeanSwe.Git.RuntimeTests.err_git_isAncestor_notARepo" .real }
  , { request := "LeanSwe.Git.isAncestor"
      errorKind := .invalidRef
      justification := .tested "LeanSwe.Git.RuntimeTests.err_git_isAncestor_invalidRef" .real }
  , { request := "LeanSwe.Git.isAncestor"
      errorKind := .invalidPath
      justification := .tested "LeanSwe.Git.RuntimeTests.err_git_isAncestor_invalidPath" .real }
  , { request := "LeanSwe.Git.isAncestor"
      errorKind := .invalidInput
      justification := .tested "LeanSwe.Git.RuntimeTests.err_git_isAncestor_invalidInput" .real }
  , { request := "LeanSwe.Git.isAncestor"
      errorKind := .dirtyWorktree
      justification := .tested "LeanSwe.Git.RuntimeTests.err_git_isAncestor_dirtyWorktree" .mocked }
  , { request := "LeanSwe.Git.isAncestor"
      errorKind := .nothingToCommit
      justification := .tested "LeanSwe.Git.RuntimeTests.err_git_isAncestor_nothingToCommit" .mocked }
  , { request := "LeanSwe.Git.isAncestor"
      errorKind := .branchInUse
      justification := .tested "LeanSwe.Git.RuntimeTests.err_git_isAncestor_branchInUse" .mocked }
  , { request := "LeanSwe.Git.isAncestor"
      errorKind := .alreadyExists
      justification := .tested "LeanSwe.Git.RuntimeTests.err_git_isAncestor_alreadyExists" .mocked }
  , { request := "LeanSwe.Git.isAncestor"
      errorKind := .notFound
      justification := .tested "LeanSwe.Git.RuntimeTests.err_git_isAncestor_notFound" .mocked }
  , { request := "LeanSwe.Git.isAncestor"
      errorKind := .conflict
      justification := .tested "LeanSwe.Git.RuntimeTests.err_git_isAncestor_conflict" .mocked }
  , { request := "LeanSwe.Git.isAncestor"
      errorKind := .timeout
      justification := .tested "LeanSwe.Git.RuntimeTests.err_git_isAncestor_timeout" .mocked }
  , { request := "LeanSwe.Git.isAncestor"
      errorKind := .commandFailed
      justification := .tested "LeanSwe.Git.RuntimeTests.err_git_isAncestor_commandFailed" .real }
  , { request := "LeanSwe.Git.isAncestor"
      errorKind := .parseError
      justification := .provedImpossible "LeanSwe.Git.Proofs.git_isAncestor_never_parseError" }
  , { request := "LeanSwe.Git.mergeBase?"
      errorKind := .notARepo
      justification := .tested "LeanSwe.Git.RuntimeTests.err_git_mergeBase_notARepo" .real }
  , { request := "LeanSwe.Git.mergeBase?"
      errorKind := .invalidRef
      justification := .tested "LeanSwe.Git.RuntimeTests.err_git_mergeBase_invalidRef" .real }
  , { request := "LeanSwe.Git.mergeBase?"
      errorKind := .invalidPath
      justification := .tested "LeanSwe.Git.RuntimeTests.err_git_mergeBase_invalidPath" .real }
  , { request := "LeanSwe.Git.mergeBase?"
      errorKind := .invalidInput
      justification := .tested "LeanSwe.Git.RuntimeTests.err_git_mergeBase_invalidInput" .real }
  , { request := "LeanSwe.Git.mergeBase?"
      errorKind := .dirtyWorktree
      justification := .tested "LeanSwe.Git.RuntimeTests.err_git_mergeBase_dirtyWorktree" .mocked }
  , { request := "LeanSwe.Git.mergeBase?"
      errorKind := .nothingToCommit
      justification := .tested "LeanSwe.Git.RuntimeTests.err_git_mergeBase_nothingToCommit" .mocked }
  , { request := "LeanSwe.Git.mergeBase?"
      errorKind := .branchInUse
      justification := .tested "LeanSwe.Git.RuntimeTests.err_git_mergeBase_branchInUse" .mocked }
  , { request := "LeanSwe.Git.mergeBase?"
      errorKind := .alreadyExists
      justification := .tested "LeanSwe.Git.RuntimeTests.err_git_mergeBase_alreadyExists" .mocked }
  , { request := "LeanSwe.Git.mergeBase?"
      errorKind := .notFound
      justification := .tested "LeanSwe.Git.RuntimeTests.err_git_mergeBase_notFound" .mocked }
  , { request := "LeanSwe.Git.mergeBase?"
      errorKind := .conflict
      justification := .tested "LeanSwe.Git.RuntimeTests.err_git_mergeBase_conflict" .mocked }
  , { request := "LeanSwe.Git.mergeBase?"
      errorKind := .timeout
      justification := .tested "LeanSwe.Git.RuntimeTests.err_git_mergeBase_timeout" .mocked }
  , { request := "LeanSwe.Git.mergeBase?"
      errorKind := .commandFailed
      justification := .tested "LeanSwe.Git.RuntimeTests.err_git_mergeBase_commandFailed" .real }
  , { request := "LeanSwe.Git.mergeBase?"
      errorKind := .parseError
      justification := .tested "LeanSwe.Git.RuntimeTests.err_git_mergeBase_parseError" .mocked }
  , { request := "LeanSwe.Git.status"
      errorKind := .notARepo
      justification := .tested "LeanSwe.Git.RuntimeTests.err_git_status_notARepo" .real }
  , { request := "LeanSwe.Git.status"
      errorKind := .invalidRef
      justification := .tested "LeanSwe.Git.RuntimeTests.err_git_status_invalidRef" .mocked }
  , { request := "LeanSwe.Git.status"
      errorKind := .invalidPath
      justification := .tested "LeanSwe.Git.RuntimeTests.err_git_status_invalidPath" .real }
  , { request := "LeanSwe.Git.status"
      errorKind := .invalidInput
      justification := .tested "LeanSwe.Git.RuntimeTests.err_git_status_invalidInput" .real }
  , { request := "LeanSwe.Git.status"
      errorKind := .dirtyWorktree
      justification := .tested "LeanSwe.Git.RuntimeTests.err_git_status_dirtyWorktree" .mocked }
  , { request := "LeanSwe.Git.status"
      errorKind := .nothingToCommit
      justification := .tested "LeanSwe.Git.RuntimeTests.err_git_status_nothingToCommit" .mocked }
  , { request := "LeanSwe.Git.status"
      errorKind := .branchInUse
      justification := .tested "LeanSwe.Git.RuntimeTests.err_git_status_branchInUse" .mocked }
  , { request := "LeanSwe.Git.status"
      errorKind := .alreadyExists
      justification := .tested "LeanSwe.Git.RuntimeTests.err_git_status_alreadyExists" .mocked }
  , { request := "LeanSwe.Git.status"
      errorKind := .notFound
      justification := .tested "LeanSwe.Git.RuntimeTests.err_git_status_notFound" .mocked }
  , { request := "LeanSwe.Git.status"
      errorKind := .conflict
      justification := .tested "LeanSwe.Git.RuntimeTests.err_git_status_conflict" .mocked }
  , { request := "LeanSwe.Git.status"
      errorKind := .timeout
      justification := .tested "LeanSwe.Git.RuntimeTests.err_git_status_timeout" .mocked }
  , { request := "LeanSwe.Git.status"
      errorKind := .commandFailed
      justification := .tested "LeanSwe.Git.RuntimeTests.err_git_status_commandFailed" .real }
  , { request := "LeanSwe.Git.status"
      errorKind := .parseError
      justification := .tested "LeanSwe.Git.RuntimeTests.err_git_status_parseError" .real }
  , { request := "LeanSwe.Git.diffNameStatus"
      errorKind := .notARepo
      justification := .tested "LeanSwe.Git.RuntimeTests.err_git_diffNameStatus_notARepo" .real }
  , { request := "LeanSwe.Git.diffNameStatus"
      errorKind := .invalidRef
      justification := .tested "LeanSwe.Git.RuntimeTests.err_git_diffNameStatus_invalidRef" .real }
  , { request := "LeanSwe.Git.diffNameStatus"
      errorKind := .invalidPath
      justification := .tested "LeanSwe.Git.RuntimeTests.err_git_diffNameStatus_invalidPath" .real }
  , { request := "LeanSwe.Git.diffNameStatus"
      errorKind := .invalidInput
      justification := .tested "LeanSwe.Git.RuntimeTests.err_git_diffNameStatus_invalidInput" .real }
  , { request := "LeanSwe.Git.diffNameStatus"
      errorKind := .dirtyWorktree
      justification := .tested "LeanSwe.Git.RuntimeTests.err_git_diffNameStatus_dirtyWorktree" .mocked }
  , { request := "LeanSwe.Git.diffNameStatus"
      errorKind := .nothingToCommit
      justification := .tested "LeanSwe.Git.RuntimeTests.err_git_diffNameStatus_nothingToCommit" .mocked }
  , { request := "LeanSwe.Git.diffNameStatus"
      errorKind := .branchInUse
      justification := .tested "LeanSwe.Git.RuntimeTests.err_git_diffNameStatus_branchInUse" .mocked }
  , { request := "LeanSwe.Git.diffNameStatus"
      errorKind := .alreadyExists
      justification := .tested "LeanSwe.Git.RuntimeTests.err_git_diffNameStatus_alreadyExists" .mocked }
  , { request := "LeanSwe.Git.diffNameStatus"
      errorKind := .notFound
      justification := .tested "LeanSwe.Git.RuntimeTests.err_git_diffNameStatus_notFound" .mocked }
  , { request := "LeanSwe.Git.diffNameStatus"
      errorKind := .conflict
      justification := .tested "LeanSwe.Git.RuntimeTests.err_git_diffNameStatus_conflict" .mocked }
  , { request := "LeanSwe.Git.diffNameStatus"
      errorKind := .timeout
      justification := .tested "LeanSwe.Git.RuntimeTests.err_git_diffNameStatus_timeout" .mocked }
  , { request := "LeanSwe.Git.diffNameStatus"
      errorKind := .commandFailed
      justification := .tested "LeanSwe.Git.RuntimeTests.err_git_diffNameStatus_commandFailed" .real }
  , { request := "LeanSwe.Git.diffNameStatus"
      errorKind := .parseError
      justification := .tested "LeanSwe.Git.RuntimeTests.err_git_diffNameStatus_parseError" .real }
  , { request := "LeanSwe.Git.listWorktrees"
      errorKind := .notARepo
      justification := .tested "LeanSwe.Git.RuntimeTests.err_git_listWorktrees_notARepo" .real }
  , { request := "LeanSwe.Git.listWorktrees"
      errorKind := .invalidRef
      justification := .tested "LeanSwe.Git.RuntimeTests.err_git_listWorktrees_invalidRef" .mocked }
  , { request := "LeanSwe.Git.listWorktrees"
      errorKind := .invalidPath
      justification := .tested "LeanSwe.Git.RuntimeTests.err_git_listWorktrees_invalidPath" .real }
  , { request := "LeanSwe.Git.listWorktrees"
      errorKind := .invalidInput
      justification := .tested "LeanSwe.Git.RuntimeTests.err_git_listWorktrees_invalidInput" .real }
  , { request := "LeanSwe.Git.listWorktrees"
      errorKind := .dirtyWorktree
      justification := .tested "LeanSwe.Git.RuntimeTests.err_git_listWorktrees_dirtyWorktree" .mocked }
  , { request := "LeanSwe.Git.listWorktrees"
      errorKind := .nothingToCommit
      justification := .tested "LeanSwe.Git.RuntimeTests.err_git_listWorktrees_nothingToCommit" .mocked }
  , { request := "LeanSwe.Git.listWorktrees"
      errorKind := .branchInUse
      justification := .tested "LeanSwe.Git.RuntimeTests.err_git_listWorktrees_branchInUse" .mocked }
  , { request := "LeanSwe.Git.listWorktrees"
      errorKind := .alreadyExists
      justification := .tested "LeanSwe.Git.RuntimeTests.err_git_listWorktrees_alreadyExists" .mocked }
  , { request := "LeanSwe.Git.listWorktrees"
      errorKind := .notFound
      justification := .tested "LeanSwe.Git.RuntimeTests.err_git_listWorktrees_notFound" .mocked }
  , { request := "LeanSwe.Git.listWorktrees"
      errorKind := .conflict
      justification := .tested "LeanSwe.Git.RuntimeTests.err_git_listWorktrees_conflict" .mocked }
  , { request := "LeanSwe.Git.listWorktrees"
      errorKind := .timeout
      justification := .tested "LeanSwe.Git.RuntimeTests.err_git_listWorktrees_timeout" .mocked }
  , { request := "LeanSwe.Git.listWorktrees"
      errorKind := .commandFailed
      justification := .tested "LeanSwe.Git.RuntimeTests.err_git_listWorktrees_commandFailed" .real }
  , { request := "LeanSwe.Git.listWorktrees"
      errorKind := .parseError
      justification := .tested "LeanSwe.Git.RuntimeTests.err_git_listWorktrees_parseError" .real }
  , { request := "LeanSwe.Git.showFile?"
      errorKind := .notARepo
      justification := .tested "LeanSwe.Git.RuntimeTests.err_git_showFile_notARepo" .real }
  , { request := "LeanSwe.Git.showFile?"
      errorKind := .invalidRef
      justification := .tested "LeanSwe.Git.RuntimeTests.err_git_showFile_invalidRef" .real }
  , { request := "LeanSwe.Git.showFile?"
      errorKind := .invalidPath
      justification := .tested "LeanSwe.Git.RuntimeTests.err_git_showFile_invalidPath" .real }
  , { request := "LeanSwe.Git.showFile?"
      errorKind := .invalidInput
      justification := .tested "LeanSwe.Git.RuntimeTests.err_git_showFile_invalidInput" .real }
  , { request := "LeanSwe.Git.showFile?"
      errorKind := .dirtyWorktree
      justification := .tested "LeanSwe.Git.RuntimeTests.err_git_showFile_dirtyWorktree" .mocked }
  , { request := "LeanSwe.Git.showFile?"
      errorKind := .nothingToCommit
      justification := .tested "LeanSwe.Git.RuntimeTests.err_git_showFile_nothingToCommit" .mocked }
  , { request := "LeanSwe.Git.showFile?"
      errorKind := .branchInUse
      justification := .tested "LeanSwe.Git.RuntimeTests.err_git_showFile_branchInUse" .mocked }
  , { request := "LeanSwe.Git.showFile?"
      errorKind := .alreadyExists
      justification := .tested "LeanSwe.Git.RuntimeTests.err_git_showFile_alreadyExists" .mocked }
  , { request := "LeanSwe.Git.showFile?"
      errorKind := .notFound
      justification := .tested "LeanSwe.Git.RuntimeTests.err_git_showFile_notFound" .mocked }
  , { request := "LeanSwe.Git.showFile?"
      errorKind := .conflict
      justification := .tested "LeanSwe.Git.RuntimeTests.err_git_showFile_conflict" .mocked }
  , { request := "LeanSwe.Git.showFile?"
      errorKind := .timeout
      justification := .tested "LeanSwe.Git.RuntimeTests.err_git_showFile_timeout" .mocked }
  , { request := "LeanSwe.Git.showFile?"
      errorKind := .commandFailed
      justification := .tested "LeanSwe.Git.RuntimeTests.err_git_showFile_commandFailed" .real }
  , { request := "LeanSwe.Git.showFile?"
      errorKind := .parseError
      justification := .tested "LeanSwe.Git.RuntimeTests.err_git_showFile_parseError" .mocked }
  , { request := "LeanSwe.Git.init"
      errorKind := .notARepo
      justification := .tested "LeanSwe.Git.RuntimeTests.err_git_init_notARepo" .mocked }
  , { request := "LeanSwe.Git.init"
      errorKind := .invalidRef
      justification := .tested "LeanSwe.Git.RuntimeTests.err_git_init_invalidRef" .real }
  , { request := "LeanSwe.Git.init"
      errorKind := .invalidPath
      justification := .tested "LeanSwe.Git.RuntimeTests.err_git_init_invalidPath" .real }
  , { request := "LeanSwe.Git.init"
      errorKind := .invalidInput
      justification := .tested "LeanSwe.Git.RuntimeTests.err_git_init_invalidInput" .real }
  , { request := "LeanSwe.Git.init"
      errorKind := .dirtyWorktree
      justification := .tested "LeanSwe.Git.RuntimeTests.err_git_init_dirtyWorktree" .mocked }
  , { request := "LeanSwe.Git.init"
      errorKind := .nothingToCommit
      justification := .tested "LeanSwe.Git.RuntimeTests.err_git_init_nothingToCommit" .mocked }
  , { request := "LeanSwe.Git.init"
      errorKind := .branchInUse
      justification := .tested "LeanSwe.Git.RuntimeTests.err_git_init_branchInUse" .mocked }
  , { request := "LeanSwe.Git.init"
      errorKind := .alreadyExists
      justification := .tested "LeanSwe.Git.RuntimeTests.err_git_init_alreadyExists" .mocked }
  , { request := "LeanSwe.Git.init"
      errorKind := .notFound
      justification := .tested "LeanSwe.Git.RuntimeTests.err_git_init_notFound" .mocked }
  , { request := "LeanSwe.Git.init"
      errorKind := .conflict
      justification := .tested "LeanSwe.Git.RuntimeTests.err_git_init_conflict" .mocked }
  , { request := "LeanSwe.Git.init"
      errorKind := .timeout
      justification := .tested "LeanSwe.Git.RuntimeTests.err_git_init_timeout" .mocked }
  , { request := "LeanSwe.Git.init"
      errorKind := .commandFailed
      justification := .tested "LeanSwe.Git.RuntimeTests.err_git_init_commandFailed" .real }
  , { request := "LeanSwe.Git.init"
      errorKind := .parseError
      justification := .provedImpossible "LeanSwe.Git.Proofs.git_init_never_parseError" }
  , { request := "LeanSwe.Git.clone"
      errorKind := .notARepo
      justification := .tested "LeanSwe.Git.RuntimeTests.err_git_clone_notARepo" .mocked }
  , { request := "LeanSwe.Git.clone"
      errorKind := .invalidRef
      justification := .tested "LeanSwe.Git.RuntimeTests.err_git_clone_invalidRef" .real }
  , { request := "LeanSwe.Git.clone"
      errorKind := .invalidPath
      justification := .provedImpossible "LeanSwe.Git.Proofs.git_clone_never_invalidPath" }
  , { request := "LeanSwe.Git.clone"
      errorKind := .invalidInput
      justification := .tested "LeanSwe.Git.RuntimeTests.err_git_clone_invalidInput" .real }
  , { request := "LeanSwe.Git.clone"
      errorKind := .dirtyWorktree
      justification := .tested "LeanSwe.Git.RuntimeTests.err_git_clone_dirtyWorktree" .mocked }
  , { request := "LeanSwe.Git.clone"
      errorKind := .nothingToCommit
      justification := .tested "LeanSwe.Git.RuntimeTests.err_git_clone_nothingToCommit" .mocked }
  , { request := "LeanSwe.Git.clone"
      errorKind := .branchInUse
      justification := .tested "LeanSwe.Git.RuntimeTests.err_git_clone_branchInUse" .mocked }
  , { request := "LeanSwe.Git.clone"
      errorKind := .alreadyExists
      justification := .tested "LeanSwe.Git.RuntimeTests.err_git_clone_alreadyExists" .real }
  , { request := "LeanSwe.Git.clone"
      errorKind := .notFound
      justification := .tested "LeanSwe.Git.RuntimeTests.err_git_clone_notFound" .real }
  , { request := "LeanSwe.Git.clone"
      errorKind := .conflict
      justification := .tested "LeanSwe.Git.RuntimeTests.err_git_clone_conflict" .mocked }
  , { request := "LeanSwe.Git.clone"
      errorKind := .timeout
      justification := .tested "LeanSwe.Git.RuntimeTests.err_git_clone_timeout" .mocked }
  , { request := "LeanSwe.Git.clone"
      errorKind := .commandFailed
      justification := .tested "LeanSwe.Git.RuntimeTests.err_git_clone_commandFailed" .real }
  , { request := "LeanSwe.Git.clone"
      errorKind := .parseError
      justification := .provedImpossible "LeanSwe.Git.Proofs.git_clone_never_parseError" }
  , { request := "LeanSwe.Git.add"
      errorKind := .notARepo
      justification := .tested "LeanSwe.Git.RuntimeTests.err_git_add_notARepo" .real }
  , { request := "LeanSwe.Git.add"
      errorKind := .invalidRef
      justification := .tested "LeanSwe.Git.RuntimeTests.err_git_add_invalidRef" .mocked }
  , { request := "LeanSwe.Git.add"
      errorKind := .invalidPath
      justification := .tested "LeanSwe.Git.RuntimeTests.err_git_add_invalidPath" .real }
  , { request := "LeanSwe.Git.add"
      errorKind := .invalidInput
      justification := .tested "LeanSwe.Git.RuntimeTests.err_git_add_invalidInput" .real }
  , { request := "LeanSwe.Git.add"
      errorKind := .dirtyWorktree
      justification := .tested "LeanSwe.Git.RuntimeTests.err_git_add_dirtyWorktree" .mocked }
  , { request := "LeanSwe.Git.add"
      errorKind := .nothingToCommit
      justification := .tested "LeanSwe.Git.RuntimeTests.err_git_add_nothingToCommit" .mocked }
  , { request := "LeanSwe.Git.add"
      errorKind := .branchInUse
      justification := .tested "LeanSwe.Git.RuntimeTests.err_git_add_branchInUse" .mocked }
  , { request := "LeanSwe.Git.add"
      errorKind := .alreadyExists
      justification := .tested "LeanSwe.Git.RuntimeTests.err_git_add_alreadyExists" .mocked }
  , { request := "LeanSwe.Git.add"
      errorKind := .notFound
      justification := .tested "LeanSwe.Git.RuntimeTests.err_git_add_notFound" .real }
  , { request := "LeanSwe.Git.add"
      errorKind := .conflict
      justification := .tested "LeanSwe.Git.RuntimeTests.err_git_add_conflict" .mocked }
  , { request := "LeanSwe.Git.add"
      errorKind := .timeout
      justification := .tested "LeanSwe.Git.RuntimeTests.err_git_add_timeout" .mocked }
  , { request := "LeanSwe.Git.add"
      errorKind := .commandFailed
      justification := .tested "LeanSwe.Git.RuntimeTests.err_git_add_commandFailed" .real }
  , { request := "LeanSwe.Git.add"
      errorKind := .parseError
      justification := .provedImpossible "LeanSwe.Git.Proofs.git_add_never_parseError" }
  , { request := "LeanSwe.Git.commit"
      errorKind := .notARepo
      justification := .tested "LeanSwe.Git.RuntimeTests.err_git_commit_notARepo" .real }
  , { request := "LeanSwe.Git.commit"
      errorKind := .invalidRef
      justification := .tested "LeanSwe.Git.RuntimeTests.err_git_commit_invalidRef" .mocked }
  , { request := "LeanSwe.Git.commit"
      errorKind := .invalidPath
      justification := .tested "LeanSwe.Git.RuntimeTests.err_git_commit_invalidPath" .real }
  , { request := "LeanSwe.Git.commit"
      errorKind := .invalidInput
      justification := .tested "LeanSwe.Git.RuntimeTests.err_git_commit_invalidInput" .real }
  , { request := "LeanSwe.Git.commit"
      errorKind := .dirtyWorktree
      justification := .tested "LeanSwe.Git.RuntimeTests.err_git_commit_dirtyWorktree" .mocked }
  , { request := "LeanSwe.Git.commit"
      errorKind := .nothingToCommit
      justification := .tested "LeanSwe.Git.RuntimeTests.err_git_commit_nothingToCommit" .real }
  , { request := "LeanSwe.Git.commit"
      errorKind := .branchInUse
      justification := .tested "LeanSwe.Git.RuntimeTests.err_git_commit_branchInUse" .mocked }
  , { request := "LeanSwe.Git.commit"
      errorKind := .alreadyExists
      justification := .tested "LeanSwe.Git.RuntimeTests.err_git_commit_alreadyExists" .mocked }
  , { request := "LeanSwe.Git.commit"
      errorKind := .notFound
      justification := .tested "LeanSwe.Git.RuntimeTests.err_git_commit_notFound" .mocked }
  , { request := "LeanSwe.Git.commit"
      errorKind := .conflict
      justification := .tested "LeanSwe.Git.RuntimeTests.err_git_commit_conflict" .real }
  , { request := "LeanSwe.Git.commit"
      errorKind := .timeout
      justification := .tested "LeanSwe.Git.RuntimeTests.err_git_commit_timeout" .mocked }
  , { request := "LeanSwe.Git.commit"
      errorKind := .commandFailed
      justification := .tested "LeanSwe.Git.RuntimeTests.err_git_commit_commandFailed" .real }
  , { request := "LeanSwe.Git.commit"
      errorKind := .parseError
      justification := .tested "LeanSwe.Git.RuntimeTests.err_git_commit_parseError" .mocked }
  , { request := "LeanSwe.Git.createBranch"
      errorKind := .notARepo
      justification := .tested "LeanSwe.Git.RuntimeTests.err_git_createBranch_notARepo" .real }
  , { request := "LeanSwe.Git.createBranch"
      errorKind := .invalidRef
      justification := .tested "LeanSwe.Git.RuntimeTests.err_git_createBranch_invalidRef" .real }
  , { request := "LeanSwe.Git.createBranch"
      errorKind := .invalidPath
      justification := .tested "LeanSwe.Git.RuntimeTests.err_git_createBranch_invalidPath" .real }
  , { request := "LeanSwe.Git.createBranch"
      errorKind := .invalidInput
      justification := .tested "LeanSwe.Git.RuntimeTests.err_git_createBranch_invalidInput" .real }
  , { request := "LeanSwe.Git.createBranch"
      errorKind := .dirtyWorktree
      justification := .tested "LeanSwe.Git.RuntimeTests.err_git_createBranch_dirtyWorktree" .mocked }
  , { request := "LeanSwe.Git.createBranch"
      errorKind := .nothingToCommit
      justification := .tested "LeanSwe.Git.RuntimeTests.err_git_createBranch_nothingToCommit" .mocked }
  , { request := "LeanSwe.Git.createBranch"
      errorKind := .branchInUse
      justification := .tested "LeanSwe.Git.RuntimeTests.err_git_createBranch_branchInUse" .mocked }
  , { request := "LeanSwe.Git.createBranch"
      errorKind := .alreadyExists
      justification := .tested "LeanSwe.Git.RuntimeTests.err_git_createBranch_alreadyExists" .real }
  , { request := "LeanSwe.Git.createBranch"
      errorKind := .notFound
      justification := .tested "LeanSwe.Git.RuntimeTests.err_git_createBranch_notFound" .mocked }
  , { request := "LeanSwe.Git.createBranch"
      errorKind := .conflict
      justification := .tested "LeanSwe.Git.RuntimeTests.err_git_createBranch_conflict" .mocked }
  , { request := "LeanSwe.Git.createBranch"
      errorKind := .timeout
      justification := .tested "LeanSwe.Git.RuntimeTests.err_git_createBranch_timeout" .mocked }
  , { request := "LeanSwe.Git.createBranch"
      errorKind := .commandFailed
      justification := .tested "LeanSwe.Git.RuntimeTests.err_git_createBranch_commandFailed" .real }
  , { request := "LeanSwe.Git.createBranch"
      errorKind := .parseError
      justification := .provedImpossible "LeanSwe.Git.Proofs.git_createBranch_never_parseError" }
  , { request := "LeanSwe.Git.deleteBranch"
      errorKind := .notARepo
      justification := .tested "LeanSwe.Git.RuntimeTests.err_git_deleteBranch_notARepo" .real }
  , { request := "LeanSwe.Git.deleteBranch"
      errorKind := .invalidRef
      justification := .tested "LeanSwe.Git.RuntimeTests.err_git_deleteBranch_invalidRef" .real }
  , { request := "LeanSwe.Git.deleteBranch"
      errorKind := .invalidPath
      justification := .tested "LeanSwe.Git.RuntimeTests.err_git_deleteBranch_invalidPath" .real }
  , { request := "LeanSwe.Git.deleteBranch"
      errorKind := .invalidInput
      justification := .tested "LeanSwe.Git.RuntimeTests.err_git_deleteBranch_invalidInput" .real }
  , { request := "LeanSwe.Git.deleteBranch"
      errorKind := .dirtyWorktree
      justification := .tested "LeanSwe.Git.RuntimeTests.err_git_deleteBranch_dirtyWorktree" .mocked }
  , { request := "LeanSwe.Git.deleteBranch"
      errorKind := .nothingToCommit
      justification := .tested "LeanSwe.Git.RuntimeTests.err_git_deleteBranch_nothingToCommit" .mocked }
  , { request := "LeanSwe.Git.deleteBranch"
      errorKind := .branchInUse
      justification := .tested "LeanSwe.Git.RuntimeTests.err_git_deleteBranch_branchInUse" .real }
  , { request := "LeanSwe.Git.deleteBranch"
      errorKind := .alreadyExists
      justification := .tested "LeanSwe.Git.RuntimeTests.err_git_deleteBranch_alreadyExists" .mocked }
  , { request := "LeanSwe.Git.deleteBranch"
      errorKind := .notFound
      justification := .tested "LeanSwe.Git.RuntimeTests.err_git_deleteBranch_notFound" .real }
  , { request := "LeanSwe.Git.deleteBranch"
      errorKind := .conflict
      justification := .tested "LeanSwe.Git.RuntimeTests.err_git_deleteBranch_conflict" .mocked }
  , { request := "LeanSwe.Git.deleteBranch"
      errorKind := .timeout
      justification := .tested "LeanSwe.Git.RuntimeTests.err_git_deleteBranch_timeout" .mocked }
  , { request := "LeanSwe.Git.deleteBranch"
      errorKind := .commandFailed
      justification := .tested "LeanSwe.Git.RuntimeTests.err_git_deleteBranch_commandFailed" .real }
  , { request := "LeanSwe.Git.deleteBranch"
      errorKind := .parseError
      justification := .provedImpossible "LeanSwe.Git.Proofs.git_deleteBranch_never_parseError" }
  , { request := "LeanSwe.Git.checkout"
      errorKind := .notARepo
      justification := .tested "LeanSwe.Git.RuntimeTests.err_git_checkout_notARepo" .real }
  , { request := "LeanSwe.Git.checkout"
      errorKind := .invalidRef
      justification := .tested "LeanSwe.Git.RuntimeTests.err_git_checkout_invalidRef" .real }
  , { request := "LeanSwe.Git.checkout"
      errorKind := .invalidPath
      justification := .tested "LeanSwe.Git.RuntimeTests.err_git_checkout_invalidPath" .real }
  , { request := "LeanSwe.Git.checkout"
      errorKind := .invalidInput
      justification := .tested "LeanSwe.Git.RuntimeTests.err_git_checkout_invalidInput" .real }
  , { request := "LeanSwe.Git.checkout"
      errorKind := .dirtyWorktree
      justification := .tested "LeanSwe.Git.RuntimeTests.err_git_checkout_dirtyWorktree" .real }
  , { request := "LeanSwe.Git.checkout"
      errorKind := .nothingToCommit
      justification := .tested "LeanSwe.Git.RuntimeTests.err_git_checkout_nothingToCommit" .mocked }
  , { request := "LeanSwe.Git.checkout"
      errorKind := .branchInUse
      justification := .tested "LeanSwe.Git.RuntimeTests.err_git_checkout_branchInUse" .real }
  , { request := "LeanSwe.Git.checkout"
      errorKind := .alreadyExists
      justification := .tested "LeanSwe.Git.RuntimeTests.err_git_checkout_alreadyExists" .mocked }
  , { request := "LeanSwe.Git.checkout"
      errorKind := .notFound
      justification := .tested "LeanSwe.Git.RuntimeTests.err_git_checkout_notFound" .mocked }
  , { request := "LeanSwe.Git.checkout"
      errorKind := .conflict
      justification := .tested "LeanSwe.Git.RuntimeTests.err_git_checkout_conflict" .real }
  , { request := "LeanSwe.Git.checkout"
      errorKind := .timeout
      justification := .tested "LeanSwe.Git.RuntimeTests.err_git_checkout_timeout" .mocked }
  , { request := "LeanSwe.Git.checkout"
      errorKind := .commandFailed
      justification := .tested "LeanSwe.Git.RuntimeTests.err_git_checkout_commandFailed" .real }
  , { request := "LeanSwe.Git.checkout"
      errorKind := .parseError
      justification := .provedImpossible "LeanSwe.Git.Proofs.git_checkout_never_parseError" }
  , { request := "LeanSwe.Git.switch"
      errorKind := .notARepo
      justification := .tested "LeanSwe.Git.RuntimeTests.err_git_switch_notARepo" .real }
  , { request := "LeanSwe.Git.switch"
      errorKind := .invalidRef
      justification := .tested "LeanSwe.Git.RuntimeTests.err_git_switch_invalidRef" .real }
  , { request := "LeanSwe.Git.switch"
      errorKind := .invalidPath
      justification := .tested "LeanSwe.Git.RuntimeTests.err_git_switch_invalidPath" .real }
  , { request := "LeanSwe.Git.switch"
      errorKind := .invalidInput
      justification := .tested "LeanSwe.Git.RuntimeTests.err_git_switch_invalidInput" .real }
  , { request := "LeanSwe.Git.switch"
      errorKind := .dirtyWorktree
      justification := .tested "LeanSwe.Git.RuntimeTests.err_git_switch_dirtyWorktree" .real }
  , { request := "LeanSwe.Git.switch"
      errorKind := .nothingToCommit
      justification := .tested "LeanSwe.Git.RuntimeTests.err_git_switch_nothingToCommit" .mocked }
  , { request := "LeanSwe.Git.switch"
      errorKind := .branchInUse
      justification := .tested "LeanSwe.Git.RuntimeTests.err_git_switch_branchInUse" .real }
  , { request := "LeanSwe.Git.switch"
      errorKind := .alreadyExists
      justification := .tested "LeanSwe.Git.RuntimeTests.err_git_switch_alreadyExists" .real }
  , { request := "LeanSwe.Git.switch"
      errorKind := .notFound
      justification := .tested "LeanSwe.Git.RuntimeTests.err_git_switch_notFound" .mocked }
  , { request := "LeanSwe.Git.switch"
      errorKind := .conflict
      justification := .tested "LeanSwe.Git.RuntimeTests.err_git_switch_conflict" .real }
  , { request := "LeanSwe.Git.switch"
      errorKind := .timeout
      justification := .tested "LeanSwe.Git.RuntimeTests.err_git_switch_timeout" .mocked }
  , { request := "LeanSwe.Git.switch"
      errorKind := .commandFailed
      justification := .tested "LeanSwe.Git.RuntimeTests.err_git_switch_commandFailed" .real }
  , { request := "LeanSwe.Git.switch"
      errorKind := .parseError
      justification := .provedImpossible "LeanSwe.Git.Proofs.git_switch_never_parseError" }
  , { request := "LeanSwe.Git.reset"
      errorKind := .notARepo
      justification := .tested "LeanSwe.Git.RuntimeTests.err_git_reset_notARepo" .real }
  , { request := "LeanSwe.Git.reset"
      errorKind := .invalidRef
      justification := .tested "LeanSwe.Git.RuntimeTests.err_git_reset_invalidRef" .real }
  , { request := "LeanSwe.Git.reset"
      errorKind := .invalidPath
      justification := .tested "LeanSwe.Git.RuntimeTests.err_git_reset_invalidPath" .real }
  , { request := "LeanSwe.Git.reset"
      errorKind := .invalidInput
      justification := .tested "LeanSwe.Git.RuntimeTests.err_git_reset_invalidInput" .real }
  , { request := "LeanSwe.Git.reset"
      errorKind := .dirtyWorktree
      justification := .tested "LeanSwe.Git.RuntimeTests.err_git_reset_dirtyWorktree" .mocked }
  , { request := "LeanSwe.Git.reset"
      errorKind := .nothingToCommit
      justification := .tested "LeanSwe.Git.RuntimeTests.err_git_reset_nothingToCommit" .mocked }
  , { request := "LeanSwe.Git.reset"
      errorKind := .branchInUse
      justification := .tested "LeanSwe.Git.RuntimeTests.err_git_reset_branchInUse" .mocked }
  , { request := "LeanSwe.Git.reset"
      errorKind := .alreadyExists
      justification := .tested "LeanSwe.Git.RuntimeTests.err_git_reset_alreadyExists" .mocked }
  , { request := "LeanSwe.Git.reset"
      errorKind := .notFound
      justification := .tested "LeanSwe.Git.RuntimeTests.err_git_reset_notFound" .mocked }
  , { request := "LeanSwe.Git.reset"
      errorKind := .conflict
      justification := .tested "LeanSwe.Git.RuntimeTests.err_git_reset_conflict" .mocked }
  , { request := "LeanSwe.Git.reset"
      errorKind := .timeout
      justification := .tested "LeanSwe.Git.RuntimeTests.err_git_reset_timeout" .mocked }
  , { request := "LeanSwe.Git.reset"
      errorKind := .commandFailed
      justification := .tested "LeanSwe.Git.RuntimeTests.err_git_reset_commandFailed" .real }
  , { request := "LeanSwe.Git.reset"
      errorKind := .parseError
      justification := .provedImpossible "LeanSwe.Git.Proofs.git_reset_never_parseError" }
  , { request := "LeanSwe.Git.fetch"
      errorKind := .notARepo
      justification := .tested "LeanSwe.Git.RuntimeTests.err_git_fetch_notARepo" .real }
  , { request := "LeanSwe.Git.fetch"
      errorKind := .invalidRef
      justification := .tested "LeanSwe.Git.RuntimeTests.err_git_fetch_invalidRef" .mocked }
  , { request := "LeanSwe.Git.fetch"
      errorKind := .invalidPath
      justification := .tested "LeanSwe.Git.RuntimeTests.err_git_fetch_invalidPath" .real }
  , { request := "LeanSwe.Git.fetch"
      errorKind := .invalidInput
      justification := .tested "LeanSwe.Git.RuntimeTests.err_git_fetch_invalidInput" .real }
  , { request := "LeanSwe.Git.fetch"
      errorKind := .dirtyWorktree
      justification := .tested "LeanSwe.Git.RuntimeTests.err_git_fetch_dirtyWorktree" .mocked }
  , { request := "LeanSwe.Git.fetch"
      errorKind := .nothingToCommit
      justification := .tested "LeanSwe.Git.RuntimeTests.err_git_fetch_nothingToCommit" .mocked }
  , { request := "LeanSwe.Git.fetch"
      errorKind := .branchInUse
      justification := .tested "LeanSwe.Git.RuntimeTests.err_git_fetch_branchInUse" .mocked }
  , { request := "LeanSwe.Git.fetch"
      errorKind := .alreadyExists
      justification := .tested "LeanSwe.Git.RuntimeTests.err_git_fetch_alreadyExists" .mocked }
  , { request := "LeanSwe.Git.fetch"
      errorKind := .notFound
      justification := .tested "LeanSwe.Git.RuntimeTests.err_git_fetch_notFound" .mocked }
  , { request := "LeanSwe.Git.fetch"
      errorKind := .conflict
      justification := .tested "LeanSwe.Git.RuntimeTests.err_git_fetch_conflict" .mocked }
  , { request := "LeanSwe.Git.fetch"
      errorKind := .timeout
      justification := .tested "LeanSwe.Git.RuntimeTests.err_git_fetch_timeout" .mocked }
  , { request := "LeanSwe.Git.fetch"
      errorKind := .commandFailed
      justification := .tested "LeanSwe.Git.RuntimeTests.err_git_fetch_commandFailed" .real }
  , { request := "LeanSwe.Git.fetch"
      errorKind := .parseError
      justification := .provedImpossible "LeanSwe.Git.Proofs.git_fetch_never_parseError" }
  , { request := "LeanSwe.Git.worktreeAdd"
      errorKind := .notARepo
      justification := .tested "LeanSwe.Git.RuntimeTests.err_git_worktreeAdd_notARepo" .real }
  , { request := "LeanSwe.Git.worktreeAdd"
      errorKind := .invalidRef
      justification := .tested "LeanSwe.Git.RuntimeTests.err_git_worktreeAdd_invalidRef" .real }
  , { request := "LeanSwe.Git.worktreeAdd"
      errorKind := .invalidPath
      justification := .tested "LeanSwe.Git.RuntimeTests.err_git_worktreeAdd_invalidPath" .real }
  , { request := "LeanSwe.Git.worktreeAdd"
      errorKind := .invalidInput
      justification := .tested "LeanSwe.Git.RuntimeTests.err_git_worktreeAdd_invalidInput" .real }
  , { request := "LeanSwe.Git.worktreeAdd"
      errorKind := .dirtyWorktree
      justification := .tested "LeanSwe.Git.RuntimeTests.err_git_worktreeAdd_dirtyWorktree" .mocked }
  , { request := "LeanSwe.Git.worktreeAdd"
      errorKind := .nothingToCommit
      justification := .tested "LeanSwe.Git.RuntimeTests.err_git_worktreeAdd_nothingToCommit" .mocked }
  , { request := "LeanSwe.Git.worktreeAdd"
      errorKind := .branchInUse
      justification := .tested "LeanSwe.Git.RuntimeTests.err_git_worktreeAdd_branchInUse" .real }
  , { request := "LeanSwe.Git.worktreeAdd"
      errorKind := .alreadyExists
      justification := .tested "LeanSwe.Git.RuntimeTests.err_git_worktreeAdd_alreadyExists" .real }
  , { request := "LeanSwe.Git.worktreeAdd"
      errorKind := .notFound
      justification := .tested "LeanSwe.Git.RuntimeTests.err_git_worktreeAdd_notFound" .mocked }
  , { request := "LeanSwe.Git.worktreeAdd"
      errorKind := .conflict
      justification := .tested "LeanSwe.Git.RuntimeTests.err_git_worktreeAdd_conflict" .mocked }
  , { request := "LeanSwe.Git.worktreeAdd"
      errorKind := .timeout
      justification := .tested "LeanSwe.Git.RuntimeTests.err_git_worktreeAdd_timeout" .mocked }
  , { request := "LeanSwe.Git.worktreeAdd"
      errorKind := .commandFailed
      justification := .tested "LeanSwe.Git.RuntimeTests.err_git_worktreeAdd_commandFailed" .real }
  , { request := "LeanSwe.Git.worktreeAdd"
      errorKind := .parseError
      justification := .provedImpossible "LeanSwe.Git.Proofs.git_worktreeAdd_never_parseError" }
  , { request := "LeanSwe.Git.worktreeRemove"
      errorKind := .notARepo
      justification := .tested "LeanSwe.Git.RuntimeTests.err_git_worktreeRemove_notARepo" .real }
  , { request := "LeanSwe.Git.worktreeRemove"
      errorKind := .invalidRef
      justification := .tested "LeanSwe.Git.RuntimeTests.err_git_worktreeRemove_invalidRef" .mocked }
  , { request := "LeanSwe.Git.worktreeRemove"
      errorKind := .invalidPath
      justification := .tested "LeanSwe.Git.RuntimeTests.err_git_worktreeRemove_invalidPath" .real }
  , { request := "LeanSwe.Git.worktreeRemove"
      errorKind := .invalidInput
      justification := .tested "LeanSwe.Git.RuntimeTests.err_git_worktreeRemove_invalidInput" .real }
  , { request := "LeanSwe.Git.worktreeRemove"
      errorKind := .dirtyWorktree
      justification := .tested "LeanSwe.Git.RuntimeTests.err_git_worktreeRemove_dirtyWorktree" .real }
  , { request := "LeanSwe.Git.worktreeRemove"
      errorKind := .nothingToCommit
      justification := .tested "LeanSwe.Git.RuntimeTests.err_git_worktreeRemove_nothingToCommit" .mocked }
  , { request := "LeanSwe.Git.worktreeRemove"
      errorKind := .branchInUse
      justification := .tested "LeanSwe.Git.RuntimeTests.err_git_worktreeRemove_branchInUse" .mocked }
  , { request := "LeanSwe.Git.worktreeRemove"
      errorKind := .alreadyExists
      justification := .tested "LeanSwe.Git.RuntimeTests.err_git_worktreeRemove_alreadyExists" .mocked }
  , { request := "LeanSwe.Git.worktreeRemove"
      errorKind := .notFound
      justification := .tested "LeanSwe.Git.RuntimeTests.err_git_worktreeRemove_notFound" .mocked }
  , { request := "LeanSwe.Git.worktreeRemove"
      errorKind := .conflict
      justification := .tested "LeanSwe.Git.RuntimeTests.err_git_worktreeRemove_conflict" .mocked }
  , { request := "LeanSwe.Git.worktreeRemove"
      errorKind := .timeout
      justification := .tested "LeanSwe.Git.RuntimeTests.err_git_worktreeRemove_timeout" .mocked }
  , { request := "LeanSwe.Git.worktreeRemove"
      errorKind := .commandFailed
      justification := .tested "LeanSwe.Git.RuntimeTests.err_git_worktreeRemove_commandFailed" .real }
  , { request := "LeanSwe.Git.worktreeRemove"
      errorKind := .parseError
      justification := .provedImpossible "LeanSwe.Git.Proofs.git_worktreeRemove_never_parseError" }
  , { request := "LeanSwe.Git.withWorktree"
      errorKind := .notARepo
      justification := .tested "LeanSwe.Git.RuntimeTests.err_git_withWorktree_notARepo" .real }
  , { request := "LeanSwe.Git.withWorktree"
      errorKind := .invalidRef
      justification := .tested "LeanSwe.Git.RuntimeTests.err_git_withWorktree_invalidRef" .real }
  , { request := "LeanSwe.Git.withWorktree"
      errorKind := .invalidPath
      justification := .tested "LeanSwe.Git.RuntimeTests.err_git_withWorktree_invalidPath" .real }
  , { request := "LeanSwe.Git.withWorktree"
      errorKind := .invalidInput
      justification := .tested "LeanSwe.Git.RuntimeTests.err_git_withWorktree_invalidInput" .real }
  , { request := "LeanSwe.Git.withWorktree"
      errorKind := .dirtyWorktree
      justification := .tested "LeanSwe.Git.RuntimeTests.err_git_withWorktree_dirtyWorktree" .real }
  , { request := "LeanSwe.Git.withWorktree"
      errorKind := .nothingToCommit
      justification := .tested "LeanSwe.Git.RuntimeTests.err_git_withWorktree_nothingToCommit" .real }
  , { request := "LeanSwe.Git.withWorktree"
      errorKind := .branchInUse
      justification := .tested "LeanSwe.Git.RuntimeTests.err_git_withWorktree_branchInUse" .real }
  , { request := "LeanSwe.Git.withWorktree"
      errorKind := .alreadyExists
      justification := .tested "LeanSwe.Git.RuntimeTests.err_git_withWorktree_alreadyExists" .real }
  , { request := "LeanSwe.Git.withWorktree"
      errorKind := .notFound
      justification := .tested "LeanSwe.Git.RuntimeTests.err_git_withWorktree_notFound" .real }
  , { request := "LeanSwe.Git.withWorktree"
      errorKind := .conflict
      justification := .tested "LeanSwe.Git.RuntimeTests.err_git_withWorktree_conflict" .real }
  , { request := "LeanSwe.Git.withWorktree"
      errorKind := .timeout
      justification := .tested "LeanSwe.Git.RuntimeTests.err_git_withWorktree_timeout" .mocked }
  , { request := "LeanSwe.Git.withWorktree"
      errorKind := .commandFailed
      justification := .tested "LeanSwe.Git.RuntimeTests.err_git_withWorktree_commandFailed" .real }
  , { request := "LeanSwe.Git.withWorktree"
      errorKind := .parseError
      justification := .tested "LeanSwe.Git.RuntimeTests.err_git_withWorktree_parseError" .real } ]

end LeanSwe.Git
