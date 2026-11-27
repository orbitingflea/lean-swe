import Core.NondetTest
import LeanSwe.Git.Types
import LeanSweProofs.Git.Model
import LeanSweProofs.Git.SpecTests.Cases

namespace LeanSwe.Git

open Core (NondetTest)
open Core.NondetTest
open LeanSwe.Git.Model

/-- `cleanGitEnv` emits explicit `none` removals for inherited `GIT_*`/locale keys and restricts surviving `GIT_*`/locale entries to safety defaults or the author/committer allowlist. -/
def test_git_cleanGitEnv_stripsInheritedGitKeys
    {runner} [NondetTest runner]
    (sanitize : Array (String × String) → Array (String × Option String) → Array (String × Option String)) :
    runner Unit := do
  let inherited ← nondet (Array (String × String))
  let extra ← nondet (Array (String × Option String))
  let out := sanitize inherited extra
  let outList := out.toList
  NondetTest.assert (inherited.toList.all fun kv =>
    (!isGitKey kv.1 && !isLocaleKey kv.1) || outList.contains (kv.1, none))
  NondetTest.assert (defaultGitSafetyEnv.all fun kv => outList.contains kv)
  NondetTest.assert (outList.all fun kv =>
    (!isGitKey kv.1 && !isLocaleKey kv.1) || kv.2 == none || defaultGitSafetyEnv.contains kv || isAllowedExtraGitKey kv.1)

/-- `cleanGitEnv` preserves valid non-`GIT_*`, non-locale extra environment entries. -/
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
  assume (isLocaleKey key = false)
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

/-- `mkRefName` rejects unsafe ref names (`"HEAD"`, `"@"`, leading `'-'`, `".."`, `"@{"`, control chars, `.lock`) with `.invalidRef`. -/
def test_git_mkRefName_rejectsUnsafeRefs
    {runner} [NondetTest runner] (buildRef : String → Except GitError RefName) : runner Unit := do
  let s ← nondet String
  assume (s = "" ∨ s = "HEAD" ∨ s.toList.head? = some '-' ∨ s = "@" ∨ hasSubstrChars ['.', '.'] s.toList = true)
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

/-- `isAncestor` is reflexive on existing commits and `false` if either commit is absent from `RepoInstance`. -/
def test_git_model_isAncestor_reflexiveAndGuarded
    {runner} [NondetTest runner]
    (ancFn : RepoInstance → CommitId → CommitId → Bool) : runner Unit := do
  let s ← nondet RepoInstance
  let a ← nondet CommitId
  let b ← nondet CommitId
  if hasCommit s a then
    NondetTest.assert (ancFn s a a = true)
  else
    NondetTest.assert (ancFn s a b = false ∧ ancFn s b a = false)

/-- On any well-formed `RepoInstance`, `isAncestor` is transitive and `mergeBase?` returns an ancestor of both inputs. -/
def test_git_model_isAncestor_transitiveAndMergeBaseValid
    {runner} [NondetTest runner]
    (ancFn : RepoInstance → CommitId → CommitId → Bool)
    (mbFn : RepoInstance → CommitId → CommitId → Option CommitId) : runner Unit := do
  let s ← nondet RepoInstance
  let a ← nondet CommitId
  let b ← nondet CommitId
  let c ← nondet CommitId
  assume (isValidRepoInstance s = true)
  if ancFn s a b && ancFn s b c then
    NondetTest.assert (ancFn s a c = true)
  match mbFn s a b with
  | none => pure ()
  | some m => NondetTest.assert (ancFn s m a = true ∧ ancFn s m b = true)

/-- Initializing a fresh repo gives an unborn `HEAD` (`headCommit? = none`, `headBranch? = some branch`), and `revParseCommit "HEAD"` fails with `.invalidRef`. -/
def test_git_api_unbornHead_behavior
    {runner} [NondetTest runner]
    (api : GitApiM (StateM GitRepoState)) : runner Unit := do
  let s₀ ← nondet GitRepoState
  let path ← nondet String
  let branch ← nondet RefName
  assume (s₀ = {})
  assume (path = "/repo")
  assume (isValidRefNameStr branch.raw = true)
  let (initRes, s₁) := (api.init path false (some branch)).run s₀
  assume (initRes = .ok ())
  let (hcRes, _) := (api.headCommit? path).run s₁
  let (hbRes, _) := (api.headBranch? path).run s₁
  let (rpRes, _) := (api.revParseCommit path "HEAD").run s₁
  NondetTest.assert (hcRes = .ok none)
  NondetTest.assert (hbRes = .ok (some branch))
  NondetTest.assert (∃ e, rpRes = .error e ∧ e.kind = .invalidRef ∧ e.message ≠ "")

/-- `commit` fails with `.nothingToCommit` when index matches `HEAD` and `allowEmpty = false`, and succeeds when `allowEmpty = true`. -/
def test_git_api_commit_emptyVsAllowEmpty
    {runner} [NondetTest runner] (api : GitApiM (StateM GitRepoState)) : runner Unit := do
  let s₀ ← nondet GitRepoState
  let repo ← nondet RepoInstance
  let wt ← nondet WorktreeSlot
  let c0 ← nondet CommitId
  let b ← nondet RefName
  assume (isValidGitRepoState s₀ = true)
  assume (s₀.repos = [repo] ∧ !repo.isBare ∧ repo.commonDir = "/repo/.git".toUTF8 ∧ repo.worktrees = [wt])
  assume (wt.rootPath = "/repo".toUTF8 ∧ s₀.vfs = .dir true true [("repo".toUTF8, .dir true true [])])
  assume (wt.head = .symbolic b ∧ findBranchCommit? repo b = some c0)
  assume (wt.index = { entries := treeOfCommit repo c0, conflicts := [], hasMergeHead := false })
  let (emptyRes, sEmpty) :=
    (api.commit "/repo" { message := "empty", allowEmpty := false }).run s₀
  let (okRes, sOk) :=
    (api.commit "/repo" { message := "allow", allowEmpty := true }).run s₀
  NondetTest.assert (∃ e, emptyRes = .error e ∧ e.kind = .nothingToCommit ∧ sEmpty = s₀)
  match okRes with
  | .error _ => NondetTest.assert False
  | .ok cid =>
    let (hcRes, _) := (api.headCommit? "/repo").run sOk
    NondetTest.assert (hcRes = .ok (some cid))

/-- `worktreeAdd` rejects checking out a branch already attached in another worktree with `.branchInUse`. -/
def test_git_api_worktreeAdd_branchInUseRejected
    {runner} [NondetTest runner] (api : GitApiM (StateM GitRepoState)) : runner Unit := do
  let s₀ ← nondet GitRepoState
  let repo ← nondet RepoInstance
  let wt ← nondet WorktreeSlot
  let b ← nondet RefName
  let c ← nondet CommitId
  assume (isValidGitRepoState s₀ = true)
  assume (s₀.repos = [repo] ∧ !repo.isBare ∧ repo.commonDir = "/repo/.git".toUTF8 ∧ repo.worktrees = [wt])
  assume (wt.rootPath = "/repo".toUTF8 ∧ s₀.vfs = .dir true true [("repo".toUTF8, .dir true true [])])
  assume (wt.head = .symbolic b ∧ findBranchCommit? repo b = some c)
  assume (isValidRefNameStr b.raw = true ∧ !isValidCommitIdStr b.raw)
  let (res, s₁) :=
    (api.worktreeAdd "/repo" { path := "/wt2", target? := some b.raw }).run s₀
  NondetTest.assert (∃ e, res = .error e ∧ e.kind = .branchInUse ∧ s₁ = s₀)

/-- `checkout` refuses dirty worktrees with `.dirtyWorktree` when `force = false` and target tree differs on the dirty path. -/
def test_git_api_checkout_dirtyWorktreeRejected
    {runner} [NondetTest runner] (api : GitApiM (StateM GitRepoState)) : runner Unit := do
  let s₀ ← nondet GitRepoState
  let repo ← nondet RepoInstance
  let wt ← nondet WorktreeSlot
  let bMain ← nondet RefName
  let bFeat ← nondet RefName
  let c0 ← nondet CommitId
  let c1 ← nondet CommitId
  assume (isValidGitRepoState s₀ = true)
  assume (s₀.repos = [repo] ∧ !repo.isBare ∧ repo.commonDir = "/repo/.git".toUTF8 ∧ repo.worktrees = [wt])
  assume (wt.rootPath = "/repo".toUTF8 ∧ wt.head = .symbolic bMain)
  assume (findBranchCommit? repo bMain = some c0 ∧ findBranchCommit? repo bFeat = some c1)
  assume (bMain ≠ bFeat ∧ isValidRefNameStr bFeat.raw = true)
  assume (treeOfCommit repo c0 = [("a.txt".toUTF8, { kind := .regular false, bytes := "v0".toUTF8 })])
  assume (treeOfCommit repo c1 = [("a.txt".toUTF8, { kind := .regular false, bytes := "v1".toUTF8 })])
  assume (wt.index = { entries := [("a.txt".toUTF8, { kind := .regular false, bytes := "v0".toUTF8 })] })
  assume (s₀.vfs = .dir true true [("repo".toUTF8, .dir true true [("a.txt".toUTF8, .file false "dirty".toUTF8)])])
  let (res, s₁) := (api.checkout "/repo" (.branch bFeat) false).run s₀
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
  assume (validateFsPathArg repoPath = .ok () ∧ validateFsPathArg wtPath = .ok ())
  let handlerFn : GitRawRequest → Nat → Except GitError GitRawOutput := fun req _ =>
    if req.args[1]? == some "add" then
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

/-- `Impl.mkApiM` strips inherited `GIT_*` and locale keys on every call, classifies stdout-only `"nothing to commit"`, returns `none` for directories in `showFile?`, and blocks option injection. -/
def test_git_raw_mkApi_isolationAndGuards
    {runner} [NondetTest runner]
    (mkApi : RawGitOpsM (StateM GitCliMockState) → GitApiM (StateM GitCliMockState)) :
    runner Unit := do
  let st₀ : GitCliMockState :=
    { inheritedEnv := #[("GIT_DIR", "/evil/.git"), ("LC_ALL", "fr_FR.UTF-8"), ("GIT_TERMINAL_PROMPT", "1"), ("PATH", "/usr/bin")]
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
    env.toList.contains ("LC_ALL", none) ∧
    env.toList.contains ("LC_ALL", some "C") ∧
    env.toList.contains ("GIT_TERMINAL_PROMPT", some "0") ∧
    env.toList.contains ("GIT_LITERAL_PATHSPECS", some "1") ∧
    env.toList.contains ("GIT_CONFIG_VALUE_0", some "all"))
  NondetTest.assert (sRes = .ok none ∧ stShow.callCount = 2)
  NondetTest.assert (∃ e, fRes = .error e ∧ e.kind = .invalidInput ∧ stFetch.callCount = 0)
  NondetTest.assert (∃ e, aRes = .error e ∧ e.kind = .invalidInput ∧ stAdd.callCount = 0)
  NondetTest.assert (∃ e, colonRes = .error e ∧ e.kind = .invalidInput ∧ stColon.callCount = 0)

/-- `Impl.mkApiM` delegates `repoRoot`, `commonDir`, `headBranch?`, `headState`, `mergeBase?`, `status`, `diffNameStatus`, and `listWorktrees` to `ops.execGit` and the pure `Model.parse*` parsers rather than returning hardcoded constants. -/
def test_git_raw_mkApi_queryAndParserDelegation
    {runner} [NondetTest runner]
    (mkApi : RawGitOpsM (StateM GitCliMockState) → GitApiM (StateM GitCliMockState)) :
    runner Unit := do
  let rootStr := "/mock/root"
  let commStr := "/mock/root/.git"
  let sha1 := String.ofList (List.replicate 40 '1')
  let sha2 := String.ofList (List.replicate 40 '2')
  let sha0 := String.ofList (List.replicate 40 '0')
  let statusBytes := " M a.txt\x00?? b.txt\x00".toUTF8
  let diffBytes := "R090\x00old.txt\x00new.txt\x00".toUTF8
  let wtBytes := ("worktree " ++ rootStr ++ "\x00HEAD " ++ sha1 ++ "\x00branch refs/heads/topic\x00\x00").toUTF8
  let st₀ : GitCliMockState :=
    { handler := fun req _ =>
        if req.args.toList.contains "--show-toplevel" then
          .ok { exitCode := 0, stdout := (rootStr ++ "\n").toUTF8, stderr := ByteArray.empty }
        else if req.args.toList.contains "--git-common-dir" then
          .ok { exitCode := 0, stdout := (commStr ++ "\n").toUTF8, stderr := ByteArray.empty }
        else if req.args.toList.contains "symbolic-ref" then
          .ok { exitCode := 0, stdout := "refs/heads/topic\n".toUTF8, stderr := ByteArray.empty }
        else if req.args.toList.contains "--verify" then
          .ok { exitCode := 0, stdout := (sha1 ++ "\n").toUTF8, stderr := ByteArray.empty }
        else if req.args.toList.contains "merge-base" then
          .ok { exitCode := 0, stdout := (sha0 ++ "\n").toUTF8, stderr := ByteArray.empty }
        else if req.args.toList.contains "--porcelain=v1" then
          .ok { exitCode := 0, stdout := statusBytes, stderr := ByteArray.empty }
        else if req.args.toList.contains "--name-status" then
          .ok { exitCode := 0, stdout := diffBytes, stderr := ByteArray.empty }
        else if req.args.toList.contains "worktree" then
          .ok { exitCode := 0, stdout := wtBytes, stderr := ByteArray.empty }
        else
          .ok { exitCode := 0, stdout := ByteArray.empty, stderr := ByteArray.empty } }
  let api := mkApi mockRawOps
  let (rrRes, stRr) := (api.repoRoot "/repo").run st₀
  let (cdRes, stCd) := (api.commonDir "/repo").run st₀
  let (hbRes, stHb) := (api.headBranch? "/repo").run st₀
  let (hsRes, stHs) := (api.headState "/repo").run st₀
  let (mbRes, stMb) := (api.mergeBase? "/repo" { hex := sha1 } { hex := sha2 }).run st₀
  let (stRes, stSt) := (api.status "/repo").run st₀
  let (dfRes, stDf) := (api.diffNameStatus "/repo" "HEAD" none #[]).run st₀
  let (wtRes, stWt) := (api.listWorktrees "/repo").run st₀
  NondetTest.assert (rrRes = .ok rootStr ∧ stRr.callCount = 1)
  NondetTest.assert (cdRes = .ok commStr ∧ stCd.callCount = 1)
  NondetTest.assert (hbRes = .ok (some { raw := "topic" }) ∧ stHb.callCount = 1)
  NondetTest.assert (hsRes = .ok (.attached { raw := "topic" } (some { hex := sha1 })) ∧ stHs.callCount = 2)
  NondetTest.assert (mbRes = .ok (some { hex := sha0 }) ∧ stMb.callCount = 1)
  NondetTest.assert (stRes = parsePorcelainStatusZ statusBytes ∧ stSt.callCount = 1)
  NondetTest.assert (dfRes = parseDiffNameStatusZ diffBytes ∧ stDf.callCount = 1)
  NondetTest.assert (wtRes = parseWorktreeListPorcelain wtBytes ∧ stWt.callCount = 1)


/-- `Impl.mkApiM` delegates remaining query and mutation operations (`isRepo`, `headCommit?`,
    `revParseCommit`, `isAncestor`, `showFile?` blob read, `init`, `clone`, `add`, `createBranch`,
    `deleteBranch`, `checkout`, `switch`, `reset`, and `fetch`) with exact CLI flags. -/
def test_git_raw_mkApi_mutationAndFlagDelegation
    {runner} [NondetTest runner]
    (mkApi : RawGitOpsM (StateM GitCliMockState) → GitApiM (StateM GitCliMockState)) :
    runner Unit :=
  rawMkApiMutationAndFlagDelegationBody mkApi

/-- `mkApiM` delegates `commit` (`-m` message, `--allow-empty`, author/committer env), `reset .soft`, `diffNameStatus`, `worktreeAdd`, `worktreeRemove`, and non-force flag variants accurately to `RawGitOpsM`. -/
def test_git_raw_mkApi_extendedFlagAndCommitDelegation
    {runner} [NondetTest runner]
    (mkApi : RawGitOpsM (StateM GitCliMockState) → GitApiM (StateM GitCliMockState)) :
    runner Unit :=
  rawMkApiExtendedFlagAndCommitDelegationBody mkApi

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


/-- `evalGitApi` distinguishes `reset .soft` (retaining staged index) from `reset .mixed` (resetting index while keeping working tree), honors `diffNameStatus` pathspec filters, prunes deleted remote-tracking refs under `fetch` iff `prune = true`, rejects safe `deleteBranch` (`force = false`) on unmerged branches with `.commandFailed`, and rejects `switch` (`create = true`, `force = false`) on existing branches with `.alreadyExists`. -/
def test_git_api_resetDiffFetchDeleteAndSwitch_semantics
    {runner} [NondetTest runner] (api : GitApiM (StateM GitRepoState)) : runner Unit :=
  apiResetDiffFetchDeleteAndSwitchBody api

/-- `mkApiM` forwards `--force` on existing-branch `switch`, `.ref` `checkout`, and detached `worktreeAdd`, supports default basename `worktreeAdd`, and delegates general revision specs (including short SHAs and `HEAD@{0}`) directly to `git`. -/
def test_git_raw_mkApi_forceAndShortShaGuards
    {runner} [NondetTest runner]
    (mkApi : RawGitOpsM (StateM GitCliMockState) → GitApiM (StateM GitCliMockState)) :
    runner Unit :=
  rawMkApiForceAndShortShaGuardsBody mkApi

/-- `mkApiM` delegates secondary revision parameters (`diffNameStatus` `revB?` and `showFile?` `rev`) and 40-hex `worktreeAdd` targets directly to stock `git` without extra subprocess probes. -/
def test_git_raw_mkApi_secondaryShortShaAnd40HexWorktreeGuards
    {runner} [NondetTest runner]
    (mkApi : RawGitOpsM (StateM GitCliMockState) → GitApiM (StateM GitCliMockState)) : runner Unit := do
  let sha1 := String.ofList (List.replicate 40 '1')
  let br40 := String.ofList (List.replicate 40 'f')
  let mkHandler : GitRawRequest → Nat → Except GitError GitRawOutput :=
    fun req _ =>
      if req.args.toList.contains "--verify" && !req.args.toList.contains "show-ref" then
        .ok { exitCode := 0, stdout := (sha1 ++ "\n").toUTF8, stderr := ByteArray.empty }
      else
        .ok { exitCode := 0, stdout := ByteArray.empty, stderr := ByteArray.empty }
  let st : GitCliMockState := { handler := mkHandler }
  let api := mkApi mockRawOps
  let (wa40Ok, stWa40) := (api.worktreeAdd "/repo" { path := "/wt40", target? := some br40 }).run st
  let (dfBShort, stDfB) := (api.diffNameStatus "/repo" "HEAD" (some "1111111") #[]).run st
  let (sfShort, stSf) := (api.showFile? "/repo" "1111111" "f.txt").run st
  NondetTest.assert (wa40Ok = .ok () ∧ stWa40.recordedRequests =
    [{ cwd := some "/repo", args := #["worktree", "add", "--", "/wt40", br40] }])
  NondetTest.assert (dfBShort = .ok #[] ∧ stDfB.recordedRequests.getLast? =
    some { cwd := some "/repo", args := #["diff", "--name-status", "-z", "HEAD", "1111111", "--"] })
  NondetTest.assert (sfShort = .ok none ∧ stSf.recordedRequests.getLast? =
    some { cwd := some "/repo", args := #["cat-file", "-t", sha1 ++ ":f.txt"] })

end LeanSwe.Git
