import Core.Assumptions
import LeanSwe.Git.Impl
import LeanSwe.Git.Interface
import LeanSwe.Git.RuntimeTests.Helpers

namespace LeanSwe.Git.RuntimeTests

open LeanSwe.Git
open LeanSwe.Git.Model

/-- Runtime assumption check for `LeanSwe.Git.assume_git_defaultRawOps_stripsPoisonedGitEnvAndHonorsBareConfig`. -/
def assume_git_defaultRawOps_stripsPoisonedGitEnvAndHonorsBareConfig : IO Unit :=
  withTempDirIO fun root => do
    let repo := root ++ "/repo"
    let c1 ← initCommittedRepo repo
    let poisonedOps : RawGitOps :=
      { listEnv := do
          match ← defaultOps.listEnv with
          | .error e => return .error e
          | .ok env => return .ok (env ++ #[
              ("GIT_DIR", "/nonexistent/evil/.git"),
              ("GIT_WORK_TREE", "/nonexistent/evil"),
              ("GIT_INDEX_FILE", "/nonexistent/evil/index"),
              ("GIT_AUTHOR_NAME", "Evil Author")
            ])
        execGit := defaultOps.execGit }
    let poisonedApi := Impl.mkApiM poisonedOps
    assertTrue ((← assertOk (← poisonedApi.headCommit? repo) "poisoned headCommit?") == some c1)
      "poisoned GIT_* env stripped before execGit"
    let bareDir := root ++ "/bare.git"
    assertOk (← Git.init bareDir true (some mainRef)) "init bare repo"
    assertTrue (← assertOk (← Git.isRepo bareDir) "bare isRepo") "bare repo recognized"
    assertErrKind (← Git.repoRoot bareDir) .notARepo "bare repoRoot returns notARepo"
    let bareReal ← IO.FS.realPath bareDir
    assertTrue ((← assertOk (← Git.commonDir bareDir) "bare commonDir") == bareReal.toString)
      "bare commonDir matches realPath"

/-- Runtime assumption check for `LeanSwe.Git.assume_git_status_porcelainV1Z_emitsUnquotedAndDestFirstRename`. -/
def assume_git_status_porcelainV1Z_emitsUnquotedAndDestFirstRename : IO Unit :=
  withTempDirIO fun root => do
    let repo := root ++ "/repo"
    assertOk (← Git.init repo false (some mainRef)) "init status repo"
    IO.FS.writeFile (repo ++ "/a b.txt") "hello\n"
    IO.FS.writeFile (repo ++ "/old name.txt") "rename me\n"
    assertOk (← Git.add repo #["a b.txt", "old name.txt"] false) "add initial"
    let _ ← assertOk (← Git.commit repo (testAuthorOpts "init" false)) "commit initial"
    IO.FS.writeFile (repo ++ "/new name.txt") "rename me\n"
    IO.FS.removeFile (repo ++ "/old name.txt")
    assertOk (← Git.add repo #[] true) "stage rename"
    IO.FS.writeFile (repo ++ "/a b.txt") "modified\n"
    IO.FS.writeFile (repo ++ "/un track.txt") "untracked\n"
    let entries ← assertOk (← Git.status repo) "status"
    assertTrue (entries.toList.contains
      { indexStatus := some .renamed, worktreeStatus := none, path := "new name.txt", origPath := some "old name.txt" })
      "status -z destination-first rename"
    assertTrue (entries.toList.contains
      { indexStatus := none, worktreeStatus := some .modified, path := "a b.txt" })
      "status -z unquoted space path modified"
    assertTrue (entries.toList.contains
      { indexStatus := some .untracked, worktreeStatus := some .untracked, path := "un track.txt" })
      "status -z unquoted space path untracked"

/-- Runtime assumption check for `LeanSwe.Git.assume_git_diffNameStatus_porcelainZ_emitsSourceFirstRename`. -/
def assume_git_diffNameStatus_porcelainZ_emitsSourceFirstRename : IO Unit :=
  withTempDirIO fun root => do
    let repo := root ++ "/repo"
    assertOk (← Git.init repo false (some mainRef)) "init diff repo"
    IO.FS.writeFile (repo ++ "/src name.txt") "same payload for rename detection\n"
    assertOk (← Git.add repo #["src name.txt"] false) "add src"
    let c1 ← assertOk (← Git.commit repo (testAuthorOpts "c1" false)) "c1"
    IO.FS.writeFile (repo ++ "/dst name.txt") "same payload for rename detection\n"
    IO.FS.removeFile (repo ++ "/src name.txt")
    IO.FS.writeFile (repo ++ "/added file.txt") "new\n"
    assertOk (← Git.add repo #[] true) "stage rename + add"
    let c2 ← assertOk (← Git.commit repo (testAuthorOpts "c2" false)) "c2"
    let diffs ← assertOk (← Git.diffNameStatus repo c1.hex (some c2.hex) #[]) "diffNameStatus"
    assertTrue (diffs.any fun d =>
      d.path == "dst name.txt" && d.origPath == some "src name.txt" &&
      match d.kind with | .renamed _ => true | _ => false)
      "diff -z source-first rename mapped to origPath/path"
    assertTrue (diffs.any fun d => d.path == "added file.txt" && d.kind == .added)
      "diff -z added entry"

/-- Runtime assumption check for `LeanSwe.Git.assume_git_listWorktrees_porcelainZ_emitsBareUnbornAndLinkedStanzas`. -/
def assume_git_listWorktrees_porcelainZ_emitsBareUnbornAndLinkedStanzas : IO Unit :=
  withTempDirIO fun root => do
    let bareDir := root ++ "/bare.git"
    assertOk (← Git.init bareDir true (some mainRef)) "init bare"
    let bareWts ← assertOk (← Git.listWorktrees bareDir) "listWorktrees bare"
    assertTrue (bareWts.size == 1 && bareWts[0]!.isBare && bareWts[0]!.head? == none && bareWts[0]!.branch? == none)
      "bare stanza parsed"

    let unborn := root ++ "/unborn"
    assertOk (← Git.init unborn false (some mainRef)) "init unborn"
    let unbornWts ← assertOk (← Git.listWorktrees unborn) "listWorktrees unborn"
    assertTrue (unbornWts.size == 1 && !unbornWts[0]!.isBare && unbornWts[0]!.head? == none && unbornWts[0]!.branch? == some mainRef)
      "unborn stanza parsed"

    let repo := root ++ "/repo"
    let c1 ← initCommittedRepo repo
    let wtDetached := root ++ "/wt-det"
    assertOk (← Git.worktreeAdd repo { path := wtDetached, detach := true }) "worktreeAdd detached"
    let wtDetReal := (← IO.FS.realPath wtDetached).toString
    let wts ← assertOk (← Git.listWorktrees repo) "listWorktrees linked"
    assertTrue (wts.size == 2) "two worktrees listed"
    assertTrue (wts.any fun w => w.path == wtDetReal && w.isDetached && w.head? == some c1 && w.branch? == none)
      "linked detached worktree stanza parsed"
    assertOk (← Git.worktreeRemove repo wtDetached false) "worktreeRemove detached"

/-- Runtime assumption check for `LeanSwe.Git.assume_git_mergeBase_andIsAncestor_matchDagSemantics`. -/
def assume_git_mergeBase_andIsAncestor_matchDagSemantics : IO Unit :=
  withTempDirIO fun root => do
    let repo := root ++ "/repo"
    let c1 ← initCommittedRepo repo
    IO.FS.writeFile (repo ++ "/f.txt") "c2\n"
    assertOk (← Git.add repo #["f.txt"] false) "add c2"
    let c2 ← assertOk (← Git.commit repo (testAuthorOpts "c2" false)) "c2"
    let featRef : RefName := { raw := "feat" }
    assertOk (← Git.switch repo featRef true none false) "switch -c feat"
    IO.FS.writeFile (repo ++ "/feat.txt") "feat\n"
    assertOk (← Git.add repo #["feat.txt"] false) "add cFeat"
    let cFeat ← assertOk (← Git.commit repo (testAuthorOpts "cFeat" false)) "cFeat"
    assertOk (← Git.switch repo mainRef false none false) "switch main"
    IO.FS.writeFile (repo ++ "/main.txt") "c3\n"
    assertOk (← Git.add repo #["main.txt"] false) "add c3"
    let c3 ← assertOk (← Git.commit repo (testAuthorOpts "c3" false)) "c3"
    assertTrue (← assertOk (← Git.isAncestor repo c1 c1) "reflexive") "c1 <= c1"
    assertTrue (← assertOk (← Git.isAncestor repo c1 c3) "transitive") "c1 <= c3"
    assertTrue (!(← assertOk (← Git.isAncestor repo c3 c1) "antisym")) "not (c3 <= c1)"
    assertTrue (!(← assertOk (← Git.isAncestor repo c3 cFeat) "incomparable")) "not (c3 <= cFeat)"
    assertTrue ((← assertOk (← Git.mergeBase? repo c3 cFeat) "mergeBase") == some c2) "mergeBase == c2"
    runProcChecked "git" #["checkout", "--orphan", "orphan"] (some repo)
    IO.FS.writeFile (repo ++ "/orphan.txt") "orphan\n"
    assertOk (← Git.add repo #["orphan.txt"] false) "add orphan"
    let cOrphan ← assertOk (← Git.commit repo (testAuthorOpts "orphan" false)) "commit orphan"
    assertTrue ((← assertOk (← Git.mergeBase? repo c3 cOrphan) "disjoint mergeBase") == none)
      "disjoint histories have no mergeBase"

/-- Runtime assumption check for `LeanSwe.Git.assume_git_headState_andShowFile_unbornDetachedAndTreeVsBlob`. -/
def assume_git_headState_andShowFile_unbornDetachedAndTreeVsBlob : IO Unit :=
  withTempDirIO fun root => do
    let repo := root ++ "/repo"
    assertOk (← Git.init repo false (some mainRef)) "init"
    assertTrue ((← assertOk (← Git.headState repo) "unborn headState") == .attached mainRef none)
      "unborn attached none"
    IO.FS.createDirAll (repo ++ "/sub")
    IO.FS.writeFile (repo ++ "/sub/item.txt") "payload\n"
    assertOk (← Git.add repo #["sub/item.txt"] false) "add sub/item.txt"
    let c1 ← assertOk (← Git.commit repo (testAuthorOpts "c1" false)) "c1"
    assertTrue ((← assertOk (← Git.headState repo) "attached c1") == .attached mainRef (some c1))
      "attached c1"
    assertOk (← Git.checkout repo (.commit c1) false) "checkout detached"
    assertTrue ((← assertOk (← Git.headState repo) "detached c1") == .detached c1) "detached c1"
    assertTrue ((← assertOk (← Git.showFile? repo "HEAD" "sub/item.txt") "showFile blob") == some "payload\n".toUTF8)
      "showFile blob"
    assertTrue ((← assertOk (← Git.showFile? repo "HEAD" "sub") "showFile tree") == none)
      "showFile tree returns none"
    assertTrue ((← assertOk (← Git.showFile? repo "HEAD" "missing.txt") "showFile missing") == none)
      "showFile missing returns none"

/-- Runtime assumption check for `LeanSwe.Git.assume_git_clone_andFetch_roundTripLocalRefsAndPrune`. -/
def assume_git_clone_andFetch_roundTripLocalRefsAndPrune : IO Unit :=
  withTempDirIO fun root => do
    let src := root ++ "/src"
    let _ ← initCommittedRepo src
    let topicRef : RefName := { raw := "topic" }
    assertOk (← Git.createBranch src topicRef none false) "create topic in src"
    let origin := root ++ "/origin.git"
    assertOk (← Git.clone src origin { bare := true }) "clone --bare"
    let copyDir := root ++ "/copy"
    assertOk (← Git.clone origin copyDir {}) "clone local"
    assertOk (← Git.fetch copyDir origin (some "+refs/heads/*:refs/remotes/origin/*") false) "fetch all"
    let _ ← assertOk (← Git.revParseCommit copyDir "refs/remotes/origin/topic") "topic fetched"
    assertOk (← Git.deleteBranch origin topicRef true) "delete topic in origin"
    assertOk (← Git.fetch copyDir origin (some "+refs/heads/*:refs/remotes/origin/*") true) "fetch --prune"
    assertErrKind (← Git.revParseCommit copyDir "refs/remotes/origin/topic") .invalidRef "pruned remote ref absent"


end LeanSwe.Git.RuntimeTests
