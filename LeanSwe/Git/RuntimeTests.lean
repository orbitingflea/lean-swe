import LeanSwe.Fs.Raw.Types
import LeanSwe.Fs.Raw.Interface
import LeanSwe.Git.Interface

namespace LeanSwe.Git.RuntimeTests

open LeanSwe.Git
open LeanSwe.Git.Model

private def assertTrue (cond : Bool) (msg : String) : IO Unit := do
  if !cond then
    throw (IO.userError s!"ASSERTION FAILED: {msg}")

private def assertOk {α : Type} (res : Except GitError α) (msg : String) : IO α := do
  match res with
  | .ok v => return v
  | .error e => throw (IO.userError s!"ASSERTION FAILED: {msg} (unexpected error: {repr e})")

private def assertErrKind {α : Type} (res : Except GitError α) (expected : GitErrorKind)
    (msg : String) : IO Unit := do
  match res with
  | .ok _ => throw (IO.userError s!"ASSERTION FAILED: {msg} (expected error {repr expected}, got ok)")
  | .error e =>
    if e.kind != expected || e.message == "" then
      throw (IO.userError s!"ASSERTION FAILED: {msg} (got {repr e}, expected {repr expected})")

private def withTempDirIO (f : String → IO Unit) : IO Unit := do
  let res ← LeanSwe.Fs.Raw.withTempDir fun dir => do
    f dir
    pure (.ok ())
  match res with
  | .ok () => pure ()
  | .error e => throw (IO.userError s!"ASSERTION FAILED: withTempDir failed: {e.message}")

private def testAuthorOpts (msg : String) (allowEmpty : Bool := false) : CommitOptions :=
  { message := msg
    allowEmpty := allowEmpty
    authorName := some "LeanSwe Test"
    authorEmail := some "test@leanswe.invalid" }

/-- Execute end-to-end real `git` repository runtime verification tests for `LeanSwe.Git`. -/
def runAll : IO Unit := do
  withTempDirIO fun root => do
    let nonRepo := root ++ "/nonrepo"
    IO.FS.createDirAll nonRepo
    assertTrue (!(← assertOk (← Git.isRepo nonRepo) "isRepo nonRepo")) "nonRepo reports false"
    assertErrKind (← Git.repoRoot nonRepo) .notARepo "repoRoot nonRepo fails with notARepo"

    let bareDir := root ++ "/bare.git"
    assertOk (← Git.init bareDir true (some { raw := "main" })) "init bare repo"
    assertTrue (← assertOk (← Git.isRepo bareDir) "isRepo bare") "bare isRepo true"
    assertErrKind (← Git.repoRoot bareDir) .notARepo "repoRoot on bare repo returns notARepo"
    let bareCommon ← assertOk (← Git.commonDir bareDir) "commonDir bare"
    let bareReal ← IO.FS.realPath bareDir
    assertTrue (bareCommon == bareReal.toString) "bare commonDir matches bare path"
    let bareWts ← assertOk (← Git.listWorktrees bareDir) "listWorktrees bare"
    assertTrue (bareWts.size == 1 && bareWts[0]!.isBare && bareWts[0]!.head? == none)
      "bare worktree list parsed without HEAD"

    let repo := root ++ "/repo"
    let mainRef : RefName ← assertOk (mkRefName "main") "mkRefName main"
    assertOk (← Git.init repo false (some mainRef)) "init repo"
    let repoReal := (← IO.FS.realPath repo).toString
    assertTrue (← assertOk (← Git.isRepo repo) "isRepo repo") "init repo isRepo true"
    assertTrue ((← assertOk (← Git.repoRoot repo) "repoRoot") == repoReal) "repoRoot matches realPath"
    assertTrue ((← assertOk (← Git.commonDir repo) "commonDir") == repoReal ++ "/.git")
      "commonDir matches .git"

    assertTrue ((← assertOk (← Git.headCommit? repo) "unborn headCommit?") == none) "unborn headCommit? is none"
    assertTrue ((← assertOk (← Git.headBranch? repo) "unborn headBranch?") == some mainRef)
      "unborn headBranch? is main"
    assertTrue ((← assertOk (← Git.headState repo) "unborn headState") == .attached mainRef none)
      "unborn headState is attached none"
    assertErrKind (← Git.revParseCommit repo "HEAD") .invalidRef "unborn revParseCommit HEAD fails"

    assertErrKind (← Git.commit repo (testAuthorOpts "empty" false)) .nothingToCommit
      "empty commit without allowEmpty returns nothingToCommit"
    let c1 ← assertOk (← Git.commit repo (testAuthorOpts "initial empty" true)) "allowEmpty commit"
    assertTrue ((← assertOk (← Git.headCommit? repo) "headCommit? c1") == some c1) "headCommit? returns c1"
    assertTrue ((← assertOk (← Git.revParseCommit repo "HEAD") "revParseCommit HEAD") == c1)
      "revParseCommit HEAD returns c1"

    let poisonedOps : RawGitOps :=
      { listEnv := do
          match ← defaultRawOps.listEnv with
          | .error e => return .error e
          | .ok env => return .ok (env ++ #[("GIT_DIR", "/nonexistent/evil/.git"), ("GIT_WORK_TREE", "/tmp")])
        execGit := defaultRawOps.execGit }
    let poisonedApi := Impl.mkApiM poisonedOps
    assertTrue ((← assertOk (← poisonedApi.headCommit? repo) "poisoned GIT_DIR stripped") == some c1)
      "poisoned GIT_* variables stripped before execGit"

    IO.FS.createDirAll (repo ++ "/subdir")
    IO.FS.writeFile (repo ++ "/subdir/nested.txt") "nested\n"
    IO.FS.writeFile (repo ++ "/a b.txt") "hello world\n"
    let stUntracked ← assertOk (← Git.status repo) "status untracked"
    assertTrue (stUntracked.any fun e =>
      e.path == "a b.txt" && e.indexStatus == some .untracked && e.worktreeStatus == some .untracked)
      "status reports untracked file with spaces"

    assertErrKind (← Git.add repo #[] false) .invalidInput "add empty paths with all=false rejected"
    assertOk (← Git.add repo #["a b.txt", "subdir/nested.txt"] false) "add explicit files"
    let c2 ← assertOk (← Git.commit repo (testAuthorOpts "add files" false)) "commit c2"

    let blob? ← assertOk (← Git.showFile? repo "HEAD" "a b.txt") "showFile? blob"
    assertTrue (blob? == some "hello world\n".toUTF8) "showFile? reads exact blob bytes"
    assertTrue ((← assertOk (← Git.showFile? repo "HEAD" "subdir") "showFile? tree") == none)
      "showFile? on directory tree returns none"
    assertTrue ((← assertOk (← Git.showFile? repo "HEAD" "missing.txt") "showFile? missing") == none)
      "showFile? on missing path returns none"
    assertErrKind (← Git.showFile? repo "HEAD:a b.txt" "x") .invalidInput
      "showFile? blocks colon in strict rev"

    IO.FS.writeFile (repo ++ "/new name.txt") "hello world\n"
    IO.FS.removeFile (repo ++ "/a b.txt")
    assertOk (← Git.add repo #[] true) "add --all stages rename"
    let stRename ← assertOk (← Git.status repo) "status rename"
    assertTrue (stRename.toList.contains
      { indexStatus := some .renamed, worktreeStatus := none, path := "new name.txt", origPath := some "a b.txt" })
      "status -z places destination in path and source in origPath"
    let c3 ← assertOk (← Git.commit repo (testAuthorOpts "rename file" false)) "commit c3"

    let diffs ← assertOk (← Git.diffNameStatus repo c2.hex (some c3.hex) #[]) "diffNameStatus rename"
    assertTrue (diffs.any fun d =>
      d.path == "new name.txt" && d.origPath == some "a b.txt" &&
      match d.kind with | .renamed _ => true | _ => false)
      "diff --name-status -z places source in origPath and destination in path"

    assertTrue (← assertOk (← Git.isAncestor repo c1 c3) "isAncestor c1 c3") "c1 is ancestor of c3"
    assertTrue (!(← assertOk (← Git.isAncestor repo c3 c1) "isAncestor c3 c1")) "c3 is not ancestor of c1"

    let featRef ← assertOk (mkRefName "feat") "mkRefName feat"
    assertOk (← Git.switch repo featRef true (some c2.hex) false) "switch -c feat at c2"
    IO.FS.writeFile (repo ++ "/feat.txt") "feat\n"
    assertOk (← Git.add repo #["feat.txt"] false) "add feat.txt"
    let cFeat ← assertOk (← Git.commit repo (testAuthorOpts "feat commit" false)) "commit cFeat"

    let mb? ← assertOk (← Git.mergeBase? repo c3 cFeat) "mergeBase? c3 cFeat"
    assertTrue (mb? == some c2) "mergeBase? returns c2"

    assertOk (← Git.checkout repo (.commit c2) false) "checkout detached c2"
    assertTrue ((← assertOk (← Git.headState repo) "detached headState") == .detached c2)
      "headState reports detached c2"
    assertOk (← Git.checkout repo (.branch mainRef) false) "checkout main"

    IO.FS.writeFile (repo ++ "/new name.txt") "dirty working tree\n"
    assertErrKind (← Git.checkout repo (.branch featRef) false) .dirtyWorktree
      "dirty checkout refused when force=false"
    assertOk (← Git.reset repo .hard "HEAD") "reset --hard cleans working tree"

    assertOk (← Git.switch repo featRef true (some c1.hex) true) "switch -C resets existing branch"
    assertTrue ((← assertOk (← Git.headCommit? repo) "headCommit? after switch -C") == some c1)
      "switch --force -C moved existing feat branch to c1"
    assertOk (← Git.checkout repo (.branch mainRef) false) "checkout main after switch -C"

    let sideRef ← assertOk (mkRefName "side") "mkRefName side"
    let missingRef ← assertOk (mkRefName "no-such-branch") "mkRefName no-such-branch"
    assertErrKind (← Git.switch repo missingRef false none false) .invalidRef
      "switch to missing branch classifies invalid reference as invalidRef"
    let missingCid ← assertOk (mkCommitId (String.ofList (List.replicate 40 '0'))) "mkCommitId missing"
    assertErrKind (← Git.isAncestor repo missingCid c1) .invalidRef
      "isAncestor on unknown commit classifies as invalidRef"
    assertErrKind (← Git.mergeBase? repo missingCid c1) .invalidRef
      "mergeBase? on unknown commit classifies as invalidRef"
    assertOk (← Git.createBranch repo sideRef (some "HEAD") false) "createBranch side"
    assertErrKind (← Git.deleteBranch repo mainRef false) .branchInUse
      "deleteBranch rejects checked-out main"
    assertOk (← Git.deleteBranch repo sideRef false) "deleteBranch removes side"

    let wtPath := root ++ "/wt-linked"
    assertOk (← Git.worktreeAdd repo { path := wtPath, target? := some featRef.raw }) "worktreeAdd feat"
    assertErrKind (← Git.worktreeAdd repo { path := root ++ "/wt-dup", target? := some mainRef.raw })
      .branchInUse "worktreeAdd rejects branch already checked out"
    let wts ← assertOk (← Git.listWorktrees repo) "listWorktrees"
    assertTrue (wts.size == 2) "two worktrees present"
    assertOk (← Git.worktreeRemove repo wtPath false) "worktreeRemove"
    assertTrue ((← assertOk (← Git.listWorktrees repo) "listWorktrees after remove").size == 1)
      "worktree removed cleanly"

    let wtBracketPath := root ++ "/wt-bracket"
    let bracketOk ← assertOk
      (← Git.withWorktree repo { path := wtBracketPath, detach := true } fun path => do
        let hc ← Git.headCommit? path
        pure (hc.map fun _ => path))
      "withWorktree ok"
    assertTrue (bracketOk == wtBracketPath) "withWorktree passed path"
    assertTrue ((← assertOk (← Git.listWorktrees repo) "listWorktrees after withWorktree ok").size == 1)
      "withWorktree cleaned up on ok"

    let boomErr : GitError := { kind := .invalidInput, message := "boom" }
    let bracketErr : Except GitError Unit ←
      Git.withWorktree repo { path := wtBracketPath, detach := true } fun _ =>
        pure (.error boomErr)
    assertErrKind bracketErr .invalidInput "withWorktree preserves action error"
    assertTrue ((← assertOk (← Git.listWorktrees repo) "listWorktrees after withWorktree error").size == 1)
      "withWorktree cleaned up on error"

    let cloneBare := root ++ "/origin.git"
    assertOk (← Git.clone repo cloneBare { bare := true }) "clone --bare"
    assertTrue (← assertOk (← Git.isRepo cloneBare) "bare clone isRepo") "bare clone valid"
    assertErrKind (← Git.fetch repo "--upload-pack=evil" none false) .invalidInput
      "fetch blocks option-like remote"
    assertOk (← Git.fetch repo cloneBare (some "+refs/heads/*:refs/remotes/origin/*") false)
      "fetch from local bare clone"

  IO.println "PASS: LeanSwe.Git runtime tests"

end LeanSwe.Git.RuntimeTests
