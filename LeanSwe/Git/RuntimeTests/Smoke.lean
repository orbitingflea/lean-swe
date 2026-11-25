import LeanSwe.Git.Impl
import LeanSwe.Git.Interface
import LeanSwe.Git.RuntimeTests.Helpers

namespace LeanSwe.Git.RuntimeTests

open LeanSwe.Git
open LeanSwe.Git.Model

/-- Helper `runIntegrationSmoke`. -/
def runIntegrationSmoke : IO Unit := do
  withTempDirIO fun root => do
    let nonRepo := root ++ "/nonrepo"
    IO.FS.createDirAll nonRepo
    assertTrue (!(← assertOk (← Git.isRepo nonRepo) "isRepo nonRepo")) "nonRepo reports false"
    assertErrKind (← Git.repoRoot nonRepo) .notARepo "repoRoot nonRepo fails with notARepo"

    let bareDir := root ++ "/bare.git"
    assertOk (← Git.init bareDir true (some mainRef)) "init bare repo"
    assertTrue (← assertOk (← Git.isRepo bareDir) "isRepo bare") "bare isRepo true"
    assertErrKind (← Git.repoRoot bareDir) .notARepo "repoRoot on bare repo returns notARepo"
    let bareCommon ← assertOk (← Git.commonDir bareDir) "commonDir bare"
    let bareReal ← IO.FS.realPath bareDir
    assertTrue (bareCommon == bareReal.toString) "bare commonDir matches bare path"
    let bareWts ← assertOk (← Git.listWorktrees bareDir) "listWorktrees bare"
    assertTrue (bareWts.size == 1 && bareWts[0]!.isBare && bareWts[0]!.head? == none)
      "bare worktree list parsed without HEAD"

    let repo := root ++ "/repo"
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

    IO.FS.createDirAll (repo ++ "/subdir")
    IO.FS.writeFile (repo ++ "/subdir/nested.txt") "nested\n"
    IO.FS.writeFile (repo ++ "/a b.txt") "hello world\n"
    assertOk (← Git.add repo #["a b.txt", "subdir/nested.txt"] false) "add explicit files"
    let c2 ← assertOk (← Git.commit repo (testAuthorOpts "add files" false)) "commit c2"
    let blob? ← assertOk (← Git.showFile? repo "HEAD" "a b.txt") "showFile? blob"
    assertTrue (blob? == some "hello world\n".toUTF8) "showFile? reads exact blob bytes"
    assertTrue ((← assertOk (← Git.showFile? repo "HEAD" "subdir") "showFile? tree") == none)
      "showFile? on directory tree returns none"

    let featRef ← assertOk (mkRefName "feat") "mkRefName feat"
    assertOk (← Git.switch repo featRef true (some c2.hex) false) "switch -c feat at c2"
    assertOk (← Git.switch repo featRef true (some c1.hex) true) "switch -C resets existing branch"
    assertTrue ((← assertOk (← Git.headCommit? repo) "headCommit? after switch -C") == some c1)
      "switch --force -C moved existing feat branch to c1"
    assertOk (← Git.checkout repo (.branch mainRef) false) "checkout main after switch -C"
    assertOk (← Git.reset repo .hard "HEAD") "reset --hard"

    let diffFiltered ← assertOk (← Git.diffNameStatus repo c1.hex (some c2.hex) #["subdir"])
      "diffNameStatus with path filter"
    assertTrue (diffFiltered.size == 1 && diffFiltered[0]!.path == "subdir/nested.txt")
      "diffNameStatus path filter restricts output to subdir/nested.txt"

    let customMsg := "subject line\n\ndetailed body"
    let cCustom ← assertOk (← Git.commit repo
      { message := customMsg
        allowEmpty := true
        authorName := some "Alice Verifier"
        authorEmail := some "alice@verifier.invalid" }) "commit custom author/message"
    let logOut ← runProcRaw "git"
      #["log", "-1", "--format=%an|%ae|%cn|%ce|%B", cCustom.hex] (some repo)
    let logStr := (String.fromUTF8? logOut.stdout).getD ""
    assertTrue (logStr.startsWith "Alice Verifier|alice@verifier.invalid|Alice Verifier|alice@verifier.invalid|subject line\n\ndetailed body")
      "commit records exact author, committer, and cleaned message"

    assertOk (← Git.reset repo .soft c1.hex) "reset --soft to c1"
    let stAfterSoft ← assertOk (← Git.status repo) "status after reset --soft"
    assertTrue (stAfterSoft.size == 2 && stAfterSoft.all (fun e => e.indexStatus == some .added && e.worktreeStatus == none))
      "reset --soft preserves index entries as staged additions"
    assertOk (← Git.reset repo .mixed c1.hex) "reset --mixed to c1"
    let stAfterMixed ← assertOk (← Git.status repo) "status after reset --mixed"
    assertTrue (stAfterMixed.any (fun e => e.indexStatus == some .untracked))
      "reset --mixed unstages entries while preserving working tree files"
    assertOk (← Git.reset repo .hard c2.hex) "reset --hard back to c2"

    let wtForcePath := root ++ "/wt-force"
    assertOk (← Git.worktreeAdd repo { path := wtForcePath, detach := true }) "worktreeAdd detach"
    IO.FS.writeFile (wtForcePath ++ "/dirty.txt") "untracked\n"
    assertErrKind (← Git.worktreeRemove repo wtForcePath false) .dirtyWorktree
      "worktreeRemove without force rejects dirty worktree"
    assertOk (← Git.worktreeRemove repo wtForcePath true) "worktreeRemove --force removes dirty worktree"

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

    let shortPrefix := String.ofList (c2.hex.toList.take 7)
    let rpShortOld ← assertOk (← Git.revParseCommit repo shortPrefix) "revParseCommit resolves short SHA"
    assertTrue (rpShortOld == c2) "revParseCommit short SHA matches c2"
    assertOk (← Git.reset repo .hard shortPrefix) "reset accepts short SHA"
    assertOk (← Git.checkout repo (.ref shortPrefix) false) "checkout .ref accepts short SHA"
    assertOk (← Git.checkout repo (.branch mainRef) false) "checkout back to main"
    assertOk (← Git.switch repo { raw := "short-sw" } true (some shortPrefix) false)
      "switch startPoint accepts short SHA"
    assertOk (← Git.switch repo mainRef false none false) "switch back to main"
    assertOk (← Git.deleteBranch repo { raw := "short-sw" } true) "cleanup short-sw"
    assertOk (← Git.createBranch repo { raw := "short-br" } (some shortPrefix) false)
      "createBranch startPoint accepts short SHA"
    assertOk (← Git.deleteBranch repo { raw := "short-br" } true) "cleanup short-br"
    let _ ← assertOk (← Git.diffNameStatus repo shortPrefix none #[]) "diffNameStatus accepts short SHA"
    let _ ← assertOk (← Git.diffNameStatus repo "HEAD" (some shortPrefix) #[]) "diffNameStatus revB accepts short SHA"
    let _ ← assertOk (← Git.showFile? repo shortPrefix "a b.txt") "showFile? accepts short SHA"
    let wtShortPath := root ++ "/wt-short"
    assertOk (← Git.worktreeAdd repo { path := wtShortPath, newBranch? := some { raw := "wt-sh" }, target? := some shortPrefix })
      "worktreeAdd target accepts short SHA"
    assertOk (← Git.worktreeRemove repo wtShortPath true) "cleanup wt-short"
    assertOk (← Git.deleteBranch repo { raw := "wt-sh" } true) "cleanup wt-sh"

    let forceBr : RefName := { raw := "force-target" }
    assertOk (← Git.switch repo forceBr true (some c1.hex) false) "create force-target at c1"
    IO.FS.writeFile (repo ++ "/only-ft.txt") "ft\n"
    assertOk (← Git.add repo #["only-ft.txt"] false) "stage only-ft"
    let _ ← assertOk (← Git.commit repo (testAuthorOpts "ft commit" false)) "commit ft"
    assertOk (← Git.switch repo mainRef false none false) "switch back to main"
    IO.FS.writeFile (repo ++ "/only-ft.txt") "untracked-collision\n"
    assertErrKind (← Git.switch repo forceBr false none false) .dirtyWorktree
      "switch existing without force rejects collision"
    assertOk (← Git.switch repo forceBr false none true) "switch existing with force overwrites collision"
    assertErrKind (← Git.switch repo mainRef true none false) .alreadyExists
      "switch -c on existing branch fails with alreadyExists"
    IO.FS.writeFile (repo ++ "/a b.txt") "dirty-for-ref-co\n"
    assertErrKind (← Git.checkout repo (.ref mainRef.raw) false) .dirtyWorktree
      "checkout .ref without force rejects dirty file"
    assertOk (← Git.checkout repo (.ref mainRef.raw) true) "checkout .ref with force overwrites dirty file"
    assertErrKind (← Git.deleteBranch repo forceBr false) .commandFailed
      "deleteBranch without force rejects unmerged branch"
    assertOk (← Git.deleteBranch repo forceBr true) "deleteBranch with force deletes unmerged branch"

/-- Helper `runExtendedParityAndGuardSmoke`. -/
def runExtendedParityAndGuardSmoke : IO Unit :=
  withTempDirIO fun root => do
    let repo := root ++ "/repo"
    let c1 ← initCommittedRepo repo
    let mainRef : RefName := { raw := "main" }

    let br40Raw := String.ofList (List.replicate 40 'f')
    let br40Ref : RefName := { raw := br40Raw }
    assertOk (← Git.createBranch repo br40Ref (some c1.hex) false) "create 40-hex local branch"
    let wt40Path := root ++ "/wt-hex40"
    assertErrKind (← Git.worktreeAdd repo { path := wt40Path, target? := some br40Raw }) .invalidRef
      "stock git worktreeAdd rejects ambiguous bare 40-hex branch not equal to a commit object"
    assertOk (← Git.worktreeAdd repo { path := wt40Path, target? := some ("refs/heads/" ++ br40Raw) })
      "worktreeAdd accepts explicit refs/heads/<40-hex> detached target"
    assertOk (← Git.worktreeRemove repo wt40Path false) "remove refs/heads/<40-hex> worktree"
    assertOk (← Git.deleteBranch repo br40Ref true) "delete 40-hex local branch"

    let fetchDstDir := root ++ "/fetch-dst-qualify"
    assertOk (← Git.init fetchDstDir false (some mainRef)) "init fetchDstDir"
    IO.FS.writeFile (fetchDstDir ++ "/seed.txt") "seed\n"
    assertOk (← Git.add fetchDstDir #[] true) "stage seed"
    let _ ← assertOk (← Git.commit fetchDstDir (testAuthorOpts "seed" false)) "commit seed"
    IO.FS.writeFile (repo ++ "/f2.txt") "second\n"
    assertOk (← Git.add repo #["f2.txt"] false) "stage f2"
    let _ ← assertOk (← Git.commit repo (testAuthorOpts "c2" false)) "commit c2"
    assertErrKind (← Git.fetch fetchDstDir repo (some "main:heads/main") false) .commandFailed
      "fetch main:heads/main refuses checked-out main"
    assertOk (← Git.fetch fetchDstDir repo (some (c1.hex ++ ":tags/qual-tag")) false)
      "fetch into tags/qual-tag"
    assertErrKind (← Git.fetch fetchDstDir repo (some "main:tags/qual-tag") false) .commandFailed
      "fetch non-force refuses clobbering existing tags/qual-tag"
    assertOk (← Git.fetch fetchDstDir repo (some "main:remotes/origin/qual") false)
      "fetch into remotes/origin/qual"
    let _ ← assertOk (← Git.revParseCommit fetchDstDir "refs/remotes/origin/qual")
      "revParseCommit refs/remotes/origin/qual"

    let cleanSubBr : RefName := { raw := "cleanns/ok" }
    assertOk (← Git.createBranch repo cleanSubBr (some c1.hex) false) "create cleanns/ok branch"
    let unbornFetchDir := root ++ "/fetch-unborn-glob"
    assertOk (← Git.init unbornFetchDir false (some mainRef)) "init unbornFetchDir"
    assertOk (← Git.fetch unbornFetchDir repo (some "+refs/heads/cleanns/*:refs/heads/*") false)
      "fetch benign glob into refs/heads/*"
    let rpCleanOk ← assertOk (← Git.revParseCommit unbornFetchDir "refs/heads/ok")
      "revParseCommit refs/heads/ok after benign glob"
    assertTrue (rpCleanOk == c1) "benign glob fetched commit matches"

    let ur1 ← assertOk (← Git.defaultOps.execGit (Model.cleanGitEnv #[] #[])
      { cwd := some repo, args := #["update-ref", "refs/pull/42/head", c1.hex] }) "update-ref refs/pull/42/head"
    assertTrue (ur1.exitCode == 0) "update-ref refs/pull/42/head exitCode=0"
    assertOk (← Git.createBranch repo { raw := "feat-alpha" } (some c1.hex) false) "create feat-alpha"
    assertOk (← Git.fetch unbornFetchDir repo (some "+refs/pull/*/head:refs/remotes/origin/pr/*") false)
      "fetch generalized single-star refs/pull/*/head"
    let rpPr42 ← assertOk (← Git.revParseCommit unbornFetchDir "refs/remotes/origin/pr/42")
      "revParseCommit refs/remotes/origin/pr/42"
    assertTrue (rpPr42 == c1) "refs/remotes/origin/pr/42 matches c1"
    assertOk (← Git.fetch unbornFetchDir repo (some "refs/heads/feat*:refs/remotes/origin/feat*") false)
      "fetch generalized single-star refs/heads/feat*"
    let rpFeat ← assertOk (← Git.revParseCommit unbornFetchDir "refs/remotes/origin/feat-alpha")
      "revParseCommit refs/remotes/origin/feat-alpha"
    assertTrue (rpFeat == c1) "refs/remotes/origin/feat-alpha matches c1"
    let ur2 ← assertOk (← Git.defaultOps.execGit (Model.cleanGitEnv #[] #[])
      { cwd := some repo, args := #["update-ref", "-d", "refs/pull/42/head"] }) "delete refs/pull/42/head"
    assertTrue (ur2.exitCode == 0) "update-ref -d refs/pull/42/head exitCode=0"
    assertOk (← Git.fetch unbornFetchDir repo (some "+refs/pull/*/head:refs/remotes/origin/pr/*") true)
      "fetch --prune generalized single-star refs/pull/*/head"
    assertErrKind (← Git.revParseCommit unbornFetchDir "refs/remotes/origin/pr/42") .invalidRef
      "pruned refs/remotes/origin/pr/42 removed"

    let seg255 := repeatCharStr 'a' 255
    let seg256 := repeatCharStr 'a' 256
    assertTrue (Model.validateFsPathArg ("/tmp/" ++ seg255)).isOk "validateFsPathArg accepts 255-byte segment"
    assertErrKind (Model.validateFsPathArg ("/tmp/" ++ seg256)) .invalidInput "validateFsPathArg rejects 256-byte segment"
    assertTrue (Model.validateCloneEndpoint ("/tmp/" ++ seg255)).isOk "validateCloneEndpoint accepts 255-byte segment"
    assertErrKind (Model.validateCloneEndpoint ("/tmp/" ++ seg256)) .invalidInput "validateCloneEndpoint rejects 256-byte segment"
    assertTrue (Model.validateRelRepoPath ("sub/" ++ seg255)).isOk "validateRelRepoPath accepts 255-byte segment"
    assertErrKind (Model.validateRelRepoPath ("sub/" ++ seg256)) .invalidInput "validateRelRepoPath rejects 256-byte segment"
    assertTrue (!Model.isValidRefNameStr (repeatCharStr 'r' 241)) "ref component keeps 240-byte headroom"

    let renRepo := root ++ "/fuzzy-ren"
    assertOk (← Git.init renRepo false (some mainRef)) "init fuzzy-ren"
    let renLines := "r01\nr02\nr03\nr04\nr05\nr06\nr07\nr08\nr09\nr10\n"
    let renEdited := "r01-edited\nr02\nr03\nr04\nr05\nr06\nr07\nr08\nr09\nr10\n"
    IO.FS.writeFile (renRepo ++ "/old.txt") renLines
    assertOk (← Git.add renRepo #["old.txt"] false) "add old.txt"
    let _ ← assertOk (← Git.commit renRepo (testAuthorOpts "ren-base" false)) "commit ren-base"
    IO.FS.removeFile (renRepo ++ "/old.txt")
    IO.FS.writeFile (renRepo ++ "/new.txt") renEdited
    assertOk (← Git.add renRepo #[] true) "stage edited move"
    let stRen ← assertOk (← Git.status renRepo) "status fuzzy rename"
    assertTrue (stRen.any fun e => e.indexStatus == some .renamed && e.path == "new.txt" && e.origPath == some "old.txt")
      "status uses default git fuzzy rename detection"
    let expStUnpaired : Array StatusEntry := #[
      { indexStatus := some .added, worktreeStatus := none, path := "new.txt" },
      { indexStatus := some .deleted, worktreeStatus := none, path := "old.txt" }
    ]
    assertTrue (Model.statusEntriesMatchUpToRenames expStUnpaired stRen)
      "statusEntriesMatchUpToRenames accepts fuzzy rename"
    assertTrue (!Model.statusEntriesMatchUpToRenames expStUnpaired #[{ indexStatus := some .modified, worktreeStatus := none, path := "new.txt" }])
      "statusEntriesMatchUpToRenames rejects non-matching kind"
    let dfRen ← assertOk (← Git.diffNameStatus renRepo "HEAD") "diffNameStatus fuzzy rename"
    assertTrue (dfRen.any fun e => match e.kind with | .renamed s => s < 100 && e.path == "new.txt" && e.origPath == some "old.txt" | _ => false)
      "diffNameStatus uses default git fuzzy rename detection (<100%)"
    let expDfUnpaired : Array DiffEntry := #[
      { kind := .added, path := "new.txt", origPath := none },
      { kind := .deleted, path := "old.txt", origPath := none }
    ]
    assertTrue (Model.diffEntriesMatchUpToRenames expDfUnpaired dfRen)
      "diffEntriesMatchUpToRenames accepts fuzzy rename"
    assertTrue (!Model.diffEntriesMatchUpToRenames expDfUnpaired #[{ kind := .renamed 101, path := "new.txt", origPath := some "old.txt" }])
      "diffEntriesMatchUpToRenames rejects score > 100"

    let nestedTop := root ++ "/nested-top"
    let nestedMid := nestedTop ++ "/sub1"
    let nestedLeaf := nestedMid ++ "/sub2"
    IO.FS.createDirAll nestedLeaf
    assertOk (← Git.init nestedLeaf false (some mainRef)) "init nestedLeaf"
    IO.FS.writeFile (nestedLeaf ++ "/leaf.txt") "leaf\n"
    assertOk (← Git.add nestedLeaf #[] true) "add nestedLeaf"
    let _ ← assertOk (← Git.commit nestedLeaf (testAuthorOpts "leaf commit" false)) "commit nestedLeaf"
    assertOk (← Git.init nestedMid false (some mainRef)) "init nestedMid"
    assertOk (← Git.add nestedMid #[] true) "add nestedMid"
    let _ ← assertOk (← Git.commit nestedMid (testAuthorOpts "mid commit" false)) "commit nestedMid"
    assertOk (← Git.init nestedTop false (some mainRef)) "init nestedTop"
    assertOk (← Git.add nestedTop #[] true) "add nestedTop"
    let _ ← assertOk (← Git.commit nestedTop (testAuthorOpts "top commit" false)) "commit nestedTop"
    IO.FS.writeFile (nestedLeaf ++ "/untracked.txt") "untracked\n"
    let topSt ← assertOk (← Git.status nestedTop) "status on 3-level nested gitlinks"
    assertTrue (topSt.size == 1 && topSt[0]?.map (·.path) == some "sub1")
      "status reports nested untracked dirt on sub1"
    let topDf ← assertOk (← Git.diffNameStatus nestedTop "HEAD" none #[])
      "diffNameStatus on 3-level nested gitlinks"
    assertTrue topDf.isEmpty "diffNameStatus ignores untracked files in nested submodules"

    let v2Root := root ++ "/v2-checks"
    let v2Repo := v2Root ++ "/repo"
    let v2WtDef := v2Root ++ "/wt-def"
    let v2Clone := v2Root ++ "/clone"
    IO.FS.createDirAll v2Repo
    assertOk (← Git.init v2Repo false (some mainRef)) "v2 init"
    IO.FS.writeFile (v2Repo ++ "/a.txt") "v2\n"
    assertOk (← Git.add v2Repo #["a.txt"] false) "v2 add"
    let cV2 ← assertOk (← Git.commit v2Repo (testAuthorOpts "  pad  \n  \n\n\nline2 \t \r\n\n  " false)) "v2 commit"
    let catOut ← assertOk (← Git.defaultOps.execGit (Model.cleanGitEnv #[] #[]) { cwd := some v2Repo, args := #["cat-file", "commit", cV2.hex] }) "v2 cat-file"
    let catStr := String.fromUTF8? catOut.stdout |>.getD ""
    assertTrue (catStr.endsWith "\n\n  pad\n\nline2\n") "v2 commit message cleanup matches git -m"
    assertErrKind (← Git.commit v2Repo (testAuthorOpts "   \n" true)) .commandFailed "v2 whitespace-only allowEmpty fails"
    let shortV2 := String.ofList (cV2.hex.toList.take 7)
    let rpReflog ← assertOk (← Git.revParseCommit v2Repo "HEAD@{0}") "v2 revParse reflog"
    let rpShort ← assertOk (← Git.revParseCommit v2Repo shortV2) "v2 revParse short sha"
    assertTrue (rpReflog == cV2 && rpShort == cV2) "v2 extended revParseCommit matches commit"
    let sfReflog ← assertOk (← Git.showFile? v2Repo "HEAD@{0}" "a.txt") "v2 showFile? reflog"
    assertTrue (sfReflog == some "v2\n".toUTF8) "v2 showFile? reflog content"
    let dfTree ← assertOk (← Git.diffNameStatus v2Repo "HEAD^{tree}" none #[]) "v2 diffNameStatus tree rev"
    assertTrue dfTree.isEmpty "v2 diffNameStatus tree rev empty"
    assertErrKind (← Git.revParseCommit v2Repo "HEAD^{tree}") .invalidRef "v2 revParseCommit rejects tree object"
    assertOk (← Git.worktreeAdd v2Repo { path := v2WtDef }) "v2 default basename worktreeAdd"
    let wtDefBr ← assertOk (← Git.headBranch? v2WtDef) "v2 default basename branch"
    assertTrue (wtDefBr == some { raw := "wt-def" }) "v2 default basename branch name"
    let dwimBr : RefName := { raw := "dwim-br" }
    assertOk (← Git.createBranch v2Repo dwimBr (some cV2.hex) false) "v2 create dwim-br"
    assertOk (← Git.clone v2Repo v2Clone {}) "v2 clone"
    assertOk (← Git.checkout v2Clone (.branch dwimBr) false) "v2 remote dwim checkout"
    assertTrue ((← assertOk (← Git.headBranch? v2Clone) "v2 dwim checkout head") == some dwimBr) "v2 dwim checkout branch"
    assertOk (← Git.switch v2Clone mainRef false none false) "v2 switch main"
    assertOk (← Git.deleteBranch v2Clone dwimBr true) "v2 delete local dwim-br"
    assertOk (← Git.switch v2Clone dwimBr false none false) "v2 remote dwim switch"
    assertTrue ((← assertOk (← Git.headBranch? v2Clone) "v2 dwim switch head") == some dwimBr) "v2 dwim switch branch"
    let br40 := String.ofList (List.replicate 40 'e')
    assertOk (← Git.createBranch v2Repo { raw := br40 } (some cV2.hex) false) "v2 create 40-hex branch"
    let wa40Res ← Git.worktreeAdd v2Repo { path := v2Root ++ "/wt40-readonly", target? := some br40 }
    assertErrKind wa40Res .invalidRef "v2 stock git rejects bare 40-hex branch name"
    assertTrue (!(← System.FilePath.pathExists (v2Root ++ "/wt40-readonly"))) "v2 40-hex rejection is read-only"
    let v2Sub := v2Repo ++ "/sub"
    IO.FS.createDirAll v2Sub
    IO.FS.writeFile (v2Repo ++ "/pdot.txt") "dot1\n"
    IO.FS.writeFile (v2Sub ++ "/s.txt") "sub1\n"
    assertOk (← Git.add v2Repo #["."] false) "v2 add dot"
    let cDot ← assertOk (← Git.commit v2Repo (testAuthorOpts "dot commit" false)) "v2 commit dot"
    IO.FS.writeFile (v2Repo ++ "/pdot.txt") "dot2\n"
    IO.FS.writeFile (v2Sub ++ "/s.txt") "sub2\n"
    let dfDot ← assertOk (← Git.diffNameStatus v2Repo "HEAD" none #["."]) "v2 diff dot"
    let dfDir ← assertOk (← Git.diffNameStatus v2Repo "HEAD" none #["sub/"]) "v2 diff dir/"
    let dfAbs ← assertOk (← Git.diffNameStatus v2Repo "HEAD" none #[v2Repo ++ "/pdot.txt"]) "v2 diff abs in-repo"
    assertTrue (dfDot.size == 2) "v2 diff dot finds both files"
    assertTrue (dfDir.size == 1 && dfDir[0]?.map (·.path) == some "sub/s.txt") "v2 diff dir/ filters sub"
    assertTrue (dfAbs.size == 1 && dfAbs[0]?.map (·.path) == some "pdot.txt") "v2 diff abs in-repo filters pdot.txt"
    assertOk (← Git.add v2Repo #["sub/"] false) "v2 add dir/"
    assertOk (← Git.add v2Repo #[v2Repo ++ "/pdot.txt"] false) "v2 add abs in-repo"
    let cAbs ← assertOk (← Git.commit v2Repo (testAuthorOpts "abs+dir" false)) "v2 commit abs+dir"
    assertTrue (cAbs != cDot) "v2 abs+dir advanced commit"

/-- Helper `runLiteralPathspecAndSpoofSmoke`. -/
def runLiteralPathspecAndSpoofSmoke : IO Unit :=
  withTempDirIO fun root => do
    let repo := root ++ "/lit-repo"
    let _ ← initCommittedRepo repo
    IO.FS.writeFile (repo ++ "/a1.txt") "sibling\n"
    IO.FS.writeFile (repo ++ "/a[12].txt") "bracket\n"
    assertOk (← Git.add repo #["a[12].txt"] false) "add literal a[12].txt"
    let stAfterBracket ← assertOk (← Git.status repo) "status after add a[12].txt"
    let stagedBracket := stAfterBracket.any fun e => e.path == "a[12].txt" && e.indexStatus == some .added
    let untrackedA1 := stAfterBracket.any fun e => e.path == "a1.txt" && e.indexStatus == some .untracked && e.worktreeStatus == some .untracked
    assertTrue stagedBracket "a[12].txt must be staged literally"
    assertTrue untrackedA1 "sibling a1.txt must remain untracked under GIT_LITERAL_PATHSPECS=1"
    assertOk (← Git.add repo #["."] false) "add dot stages both a[12].txt and a1.txt"
    let stAfterDot ← assertOk (← Git.status repo) "status after add ."
    assertTrue (stAfterDot.any fun e => e.path == "a1.txt" && e.indexStatus == some .added) "a1.txt staged by add ."
    let _ ← assertOk (← Git.commit repo (testAuthorOpts "lit-bracket" false)) "commit bracket pair"

    let litPaths : Array String := #["b*.txt", "c?.txt", "d\\e.txt", ":colon.txt", ":(top)x.txt", "-dash.txt"]
    for lp in litPaths do
      assertTrue (!Model.isExtendedPathspec lp) s!"literal pathspec {lp} must not be extended"
      IO.FS.writeFile (repo ++ "/" ++ lp) "v1\n"
    assertOk (← Git.add repo litPaths false) "add literal special-char filenames"
    let _ ← assertOk (← Git.commit repo (testAuthorOpts "lit-specials" false)) "commit special-char filenames"
    for lp in litPaths do
      IO.FS.writeFile (repo ++ "/" ++ lp) "v2\n"
    let litDiff ← assertOk (← Git.diffNameStatus repo "HEAD" none litPaths) "diff literal special-char filenames"
    assertTrue (litDiff.size == litPaths.size) "diff returns every modified literal special-char file"
    assertErrKind (← Git.add repo #["*.txt"] false) .notFound "missing literal *.txt is notFound"
    assertErrKind (← Git.add repo #[":(exclude)a1.txt"] false) .notFound "missing literal :(exclude) is notFound"
    assertErrKind (← Git.add repo #["-f"] false) .notFound "missing literal -f is notFound"
    let missDiff ← assertOk (← Git.diffNameStatus repo "HEAD" none #[":(exclude)a[12].txt", "*.txt", "-f"]) "diff missing literals empty"
    assertTrue missDiff.isEmpty "diff missing literal special pathspecs empty"
    assertErrKind (← Git.add repo #["already exists.txt"] false) .notFound "spoofed phrase already exists.txt missing is notFound"
    assertErrKind (← Git.add repo #["not a git repository.txt"] false) .notFound "spoofed phrase not a git repository.txt missing is notFound"


end LeanSwe.Git.RuntimeTests
