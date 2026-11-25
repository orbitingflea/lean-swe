import Core.NondetTest
import LeanSwe.Git.Types
import LeanSwe.Git.Model

namespace LeanSwe.Git

open Core (NondetTest)
open Core.NondetTest
open LeanSwe.Git.Model

/-- Shared body for `test_git_raw_mkApi_mutationAndFlagDelegation`. -/
abbrev rawMkApiMutationAndFlagDelegationBody
    {runner} [NondetTest runner]
    (mkApi : RawGitOpsM (StateM GitCliMockState) → GitApiM (StateM GitCliMockState)) :
    runner Unit := do
  let sha1 := String.ofList (List.replicate 40 '1')
  let sha2 := String.ofList (List.replicate 40 '2')
  let stOk : GitCliMockState :=
    { handler := fun req _ =>
        if req.args == #["cat-file", "-t", sha1 ++ ":f.txt"] then
          .ok { exitCode := 0, stdout := "blob\n".toUTF8, stderr := ByteArray.empty }
        else if req.args == #["cat-file", "blob", sha1 ++ ":f.txt"] then
          .ok { exitCode := 0, stdout := "hello".toUTF8, stderr := ByteArray.empty }
        else if req.args.toList.contains "--verify" && !req.args.toList.contains "show-ref" then
          .ok { exitCode := 0, stdout := (sha1 ++ "\n").toUTF8, stderr := ByteArray.empty }
        else
          .ok { exitCode := 0, stdout := ByteArray.empty, stderr := ByteArray.empty } }
  let stExit1 : GitCliMockState :=
    { handler := fun _ _ =>
        .ok { exitCode := 1, stdout := ByteArray.empty, stderr := ByteArray.empty } }
  let api := mkApi mockRawOps
  let (irRes, stIr) := (api.isRepo "/repo").run stOk
  let (hcRes, stHc) := (api.headCommit? "/repo").run stOk
  let (rpRes, stRp) := (api.revParseCommit "/repo" "HEAD").run stOk
  let (iaTrue, _) := (api.isAncestor "/repo" { hex := sha1 } { hex := sha2 }).run stOk
  let (iaFalse, _) := (api.isAncestor "/repo" { hex := sha1 } { hex := sha2 }).run stExit1
  let (sfRes, stSf) := (api.showFile? "/repo" "HEAD" "f.txt").run stOk
  let (inRes, stIn) := (api.init "/newrepo" true (some { raw := "dev" })).run stOk
  let (clRes, stCl) := (api.clone "/src" "/dst" { bare := true, singleBranch := true, depth? := some 1, branch? := some "dev" }).run stOk
  let (adRes, stAd) := (api.add "/repo" #["a.txt"] true).run stOk
  let (cbRes, stCb) := (api.createBranch "/repo" { raw := "feat" } (some "HEAD") true).run stOk
  let (dbF, stDbF) := (api.deleteBranch "/repo" { raw := "feat" } true).run stOk
  let (dbS, stDbS) := (api.deleteBranch "/repo" { raw := "feat" } false).run stOk
  let (coRes, stCo) := (api.checkout "/repo" (.branch { raw := "feat" }) true).run stOk
  let (swRes, stSw) := (api.switch "/repo" { raw := "feat" } true (some "HEAD") true).run stOk
  let (rsM, stRsM) := (api.reset "/repo" .mixed "HEAD").run stOk
  let (rsH, stRsH) := (api.reset "/repo" .hard "HEAD").run stOk
  let (feRes, stFe) := (api.fetch "/repo" "origin" (some "HEAD") true).run stOk
  NondetTest.assert (irRes = .ok true ∧ stIr.callCount = 1)
  NondetTest.assert (hcRes = .ok (some { hex := sha1 }) ∧ stHc.callCount = 1)
  NondetTest.assert (rpRes = .ok { hex := sha1 } ∧ stRp.callCount = 1)
  NondetTest.assert (iaTrue = .ok true ∧ iaFalse = .ok false)
  NondetTest.assert (sfRes = .ok (some "hello".toUTF8) ∧ stSf.callCount = 3)
  NondetTest.assert (inRes = .ok () ∧ stIn.recordedRequests.getLast? = some { cwd := none, args := #["init", "--bare", "-b", "dev", "--", "/newrepo"] })
  NondetTest.assert (clRes = .ok () ∧ stCl.recordedRequests.getLast? = some { cwd := none, args := #["clone", "--bare", "--single-branch", "--depth", "1", "--branch", "dev", "--", "/src", "/dst"] })
  NondetTest.assert (adRes = .ok () ∧ stAd.recordedRequests.getLast? = some { cwd := some "/repo", args := #["add", "--all", "--", "a.txt"] })
  NondetTest.assert (cbRes = .ok () ∧ stCb.recordedRequests.getLast? = some { cwd := some "/repo", args := #["branch", "-f", "--", "feat", "HEAD"] })
  NondetTest.assert (dbF = .ok () ∧ stDbF.recordedRequests.getLast? = some { cwd := some "/repo", args := #["branch", "-D", "--", "feat"] })
  NondetTest.assert (dbS = .ok () ∧ stDbS.recordedRequests.getLast? = some { cwd := some "/repo", args := #["branch", "-d", "--", "feat"] })
  NondetTest.assert (coRes = .ok () ∧ stCo.recordedRequests.getLast? = some { cwd := some "/repo", args := #["checkout", "--force", "feat", "--"] })
  NondetTest.assert (swRes = .ok () ∧ stSw.recordedRequests.getLast? = some { cwd := some "/repo", args := #["switch", "--force", "-C", "feat", "HEAD"] })
  NondetTest.assert (rsM = .ok () ∧ stRsM.recordedRequests.getLast? = some { cwd := some "/repo", args := #["reset", "--mixed", "HEAD", "--"] })
  NondetTest.assert (rsH = .ok () ∧ stRsH.recordedRequests.getLast? = some { cwd := some "/repo", args := #["reset", "--hard", "HEAD", "--"] })
  NondetTest.assert (feRes = .ok () ∧ stFe.recordedRequests.getLast? = some { cwd := some "/repo", args := #["fetch", "--prune", "origin", "HEAD"] })


/-- Shared body for `test_git_raw_mkApi_extendedFlagAndCommitDelegation`. -/
abbrev rawMkApiExtendedFlagAndCommitDelegationBody
    {runner} [NondetTest runner]
    (mkApi : RawGitOpsM (StateM GitCliMockState) → GitApiM (StateM GitCliMockState)) :
    runner Unit := do
  let sha1 := String.ofList (List.replicate 40 '1')
  let stOk : GitCliMockState :=
    { handler := fun req _ =>
        if req.args.toList.contains "--verify" && !req.args.toList.contains "show-ref" then
          .ok { exitCode := 0, stdout := (sha1 ++ "\n").toUTF8, stderr := ByteArray.empty }
        else
          .ok { exitCode := 0, stdout := ByteArray.empty, stderr := ByteArray.empty } }
  let api := mkApi mockRawOps
  let (cmFull, stCmFull) := (api.commit "/repo"
    { message := "msg\nbody"
      allowEmpty := true
      authorName := some "Alice"
      authorEmail := some "alice@example.com" }).run stOk
  let (cmPlain, stCmPlain) := (api.commit "/repo"
    { message := "plain", allowEmpty := false }).run stOk
  let (rsS, stRsS) := (api.reset "/repo" .soft "HEAD").run stOk
  let (df2, stDf2) := (api.diffNameStatus "/repo" "HEAD" (some "HEAD~1") #["a.txt", "sub/b.txt"]).run stOk
  let (df1, stDf1) := (api.diffNameStatus "/repo" "HEAD" none #[]).run stOk
  let (waF, stWaF) := (api.worktreeAdd "/repo"
    { path := "/wt1", newBranch? := some { raw := "wtbr" }, target? := some "HEAD", force := true }).run stOk
  let (waD, stWaD) := (api.worktreeAdd "/repo"
    { path := "/wt2", detach := true }).run stOk
  let (wrF, stWrF) := (api.worktreeRemove "/repo" "/wt1" true).run stOk
  let (wrS, stWrS) := (api.worktreeRemove "/repo" "/wt1" false).run stOk
  let (coC0, stCoC0) := (api.checkout "/repo" (.commit { hex := sha1 }) false).run stOk
  let (coC1, stCoC1) := (api.checkout "/repo" (.commit { hex := sha1 }) true).run stOk
  let (coR, stCoR) := (api.checkout "/repo" (.ref "HEAD~1") false).run stOk
  let (coB, stCoB) := (api.checkout "/repo" (.branch { raw := "feat" }) false).run stOk
  let (swC, stSwC) := (api.switch "/repo" { raw := "feat" } true none false).run stOk
  let (swE, stSwE) := (api.switch "/repo" { raw := "feat" } false none false).run stOk
  let (adP, stAdP) := (api.add "/repo" #["a.txt"] false).run stOk
  let (adA, stAdA) := (api.add "/repo" #[] true).run stOk
  let (inP, stInP) := (api.init "/newrepo" false none).run stOk
  let (clP, stClP) := (api.clone "/src" "/dst" {}).run stOk
  let (cbP, stCbP) := (api.createBranch "/repo" { raw := "feat" } none false).run stOk
  let (feP, stFeP) := (api.fetch "/repo" "origin" none false).run stOk
  NondetTest.assert (cmFull = .ok { hex := sha1 } ∧ stCmFull.recordedRequests[0]? = some
    { cwd := some "/repo"
      args := #["commit", "--no-gpg-sign", "-m", "msg\nbody", "--allow-empty"]
      extraEnv := #[
        ("GIT_AUTHOR_NAME", some "Alice"),
        ("GIT_COMMITTER_NAME", some "Alice"),
        ("GIT_AUTHOR_EMAIL", some "alice@example.com"),
        ("GIT_COMMITTER_EMAIL", some "alice@example.com")
      ] })
  NondetTest.assert (cmPlain = .ok { hex := sha1 } ∧ stCmPlain.recordedRequests[0]? = some
    { cwd := some "/repo"
      args := #["commit", "--no-gpg-sign", "-m", "plain"]
      extraEnv := #[] })
  NondetTest.assert (rsS = .ok () ∧ stRsS.recordedRequests.getLast? =
    some { cwd := some "/repo", args := #["reset", "--soft", "HEAD", "--"] })
  NondetTest.assert (df2 = .ok #[] ∧ stDf2.recordedRequests.getLast? =
    some { cwd := some "/repo", args := #["diff", "--name-status", "-z", "HEAD", "HEAD~1", "--", "a.txt", "sub/b.txt"] })
  NondetTest.assert (df1 = .ok #[] ∧ stDf1.recordedRequests.getLast? =
    some { cwd := some "/repo", args := #["diff", "--name-status", "-z", "HEAD", "--"] })
  NondetTest.assert (waF = .ok () ∧ stWaF.recordedRequests.getLast? =
    some { cwd := some "/repo", args := #["worktree", "add", "--force", "-b", "wtbr", "--", "/wt1", "HEAD"] })
  NondetTest.assert (waD = .ok () ∧ stWaD.recordedRequests.getLast? =
    some { cwd := some "/repo", args := #["worktree", "add", "--detach", "--", "/wt2"] })
  NondetTest.assert (wrF = .ok () ∧ stWrF.recordedRequests.getLast? =
    some { cwd := some "/repo", args := #["worktree", "remove", "--force", "--", "/wt1"] })
  NondetTest.assert (wrS = .ok () ∧ stWrS.recordedRequests.getLast? =
    some { cwd := some "/repo", args := #["worktree", "remove", "--", "/wt1"] })
  NondetTest.assert (coC0 = .ok () ∧ stCoC0.recordedRequests.getLast? =
    some { cwd := some "/repo", args := #["checkout", "--detach", sha1, "--"] })
  NondetTest.assert (coC1 = .ok () ∧ stCoC1.recordedRequests.getLast? =
    some { cwd := some "/repo", args := #["checkout", "--force", "--detach", sha1, "--"] })
  NondetTest.assert (coR = .ok () ∧ stCoR.recordedRequests.getLast? =
    some { cwd := some "/repo", args := #["checkout", "HEAD~1", "--"] })
  NondetTest.assert (coB = .ok () ∧ stCoB.recordedRequests.getLast? =
    some { cwd := some "/repo", args := #["checkout", "feat", "--"] })
  NondetTest.assert (swC = .ok () ∧ stSwC.recordedRequests.getLast? =
    some { cwd := some "/repo", args := #["switch", "-c", "feat"] })
  NondetTest.assert (swE = .ok () ∧ stSwE.recordedRequests.getLast? =
    some { cwd := some "/repo", args := #["switch", "feat"] })
  NondetTest.assert (adP = .ok () ∧ stAdP.recordedRequests.getLast? =
    some { cwd := some "/repo", args := #["add", "--", "a.txt"] })
  NondetTest.assert (adA = .ok () ∧ stAdA.recordedRequests.getLast? =
    some { cwd := some "/repo", args := #["add", "--all"] })
  NondetTest.assert (inP = .ok () ∧ stInP.recordedRequests.getLast? =
    some { cwd := none, args := #["init", "--", "/newrepo"] })
  NondetTest.assert (clP = .ok () ∧ stClP.recordedRequests.getLast? =
    some { cwd := none, args := #["clone", "--", "/src", "/dst"] })
  NondetTest.assert (cbP = .ok () ∧ stCbP.recordedRequests.getLast? =
    some { cwd := some "/repo", args := #["branch", "--", "feat"] })
  NondetTest.assert (feP = .ok () ∧ stFeP.recordedRequests.getLast? =
    some { cwd := some "/repo", args := #["fetch", "origin"] })


/-- Shared body for `test_git_api_resetDiffFetchDeleteAndSwitch_semantics`. -/
abbrev apiResetDiffFetchDeleteAndSwitchBody
    {runner} [NondetTest runner] (api : GitApiM (StateM GitRepoState)) : runner Unit := do
  let c0 : CommitId := { hex := String.ofList (List.replicate 40 '0') }
  let c1 : CommitId := { hex := String.ofList (List.replicate 40 '1') }
  let eA0 : GitTreeEntry := { kind := .regular false, bytes := "v0".toUTF8 }
  let eA1 : GitTreeEntry := { kind := .regular false, bytes := "v1".toUTF8 }
  let eSub : GitTreeEntry := { kind := .regular false, bytes := "sub1".toUTF8 }
  let tree0 : List (ByteArray × GitTreeEntry) := [("a.txt".toUTF8, eA0)]
  let tree1 : List (ByteArray × GitTreeEntry) := [("a.txt".toUTF8, eA1), ("sub/b.txt".toUTF8, eSub)]
  let sResetDiff : GitRepoState :=
    { vfs := .dir true true [("repo".toUTF8, .dir true true [
        (".git".toUTF8, .dir true true []),
        ("a.txt".toUTF8, .file false "v1".toUTF8),
        ("sub".toUTF8, .dir true true [("b.txt".toUTF8, .file false "sub1".toUTF8)])
      ])]
      repos := [{
        commonDir := "/repo/.git".toUTF8
        commits := [
          { id := c0, parents := [], tree := tree0 },
          { id := c1, parents := [c0], tree := tree1 }
        ]
        refs := [("refs/heads/main", c1)]
        worktrees := [{ rootPath := "/repo".toUTF8, head := .symbolic { raw := "main" }, index := { entries := tree1 } }]
      }] }
  let (softRes, sAfterSoft) := (api.reset "/repo" .soft c0.hex).run sResetDiff
  let (softHc, _) := (api.headCommit? "/repo").run sAfterSoft
  let (softSt, _) := (api.status "/repo").run sAfterSoft
  let (mixRes, sAfterMix) := (api.reset "/repo" .mixed c0.hex).run sResetDiff
  let (mixHc, _) := (api.headCommit? "/repo").run sAfterMix
  let (mixSt, _) := (api.status "/repo").run sAfterMix
  let (diffSub, _) := (api.diffNameStatus "/repo" c0.hex (some c1.hex) #["sub"]).run sResetDiff
  NondetTest.assert (softRes = .ok () ∧ softHc = .ok (some c0) ∧ softSt = .ok #[
    { indexStatus := some .modified, worktreeStatus := none, path := "a.txt" },
    { indexStatus := some .added, worktreeStatus := none, path := "sub/b.txt" }
  ])
  NondetTest.assert (mixRes = .ok () ∧ mixHc = .ok (some c0) ∧ mixSt = .ok #[
    { indexStatus := none, worktreeStatus := some .modified, path := "a.txt" },
    { indexStatus := some .untracked, worktreeStatus := some .untracked, path := "sub/" }
  ])
  NondetTest.assert (diffSub = .ok #[{ kind := .added, path := "sub/b.txt", origPath := none }])

  let sFetch : GitRepoState :=
    { vfs := .dir true true [
        ("origin".toUTF8, .dir true true [(".git".toUTF8, .dir true true [])]),
        ("clone".toUTF8, .dir true true [(".git".toUTF8, .dir true true [])])
      ]
      repos := [
        { commonDir := "/origin/.git".toUTF8
          commits := [{ id := c0, parents := [], tree := tree0 }]
          refs := [("refs/heads/main", c0)]
          worktrees := [{ rootPath := "/origin".toUTF8, head := .symbolic { raw := "main" }, index := { entries := tree0 } }] },
        { commonDir := "/clone/.git".toUTF8
          commits := [{ id := c0, parents := [], tree := tree0 }]
          refs := [("refs/heads/main", c0), ("refs/remotes/origin/main", c0), ("refs/remotes/origin/stale", c0)]
          remotes := [{ name := "origin", url := "/origin", fetchSpecs := ["+refs/heads/*:refs/remotes/origin/*"] }]
          worktrees := [{ rootPath := "/clone".toUTF8, head := .symbolic { raw := "main" }, index := { entries := tree0 } }] }
      ] }
  let (fNoPrune, sNoPrune) := (api.fetch "/clone" "origin" none false).run sFetch
  let (rpKept, _) := (api.revParseCommit "/clone" "origin/stale").run sNoPrune
  let (fPrune, sPruned) := (api.fetch "/clone" "origin" none true).run sFetch
  let (rpGone, _) := (api.revParseCommit "/clone" "origin/stale").run sPruned
  let (rpMain, _) := (api.revParseCommit "/clone" "origin/main").run sPruned
  NondetTest.assert (fNoPrune = .ok () ∧ rpKept = .ok c0)
  NondetTest.assert (fPrune = .ok () ∧ rpMain = .ok c0 ∧ ∃ e, rpGone = .error e ∧ e.kind = .invalidRef)

  let sBranch : GitRepoState :=
    { vfs := .dir true true [("repo".toUTF8, .dir true true [
        (".git".toUTF8, .dir true true []),
        ("a.txt".toUTF8, .file false "v0".toUTF8)
      ])]
      repos := [{
        commonDir := "/repo/.git".toUTF8
        commits := [
          { id := c0, parents := [], tree := tree0 },
          { id := c1, parents := [c0], tree := tree0 }
        ]
        refs := [("refs/heads/main", c0), ("refs/heads/topic", c1)]
        worktrees := [{ rootPath := "/repo".toUTF8, head := .symbolic { raw := "main" }, index := { entries := tree0 } }]
      }] }
  let (delSafe, sDelSafe) := (api.deleteBranch "/repo" { raw := "topic" } false).run sBranch
  let (delForce, sDelForce) := (api.deleteBranch "/repo" { raw := "topic" } true).run sBranch
  let (rpDelTopic, _) := (api.revParseCommit "/repo" "topic").run sDelForce
  let (swCreateDup, sSwDup) := (api.switch "/repo" { raw := "topic" } true none false).run sBranch
  let (swCreateForce, sSwForce) := (api.switch "/repo" { raw := "topic" } true none true).run sBranch
  let (hsAfterSwF, _) := (api.headState "/repo").run sSwForce
  NondetTest.assert (∃ e, delSafe = .error e ∧ e.kind = .commandFailed ∧ sDelSafe = sBranch)
  NondetTest.assert (delForce = .ok () ∧ ∃ e, rpDelTopic = .error e ∧ e.kind = .invalidRef)
  NondetTest.assert (∃ e, swCreateDup = .error e ∧ e.kind = .alreadyExists ∧ sSwDup = sBranch)
  NondetTest.assert (swCreateForce = .ok () ∧ hsAfterSwF = .ok (.attached { raw := "topic" } (some c0)))


/-- Shared body for `test_git_raw_mkApi_forceAndShortShaGuards`. -/
abbrev rawMkApiForceAndShortShaGuardsBody
    {runner} [NondetTest runner]
    (mkApi : RawGitOpsM (StateM GitCliMockState) → GitApiM (StateM GitCliMockState)) :
    runner Unit := do
  let sha1 := String.ofList (List.replicate 40 '1')
  let stOk : GitCliMockState :=
    { handler := fun req _ =>
        if req.args.toList.contains "--verify" && !req.args.toList.contains "show-ref" then
          .ok { exitCode := 0, stdout := (sha1 ++ "\n").toUTF8, stderr := ByteArray.empty }
        else
          .ok { exitCode := 0, stdout := ByteArray.empty, stderr := ByteArray.empty } }
  let api := mkApi mockRawOps
  let (swEF, stSwEF) := (api.switch "/repo" { raw := "feat" } false none true).run stOk
  let (coRF, stCoRF) := (api.checkout "/repo" (.ref "HEAD~1") true).run stOk
  let (waDF, stWaDF) := (api.worktreeAdd "/repo" { path := "/wt3", detach := true, force := true }).run stOk
  let (waDef, stWaDef) := (api.worktreeAdd "/repo" { path := "/wt_def" }).run stOk
  let (rsRefOk, stRsRefOk) := (api.reset "/repo" .hard "feat~1").run stOk
  let (rpShort, _) := (api.revParseCommit "/repo" "1111111").run stOk
  let (rsShort, stRsShort) := (api.reset "/repo" .hard "1111111").run stOk
  let (coShort, stCoShort) := (api.checkout "/repo" (.ref "1111111") false).run stOk
  let (swShort, stSwShort) := (api.switch "/repo" { raw := "newbr" } true (some "1111111") false).run stOk
  let (cbShort, stCbShort) := (api.createBranch "/repo" { raw := "newbr" } (some "1111111") false).run stOk
  let (dfShort, stDfShort) := (api.diffNameStatus "/repo" "1111111" none #[]).run stOk
  let (waShort, stWaShort) := (api.worktreeAdd "/repo" { path := "/wt4", newBranch? := some { raw := "wtb" }, target? := some "1111111" }).run stOk
  let (rpReflog, _) := (api.revParseCommit "/repo" "HEAD@{0}").run stOk
  NondetTest.assert (swEF = .ok () ∧ stSwEF.recordedRequests.getLast? =
    some { cwd := some "/repo", args := #["switch", "--force", "feat"] })
  NondetTest.assert (coRF = .ok () ∧ stCoRF.recordedRequests.getLast? =
    some { cwd := some "/repo", args := #["checkout", "--force", "HEAD~1", "--"] })
  NondetTest.assert (waDF = .ok () ∧ stWaDF.recordedRequests.getLast? =
    some { cwd := some "/repo", args := #["worktree", "add", "--force", "--detach", "--", "/wt3"] })
  NondetTest.assert (waDef = .ok () ∧ stWaDef.recordedRequests.getLast? =
    some { cwd := some "/repo", args := #["worktree", "add", "--", "/wt_def"] })
  NondetTest.assert (rsRefOk = .ok () ∧ stRsRefOk.recordedRequests.getLast? =
    some { cwd := some "/repo", args := #["reset", "--hard", "feat~1", "--"] })
  NondetTest.assert (rpShort = .ok { hex := sha1 } ∧ rpReflog = .ok { hex := sha1 })
  NondetTest.assert (rsShort = .ok () ∧ stRsShort.recordedRequests.getLast? =
    some { cwd := some "/repo", args := #["reset", "--hard", "1111111", "--"] })
  NondetTest.assert (coShort = .ok () ∧ stCoShort.recordedRequests.getLast? =
    some { cwd := some "/repo", args := #["checkout", "1111111", "--"] })
  NondetTest.assert (swShort = .ok () ∧ stSwShort.recordedRequests.getLast? =
    some { cwd := some "/repo", args := #["switch", "-c", "newbr", "1111111"] })
  NondetTest.assert (cbShort = .ok () ∧ stCbShort.recordedRequests.getLast? =
    some { cwd := some "/repo", args := #["branch", "--", "newbr", "1111111"] })
  NondetTest.assert (dfShort = .ok #[] ∧ stDfShort.recordedRequests.getLast? =
    some { cwd := some "/repo", args := #["diff", "--name-status", "-z", "1111111", "--"] })
  NondetTest.assert (waShort = .ok () ∧ stWaShort.recordedRequests.getLast? =
    some { cwd := some "/repo", args := #["worktree", "add", "-b", "wtb", "--", "/wt4", "1111111"] })


end LeanSwe.Git
