import LeanSwe.Git.Types
import LeanSwe.Git.Model
import LeanSwe.Git.Impl
import LeanSwe.Git.Interface
import LeanSwe.Git.SpecTests
import LeanSwe.Git.Proofs.ParserProofs

set_option Elab.async false
set_option maxRecDepth 4096

namespace LeanSwe.Git.Proofs

open Core
open Core.NondetTest
open LeanSwe.Git
open LeanSwe.Git.Model

private theorem runGitChecked_eq_of_ok (ops : RawGitOpsM (StateM GitCliMockState))
    (cmd : String) (req : GitRawRequest) (st st' : GitCliMockState) (out : GitRawOutput)
    (hRaw : Impl.runGitRaw ops req st = (.ok out, st')) (hExit : out.exitCode = 0) :
    Impl.runGitChecked ops cmd req st = (.ok out, st') := by
  unfold Impl.runGitChecked
  dsimp only [bind, StateT.bind, pure, StateT.pure]
  rw [hRaw]
  dsimp only
  rw [hExit]
  rfl

private def mkDelegationState (rootStr commStr sha1 _sha2 sha0 : String)
    (statusBytes diffBytes wtBytes : ByteArray) : GitCliMockState :=
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

private theorem runGitRaw_repo_ok (args : Array String)
    (hArgs : (args.all fun a => !hasNulChar a.toList) = true)
    (st : GitCliMockState) (out : GitRawOutput)
    (hHand : st.handler { cwd := some "/repo", args := args } st.callCount = .ok out) :
    Impl.runGitRaw mockRawOps { cwd := some "/repo", args := args } st =
      (.ok out, { st with
        recordedEnvs := st.recordedEnvs ++ [cleanGitEnv st.inheritedEnv #[]]
        recordedRequests := st.recordedRequests ++ [{ cwd := some "/repo", args := args }]
        callCount := st.callCount + 1 }) := by
  have hCwdOk : Impl.validateCwd? (some "/repo") = .ok () := by
    unfold Impl.validateCwd?
    simp [isValidPathArgImpl_eq, show isValidPathArg "/repo" = true from by decide]
  have hExtraOk : Impl.validateExtraEnv #[] = .ok () := by
    unfold Impl.validateExtraEnv; simp
  unfold Impl.runGitRaw
  simp only [hasNulCharImpl_eq, cleanGitEnvImpl_eq, hCwdOk, hExtraOk, hArgs, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
    bind, StateT.bind, mockRawOps]
  rw [hHand]

private theorem repoRoot_delegation_ok (rootStr commStr sha1 sha2 sha0 : String)
    (statusBytes diffBytes wtBytes : ByteArray)
    (hRoot : rootStr = "/mock/root") :
    let st₀ := mkDelegationState rootStr commStr sha1 sha2 sha0 statusBytes diffBytes wtBytes
    (((Impl.mkApiM mockRawOps).repoRoot "/repo").run st₀).1 = .ok rootStr ∧
    (((Impl.mkApiM mockRawOps).repoRoot "/repo").run st₀).2.callCount = 1 := by
  subst hRoot
  dsimp only
  let st₀ := mkDelegationState "/mock/root" commStr sha1 sha2 sha0 statusBytes diffBytes wtBytes
  have hRepoOk : Impl.validateRepoPath "/repo" = .ok () := by cbv
  let args := #["rev-parse", "--path-format=absolute", "--show-toplevel"]
  have hA : (args.all fun a => !hasNulChar a.toList) = true :=
    all_no_nul_of_list args.toList (by decide)
  have hC : (args.toList.contains "--show-toplevel") = true := by decide
  have hHand : st₀.handler { cwd := some "/repo", args := args } st₀.callCount =
      .ok { exitCode := 0, stdout := ("/mock/root" ++ "\n").toUTF8, stderr := ByteArray.empty } := by
    dsimp only [st₀, mkDelegationState]; simp only [hC, ↓reduceIte]
  have hRaw := runGitRaw_repo_ok args hA st₀ _ hHand
  have hChk := runGitChecked_eq_of_ok mockRawOps "rev-parse" _ st₀ _ _ hRaw rfl
  change (Impl.repoRootImpl mockRawOps "/repo" st₀).1 = .ok "/mock/root" ∧
    (Impl.repoRootImpl mockRawOps "/repo" st₀).2.callCount = 1
  unfold Impl.repoRootImpl
  simp only [hRepoOk, bind, StateT.bind, pure]
  rw [hChk]
  dsimp only
  rw [decodeUtf8Checked_toUTF8]
  dsimp only [StateT.pure]
  rw [show Impl.stripSingleTrailingLf ("/mock/root" ++ "\n") = "/mock/root" from by cbv]
  exact ⟨rfl, rfl⟩

private theorem commonDir_delegation_ok (rootStr commStr sha1 sha2 sha0 : String)
    (statusBytes diffBytes wtBytes : ByteArray)
    (hComm : commStr = "/mock/root/.git") :
    let st₀ := mkDelegationState rootStr commStr sha1 sha2 sha0 statusBytes diffBytes wtBytes
    (((Impl.mkApiM mockRawOps).commonDir "/repo").run st₀).1 = .ok commStr ∧
    (((Impl.mkApiM mockRawOps).commonDir "/repo").run st₀).2.callCount = 1 := by
  subst hComm
  dsimp only
  let st₀ := mkDelegationState rootStr "/mock/root/.git" sha1 sha2 sha0 statusBytes diffBytes wtBytes
  have hRepoOk : Impl.validateRepoPath "/repo" = .ok () := by cbv
  let args := #["rev-parse", "--path-format=absolute", "--git-common-dir"]
  have hA : (args.all fun a => !hasNulChar a.toList) = true :=
    all_no_nul_of_list args.toList (by decide)
  have hC1 : (args.toList.contains "--show-toplevel") = false := by decide
  have hC2 : (args.toList.contains "--git-common-dir") = true := by decide
  have hHand : st₀.handler { cwd := some "/repo", args := args } st₀.callCount =
      .ok { exitCode := 0, stdout := ("/mock/root/.git" ++ "\n").toUTF8, stderr := ByteArray.empty } := by
    dsimp only [st₀, mkDelegationState]; simp only [hC1, hC2, Bool.false_eq_true, ↓reduceIte]
  have hRaw := runGitRaw_repo_ok args hA st₀ _ hHand
  have hChk := runGitChecked_eq_of_ok mockRawOps "rev-parse" _ st₀ _ _ hRaw rfl
  change (Impl.commonDirImpl mockRawOps "/repo" st₀).1 = .ok "/mock/root/.git" ∧
    (Impl.commonDirImpl mockRawOps "/repo" st₀).2.callCount = 1
  unfold Impl.commonDirImpl
  simp only [hRepoOk, bind, StateT.bind, pure]
  rw [hChk]
  dsimp only
  rw [decodeUtf8Checked_toUTF8]
  dsimp only [StateT.pure]
  rw [show Impl.stripSingleTrailingLf ("/mock/root/.git" ++ "\n") = "/mock/root/.git" from by cbv]
  exact ⟨rfl, rfl⟩

private theorem headBranch_run_ok (rootStr commStr sha1 sha2 sha0 : String)
    (statusBytes diffBytes wtBytes : ByteArray) (st : GitCliMockState)
    (hEqH : st.handler = (mkDelegationState rootStr commStr sha1 sha2 sha0 statusBytes diffBytes wtBytes).handler) :
    Impl.headBranchImpl mockRawOps "/repo" st =
      (.ok (some { raw := "topic" }),
       { st with
         recordedEnvs := st.recordedEnvs ++ [cleanGitEnv st.inheritedEnv #[]]
         recordedRequests := st.recordedRequests ++ [{ cwd := some "/repo", args := #["symbolic-ref", "--quiet", "HEAD"] }]
         callCount := st.callCount + 1 }) := by
  have hRepoOk : Impl.validateRepoPath "/repo" = .ok () := by cbv
  let args := #["symbolic-ref", "--quiet", "HEAD"]
  have hA : (args.all fun a => !hasNulChar a.toList) = true :=
    all_no_nul_of_list args.toList (by decide)
  have hC1 : (args.toList.contains "--show-toplevel") = false := by decide
  have hC2 : (args.toList.contains "--git-common-dir") = false := by decide
  have hC3 : (args.toList.contains "symbolic-ref") = true := by decide
  have hHand : st.handler { cwd := some "/repo", args := args } st.callCount =
      .ok { exitCode := 0, stdout := "refs/heads/topic\n".toUTF8, stderr := ByteArray.empty } := by
    rw [hEqH]; dsimp only [mkDelegationState]; simp only [hC1, hC2, hC3, Bool.false_eq_true, ↓reduceIte]
  have hRaw := runGitRaw_repo_ok args hA st _ hHand
  unfold Impl.headBranchImpl
  simp only [hRepoOk, bind, StateT.bind, pure]
  rw [hRaw]
  dsimp only
  simp only [beq_self_eq_true, ↓reduceIte]
  rw [decodeUtf8Checked_toUTF8]
  dsimp only [StateT.pure]
  rw [show Impl.trimTrailingNewlines "refs/heads/topic\n" = "refs/heads/topic" from by cbv]
  rw [show ("refs/heads/topic".startsWith "refs/heads/") = true from by cbv]
  simp only [↓reduceIte]
  rw [show String.ofList ("refs/heads/topic".toList.drop 11) = "topic" from by cbv]
  rw [mkRefNameImpl_eq, show mkRefName "topic" = .ok { raw := "topic" } from by cbv]
  rfl

private theorem headState_delegation_ok (rootStr commStr sha1 sha2 sha0 : String)
    (statusBytes diffBytes wtBytes : ByteArray)
    (hSha1 : sha1 = String.ofList (List.replicate 40 '1')) :
    let st₀ := mkDelegationState rootStr commStr sha1 sha2 sha0 statusBytes diffBytes wtBytes
    (((Impl.mkApiM mockRawOps).headState "/repo").run st₀).1 =
      .ok (.attached { raw := "topic" } (some { hex := sha1 })) ∧
    (((Impl.mkApiM mockRawOps).headState "/repo").run st₀).2.callCount = 2 := by
  subst hSha1
  dsimp only
  let sha1 := String.ofList (List.replicate 40 '1')
  let st₀ := mkDelegationState rootStr commStr sha1 sha2 sha0 statusBytes diffBytes wtBytes
  have hRepoOk : Impl.validateRepoPath "/repo" = .ok () := by cbv
  let req0 : GitRawRequest := { cwd := some "/repo", args := #["symbolic-ref", "--quiet", "HEAD"] }
  let st1 : GitCliMockState := { st₀ with
    recordedEnvs := st₀.recordedEnvs ++ [cleanGitEnv st₀.inheritedEnv #[]]
    recordedRequests := st₀.recordedRequests ++ [req0]
    callCount := st₀.callCount + 1 }
  let args := #["rev-parse", "-q", "--verify", "HEAD^{commit}"]
  have hA : (args.all fun a => !hasNulChar a.toList) = true :=
    all_no_nul_of_list args.toList (by decide)
  have hC1 : (args.toList.contains "--show-toplevel") = false := by decide
  have hC2 : (args.toList.contains "--git-common-dir") = false := by decide
  have hC3 : (args.toList.contains "symbolic-ref") = false := by decide
  have hC4 : (args.toList.contains "--verify") = true := by decide
  have hHand : st1.handler { cwd := some "/repo", args := args } st1.callCount =
      .ok { exitCode := 0, stdout := (sha1 ++ "\n").toUTF8, stderr := ByteArray.empty } := by
    change st₀.handler { cwd := some "/repo", args := args } st1.callCount = _
    dsimp only [st₀, mkDelegationState]; simp only [hC1, hC2, hC3, hC4, Bool.false_eq_true, ↓reduceIte]
  have hRaw := runGitRaw_repo_ok args hA st1 _ hHand
  change (Impl.headStateImpl mockRawOps "/repo" st₀).1 =
      .ok (.attached { raw := "topic" } (some { hex := sha1 })) ∧
    (Impl.headStateImpl mockRawOps "/repo" st₀).2.callCount = 2
  unfold Impl.headStateImpl
  dsimp only [bind, StateT.bind, pure, StateT.pure]
  rw [headBranch_run_ok rootStr commStr sha1 sha2 sha0 statusBytes diffBytes wtBytes st₀ rfl]
  dsimp only
  unfold Impl.headCommitImpl
  simp only [hRepoOk, bind, StateT.bind, pure]
  dsimp only [st1] at hRaw
  rw [hRaw]
  dsimp only
  simp only [beq_self_eq_true, ↓reduceIte]
  rw [decodeUtf8Checked_toUTF8]
  dsimp only [StateT.pure]
  have hCid : Impl.mkCommitIdImpl (Impl.trimTrailingNewlines (sha1 ++ "\n")) = .ok { hex := sha1 } := by cbv
  rw [hCid]
  exact ⟨rfl, rfl⟩

private theorem mergeBase_delegation_ok (rootStr commStr sha1 sha2 sha0 : String)
    (statusBytes diffBytes wtBytes : ByteArray)
    (hSha1 : sha1 = String.ofList (List.replicate 40 '1'))
    (hSha2 : sha2 = String.ofList (List.replicate 40 '2'))
    (hSha0 : sha0 = String.ofList (List.replicate 40 '0')) :
    let st₀ := mkDelegationState rootStr commStr sha1 sha2 sha0 statusBytes diffBytes wtBytes
    (((Impl.mkApiM mockRawOps).mergeBase? "/repo" { hex := sha1 } { hex := sha2 }).run st₀).1 =
      .ok (some { hex := sha0 }) ∧
    (((Impl.mkApiM mockRawOps).mergeBase? "/repo" { hex := sha1 } { hex := sha2 }).run st₀).2.callCount = 1 := by
  subst hSha1; subst hSha2; subst hSha0
  dsimp only
  let sha1 := String.ofList (List.replicate 40 '1')
  let sha2 := String.ofList (List.replicate 40 '2')
  let sha0 := String.ofList (List.replicate 40 '0')
  let st₀ := mkDelegationState rootStr commStr sha1 sha2 sha0 statusBytes diffBytes wtBytes
  have hRepoOk : Impl.validateRepoPath "/repo" = .ok () := by cbv
  let args := #["merge-base", sha1, sha2]
  have hA : (args.all fun a => !hasNulChar a.toList) = true := by cbv
  have hC1 : (args.toList.contains "--show-toplevel") = false := by dsimp only [args, sha1, sha2]; decide
  have hC2 : (args.toList.contains "--git-common-dir") = false := by dsimp only [args, sha1, sha2]; decide
  have hC3 : (args.toList.contains "symbolic-ref") = false := by dsimp only [args, sha1, sha2]; decide
  have hC4 : (args.toList.contains "--verify") = false := by dsimp only [args, sha1, sha2]; decide
  have hC5 : (args.toList.contains "merge-base") = true := by decide
  have hHand : st₀.handler { cwd := some "/repo", args := args } st₀.callCount =
      .ok { exitCode := 0, stdout := (sha0 ++ "\n").toUTF8, stderr := ByteArray.empty } := by
    dsimp only [st₀, mkDelegationState]; simp only [hC1, hC2, hC3, hC4, hC5, Bool.false_eq_true, ↓reduceIte]
  have hRaw := runGitRaw_repo_ok args hA st₀ _ hHand
  change (Impl.mergeBaseImpl mockRawOps "/repo" { hex := sha1 } { hex := sha2 } st₀).1 =
      .ok (some { hex := sha0 }) ∧
    (Impl.mergeBaseImpl mockRawOps "/repo" { hex := sha1 } { hex := sha2 } st₀).2.callCount = 1
  unfold Impl.mergeBaseImpl
  simp only [hRepoOk, isValidCommitIdStrImpl_eq,
    show (!isValidCommitIdStr sha1 || !isValidCommitIdStr sha2) = false from by cbv,
    Bool.false_eq_true, ↓reduceIte, bind, StateT.bind, pure]
  rw [hRaw]
  dsimp only
  simp only [beq_self_eq_true, ↓reduceIte]
  rw [decodeUtf8Checked_toUTF8]
  dsimp only [StateT.pure]
  have hMk : Impl.mkCommitIdImpl (Impl.trimTrailingNewlines (sha0 ++ "\n")) = .ok { hex := sha0 } := by cbv
  rw [hMk]
  exact ⟨rfl, rfl⟩

private theorem status_delegation_ok (rootStr commStr sha1 sha2 sha0 : String)
    (statusBytes diffBytes wtBytes : ByteArray) :
    let st₀ := mkDelegationState rootStr commStr sha1 sha2 sha0 statusBytes diffBytes wtBytes
    (((Impl.mkApiM mockRawOps).status "/repo").run st₀).1 = parsePorcelainStatusZ statusBytes ∧
    (((Impl.mkApiM mockRawOps).status "/repo").run st₀).2.callCount = 1 := by
  dsimp only
  let st₀ := mkDelegationState rootStr commStr sha1 sha2 sha0 statusBytes diffBytes wtBytes
  have hRepoOk : Impl.validateRepoPath "/repo" = .ok () := by cbv
  let args := #["status", "--porcelain=v1", "--untracked-files=normal", "-z"]
  have hA : (args.all fun a => !hasNulChar a.toList) = true :=
    all_no_nul_of_list args.toList (by decide)
  have hC1 : (args.toList.contains "--show-toplevel") = false := by decide
  have hC2 : (args.toList.contains "--git-common-dir") = false := by decide
  have hC3 : (args.toList.contains "symbolic-ref") = false := by decide
  have hC4 : (args.toList.contains "--verify") = false := by decide
  have hC5 : (args.toList.contains "merge-base") = false := by decide
  have hC6 : (args.toList.contains "--porcelain=v1") = true := by decide
  have hHand : st₀.handler { cwd := some "/repo", args := args } st₀.callCount =
      .ok { exitCode := 0, stdout := statusBytes, stderr := ByteArray.empty } := by
    dsimp only [st₀, mkDelegationState]; simp only [hC1, hC2, hC3, hC4, hC5, hC6, Bool.false_eq_true, ↓reduceIte]
  have hRaw := runGitRaw_repo_ok args hA st₀ _ hHand
  have hChk := runGitChecked_eq_of_ok mockRawOps "status" _ st₀ _ _ hRaw rfl
  change (Impl.statusImpl mockRawOps "/repo" st₀).1 = parsePorcelainStatusZ statusBytes ∧
    (Impl.statusImpl mockRawOps "/repo" st₀).2.callCount = 1
  unfold Impl.statusImpl
  simp only [hRepoOk, bind, StateT.bind, pure]
  rw [hChk]
  dsimp only [StateT.pure]
  exact ⟨parsePorcelainStatusZImpl_eq statusBytes, rfl⟩

private theorem diffNameStatus_delegation_ok (rootStr commStr sha1 sha2 sha0 : String)
    (statusBytes diffBytes wtBytes : ByteArray) :
    let st₀ := mkDelegationState rootStr commStr sha1 sha2 sha0 statusBytes diffBytes wtBytes
    (((Impl.mkApiM mockRawOps).diffNameStatus "/repo" "HEAD" none #[]).run st₀).1 =
      parseDiffNameStatusZ diffBytes ∧
    (((Impl.mkApiM mockRawOps).diffNameStatus "/repo" "HEAD" none #[]).run st₀).2.callCount = 1 := by
  dsimp only
  let st₀ := mkDelegationState rootStr commStr sha1 sha2 sha0 statusBytes diffBytes wtBytes
  have hRepoOk : Impl.validateRepoPath "/repo" = .ok () := by cbv
  let args := #["diff", "--name-status", "-z", "HEAD", "--"]
  have hA : (args.all fun a => !hasNulChar a.toList) = true :=
    all_no_nul_of_list args.toList (by decide)
  have hE1 : (args.toList.contains "--show-toplevel") = false := by decide
  have hE2 : (args.toList.contains "--git-common-dir") = false := by decide
  have hE3 : (args.toList.contains "symbolic-ref") = false := by decide
  have hE4 : (args.toList.contains "--verify") = false := by decide
  have hE5 : (args.toList.contains "merge-base") = false := by decide
  have hE6 : (args.toList.contains "--porcelain=v1") = false := by decide
  have hE7 : (args.toList.contains "--name-status") = true := by decide
  have hHand : st₀.handler { cwd := some "/repo", args := args } st₀.callCount =
      .ok { exitCode := 0, stdout := diffBytes, stderr := ByteArray.empty } := by
    dsimp only [st₀, mkDelegationState]
    simp only [hE1, hE2, hE3, hE4, hE5, hE6, hE7, Bool.false_eq_true, ↓reduceIte]
  have hRaw := runGitRaw_repo_ok args hA st₀ _ hHand
  have hChk := runGitChecked_eq_of_ok mockRawOps "diff" _ st₀ _ _ hRaw rfl
  change (Impl.diffNameStatusImpl mockRawOps "/repo" "HEAD" none #[] st₀).1 =
      parseDiffNameStatusZ diffBytes ∧
    (Impl.diffNameStatusImpl mockRawOps "/repo" "HEAD" none #[] st₀).2.callCount = 1
  unfold Impl.diffNameStatusImpl
  have hRev : isValidStrictRevSpec "HEAD" = true := by cbv
  have hPaths : ((#[] : Array String).all isValidPathArg) = true := by cbv
  have hDiffArgs :
      (#["diff", "--name-status", "-z", "HEAD"] ++ (#[] : Array String) ++
        #["--"] ++ (#[] : Array String)) = args := rfl
  simp only [hRepoOk, isValidStrictRevSpecImpl_eq, isValidPathArgImpl_eq, hRev, hPaths, Bool.not_true, Bool.false_eq_true, ↓reduceIte, bind, StateT.bind, pure]
  rw [hDiffArgs, hChk]
  dsimp only [StateT.pure]
  exact ⟨parseDiffNameStatusZImpl_eq diffBytes, rfl⟩

private theorem listWorktrees_delegation_ok (rootStr commStr sha1 sha2 sha0 : String)
    (statusBytes diffBytes wtBytes : ByteArray) :
    let st₀ := mkDelegationState rootStr commStr sha1 sha2 sha0 statusBytes diffBytes wtBytes
    (((Impl.mkApiM mockRawOps).listWorktrees "/repo").run st₀).1 =
      parseWorktreeListPorcelain wtBytes ∧
    (((Impl.mkApiM mockRawOps).listWorktrees "/repo").run st₀).2.callCount = 1 := by
  dsimp only
  let st₀ := mkDelegationState rootStr commStr sha1 sha2 sha0 statusBytes diffBytes wtBytes
  have hRepoOk : Impl.validateRepoPath "/repo" = .ok () := by cbv
  let args := #["worktree", "list", "--porcelain", "-z"]
  have hA : (args.all fun a => !hasNulChar a.toList) = true :=
    all_no_nul_of_list args.toList (by decide)
  have hF1 : (args.toList.contains "--show-toplevel") = false := by decide
  have hF2 : (args.toList.contains "--git-common-dir") = false := by decide
  have hF3 : (args.toList.contains "symbolic-ref") = false := by decide
  have hF4 : (args.toList.contains "--verify") = false := by decide
  have hF5 : (args.toList.contains "merge-base") = false := by decide
  have hF6 : (args.toList.contains "--porcelain=v1") = false := by decide
  have hF7 : (args.toList.contains "--name-status") = false := by decide
  have hF8 : (args.toList.contains "worktree") = true := by decide
  have hHand : st₀.handler { cwd := some "/repo", args := args } st₀.callCount =
      .ok { exitCode := 0, stdout := wtBytes, stderr := ByteArray.empty } := by
    dsimp only [st₀, mkDelegationState]
    simp only [hF1, hF2, hF3, hF4, hF5, hF6, hF7, hF8, Bool.false_eq_true, ↓reduceIte]
  have hRaw := runGitRaw_repo_ok args hA st₀ _ hHand
  have hChk := runGitChecked_eq_of_ok mockRawOps "worktree" _ st₀ _ _ hRaw rfl
  change (Impl.listWorktreesImpl mockRawOps "/repo" st₀).1 = parseWorktreeListPorcelain wtBytes ∧
    (Impl.listWorktreesImpl mockRawOps "/repo" st₀).2.callCount = 1
  unfold Impl.listWorktreesImpl
  simp only [hRepoOk, bind, StateT.bind, pure]
  rw [hChk]
  dsimp only [StateT.pure]
  exact ⟨parseWorktreeListPorcelainImpl_eq wtBytes, rfl⟩

/-- Proof of `test_git_raw_mkApi_queryAndParserDelegation` for `Impl.mkApiM`. -/
theorem proof_git_raw_mkApi_queryAndParserDelegation :
    AllPass (test_git_raw_mkApi_queryAndParserDelegation (fun ops => Impl.mkApiM ops)) := by
  dsimp only [test_git_raw_mkApi_queryAndParserDelegation, AllPass, assert]
  let rootStr := "/mock/root"
  let commStr := "/mock/root/.git"
  let sha1 := String.ofList (List.replicate 40 '1')
  let sha2 := String.ofList (List.replicate 40 '2')
  let sha0 := String.ofList (List.replicate 40 '0')
  let statusBytes := " M a.txt\x00?? b.txt\x00".toUTF8
  let diffBytes := "R090\x00old.txt\x00new.txt\x00".toUTF8
  let wtBytes := ("worktree " ++ rootStr ++ "\x00HEAD " ++ sha1 ++ "\x00branch refs/heads/topic\x00\x00").toUTF8
  have hRr := repoRoot_delegation_ok rootStr commStr sha1 sha2 sha0 statusBytes diffBytes wtBytes rfl
  have hCd := commonDir_delegation_ok rootStr commStr sha1 sha2 sha0 statusBytes diffBytes wtBytes rfl
  have hHb :
      (((Impl.mkApiM mockRawOps).headBranch? "/repo").run
        (mkDelegationState rootStr commStr sha1 sha2 sha0 statusBytes diffBytes wtBytes)).1 =
        .ok (some { raw := "topic" }) ∧
      (((Impl.mkApiM mockRawOps).headBranch? "/repo").run
        (mkDelegationState rootStr commStr sha1 sha2 sha0 statusBytes diffBytes wtBytes)).2.callCount = 1 := by
    let st₀ := mkDelegationState rootStr commStr sha1 sha2 sha0 statusBytes diffBytes wtBytes
    change (Impl.headBranchImpl mockRawOps "/repo" st₀).1 = .ok (some { raw := "topic" }) ∧
      (Impl.headBranchImpl mockRawOps "/repo" st₀).2.callCount = 1
    rw [headBranch_run_ok rootStr commStr sha1 sha2 sha0 statusBytes diffBytes wtBytes st₀ rfl]
    exact ⟨rfl, rfl⟩
  have hHs := headState_delegation_ok rootStr commStr sha1 sha2 sha0 statusBytes diffBytes wtBytes rfl
  have hMb := mergeBase_delegation_ok rootStr commStr sha1 sha2 sha0 statusBytes diffBytes wtBytes rfl rfl rfl
  have hSt := status_delegation_ok rootStr commStr sha1 sha2 sha0 statusBytes diffBytes wtBytes
  have hDf := diffNameStatus_delegation_ok rootStr commStr sha1 sha2 sha0 statusBytes diffBytes wtBytes
  have hWt := listWorktrees_delegation_ok rootStr commStr sha1 sha2 sha0 statusBytes diffBytes wtBytes
  exact ⟨hRr, hCd, hHb, hHs, hMb, hSt, hDf, hWt, trivial⟩

end LeanSwe.Git.Proofs
