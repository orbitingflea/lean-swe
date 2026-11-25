import LeanSwe.Git.Impl
import LeanSwe.Git.Interface
import LeanSwe.Git.RuntimeTests.Helpers

namespace LeanSwe.Git.RuntimeTests

open LeanSwe.Git
open LeanSwe.Git.Model

/-- Mocked error-coverage test for `LeanSwe.Git.createBranch` returning `.nothingToCommit`. -/
def err_git_createBranch_nothingToCommit : IO Unit :=
  runMockErr .nothingToCommit (fun api => api.createBranch "/mock/repo" mainRef none false)

/-- Mocked error-coverage test for `LeanSwe.Git.createBranch` returning `.branchInUse`. -/
def err_git_createBranch_branchInUse : IO Unit :=
  runMockErr .branchInUse (fun api => api.createBranch "/mock/repo" mainRef none false)

/-- Real error-coverage test for `LeanSwe.Git.createBranch` returning `.alreadyExists`. -/
def err_git_createBranch_alreadyExists : IO Unit :=
  runRealCommittedErr .alreadyExists "createBranch alreadyExists" (fun repo _ => Git.createBranch repo mainRef)

/-- Mocked error-coverage test for `LeanSwe.Git.createBranch` returning `.notFound`. -/
def err_git_createBranch_notFound : IO Unit :=
  runMockErr .notFound (fun api => api.createBranch "/mock/repo" mainRef none false)

/-- Mocked error-coverage test for `LeanSwe.Git.createBranch` returning `.conflict`. -/
def err_git_createBranch_conflict : IO Unit :=
  runMockErr .conflict (fun api => api.createBranch "/mock/repo" mainRef none false)

/-- Mocked error-coverage test for `LeanSwe.Git.createBranch` returning `.timeout`. -/
def err_git_createBranch_timeout : IO Unit :=
  runMockErr .timeout (fun api => api.createBranch "/mock/repo" mainRef none false)

/-- Real error-coverage test for `LeanSwe.Git.createBranch` returning `.commandFailed`. -/
def err_git_createBranch_commandFailed : IO Unit :=
  runRealMissingDirErr (fun p => Git.createBranch p mainRef)

/-- Real error-coverage test for `LeanSwe.Git.deleteBranch` returning `.notARepo`. -/
def err_git_deleteBranch_notARepo : IO Unit :=
  runRealNonRepoErr (fun p => Git.deleteBranch p mainRef)

/-- Real error-coverage test for `LeanSwe.Git.deleteBranch` returning `.invalidRef`. -/
def err_git_deleteBranch_invalidRef : IO Unit :=
  runRealCommittedErr .invalidRef "deleteBranch invalidRef" (fun repo _ => Git.deleteBranch repo badRef)

/-- Real error-coverage test for `LeanSwe.Git.deleteBranch` returning `.invalidPath`. -/
def err_git_deleteBranch_invalidPath : IO Unit :=
  runRealErr .invalidPath "deleteBranch invalidPath" (Git.deleteBranch "" mainRef)

/-- Real error-coverage test for `LeanSwe.Git.deleteBranch` returning `.invalidInput`. -/
def err_git_deleteBranch_invalidInput : IO Unit :=
  runRealErr .invalidInput "deleteBranch invalidInput" (Git.deleteBranch longInvalidPath mainRef)

/-- Mocked error-coverage test for `LeanSwe.Git.deleteBranch` returning `.dirtyWorktree`. -/
def err_git_deleteBranch_dirtyWorktree : IO Unit :=
  runMockErr .dirtyWorktree (fun api => api.deleteBranch "/mock/repo" mainRef false)

/-- Mocked error-coverage test for `LeanSwe.Git.deleteBranch` returning `.nothingToCommit`. -/
def err_git_deleteBranch_nothingToCommit : IO Unit :=
  runMockErr .nothingToCommit (fun api => api.deleteBranch "/mock/repo" mainRef false)

/-- Real error-coverage test for `LeanSwe.Git.deleteBranch` returning `.branchInUse`. -/
def err_git_deleteBranch_branchInUse : IO Unit :=
  runRealCommittedErr .branchInUse "deleteBranch branchInUse" (fun repo _ => Git.deleteBranch repo mainRef)

/-- Mocked error-coverage test for `LeanSwe.Git.deleteBranch` returning `.alreadyExists`. -/
def err_git_deleteBranch_alreadyExists : IO Unit :=
  runMockErr .alreadyExists (fun api => api.deleteBranch "/mock/repo" mainRef false)

/-- Real error-coverage test for `LeanSwe.Git.deleteBranch` returning `.notFound`. -/
def err_git_deleteBranch_notFound : IO Unit :=
  runRealCommittedErr .notFound "deleteBranch notFound" (fun repo _ => Git.deleteBranch repo missingRef)

/-- Mocked error-coverage test for `LeanSwe.Git.deleteBranch` returning `.conflict`. -/
def err_git_deleteBranch_conflict : IO Unit :=
  runMockErr .conflict (fun api => api.deleteBranch "/mock/repo" mainRef false)

/-- Mocked error-coverage test for `LeanSwe.Git.deleteBranch` returning `.timeout`. -/
def err_git_deleteBranch_timeout : IO Unit :=
  runMockErr .timeout (fun api => api.deleteBranch "/mock/repo" mainRef false)

/-- Real error-coverage test for `LeanSwe.Git.deleteBranch` returning `.commandFailed`. -/
def err_git_deleteBranch_commandFailed : IO Unit :=
  runRealMissingDirErr (fun p => Git.deleteBranch p mainRef)

/-- Real error-coverage test for `LeanSwe.Git.checkout` returning `.notARepo`. -/
def err_git_checkout_notARepo : IO Unit :=
  runRealNonRepoErr (fun p => Git.checkout p (.branch mainRef))

/-- Real error-coverage test for `LeanSwe.Git.checkout` returning `.invalidRef`. -/
def err_git_checkout_invalidRef : IO Unit :=
  runRealCommittedErr .invalidRef "checkout invalidRef" (fun repo _ => Git.checkout repo (.branch missingRef))

/-- Real error-coverage test for `LeanSwe.Git.checkout` returning `.invalidPath`. -/
def err_git_checkout_invalidPath : IO Unit :=
  runRealErr .invalidPath "checkout invalidPath" (Git.checkout "" (.branch mainRef))

/-- Real error-coverage test for `LeanSwe.Git.checkout` returning `.invalidInput`. -/
def err_git_checkout_invalidInput : IO Unit :=
  runRealErr .invalidInput "checkout invalidInput" (Git.checkout "/tmp" (.ref "HEAD:bad"))

/-- Real error-coverage test for `LeanSwe.Git.checkout` returning `.dirtyWorktree`. -/
def err_git_checkout_dirtyWorktree : IO Unit :=
  runRealCheckoutDirtyErr

/-- Mocked error-coverage test for `LeanSwe.Git.checkout` returning `.nothingToCommit`. -/
def err_git_checkout_nothingToCommit : IO Unit :=
  runMockErr .nothingToCommit (fun api => api.checkout "/mock/repo" (.branch mainRef) false)

/-- Real error-coverage test for `LeanSwe.Git.checkout` returning `.branchInUse`. -/
def err_git_checkout_branchInUse : IO Unit :=
  runRealCheckoutBranchInUseErr

/-- Mocked error-coverage test for `LeanSwe.Git.checkout` returning `.alreadyExists`. -/
def err_git_checkout_alreadyExists : IO Unit :=
  runMockErr .alreadyExists (fun api => api.checkout "/mock/repo" (.branch mainRef) false)

/-- Mocked error-coverage test for `LeanSwe.Git.checkout` returning `.notFound`. -/
def err_git_checkout_notFound : IO Unit :=
  runMockErr .notFound (fun api => api.checkout "/mock/repo" (.branch mainRef) false)

/-- Real error-coverage test for `LeanSwe.Git.checkout` returning `.conflict`. -/
def err_git_checkout_conflict : IO Unit :=
  runRealCheckoutConflictErr

/-- Mocked error-coverage test for `LeanSwe.Git.checkout` returning `.timeout`. -/
def err_git_checkout_timeout : IO Unit :=
  runMockErr .timeout (fun api => api.checkout "/mock/repo" (.branch mainRef) false)

/-- Real error-coverage test for `LeanSwe.Git.checkout` returning `.commandFailed`. -/
def err_git_checkout_commandFailed : IO Unit :=
  runRealMissingDirErr (fun p => Git.checkout p (.branch mainRef))

/-- Real error-coverage test for `LeanSwe.Git.switch` returning `.notARepo`. -/
def err_git_switch_notARepo : IO Unit :=
  runRealNonRepoErr (fun p => Git.switch p mainRef)

/-- Real error-coverage test for `LeanSwe.Git.switch` returning `.invalidRef`. -/
def err_git_switch_invalidRef : IO Unit :=
  runRealCommittedErr .invalidRef "switch invalidRef" (fun repo _ => Git.switch repo missingRef)

/-- Real error-coverage test for `LeanSwe.Git.switch` returning `.invalidPath`. -/
def err_git_switch_invalidPath : IO Unit :=
  runRealErr .invalidPath "switch invalidPath" (Git.switch "" mainRef)

/-- Real error-coverage test for `LeanSwe.Git.switch` returning `.invalidInput`. -/
def err_git_switch_invalidInput : IO Unit :=
  runRealErr .invalidInput "switch invalidInput" (Git.switch "/tmp" mainRef false (some "HEAD"))

/-- Real error-coverage test for `LeanSwe.Git.switch` returning `.dirtyWorktree`. -/
def err_git_switch_dirtyWorktree : IO Unit :=
  runRealSwitchDirtyErr

/-- Mocked error-coverage test for `LeanSwe.Git.switch` returning `.nothingToCommit`. -/
def err_git_switch_nothingToCommit : IO Unit :=
  runMockErr .nothingToCommit (fun api => api.switch "/mock/repo" mainRef false none false)

/-- Real error-coverage test for `LeanSwe.Git.switch` returning `.branchInUse`. -/
def err_git_switch_branchInUse : IO Unit :=
  runRealSwitchBranchInUseErr

/-- Real error-coverage test for `LeanSwe.Git.switch` returning `.alreadyExists`. -/
def err_git_switch_alreadyExists : IO Unit :=
  runRealCommittedErr .alreadyExists "switch alreadyExists" (fun repo _ => Git.switch repo mainRef true)

/-- Mocked error-coverage test for `LeanSwe.Git.switch` returning `.notFound`. -/
def err_git_switch_notFound : IO Unit :=
  runMockErr .notFound (fun api => api.switch "/mock/repo" mainRef false none false)

/-- Real error-coverage test for `LeanSwe.Git.switch` returning `.conflict`. -/
def err_git_switch_conflict : IO Unit :=
  runRealSwitchConflictErr

/-- Mocked error-coverage test for `LeanSwe.Git.switch` returning `.timeout`. -/
def err_git_switch_timeout : IO Unit :=
  runMockErr .timeout (fun api => api.switch "/mock/repo" mainRef false none false)

/-- Real error-coverage test for `LeanSwe.Git.switch` returning `.commandFailed`. -/
def err_git_switch_commandFailed : IO Unit :=
  runRealMissingDirErr (fun p => Git.switch p mainRef)

/-- Real error-coverage test for `LeanSwe.Git.reset` returning `.notARepo`. -/
def err_git_reset_notARepo : IO Unit :=
  runRealNonRepoErr (fun p => Git.reset p .hard "HEAD")

/-- Real error-coverage test for `LeanSwe.Git.reset` returning `.invalidRef`. -/
def err_git_reset_invalidRef : IO Unit :=
  runRealCommittedErr .invalidRef "reset invalidRef" (fun repo _ => Git.reset repo .hard zeroCid.hex)

/-- Real error-coverage test for `LeanSwe.Git.reset` returning `.invalidPath`. -/
def err_git_reset_invalidPath : IO Unit :=
  runRealErr .invalidPath "reset invalidPath" (Git.reset "" .hard "HEAD")

/-- Real error-coverage test for `LeanSwe.Git.reset` returning `.invalidInput`. -/
def err_git_reset_invalidInput : IO Unit :=
  runRealErr .invalidInput "reset invalidInput" (Git.reset "/tmp" .hard "HEAD:bad")

/-- Mocked error-coverage test for `LeanSwe.Git.reset` returning `.dirtyWorktree`. -/
def err_git_reset_dirtyWorktree : IO Unit :=
  runMockErr .dirtyWorktree (fun api => api.reset "/mock/repo" .hard "HEAD")

/-- Mocked error-coverage test for `LeanSwe.Git.reset` returning `.nothingToCommit`. -/
def err_git_reset_nothingToCommit : IO Unit :=
  runMockErr .nothingToCommit (fun api => api.reset "/mock/repo" .hard "HEAD")

/-- Mocked error-coverage test for `LeanSwe.Git.reset` returning `.branchInUse`. -/
def err_git_reset_branchInUse : IO Unit :=
  runMockErr .branchInUse (fun api => api.reset "/mock/repo" .hard "HEAD")

/-- Mocked error-coverage test for `LeanSwe.Git.reset` returning `.alreadyExists`. -/
def err_git_reset_alreadyExists : IO Unit :=
  runMockErr .alreadyExists (fun api => api.reset "/mock/repo" .hard "HEAD")

/-- Mocked error-coverage test for `LeanSwe.Git.reset` returning `.notFound`. -/
def err_git_reset_notFound : IO Unit :=
  runMockErr .notFound (fun api => api.reset "/mock/repo" .hard "HEAD")

/-- Mocked error-coverage test for `LeanSwe.Git.reset` returning `.conflict`. -/
def err_git_reset_conflict : IO Unit :=
  runMockErr .conflict (fun api => api.reset "/mock/repo" .hard "HEAD")

/-- Mocked error-coverage test for `LeanSwe.Git.reset` returning `.timeout`. -/
def err_git_reset_timeout : IO Unit :=
  runMockErr .timeout (fun api => api.reset "/mock/repo" .hard "HEAD")

/-- Real error-coverage test for `LeanSwe.Git.reset` returning `.commandFailed`. -/
def err_git_reset_commandFailed : IO Unit :=
  runRealMissingDirErr (fun p => Git.reset p .hard "HEAD")

/-- Real error-coverage test for `LeanSwe.Git.fetch` returning `.notARepo`. -/
def err_git_fetch_notARepo : IO Unit :=
  runRealNonRepoErr (fun p => Git.fetch p "origin")

/-- Mocked error-coverage test for `LeanSwe.Git.fetch` returning `.invalidRef`. -/
def err_git_fetch_invalidRef : IO Unit :=
  runMockErr .invalidRef (fun api => api.fetch "/mock/repo" "origin" none false)

/-- Real error-coverage test for `LeanSwe.Git.fetch` returning `.invalidPath`. -/
def err_git_fetch_invalidPath : IO Unit :=
  runRealErr .invalidPath "fetch invalidPath" (Git.fetch "" "origin")

/-- Real error-coverage test for `LeanSwe.Git.fetch` returning `.invalidInput`. -/
def err_git_fetch_invalidInput : IO Unit :=
  runRealErr .invalidInput "fetch invalidInput" (Git.fetch "/tmp" "--upload-pack=evil")

/-- Mocked error-coverage test for `LeanSwe.Git.fetch` returning `.dirtyWorktree`. -/
def err_git_fetch_dirtyWorktree : IO Unit :=
  runMockErr .dirtyWorktree (fun api => api.fetch "/mock/repo" "origin" none false)

/-- Mocked error-coverage test for `LeanSwe.Git.fetch` returning `.nothingToCommit`. -/
def err_git_fetch_nothingToCommit : IO Unit :=
  runMockErr .nothingToCommit (fun api => api.fetch "/mock/repo" "origin" none false)

/-- Mocked error-coverage test for `LeanSwe.Git.fetch` returning `.branchInUse`. -/
def err_git_fetch_branchInUse : IO Unit :=
  runMockErr .branchInUse (fun api => api.fetch "/mock/repo" "origin" none false)

/-- Mocked error-coverage test for `LeanSwe.Git.fetch` returning `.alreadyExists`. -/
def err_git_fetch_alreadyExists : IO Unit :=
  runMockErr .alreadyExists (fun api => api.fetch "/mock/repo" "origin" none false)

/-- Mocked error-coverage test for `LeanSwe.Git.fetch` returning `.notFound`. -/
def err_git_fetch_notFound : IO Unit :=
  runMockErr .notFound (fun api => api.fetch "/mock/repo" "origin" none false)

/-- Mocked error-coverage test for `LeanSwe.Git.fetch` returning `.conflict`. -/
def err_git_fetch_conflict : IO Unit :=
  runMockErr .conflict (fun api => api.fetch "/mock/repo" "origin" none false)

/-- Mocked error-coverage test for `LeanSwe.Git.fetch` returning `.timeout`. -/
def err_git_fetch_timeout : IO Unit :=
  runMockErr .timeout (fun api => api.fetch "/mock/repo" "origin" none false)

/-- Real error-coverage test for `LeanSwe.Git.fetch` returning `.commandFailed`. -/
def err_git_fetch_commandFailed : IO Unit :=
  runRealMissingDirErr (fun p => Git.fetch p "origin")

/-- Real error-coverage test for `LeanSwe.Git.worktreeAdd` returning `.notARepo`. -/
def err_git_worktreeAdd_notARepo : IO Unit :=
  runRealNonRepoErr (fun p => Git.worktreeAdd p { path := p ++ "/wt", detach := true })

/-- Real error-coverage test for `LeanSwe.Git.worktreeAdd` returning `.invalidRef`. -/
def err_git_worktreeAdd_invalidRef : IO Unit :=
  runRealCommittedErr .invalidRef "worktreeAdd invalidRef" (fun repo _ => Git.worktreeAdd repo { path := repo ++ "-wt", target? := some "no-such-ref" })

/-- Real error-coverage test for `LeanSwe.Git.worktreeAdd` returning `.invalidPath`. -/
def err_git_worktreeAdd_invalidPath : IO Unit :=
  runRealErr .invalidPath "worktreeAdd invalidPath" (Git.worktreeAdd "" { path := "/wt", detach := true })

/-- Real error-coverage test for `LeanSwe.Git.worktreeAdd` returning `.invalidInput`. -/
def err_git_worktreeAdd_invalidInput : IO Unit :=
  runRealErr .invalidInput "worktreeAdd invalidInput" (Git.worktreeAdd "/tmp" { path := "/tmp/wt", detach := true, newBranch? := some mainRef })

/-- Mocked error-coverage test for `LeanSwe.Git.worktreeAdd` returning `.dirtyWorktree`. -/
def err_git_worktreeAdd_dirtyWorktree : IO Unit :=
  runMockErr .dirtyWorktree (fun api => api.worktreeAdd "/mock/repo" { path := "/mock/wt", detach := true })

/-- Mocked error-coverage test for `LeanSwe.Git.worktreeAdd` returning `.nothingToCommit`. -/
def err_git_worktreeAdd_nothingToCommit : IO Unit :=
  runMockErr .nothingToCommit (fun api => api.worktreeAdd "/mock/repo" { path := "/mock/wt", detach := true })

/-- Real error-coverage test for `LeanSwe.Git.worktreeAdd` returning `.branchInUse`. -/
def err_git_worktreeAdd_branchInUse : IO Unit :=
  runRealCommittedErr .branchInUse "worktreeAdd branchInUse" (fun repo _ => Git.worktreeAdd repo { path := repo ++ "-wt", target? := some mainRef.raw })

/-- Real error-coverage test for `LeanSwe.Git.worktreeAdd` returning `.alreadyExists`. -/
def err_git_worktreeAdd_alreadyExists : IO Unit :=
  runRealWorktreeAddAlreadyExistsErr

/-- Mocked error-coverage test for `LeanSwe.Git.worktreeAdd` returning `.notFound`. -/
def err_git_worktreeAdd_notFound : IO Unit :=
  runMockErr .notFound (fun api => api.worktreeAdd "/mock/repo" { path := "/mock/wt", detach := true })

/-- Mocked error-coverage test for `LeanSwe.Git.worktreeAdd` returning `.conflict`. -/
def err_git_worktreeAdd_conflict : IO Unit :=
  runMockErr .conflict (fun api => api.worktreeAdd "/mock/repo" { path := "/mock/wt", detach := true })

/-- Mocked error-coverage test for `LeanSwe.Git.worktreeAdd` returning `.timeout`. -/
def err_git_worktreeAdd_timeout : IO Unit :=
  runMockErr .timeout (fun api => api.worktreeAdd "/mock/repo" { path := "/mock/wt", detach := true })

/-- Real error-coverage test for `LeanSwe.Git.worktreeAdd` returning `.commandFailed`. -/
def err_git_worktreeAdd_commandFailed : IO Unit :=
  runRealMissingDirErr (fun p => Git.worktreeAdd p { path := p ++ "-wt", detach := true })

/-- Real error-coverage test for `LeanSwe.Git.worktreeRemove` returning `.notARepo`. -/
def err_git_worktreeRemove_notARepo : IO Unit :=
  runRealNonRepoErr (fun p => Git.worktreeRemove p (p ++ "/wt"))

/-- Mocked error-coverage test for `LeanSwe.Git.worktreeRemove` returning `.invalidRef`. -/
def err_git_worktreeRemove_invalidRef : IO Unit :=
  runMockErr .invalidRef (fun api => api.worktreeRemove "/mock/repo" "/mock/wt" false)

/-- Real error-coverage test for `LeanSwe.Git.worktreeRemove` returning `.invalidPath`. -/
def err_git_worktreeRemove_invalidPath : IO Unit :=
  runRealErr .invalidPath "worktreeRemove invalidPath" (Git.worktreeRemove "" "/wt")

/-- Real error-coverage test for `LeanSwe.Git.worktreeRemove` returning `.invalidInput`. -/
def err_git_worktreeRemove_invalidInput : IO Unit :=
  runRealErr .invalidInput "worktreeRemove invalidInput" (Git.worktreeRemove longInvalidPath "/tmp/wt")

/-- Real error-coverage test for `LeanSwe.Git.worktreeRemove` returning `.dirtyWorktree`. -/
def err_git_worktreeRemove_dirtyWorktree : IO Unit :=
  runRealWorktreeRemoveDirtyErr

/-- Mocked error-coverage test for `LeanSwe.Git.worktreeRemove` returning `.nothingToCommit`. -/
def err_git_worktreeRemove_nothingToCommit : IO Unit :=
  runMockErr .nothingToCommit (fun api => api.worktreeRemove "/mock/repo" "/mock/wt" false)

/-- Mocked error-coverage test for `LeanSwe.Git.worktreeRemove` returning `.branchInUse`. -/
def err_git_worktreeRemove_branchInUse : IO Unit :=
  runMockErr .branchInUse (fun api => api.worktreeRemove "/mock/repo" "/mock/wt" false)

/-- Mocked error-coverage test for `LeanSwe.Git.worktreeRemove` returning `.alreadyExists`. -/
def err_git_worktreeRemove_alreadyExists : IO Unit :=
  runMockErr .alreadyExists (fun api => api.worktreeRemove "/mock/repo" "/mock/wt" false)

/-- Mocked error-coverage test for `LeanSwe.Git.worktreeRemove` returning `.notFound`. -/
def err_git_worktreeRemove_notFound : IO Unit :=
  runMockErr .notFound (fun api => api.worktreeRemove "/mock/repo" "/mock/wt" false)

/-- Mocked error-coverage test for `LeanSwe.Git.worktreeRemove` returning `.conflict`. -/
def err_git_worktreeRemove_conflict : IO Unit :=
  runMockErr .conflict (fun api => api.worktreeRemove "/mock/repo" "/mock/wt" false)

/-- Mocked error-coverage test for `LeanSwe.Git.worktreeRemove` returning `.timeout`. -/
def err_git_worktreeRemove_timeout : IO Unit :=
  runMockErr .timeout (fun api => api.worktreeRemove "/mock/repo" "/mock/wt" false)

/-- Real error-coverage test for `LeanSwe.Git.worktreeRemove` returning `.commandFailed`. -/
def err_git_worktreeRemove_commandFailed : IO Unit :=
  runRealMissingDirErr (fun p => Git.worktreeRemove p (p ++ "-wt"))

/-- Real error-coverage test for `LeanSwe.Git.withWorktree` returning `.notARepo`. -/
def err_git_withWorktree_notARepo : IO Unit :=
  runRealNonRepoErr (fun p => Git.withWorktree p { path := p ++ "/wt", detach := true } (fun _ => pure (.ok ())))

/-- Real error-coverage test for `LeanSwe.Git.withWorktree` returning `.invalidRef`. -/
def err_git_withWorktree_invalidRef : IO Unit :=
  runRealCommittedErr .invalidRef "withWorktree invalidRef" (fun repo _ => Git.withWorktree repo { path := repo ++ "-wt", target? := some "no-such-ref" } (fun _ => pure (.ok ())))

/-- Real error-coverage test for `LeanSwe.Git.withWorktree` returning `.invalidPath`. -/
def err_git_withWorktree_invalidPath : IO Unit :=
  runRealErr .invalidPath "withWorktree invalidPath" (Git.withWorktree "" { path := "/wt", detach := true } (fun _ => pure (.ok ())))

/-- Real error-coverage test for `LeanSwe.Git.withWorktree` returning `.invalidInput`. -/
def err_git_withWorktree_invalidInput : IO Unit :=
  runRealErr .invalidInput "withWorktree invalidInput" (Git.withWorktree "/tmp" { path := "/tmp/wt", detach := true, newBranch? := some mainRef } (fun _ => pure (.ok ())))

/-- Real error-coverage test for `LeanSwe.Git.withWorktree` returning `.dirtyWorktree`. -/
def err_git_withWorktree_dirtyWorktree : IO Unit :=
  runRealWithWorktreeDirtyErr

/-- Real error-coverage test for `LeanSwe.Git.withWorktree` returning `.nothingToCommit`. -/
def err_git_withWorktree_nothingToCommit : IO Unit :=
  runRealWithWorktreeNothingToCommitErr

/-- Real error-coverage test for `LeanSwe.Git.withWorktree` returning `.branchInUse`. -/
def err_git_withWorktree_branchInUse : IO Unit :=
  runRealCommittedErr .branchInUse "withWorktree branchInUse" (fun repo _ => Git.withWorktree repo { path := repo ++ "-wt", target? := some mainRef.raw } (fun _ => pure (.ok ())))

/-- Real error-coverage test for `LeanSwe.Git.withWorktree` returning `.alreadyExists`. -/
def err_git_withWorktree_alreadyExists : IO Unit :=
  runRealWithWorktreeAlreadyExistsErr

/-- Real error-coverage test for `LeanSwe.Git.withWorktree` returning `.notFound`. -/
def err_git_withWorktree_notFound : IO Unit :=
  runRealWithWorktreeNotFoundErr

/-- Real error-coverage test for `LeanSwe.Git.withWorktree` returning `.conflict`. -/
def err_git_withWorktree_conflict : IO Unit :=
  runRealWithWorktreeConflictErr

/-- Mocked error-coverage test for `LeanSwe.Git.withWorktree` returning `.timeout`. -/
def err_git_withWorktree_timeout : IO Unit :=
  runMockErr .timeout (fun api => api.withWorktree "/mock/repo" { path := "/mock/wt", detach := true } (fun _ => pure (.ok ())))

/-- Real error-coverage test for `LeanSwe.Git.withWorktree` returning `.commandFailed`. -/
def err_git_withWorktree_commandFailed : IO Unit :=
  runRealMissingDirErr (fun p => Git.withWorktree p { path := p ++ "-wt", detach := true } (fun _ => pure (.ok ())))

/-- Real error-coverage test for `LeanSwe.Git.withWorktree` returning `.parseError`. -/
def err_git_withWorktree_parseError : IO Unit :=
  runRealWithWorktreeParseError


end LeanSwe.Git.RuntimeTests
