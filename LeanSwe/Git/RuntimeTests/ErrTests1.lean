import LeanSwe.Git.Impl
import LeanSwe.Git.Interface
import LeanSwe.Git.RuntimeTests.Helpers

namespace LeanSwe.Git.RuntimeTests

open LeanSwe.Git
open LeanSwe.Git.Model

/-- Mocked error-coverage test for `LeanSwe.Git.isRepo` returning `.invalidRef`. -/
def err_git_isRepo_invalidRef : IO Unit :=
  runMockErr .invalidRef (fun api => api.isRepo "/mock/repo")

/-- Real error-coverage test for `LeanSwe.Git.isRepo` returning `.invalidPath`. -/
def err_git_isRepo_invalidPath : IO Unit :=
  runRealErr .invalidPath "isRepo invalidPath" (Git.isRepo "")

/-- Real error-coverage test for `LeanSwe.Git.isRepo` returning `.invalidInput`. -/
def err_git_isRepo_invalidInput : IO Unit :=
  runRealErr .invalidInput "isRepo invalidInput" (Git.isRepo longInvalidPath)

/-- Mocked error-coverage test for `LeanSwe.Git.isRepo` returning `.dirtyWorktree`. -/
def err_git_isRepo_dirtyWorktree : IO Unit :=
  runMockErr .dirtyWorktree (fun api => api.isRepo "/mock/repo")

/-- Mocked error-coverage test for `LeanSwe.Git.isRepo` returning `.nothingToCommit`. -/
def err_git_isRepo_nothingToCommit : IO Unit :=
  runMockErr .nothingToCommit (fun api => api.isRepo "/mock/repo")

/-- Mocked error-coverage test for `LeanSwe.Git.isRepo` returning `.branchInUse`. -/
def err_git_isRepo_branchInUse : IO Unit :=
  runMockErr .branchInUse (fun api => api.isRepo "/mock/repo")

/-- Mocked error-coverage test for `LeanSwe.Git.isRepo` returning `.alreadyExists`. -/
def err_git_isRepo_alreadyExists : IO Unit :=
  runMockErr .alreadyExists (fun api => api.isRepo "/mock/repo")

/-- Mocked error-coverage test for `LeanSwe.Git.isRepo` returning `.notFound`. -/
def err_git_isRepo_notFound : IO Unit :=
  runMockErr .notFound (fun api => api.isRepo "/mock/repo")

/-- Mocked error-coverage test for `LeanSwe.Git.isRepo` returning `.conflict`. -/
def err_git_isRepo_conflict : IO Unit :=
  runMockErr .conflict (fun api => api.isRepo "/mock/repo")

/-- Mocked error-coverage test for `LeanSwe.Git.isRepo` returning `.timeout`. -/
def err_git_isRepo_timeout : IO Unit :=
  runMockErr .timeout (fun api => api.isRepo "/mock/repo")

/-- Real error-coverage test for `LeanSwe.Git.isRepo` returning `.commandFailed`. -/
def err_git_isRepo_commandFailed : IO Unit :=
  runRealMissingDirErr Git.isRepo

/-- Real error-coverage test for `LeanSwe.Git.repoRoot` returning `.notARepo`. -/
def err_git_repoRoot_notARepo : IO Unit :=
  runRealNonRepoErr Git.repoRoot

/-- Mocked error-coverage test for `LeanSwe.Git.repoRoot` returning `.invalidRef`. -/
def err_git_repoRoot_invalidRef : IO Unit :=
  runMockErr .invalidRef (fun api => api.repoRoot "/mock/repo")

/-- Real error-coverage test for `LeanSwe.Git.repoRoot` returning `.invalidPath`. -/
def err_git_repoRoot_invalidPath : IO Unit :=
  runRealErr .invalidPath "repoRoot invalidPath" (Git.repoRoot "")

/-- Real error-coverage test for `LeanSwe.Git.repoRoot` returning `.invalidInput`. -/
def err_git_repoRoot_invalidInput : IO Unit :=
  runRealErr .invalidInput "repoRoot invalidInput" (Git.repoRoot longInvalidPath)

/-- Mocked error-coverage test for `LeanSwe.Git.repoRoot` returning `.dirtyWorktree`. -/
def err_git_repoRoot_dirtyWorktree : IO Unit :=
  runMockErr .dirtyWorktree (fun api => api.repoRoot "/mock/repo")

/-- Mocked error-coverage test for `LeanSwe.Git.repoRoot` returning `.nothingToCommit`. -/
def err_git_repoRoot_nothingToCommit : IO Unit :=
  runMockErr .nothingToCommit (fun api => api.repoRoot "/mock/repo")

/-- Mocked error-coverage test for `LeanSwe.Git.repoRoot` returning `.branchInUse`. -/
def err_git_repoRoot_branchInUse : IO Unit :=
  runMockErr .branchInUse (fun api => api.repoRoot "/mock/repo")

/-- Mocked error-coverage test for `LeanSwe.Git.repoRoot` returning `.alreadyExists`. -/
def err_git_repoRoot_alreadyExists : IO Unit :=
  runMockErr .alreadyExists (fun api => api.repoRoot "/mock/repo")

/-- Mocked error-coverage test for `LeanSwe.Git.repoRoot` returning `.notFound`. -/
def err_git_repoRoot_notFound : IO Unit :=
  runMockErr .notFound (fun api => api.repoRoot "/mock/repo")

/-- Mocked error-coverage test for `LeanSwe.Git.repoRoot` returning `.conflict`. -/
def err_git_repoRoot_conflict : IO Unit :=
  runMockErr .conflict (fun api => api.repoRoot "/mock/repo")

/-- Mocked error-coverage test for `LeanSwe.Git.repoRoot` returning `.timeout`. -/
def err_git_repoRoot_timeout : IO Unit :=
  runMockErr .timeout (fun api => api.repoRoot "/mock/repo")

/-- Real error-coverage test for `LeanSwe.Git.repoRoot` returning `.commandFailed`. -/
def err_git_repoRoot_commandFailed : IO Unit :=
  runRealMissingDirErr Git.repoRoot

/-- Real error-coverage test for `LeanSwe.Git.repoRoot` returning `.parseError`. -/
def err_git_repoRoot_parseError : IO Unit :=
  withBadUtf8Repo fun link => do assertErrKind (← Git.repoRoot link) .parseError "repoRoot parseError"

/-- Real error-coverage test for `LeanSwe.Git.commonDir` returning `.notARepo`. -/
def err_git_commonDir_notARepo : IO Unit :=
  runRealNonRepoErr Git.commonDir

/-- Mocked error-coverage test for `LeanSwe.Git.commonDir` returning `.invalidRef`. -/
def err_git_commonDir_invalidRef : IO Unit :=
  runMockErr .invalidRef (fun api => api.commonDir "/mock/repo")

/-- Real error-coverage test for `LeanSwe.Git.commonDir` returning `.invalidPath`. -/
def err_git_commonDir_invalidPath : IO Unit :=
  runRealErr .invalidPath "commonDir invalidPath" (Git.commonDir "")

/-- Real error-coverage test for `LeanSwe.Git.commonDir` returning `.invalidInput`. -/
def err_git_commonDir_invalidInput : IO Unit :=
  runRealErr .invalidInput "commonDir invalidInput" (Git.commonDir longInvalidPath)

/-- Mocked error-coverage test for `LeanSwe.Git.commonDir` returning `.dirtyWorktree`. -/
def err_git_commonDir_dirtyWorktree : IO Unit :=
  runMockErr .dirtyWorktree (fun api => api.commonDir "/mock/repo")

/-- Mocked error-coverage test for `LeanSwe.Git.commonDir` returning `.nothingToCommit`. -/
def err_git_commonDir_nothingToCommit : IO Unit :=
  runMockErr .nothingToCommit (fun api => api.commonDir "/mock/repo")

/-- Mocked error-coverage test for `LeanSwe.Git.commonDir` returning `.branchInUse`. -/
def err_git_commonDir_branchInUse : IO Unit :=
  runMockErr .branchInUse (fun api => api.commonDir "/mock/repo")

/-- Mocked error-coverage test for `LeanSwe.Git.commonDir` returning `.alreadyExists`. -/
def err_git_commonDir_alreadyExists : IO Unit :=
  runMockErr .alreadyExists (fun api => api.commonDir "/mock/repo")

/-- Mocked error-coverage test for `LeanSwe.Git.commonDir` returning `.notFound`. -/
def err_git_commonDir_notFound : IO Unit :=
  runMockErr .notFound (fun api => api.commonDir "/mock/repo")

/-- Mocked error-coverage test for `LeanSwe.Git.commonDir` returning `.conflict`. -/
def err_git_commonDir_conflict : IO Unit :=
  runMockErr .conflict (fun api => api.commonDir "/mock/repo")

/-- Mocked error-coverage test for `LeanSwe.Git.commonDir` returning `.timeout`. -/
def err_git_commonDir_timeout : IO Unit :=
  runMockErr .timeout (fun api => api.commonDir "/mock/repo")

/-- Real error-coverage test for `LeanSwe.Git.commonDir` returning `.commandFailed`. -/
def err_git_commonDir_commandFailed : IO Unit :=
  runRealMissingDirErr Git.commonDir

/-- Real error-coverage test for `LeanSwe.Git.commonDir` returning `.parseError`. -/
def err_git_commonDir_parseError : IO Unit :=
  withBadUtf8Repo fun link => do assertErrKind (← Git.commonDir link) .parseError "commonDir parseError"

/-- Real error-coverage test for `LeanSwe.Git.headCommit?` returning `.notARepo`. -/
def err_git_headCommit_notARepo : IO Unit :=
  runRealNonRepoErr Git.headCommit?

/-- Mocked error-coverage test for `LeanSwe.Git.headCommit?` returning `.invalidRef`. -/
def err_git_headCommit_invalidRef : IO Unit :=
  runMockErr .invalidRef (fun api => api.headCommit? "/mock/repo")

/-- Real error-coverage test for `LeanSwe.Git.headCommit?` returning `.invalidPath`. -/
def err_git_headCommit_invalidPath : IO Unit :=
  runRealErr .invalidPath "headCommit? invalidPath" (Git.headCommit? "")

/-- Real error-coverage test for `LeanSwe.Git.headCommit?` returning `.invalidInput`. -/
def err_git_headCommit_invalidInput : IO Unit :=
  runRealErr .invalidInput "headCommit? invalidInput" (Git.headCommit? longInvalidPath)

/-- Mocked error-coverage test for `LeanSwe.Git.headCommit?` returning `.dirtyWorktree`. -/
def err_git_headCommit_dirtyWorktree : IO Unit :=
  runMockErr .dirtyWorktree (fun api => api.headCommit? "/mock/repo")

/-- Mocked error-coverage test for `LeanSwe.Git.headCommit?` returning `.nothingToCommit`. -/
def err_git_headCommit_nothingToCommit : IO Unit :=
  runMockErr .nothingToCommit (fun api => api.headCommit? "/mock/repo")

/-- Mocked error-coverage test for `LeanSwe.Git.headCommit?` returning `.branchInUse`. -/
def err_git_headCommit_branchInUse : IO Unit :=
  runMockErr .branchInUse (fun api => api.headCommit? "/mock/repo")

/-- Mocked error-coverage test for `LeanSwe.Git.headCommit?` returning `.alreadyExists`. -/
def err_git_headCommit_alreadyExists : IO Unit :=
  runMockErr .alreadyExists (fun api => api.headCommit? "/mock/repo")

/-- Mocked error-coverage test for `LeanSwe.Git.headCommit?` returning `.notFound`. -/
def err_git_headCommit_notFound : IO Unit :=
  runMockErr .notFound (fun api => api.headCommit? "/mock/repo")

/-- Mocked error-coverage test for `LeanSwe.Git.headCommit?` returning `.conflict`. -/
def err_git_headCommit_conflict : IO Unit :=
  runMockErr .conflict (fun api => api.headCommit? "/mock/repo")

/-- Mocked error-coverage test for `LeanSwe.Git.headCommit?` returning `.timeout`. -/
def err_git_headCommit_timeout : IO Unit :=
  runMockErr .timeout (fun api => api.headCommit? "/mock/repo")

/-- Real error-coverage test for `LeanSwe.Git.headCommit?` returning `.commandFailed`. -/
def err_git_headCommit_commandFailed : IO Unit :=
  runRealMissingDirErr Git.headCommit?

/-- Mocked error-coverage test for `LeanSwe.Git.headCommit?` returning `.parseError`. -/
def err_git_headCommit_parseError : IO Unit :=
  runMockErr .parseError (fun api => api.headCommit? "/mock/repo")

/-- Real error-coverage test for `LeanSwe.Git.headBranch?` returning `.notARepo`. -/
def err_git_headBranch_notARepo : IO Unit :=
  runRealNonRepoErr Git.headBranch?

/-- Mocked error-coverage test for `LeanSwe.Git.headBranch?` returning `.invalidRef`. -/
def err_git_headBranch_invalidRef : IO Unit :=
  runMockErr .invalidRef (fun api => api.headBranch? "/mock/repo")

/-- Real error-coverage test for `LeanSwe.Git.headBranch?` returning `.invalidPath`. -/
def err_git_headBranch_invalidPath : IO Unit :=
  runRealErr .invalidPath "headBranch? invalidPath" (Git.headBranch? "")

/-- Real error-coverage test for `LeanSwe.Git.headBranch?` returning `.invalidInput`. -/
def err_git_headBranch_invalidInput : IO Unit :=
  runRealErr .invalidInput "headBranch? invalidInput" (Git.headBranch? longInvalidPath)

/-- Mocked error-coverage test for `LeanSwe.Git.headBranch?` returning `.dirtyWorktree`. -/
def err_git_headBranch_dirtyWorktree : IO Unit :=
  runMockErr .dirtyWorktree (fun api => api.headBranch? "/mock/repo")

/-- Mocked error-coverage test for `LeanSwe.Git.headBranch?` returning `.nothingToCommit`. -/
def err_git_headBranch_nothingToCommit : IO Unit :=
  runMockErr .nothingToCommit (fun api => api.headBranch? "/mock/repo")

/-- Mocked error-coverage test for `LeanSwe.Git.headBranch?` returning `.branchInUse`. -/
def err_git_headBranch_branchInUse : IO Unit :=
  runMockErr .branchInUse (fun api => api.headBranch? "/mock/repo")

/-- Mocked error-coverage test for `LeanSwe.Git.headBranch?` returning `.alreadyExists`. -/
def err_git_headBranch_alreadyExists : IO Unit :=
  runMockErr .alreadyExists (fun api => api.headBranch? "/mock/repo")

/-- Mocked error-coverage test for `LeanSwe.Git.headBranch?` returning `.notFound`. -/
def err_git_headBranch_notFound : IO Unit :=
  runMockErr .notFound (fun api => api.headBranch? "/mock/repo")

/-- Mocked error-coverage test for `LeanSwe.Git.headBranch?` returning `.conflict`. -/
def err_git_headBranch_conflict : IO Unit :=
  runMockErr .conflict (fun api => api.headBranch? "/mock/repo")

/-- Mocked error-coverage test for `LeanSwe.Git.headBranch?` returning `.timeout`. -/
def err_git_headBranch_timeout : IO Unit :=
  runMockErr .timeout (fun api => api.headBranch? "/mock/repo")

/-- Real error-coverage test for `LeanSwe.Git.headBranch?` returning `.commandFailed`. -/
def err_git_headBranch_commandFailed : IO Unit :=
  runRealMissingDirErr Git.headBranch?

/-- Mocked error-coverage test for `LeanSwe.Git.headBranch?` returning `.parseError`. -/
def err_git_headBranch_parseError : IO Unit :=
  runMockErr .parseError (fun api => api.headBranch? "/mock/repo")

/-- Real error-coverage test for `LeanSwe.Git.headState` returning `.notARepo`. -/
def err_git_headState_notARepo : IO Unit :=
  runRealNonRepoErr Git.headState

/-- Mocked error-coverage test for `LeanSwe.Git.headState` returning `.invalidRef`. -/
def err_git_headState_invalidRef : IO Unit :=
  runMockErr .invalidRef (fun api => api.headState "/mock/repo")

/-- Real error-coverage test for `LeanSwe.Git.headState` returning `.invalidPath`. -/
def err_git_headState_invalidPath : IO Unit :=
  runRealErr .invalidPath "headState invalidPath" (Git.headState "")

/-- Real error-coverage test for `LeanSwe.Git.headState` returning `.invalidInput`. -/
def err_git_headState_invalidInput : IO Unit :=
  runRealErr .invalidInput "headState invalidInput" (Git.headState longInvalidPath)

/-- Mocked error-coverage test for `LeanSwe.Git.headState` returning `.dirtyWorktree`. -/
def err_git_headState_dirtyWorktree : IO Unit :=
  runMockErr .dirtyWorktree (fun api => api.headState "/mock/repo")

/-- Mocked error-coverage test for `LeanSwe.Git.headState` returning `.nothingToCommit`. -/
def err_git_headState_nothingToCommit : IO Unit :=
  runMockErr .nothingToCommit (fun api => api.headState "/mock/repo")

/-- Mocked error-coverage test for `LeanSwe.Git.headState` returning `.branchInUse`. -/
def err_git_headState_branchInUse : IO Unit :=
  runMockErr .branchInUse (fun api => api.headState "/mock/repo")

/-- Mocked error-coverage test for `LeanSwe.Git.headState` returning `.alreadyExists`. -/
def err_git_headState_alreadyExists : IO Unit :=
  runMockErr .alreadyExists (fun api => api.headState "/mock/repo")

/-- Mocked error-coverage test for `LeanSwe.Git.headState` returning `.notFound`. -/
def err_git_headState_notFound : IO Unit :=
  runMockErr .notFound (fun api => api.headState "/mock/repo")

/-- Mocked error-coverage test for `LeanSwe.Git.headState` returning `.conflict`. -/
def err_git_headState_conflict : IO Unit :=
  runMockErr .conflict (fun api => api.headState "/mock/repo")

/-- Mocked error-coverage test for `LeanSwe.Git.headState` returning `.timeout`. -/
def err_git_headState_timeout : IO Unit :=
  runMockErr .timeout (fun api => api.headState "/mock/repo")

/-- Real error-coverage test for `LeanSwe.Git.headState` returning `.commandFailed`. -/
def err_git_headState_commandFailed : IO Unit :=
  runRealMissingDirErr Git.headState

/-- Mocked error-coverage test for `LeanSwe.Git.headState` returning `.parseError`. -/
def err_git_headState_parseError : IO Unit :=
  runMockErr .parseError (fun api => api.headState "/mock/repo")

/-- Real error-coverage test for `LeanSwe.Git.revParseCommit` returning `.notARepo`. -/
def err_git_revParseCommit_notARepo : IO Unit :=
  runRealNonRepoErr (fun p => Git.revParseCommit p "HEAD")

/-- Real error-coverage test for `LeanSwe.Git.revParseCommit` returning `.invalidRef`. -/
def err_git_revParseCommit_invalidRef : IO Unit :=
  runRealCommittedErr .invalidRef "revParseCommit invalidRef" (fun repo _ => Git.revParseCommit repo "no-such-ref")

/-- Real error-coverage test for `LeanSwe.Git.revParseCommit` returning `.invalidPath`. -/
def err_git_revParseCommit_invalidPath : IO Unit :=
  runRealErr .invalidPath "revParseCommit invalidPath" (Git.revParseCommit "" "HEAD")

/-- Real error-coverage test for `LeanSwe.Git.revParseCommit` returning `.invalidInput`. -/
def err_git_revParseCommit_invalidInput : IO Unit :=
  runRealErr .invalidInput "revParseCommit invalidInput" (Git.revParseCommit "/tmp" "-bad")

/-- Mocked error-coverage test for `LeanSwe.Git.revParseCommit` returning `.dirtyWorktree`. -/
def err_git_revParseCommit_dirtyWorktree : IO Unit :=
  runMockErr .dirtyWorktree (fun api => api.revParseCommit "/mock/repo" "HEAD")

/-- Mocked error-coverage test for `LeanSwe.Git.revParseCommit` returning `.nothingToCommit`. -/
def err_git_revParseCommit_nothingToCommit : IO Unit :=
  runMockErr .nothingToCommit (fun api => api.revParseCommit "/mock/repo" "HEAD")

/-- Mocked error-coverage test for `LeanSwe.Git.revParseCommit` returning `.branchInUse`. -/
def err_git_revParseCommit_branchInUse : IO Unit :=
  runMockErr .branchInUse (fun api => api.revParseCommit "/mock/repo" "HEAD")

/-- Mocked error-coverage test for `LeanSwe.Git.revParseCommit` returning `.alreadyExists`. -/
def err_git_revParseCommit_alreadyExists : IO Unit :=
  runMockErr .alreadyExists (fun api => api.revParseCommit "/mock/repo" "HEAD")

/-- Mocked error-coverage test for `LeanSwe.Git.revParseCommit` returning `.notFound`. -/
def err_git_revParseCommit_notFound : IO Unit :=
  runMockErr .notFound (fun api => api.revParseCommit "/mock/repo" "HEAD")

/-- Mocked error-coverage test for `LeanSwe.Git.revParseCommit` returning `.conflict`. -/
def err_git_revParseCommit_conflict : IO Unit :=
  runMockErr .conflict (fun api => api.revParseCommit "/mock/repo" "HEAD")

/-- Mocked error-coverage test for `LeanSwe.Git.revParseCommit` returning `.timeout`. -/
def err_git_revParseCommit_timeout : IO Unit :=
  runMockErr .timeout (fun api => api.revParseCommit "/mock/repo" "HEAD")

/-- Real error-coverage test for `LeanSwe.Git.revParseCommit` returning `.commandFailed`. -/
def err_git_revParseCommit_commandFailed : IO Unit :=
  runRealMissingDirErr (fun p => Git.revParseCommit p "HEAD")

/-- Mocked error-coverage test for `LeanSwe.Git.revParseCommit` returning `.parseError`. -/
def err_git_revParseCommit_parseError : IO Unit :=
  runMockErr .parseError (fun api => api.revParseCommit "/mock/repo" "HEAD")

/-- Real error-coverage test for `LeanSwe.Git.isAncestor` returning `.notARepo`. -/
def err_git_isAncestor_notARepo : IO Unit :=
  runRealNonRepoErr (fun p => Git.isAncestor p dummyCid dummyCid)

/-- Real error-coverage test for `LeanSwe.Git.isAncestor` returning `.invalidRef`. -/
def err_git_isAncestor_invalidRef : IO Unit :=
  runRealCommittedErr .invalidRef "isAncestor invalidRef" (fun repo cid => Git.isAncestor repo zeroCid cid)

/-- Real error-coverage test for `LeanSwe.Git.isAncestor` returning `.invalidPath`. -/
def err_git_isAncestor_invalidPath : IO Unit :=
  runRealErr .invalidPath "isAncestor invalidPath" (Git.isAncestor "" dummyCid dummyCid)

/-- Real error-coverage test for `LeanSwe.Git.isAncestor` returning `.invalidInput`. -/
def err_git_isAncestor_invalidInput : IO Unit :=
  runRealErr .invalidInput "isAncestor invalidInput" (Git.isAncestor longInvalidPath dummyCid dummyCid)

/-- Mocked error-coverage test for `LeanSwe.Git.isAncestor` returning `.dirtyWorktree`. -/
def err_git_isAncestor_dirtyWorktree : IO Unit :=
  runMockErr .dirtyWorktree (fun api => api.isAncestor "/mock/repo" dummyCid dummyCid)

/-- Mocked error-coverage test for `LeanSwe.Git.isAncestor` returning `.nothingToCommit`. -/
def err_git_isAncestor_nothingToCommit : IO Unit :=
  runMockErr .nothingToCommit (fun api => api.isAncestor "/mock/repo" dummyCid dummyCid)

/-- Mocked error-coverage test for `LeanSwe.Git.isAncestor` returning `.branchInUse`. -/
def err_git_isAncestor_branchInUse : IO Unit :=
  runMockErr .branchInUse (fun api => api.isAncestor "/mock/repo" dummyCid dummyCid)

/-- Mocked error-coverage test for `LeanSwe.Git.isAncestor` returning `.alreadyExists`. -/
def err_git_isAncestor_alreadyExists : IO Unit :=
  runMockErr .alreadyExists (fun api => api.isAncestor "/mock/repo" dummyCid dummyCid)

/-- Mocked error-coverage test for `LeanSwe.Git.isAncestor` returning `.notFound`. -/
def err_git_isAncestor_notFound : IO Unit :=
  runMockErr .notFound (fun api => api.isAncestor "/mock/repo" dummyCid dummyCid)

/-- Mocked error-coverage test for `LeanSwe.Git.isAncestor` returning `.conflict`. -/
def err_git_isAncestor_conflict : IO Unit :=
  runMockErr .conflict (fun api => api.isAncestor "/mock/repo" dummyCid dummyCid)

/-- Mocked error-coverage test for `LeanSwe.Git.isAncestor` returning `.timeout`. -/
def err_git_isAncestor_timeout : IO Unit :=
  runMockErr .timeout (fun api => api.isAncestor "/mock/repo" dummyCid dummyCid)

/-- Real error-coverage test for `LeanSwe.Git.isAncestor` returning `.commandFailed`. -/
def err_git_isAncestor_commandFailed : IO Unit :=
  runRealMissingDirErr (fun p => Git.isAncestor p dummyCid dummyCid)

/-- Real error-coverage test for `LeanSwe.Git.mergeBase?` returning `.notARepo`. -/
def err_git_mergeBase_notARepo : IO Unit :=
  runRealNonRepoErr (fun p => Git.mergeBase? p dummyCid dummyCid)

/-- Real error-coverage test for `LeanSwe.Git.mergeBase?` returning `.invalidRef`. -/
def err_git_mergeBase_invalidRef : IO Unit :=
  runRealCommittedErr .invalidRef "mergeBase? invalidRef" (fun repo cid => Git.mergeBase? repo zeroCid cid)

/-- Real error-coverage test for `LeanSwe.Git.mergeBase?` returning `.invalidPath`. -/
def err_git_mergeBase_invalidPath : IO Unit :=
  runRealErr .invalidPath "mergeBase? invalidPath" (Git.mergeBase? "" dummyCid dummyCid)

/-- Real error-coverage test for `LeanSwe.Git.mergeBase?` returning `.invalidInput`. -/
def err_git_mergeBase_invalidInput : IO Unit :=
  runRealErr .invalidInput "mergeBase? invalidInput" (Git.mergeBase? longInvalidPath dummyCid dummyCid)

/-- Mocked error-coverage test for `LeanSwe.Git.mergeBase?` returning `.dirtyWorktree`. -/
def err_git_mergeBase_dirtyWorktree : IO Unit :=
  runMockErr .dirtyWorktree (fun api => api.mergeBase? "/mock/repo" dummyCid dummyCid)

/-- Mocked error-coverage test for `LeanSwe.Git.mergeBase?` returning `.nothingToCommit`. -/
def err_git_mergeBase_nothingToCommit : IO Unit :=
  runMockErr .nothingToCommit (fun api => api.mergeBase? "/mock/repo" dummyCid dummyCid)

/-- Mocked error-coverage test for `LeanSwe.Git.mergeBase?` returning `.branchInUse`. -/
def err_git_mergeBase_branchInUse : IO Unit :=
  runMockErr .branchInUse (fun api => api.mergeBase? "/mock/repo" dummyCid dummyCid)

/-- Mocked error-coverage test for `LeanSwe.Git.mergeBase?` returning `.alreadyExists`. -/
def err_git_mergeBase_alreadyExists : IO Unit :=
  runMockErr .alreadyExists (fun api => api.mergeBase? "/mock/repo" dummyCid dummyCid)

/-- Mocked error-coverage test for `LeanSwe.Git.mergeBase?` returning `.notFound`. -/
def err_git_mergeBase_notFound : IO Unit :=
  runMockErr .notFound (fun api => api.mergeBase? "/mock/repo" dummyCid dummyCid)

/-- Mocked error-coverage test for `LeanSwe.Git.mergeBase?` returning `.conflict`. -/
def err_git_mergeBase_conflict : IO Unit :=
  runMockErr .conflict (fun api => api.mergeBase? "/mock/repo" dummyCid dummyCid)

/-- Mocked error-coverage test for `LeanSwe.Git.mergeBase?` returning `.timeout`. -/
def err_git_mergeBase_timeout : IO Unit :=
  runMockErr .timeout (fun api => api.mergeBase? "/mock/repo" dummyCid dummyCid)


end LeanSwe.Git.RuntimeTests
