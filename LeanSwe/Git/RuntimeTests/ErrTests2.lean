import LeanSwe.Git.Impl
import LeanSwe.Git.Interface
import LeanSwe.Git.RuntimeTests.Helpers

namespace LeanSwe.Git.RuntimeTests

open LeanSwe.Git
open LeanSwe.Git.Model

/-- Real error-coverage test for `LeanSwe.Git.mergeBase?` returning `.commandFailed`. -/
def err_git_mergeBase_commandFailed : IO Unit :=
  runRealMissingDirErr (fun p => Git.mergeBase? p dummyCid dummyCid)

/-- Mocked error-coverage test for `LeanSwe.Git.mergeBase?` returning `.parseError`. -/
def err_git_mergeBase_parseError : IO Unit :=
  runMockErr .parseError (fun api => api.mergeBase? "/mock/repo" dummyCid dummyCid)

/-- Real error-coverage test for `LeanSwe.Git.status` returning `.notARepo`. -/
def err_git_status_notARepo : IO Unit :=
  runRealNonRepoErr Git.status

/-- Mocked error-coverage test for `LeanSwe.Git.status` returning `.invalidRef`. -/
def err_git_status_invalidRef : IO Unit :=
  runMockErr .invalidRef (fun api => api.status "/mock/repo")

/-- Real error-coverage test for `LeanSwe.Git.status` returning `.invalidPath`. -/
def err_git_status_invalidPath : IO Unit :=
  runRealErr .invalidPath "status invalidPath" (Git.status "")

/-- Real error-coverage test for `LeanSwe.Git.status` returning `.invalidInput`. -/
def err_git_status_invalidInput : IO Unit :=
  runRealErr .invalidInput "status invalidInput" (Git.status longInvalidPath)

/-- Mocked error-coverage test for `LeanSwe.Git.status` returning `.dirtyWorktree`. -/
def err_git_status_dirtyWorktree : IO Unit :=
  runMockErr .dirtyWorktree (fun api => api.status "/mock/repo")

/-- Mocked error-coverage test for `LeanSwe.Git.status` returning `.nothingToCommit`. -/
def err_git_status_nothingToCommit : IO Unit :=
  runMockErr .nothingToCommit (fun api => api.status "/mock/repo")

/-- Mocked error-coverage test for `LeanSwe.Git.status` returning `.branchInUse`. -/
def err_git_status_branchInUse : IO Unit :=
  runMockErr .branchInUse (fun api => api.status "/mock/repo")

/-- Mocked error-coverage test for `LeanSwe.Git.status` returning `.alreadyExists`. -/
def err_git_status_alreadyExists : IO Unit :=
  runMockErr .alreadyExists (fun api => api.status "/mock/repo")

/-- Mocked error-coverage test for `LeanSwe.Git.status` returning `.notFound`. -/
def err_git_status_notFound : IO Unit :=
  runMockErr .notFound (fun api => api.status "/mock/repo")

/-- Mocked error-coverage test for `LeanSwe.Git.status` returning `.conflict`. -/
def err_git_status_conflict : IO Unit :=
  runMockErr .conflict (fun api => api.status "/mock/repo")

/-- Mocked error-coverage test for `LeanSwe.Git.status` returning `.timeout`. -/
def err_git_status_timeout : IO Unit :=
  runMockErr .timeout (fun api => api.status "/mock/repo")

/-- Real error-coverage test for `LeanSwe.Git.status` returning `.commandFailed`. -/
def err_git_status_commandFailed : IO Unit :=
  runRealMissingDirErr Git.status

/-- Real error-coverage test for `LeanSwe.Git.status` returning `.parseError`. -/
def err_git_status_parseError : IO Unit :=
  withBadUtf8UntrackedRepo fun repo => do assertErrKind (← Git.status repo) .parseError "status parseError"

/-- Real error-coverage test for `LeanSwe.Git.diffNameStatus` returning `.notARepo`. -/
def err_git_diffNameStatus_notARepo : IO Unit :=
  runRealNonRepoErr (fun p => Git.diffNameStatus p "HEAD")

/-- Real error-coverage test for `LeanSwe.Git.diffNameStatus` returning `.invalidRef`. -/
def err_git_diffNameStatus_invalidRef : IO Unit :=
  runRealCommittedErr .invalidRef "diffNameStatus invalidRef" (fun repo _ => Git.diffNameStatus repo "no-such-ref")

/-- Real error-coverage test for `LeanSwe.Git.diffNameStatus` returning `.invalidPath`. -/
def err_git_diffNameStatus_invalidPath : IO Unit :=
  runRealErr .invalidPath "diffNameStatus invalidPath" (Git.diffNameStatus "" "HEAD")

/-- Real error-coverage test for `LeanSwe.Git.diffNameStatus` returning `.invalidInput`. -/
def err_git_diffNameStatus_invalidInput : IO Unit :=
  runRealErr .invalidInput "diffNameStatus invalidInput" (Git.diffNameStatus "/tmp" "HEAD:bad")

/-- Mocked error-coverage test for `LeanSwe.Git.diffNameStatus` returning `.dirtyWorktree`. -/
def err_git_diffNameStatus_dirtyWorktree : IO Unit :=
  runMockErr .dirtyWorktree (fun api => api.diffNameStatus "/mock/repo" "HEAD" none #[])

/-- Mocked error-coverage test for `LeanSwe.Git.diffNameStatus` returning `.nothingToCommit`. -/
def err_git_diffNameStatus_nothingToCommit : IO Unit :=
  runMockErr .nothingToCommit (fun api => api.diffNameStatus "/mock/repo" "HEAD" none #[])

/-- Mocked error-coverage test for `LeanSwe.Git.diffNameStatus` returning `.branchInUse`. -/
def err_git_diffNameStatus_branchInUse : IO Unit :=
  runMockErr .branchInUse (fun api => api.diffNameStatus "/mock/repo" "HEAD" none #[])

/-- Mocked error-coverage test for `LeanSwe.Git.diffNameStatus` returning `.alreadyExists`. -/
def err_git_diffNameStatus_alreadyExists : IO Unit :=
  runMockErr .alreadyExists (fun api => api.diffNameStatus "/mock/repo" "HEAD" none #[])

/-- Mocked error-coverage test for `LeanSwe.Git.diffNameStatus` returning `.notFound`. -/
def err_git_diffNameStatus_notFound : IO Unit :=
  runMockErr .notFound (fun api => api.diffNameStatus "/mock/repo" "HEAD" none #[])

/-- Mocked error-coverage test for `LeanSwe.Git.diffNameStatus` returning `.conflict`. -/
def err_git_diffNameStatus_conflict : IO Unit :=
  runMockErr .conflict (fun api => api.diffNameStatus "/mock/repo" "HEAD" none #[])

/-- Mocked error-coverage test for `LeanSwe.Git.diffNameStatus` returning `.timeout`. -/
def err_git_diffNameStatus_timeout : IO Unit :=
  runMockErr .timeout (fun api => api.diffNameStatus "/mock/repo" "HEAD" none #[])

/-- Real error-coverage test for `LeanSwe.Git.diffNameStatus` returning `.commandFailed`. -/
def err_git_diffNameStatus_commandFailed : IO Unit :=
  runRealMissingDirErr (fun p => Git.diffNameStatus p "HEAD")

/-- Real error-coverage test for `LeanSwe.Git.diffNameStatus` returning `.parseError`. -/
def err_git_diffNameStatus_parseError : IO Unit :=
  withBadUtf8CommittedRepo fun repo c1 c2 => do assertErrKind (← Git.diffNameStatus repo c1.hex (some c2.hex)) .parseError "diffNameStatus parseError"

/-- Real error-coverage test for `LeanSwe.Git.listWorktrees` returning `.notARepo`. -/
def err_git_listWorktrees_notARepo : IO Unit :=
  runRealNonRepoErr Git.listWorktrees

/-- Mocked error-coverage test for `LeanSwe.Git.listWorktrees` returning `.invalidRef`. -/
def err_git_listWorktrees_invalidRef : IO Unit :=
  runMockErr .invalidRef (fun api => api.listWorktrees "/mock/repo")

/-- Real error-coverage test for `LeanSwe.Git.listWorktrees` returning `.invalidPath`. -/
def err_git_listWorktrees_invalidPath : IO Unit :=
  runRealErr .invalidPath "listWorktrees invalidPath" (Git.listWorktrees "")

/-- Real error-coverage test for `LeanSwe.Git.listWorktrees` returning `.invalidInput`. -/
def err_git_listWorktrees_invalidInput : IO Unit :=
  runRealErr .invalidInput "listWorktrees invalidInput" (Git.listWorktrees longInvalidPath)

/-- Mocked error-coverage test for `LeanSwe.Git.listWorktrees` returning `.dirtyWorktree`. -/
def err_git_listWorktrees_dirtyWorktree : IO Unit :=
  runMockErr .dirtyWorktree (fun api => api.listWorktrees "/mock/repo")

/-- Mocked error-coverage test for `LeanSwe.Git.listWorktrees` returning `.nothingToCommit`. -/
def err_git_listWorktrees_nothingToCommit : IO Unit :=
  runMockErr .nothingToCommit (fun api => api.listWorktrees "/mock/repo")

/-- Mocked error-coverage test for `LeanSwe.Git.listWorktrees` returning `.branchInUse`. -/
def err_git_listWorktrees_branchInUse : IO Unit :=
  runMockErr .branchInUse (fun api => api.listWorktrees "/mock/repo")

/-- Mocked error-coverage test for `LeanSwe.Git.listWorktrees` returning `.alreadyExists`. -/
def err_git_listWorktrees_alreadyExists : IO Unit :=
  runMockErr .alreadyExists (fun api => api.listWorktrees "/mock/repo")

/-- Mocked error-coverage test for `LeanSwe.Git.listWorktrees` returning `.notFound`. -/
def err_git_listWorktrees_notFound : IO Unit :=
  runMockErr .notFound (fun api => api.listWorktrees "/mock/repo")

/-- Mocked error-coverage test for `LeanSwe.Git.listWorktrees` returning `.conflict`. -/
def err_git_listWorktrees_conflict : IO Unit :=
  runMockErr .conflict (fun api => api.listWorktrees "/mock/repo")

/-- Mocked error-coverage test for `LeanSwe.Git.listWorktrees` returning `.timeout`. -/
def err_git_listWorktrees_timeout : IO Unit :=
  runMockErr .timeout (fun api => api.listWorktrees "/mock/repo")

/-- Real error-coverage test for `LeanSwe.Git.listWorktrees` returning `.commandFailed`. -/
def err_git_listWorktrees_commandFailed : IO Unit :=
  runRealMissingDirErr Git.listWorktrees

/-- Real error-coverage test for `LeanSwe.Git.listWorktrees` returning `.parseError`. -/
def err_git_listWorktrees_parseError : IO Unit :=
  withBadUtf8Repo fun link => do assertErrKind (← Git.listWorktrees link) .parseError "listWorktrees parseError"

/-- Real error-coverage test for `LeanSwe.Git.showFile?` returning `.notARepo`. -/
def err_git_showFile_notARepo : IO Unit :=
  runRealNonRepoErr (fun p => Git.showFile? p "HEAD" "f.txt")

/-- Real error-coverage test for `LeanSwe.Git.showFile?` returning `.invalidRef`. -/
def err_git_showFile_invalidRef : IO Unit :=
  runRealCommittedErr .invalidRef "showFile? invalidRef" (fun repo _ => Git.showFile? repo "no-such-ref" "f.txt")

/-- Real error-coverage test for `LeanSwe.Git.showFile?` returning `.invalidPath`. -/
def err_git_showFile_invalidPath : IO Unit :=
  runRealErr .invalidPath "showFile? invalidPath" (Git.showFile? "" "HEAD" "f.txt")

/-- Real error-coverage test for `LeanSwe.Git.showFile?` returning `.invalidInput`. -/
def err_git_showFile_invalidInput : IO Unit :=
  runRealErr .invalidInput "showFile? invalidInput" (Git.showFile? "/tmp" "HEAD:bad" "f.txt")

/-- Mocked error-coverage test for `LeanSwe.Git.showFile?` returning `.dirtyWorktree`. -/
def err_git_showFile_dirtyWorktree : IO Unit :=
  runMockErr .dirtyWorktree (fun api => api.showFile? "/mock/repo" "HEAD" "file.txt")

/-- Mocked error-coverage test for `LeanSwe.Git.showFile?` returning `.nothingToCommit`. -/
def err_git_showFile_nothingToCommit : IO Unit :=
  runMockErr .nothingToCommit (fun api => api.showFile? "/mock/repo" "HEAD" "file.txt")

/-- Mocked error-coverage test for `LeanSwe.Git.showFile?` returning `.branchInUse`. -/
def err_git_showFile_branchInUse : IO Unit :=
  runMockErr .branchInUse (fun api => api.showFile? "/mock/repo" "HEAD" "file.txt")

/-- Mocked error-coverage test for `LeanSwe.Git.showFile?` returning `.alreadyExists`. -/
def err_git_showFile_alreadyExists : IO Unit :=
  runMockErr .alreadyExists (fun api => api.showFile? "/mock/repo" "HEAD" "file.txt")

/-- Mocked error-coverage test for `LeanSwe.Git.showFile?` returning `.notFound`. -/
def err_git_showFile_notFound : IO Unit :=
  runMockErr .notFound (fun api => api.showFile? "/mock/repo" "HEAD" "file.txt")

/-- Mocked error-coverage test for `LeanSwe.Git.showFile?` returning `.conflict`. -/
def err_git_showFile_conflict : IO Unit :=
  runMockErr .conflict (fun api => api.showFile? "/mock/repo" "HEAD" "file.txt")

/-- Mocked error-coverage test for `LeanSwe.Git.showFile?` returning `.timeout`. -/
def err_git_showFile_timeout : IO Unit :=
  runMockErr .timeout (fun api => api.showFile? "/mock/repo" "HEAD" "file.txt")

/-- Real error-coverage test for `LeanSwe.Git.showFile?` returning `.commandFailed`. -/
def err_git_showFile_commandFailed : IO Unit :=
  runRealMissingDirErr (fun p => Git.showFile? p "HEAD" "f.txt")

/-- Mocked error-coverage test for `LeanSwe.Git.showFile?` returning `.parseError`. -/
def err_git_showFile_parseError : IO Unit :=
  runMockErr .parseError (fun api => api.showFile? "/mock/repo" "HEAD" "file.txt")

/-- Mocked error-coverage test for `LeanSwe.Git.init` returning `.notARepo`. -/
def err_git_init_notARepo : IO Unit :=
  runMockErr .notARepo (fun api => api.init "/mock/repo" false none)

/-- Real error-coverage test for `LeanSwe.Git.init` returning `.invalidRef`. -/
def err_git_init_invalidRef : IO Unit :=
  withTempDirIO fun root => do assertErrKind (← Git.init (root ++ "/repo") false (some badRef)) .invalidRef "init invalidRef"

/-- Real error-coverage test for `LeanSwe.Git.init` returning `.invalidPath`. -/
def err_git_init_invalidPath : IO Unit :=
  runRealErr .invalidPath "init invalidPath" (Git.init "")

/-- Real error-coverage test for `LeanSwe.Git.init` returning `.invalidInput`. -/
def err_git_init_invalidInput : IO Unit :=
  runRealErr .invalidInput "init invalidInput" (Git.init hugeInvalidPath)

/-- Mocked error-coverage test for `LeanSwe.Git.init` returning `.dirtyWorktree`. -/
def err_git_init_dirtyWorktree : IO Unit :=
  runMockErr .dirtyWorktree (fun api => api.init "/mock/repo" false none)

/-- Mocked error-coverage test for `LeanSwe.Git.init` returning `.nothingToCommit`. -/
def err_git_init_nothingToCommit : IO Unit :=
  runMockErr .nothingToCommit (fun api => api.init "/mock/repo" false none)

/-- Mocked error-coverage test for `LeanSwe.Git.init` returning `.branchInUse`. -/
def err_git_init_branchInUse : IO Unit :=
  runMockErr .branchInUse (fun api => api.init "/mock/repo" false none)

/-- Mocked error-coverage test for `LeanSwe.Git.init` returning `.alreadyExists`. -/
def err_git_init_alreadyExists : IO Unit :=
  runMockErr .alreadyExists (fun api => api.init "/mock/repo" false none)

/-- Mocked error-coverage test for `LeanSwe.Git.init` returning `.notFound`. -/
def err_git_init_notFound : IO Unit :=
  runMockErr .notFound (fun api => api.init "/mock/repo" false none)

/-- Mocked error-coverage test for `LeanSwe.Git.init` returning `.conflict`. -/
def err_git_init_conflict : IO Unit :=
  runMockErr .conflict (fun api => api.init "/mock/repo" false none)

/-- Mocked error-coverage test for `LeanSwe.Git.init` returning `.timeout`. -/
def err_git_init_timeout : IO Unit :=
  runMockErr .timeout (fun api => api.init "/mock/repo" false none)

/-- Real error-coverage test for `LeanSwe.Git.init` returning `.commandFailed`. -/
def err_git_init_commandFailed : IO Unit :=
  runRealInitOnFileErr

/-- Mocked error-coverage test for `LeanSwe.Git.clone` returning `.notARepo`. -/
def err_git_clone_notARepo : IO Unit :=
  runMockErr .notARepo (fun api => api.clone "/mock/src" "/mock/dst" {})

/-- Real error-coverage test for `LeanSwe.Git.clone` returning `.invalidRef`. -/
def err_git_clone_invalidRef : IO Unit :=
  withTempDirIO fun root => do let src := root ++ "/src"; let _ ← initCommittedRepo src; assertErrKind (← Git.clone src (root ++ "/dst") { branch? := some badRef.raw }) .invalidRef "clone invalidRef"

/-- Real error-coverage test for `LeanSwe.Git.clone` returning `.invalidInput`. -/
def err_git_clone_invalidInput : IO Unit :=
  runRealErr .invalidInput "clone invalidInput" (Git.clone "-evil" "/tmp/dst")

/-- Mocked error-coverage test for `LeanSwe.Git.clone` returning `.dirtyWorktree`. -/
def err_git_clone_dirtyWorktree : IO Unit :=
  runMockErr .dirtyWorktree (fun api => api.clone "/mock/src" "/mock/dst" {})

/-- Mocked error-coverage test for `LeanSwe.Git.clone` returning `.nothingToCommit`. -/
def err_git_clone_nothingToCommit : IO Unit :=
  runMockErr .nothingToCommit (fun api => api.clone "/mock/src" "/mock/dst" {})

/-- Mocked error-coverage test for `LeanSwe.Git.clone` returning `.branchInUse`. -/
def err_git_clone_branchInUse : IO Unit :=
  runMockErr .branchInUse (fun api => api.clone "/mock/src" "/mock/dst" {})

/-- Real error-coverage test for `LeanSwe.Git.clone` returning `.alreadyExists`. -/
def err_git_clone_alreadyExists : IO Unit :=
  runRealCloneAlreadyExistsErr

/-- Real error-coverage test for `LeanSwe.Git.clone` returning `.notFound`. -/
def err_git_clone_notFound : IO Unit :=
  runRealCloneNotFoundErr

/-- Mocked error-coverage test for `LeanSwe.Git.clone` returning `.conflict`. -/
def err_git_clone_conflict : IO Unit :=
  runMockErr .conflict (fun api => api.clone "/mock/src" "/mock/dst" {})

/-- Mocked error-coverage test for `LeanSwe.Git.clone` returning `.timeout`. -/
def err_git_clone_timeout : IO Unit :=
  runMockErr .timeout (fun api => api.clone "/mock/src" "/mock/dst" {})

/-- Real error-coverage test for `LeanSwe.Git.clone` returning `.commandFailed`. -/
def err_git_clone_commandFailed : IO Unit :=
  runRealCloneNonRepoErr

/-- Real error-coverage test for `LeanSwe.Git.add` returning `.notARepo`. -/
def err_git_add_notARepo : IO Unit :=
  runRealNonRepoErr (fun p => Git.add p #["f.txt"] false)

/-- Mocked error-coverage test for `LeanSwe.Git.add` returning `.invalidRef`. -/
def err_git_add_invalidRef : IO Unit :=
  runMockErr .invalidRef (fun api => api.add "/mock/repo" #["file.txt"] false)

/-- Real error-coverage test for `LeanSwe.Git.add` returning `.invalidPath`. -/
def err_git_add_invalidPath : IO Unit :=
  runRealErr .invalidPath "add invalidPath" (Git.add "" #["f.txt"] false)

/-- Real error-coverage test for `LeanSwe.Git.add` returning `.invalidInput`. -/
def err_git_add_invalidInput : IO Unit :=
  runRealErr .invalidInput "add invalidInput" (Git.add "/tmp" #[] false)

/-- Mocked error-coverage test for `LeanSwe.Git.add` returning `.dirtyWorktree`. -/
def err_git_add_dirtyWorktree : IO Unit :=
  runMockErr .dirtyWorktree (fun api => api.add "/mock/repo" #["file.txt"] false)

/-- Mocked error-coverage test for `LeanSwe.Git.add` returning `.nothingToCommit`. -/
def err_git_add_nothingToCommit : IO Unit :=
  runMockErr .nothingToCommit (fun api => api.add "/mock/repo" #["file.txt"] false)

/-- Mocked error-coverage test for `LeanSwe.Git.add` returning `.branchInUse`. -/
def err_git_add_branchInUse : IO Unit :=
  runMockErr .branchInUse (fun api => api.add "/mock/repo" #["file.txt"] false)

/-- Mocked error-coverage test for `LeanSwe.Git.add` returning `.alreadyExists`. -/
def err_git_add_alreadyExists : IO Unit :=
  runMockErr .alreadyExists (fun api => api.add "/mock/repo" #["file.txt"] false)

/-- Real error-coverage test for `LeanSwe.Git.add` returning `.notFound`. -/
def err_git_add_notFound : IO Unit :=
  runRealCommittedErr .notFound "add notFound" (fun repo _ => Git.add repo #["missing.txt"] false)

/-- Mocked error-coverage test for `LeanSwe.Git.add` returning `.conflict`. -/
def err_git_add_conflict : IO Unit :=
  runMockErr .conflict (fun api => api.add "/mock/repo" #["file.txt"] false)

/-- Mocked error-coverage test for `LeanSwe.Git.add` returning `.timeout`. -/
def err_git_add_timeout : IO Unit :=
  runMockErr .timeout (fun api => api.add "/mock/repo" #["file.txt"] false)

/-- Real error-coverage test for `LeanSwe.Git.add` returning `.commandFailed`. -/
def err_git_add_commandFailed : IO Unit :=
  runRealMissingDirErr (fun p => Git.add p #["f.txt"] false)

/-- Real error-coverage test for `LeanSwe.Git.commit` returning `.notARepo`. -/
def err_git_commit_notARepo : IO Unit :=
  runRealNonRepoErr (fun p => Git.commit p (testAuthorOpts "m"))

/-- Mocked error-coverage test for `LeanSwe.Git.commit` returning `.invalidRef`. -/
def err_git_commit_invalidRef : IO Unit :=
  runMockErr .invalidRef (fun api => api.commit "/mock/repo" { message := "msg" })

/-- Real error-coverage test for `LeanSwe.Git.commit` returning `.invalidPath`. -/
def err_git_commit_invalidPath : IO Unit :=
  runRealErr .invalidPath "commit invalidPath" (Git.commit "" { message := "m" })

/-- Real error-coverage test for `LeanSwe.Git.commit` returning `.invalidInput`. -/
def err_git_commit_invalidInput : IO Unit :=
  runRealErr .invalidInput "commit invalidInput" (Git.commit "/tmp" { message := "" })

/-- Mocked error-coverage test for `LeanSwe.Git.commit` returning `.dirtyWorktree`. -/
def err_git_commit_dirtyWorktree : IO Unit :=
  runMockErr .dirtyWorktree (fun api => api.commit "/mock/repo" { message := "msg" })

/-- Real error-coverage test for `LeanSwe.Git.commit` returning `.nothingToCommit`. -/
def err_git_commit_nothingToCommit : IO Unit :=
  runRealCommittedErr .nothingToCommit "commit nothingToCommit" (fun repo _ => Git.commit repo (testAuthorOpts "empty" false))

/-- Mocked error-coverage test for `LeanSwe.Git.commit` returning `.branchInUse`. -/
def err_git_commit_branchInUse : IO Unit :=
  runMockErr .branchInUse (fun api => api.commit "/mock/repo" { message := "msg" })

/-- Mocked error-coverage test for `LeanSwe.Git.commit` returning `.alreadyExists`. -/
def err_git_commit_alreadyExists : IO Unit :=
  runMockErr .alreadyExists (fun api => api.commit "/mock/repo" { message := "msg" })

/-- Mocked error-coverage test for `LeanSwe.Git.commit` returning `.notFound`. -/
def err_git_commit_notFound : IO Unit :=
  runMockErr .notFound (fun api => api.commit "/mock/repo" { message := "msg" })

/-- Real error-coverage test for `LeanSwe.Git.commit` returning `.conflict`. -/
def err_git_commit_conflict : IO Unit :=
  runRealCommitConflictErr

/-- Mocked error-coverage test for `LeanSwe.Git.commit` returning `.timeout`. -/
def err_git_commit_timeout : IO Unit :=
  runMockErr .timeout (fun api => api.commit "/mock/repo" { message := "msg" })

/-- Real error-coverage test for `LeanSwe.Git.commit` returning `.commandFailed`. -/
def err_git_commit_commandFailed : IO Unit :=
  runRealMissingDirErr (fun p => Git.commit p (testAuthorOpts "m"))

/-- Mocked error-coverage test for `LeanSwe.Git.commit` returning `.parseError`. -/
def err_git_commit_parseError : IO Unit :=
  runMockErr .parseError (fun api => api.commit "/mock/repo" { message := "msg" })

/-- Real error-coverage test for `LeanSwe.Git.createBranch` returning `.notARepo`. -/
def err_git_createBranch_notARepo : IO Unit :=
  runRealNonRepoErr (fun p => Git.createBranch p mainRef)

/-- Real error-coverage test for `LeanSwe.Git.createBranch` returning `.invalidRef`. -/
def err_git_createBranch_invalidRef : IO Unit :=
  runRealCommittedErr .invalidRef "createBranch invalidRef" (fun repo _ => Git.createBranch repo badRef)

/-- Real error-coverage test for `LeanSwe.Git.createBranch` returning `.invalidPath`. -/
def err_git_createBranch_invalidPath : IO Unit :=
  runRealErr .invalidPath "createBranch invalidPath" (Git.createBranch "" mainRef)

/-- Real error-coverage test for `LeanSwe.Git.createBranch` returning `.invalidInput`. -/
def err_git_createBranch_invalidInput : IO Unit :=
  runRealErr .invalidInput "createBranch invalidInput" (Git.createBranch "/tmp" mainRef (some "HEAD:bad"))

/-- Mocked error-coverage test for `LeanSwe.Git.createBranch` returning `.dirtyWorktree`. -/
def err_git_createBranch_dirtyWorktree : IO Unit :=
  runMockErr .dirtyWorktree (fun api => api.createBranch "/mock/repo" mainRef none false)


end LeanSwe.Git.RuntimeTests
