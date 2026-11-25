import Core.Assumptions
import LeanSwe.Git.RuntimeTests.Helpers
import LeanSwe.Git.RuntimeTests.Assumptions
import LeanSwe.Git.RuntimeTests.ErrTests1
import LeanSwe.Git.RuntimeTests.ErrTests2
import LeanSwe.Git.RuntimeTests.ErrTests3
import LeanSwe.Git.RuntimeTests.Smoke
import LeanSwe.Git.RuntimeTests.MutateExtra

namespace LeanSwe.Git.RuntimeTests

open LeanSwe.Git
open LeanSwe.Git.Model

/-- Registered external-world assumption probes for `LeanSwe.Git`. -/
def registeredAssumptions : Array Core.RegisteredAssumption :=
  #[ { specName := "LeanSwe.Git.assume_git_defaultRawOps_stripsPoisonedGitEnvAndHonorsBareConfig", run := assume_git_defaultRawOps_stripsPoisonedGitEnvAndHonorsBareConfig }
   , { specName := "LeanSwe.Git.assume_git_status_porcelainV1Z_emitsUnquotedAndDestFirstRename", run := assume_git_status_porcelainV1Z_emitsUnquotedAndDestFirstRename }
   , { specName := "LeanSwe.Git.assume_git_diffNameStatus_porcelainZ_emitsSourceFirstRename", run := assume_git_diffNameStatus_porcelainZ_emitsSourceFirstRename }
   , { specName := "LeanSwe.Git.assume_git_listWorktrees_porcelainZ_emitsBareUnbornAndLinkedStanzas", run := assume_git_listWorktrees_porcelainZ_emitsBareUnbornAndLinkedStanzas }
   , { specName := "LeanSwe.Git.assume_git_mergeBase_andIsAncestor_matchDagSemantics", run := assume_git_mergeBase_andIsAncestor_matchDagSemantics }
   , { specName := "LeanSwe.Git.assume_git_headState_andShowFile_unbornDetachedAndTreeVsBlob", run := assume_git_headState_andShowFile_unbornDetachedAndTreeVsBlob }
   , { specName := "LeanSwe.Git.assume_git_clone_andFetch_roundTripLocalRefsAndPrune", run := assume_git_clone_andFetch_roundTripLocalRefsAndPrune } ]


set_option maxRecDepth 2048 in
/-- Registered error-coverage tests for `LeanSwe.Git`. -/
def registeredErrorTests : Array Core.RegisteredErrorTest :=
  List.toArray (
    { testName := "LeanSwe.Git.RuntimeTests.err_git_isRepo_invalidRef", mode := .mocked, run := err_git_isRepo_invalidRef }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_isRepo_invalidPath", mode := .real, run := err_git_isRepo_invalidPath }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_isRepo_invalidInput", mode := .real, run := err_git_isRepo_invalidInput }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_isRepo_dirtyWorktree", mode := .mocked, run := err_git_isRepo_dirtyWorktree }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_isRepo_nothingToCommit", mode := .mocked, run := err_git_isRepo_nothingToCommit }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_isRepo_branchInUse", mode := .mocked, run := err_git_isRepo_branchInUse }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_isRepo_alreadyExists", mode := .mocked, run := err_git_isRepo_alreadyExists }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_isRepo_notFound", mode := .mocked, run := err_git_isRepo_notFound }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_isRepo_conflict", mode := .mocked, run := err_git_isRepo_conflict }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_isRepo_timeout", mode := .mocked, run := err_git_isRepo_timeout }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_isRepo_commandFailed", mode := .real, run := err_git_isRepo_commandFailed }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_repoRoot_notARepo", mode := .real, run := err_git_repoRoot_notARepo }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_repoRoot_invalidRef", mode := .mocked, run := err_git_repoRoot_invalidRef }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_repoRoot_invalidPath", mode := .real, run := err_git_repoRoot_invalidPath }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_repoRoot_invalidInput", mode := .real, run := err_git_repoRoot_invalidInput }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_repoRoot_dirtyWorktree", mode := .mocked, run := err_git_repoRoot_dirtyWorktree }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_repoRoot_nothingToCommit", mode := .mocked, run := err_git_repoRoot_nothingToCommit }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_repoRoot_branchInUse", mode := .mocked, run := err_git_repoRoot_branchInUse }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_repoRoot_alreadyExists", mode := .mocked, run := err_git_repoRoot_alreadyExists }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_repoRoot_notFound", mode := .mocked, run := err_git_repoRoot_notFound }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_repoRoot_conflict", mode := .mocked, run := err_git_repoRoot_conflict }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_repoRoot_timeout", mode := .mocked, run := err_git_repoRoot_timeout }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_repoRoot_commandFailed", mode := .real, run := err_git_repoRoot_commandFailed }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_repoRoot_parseError", mode := .real, run := err_git_repoRoot_parseError }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_commonDir_notARepo", mode := .real, run := err_git_commonDir_notARepo }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_commonDir_invalidRef", mode := .mocked, run := err_git_commonDir_invalidRef }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_commonDir_invalidPath", mode := .real, run := err_git_commonDir_invalidPath }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_commonDir_invalidInput", mode := .real, run := err_git_commonDir_invalidInput }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_commonDir_dirtyWorktree", mode := .mocked, run := err_git_commonDir_dirtyWorktree }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_commonDir_nothingToCommit", mode := .mocked, run := err_git_commonDir_nothingToCommit }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_commonDir_branchInUse", mode := .mocked, run := err_git_commonDir_branchInUse }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_commonDir_alreadyExists", mode := .mocked, run := err_git_commonDir_alreadyExists }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_commonDir_notFound", mode := .mocked, run := err_git_commonDir_notFound }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_commonDir_conflict", mode := .mocked, run := err_git_commonDir_conflict }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_commonDir_timeout", mode := .mocked, run := err_git_commonDir_timeout }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_commonDir_commandFailed", mode := .real, run := err_git_commonDir_commandFailed }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_commonDir_parseError", mode := .real, run := err_git_commonDir_parseError }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_headCommit_notARepo", mode := .real, run := err_git_headCommit_notARepo }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_headCommit_invalidRef", mode := .mocked, run := err_git_headCommit_invalidRef }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_headCommit_invalidPath", mode := .real, run := err_git_headCommit_invalidPath }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_headCommit_invalidInput", mode := .real, run := err_git_headCommit_invalidInput }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_headCommit_dirtyWorktree", mode := .mocked, run := err_git_headCommit_dirtyWorktree }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_headCommit_nothingToCommit", mode := .mocked, run := err_git_headCommit_nothingToCommit }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_headCommit_branchInUse", mode := .mocked, run := err_git_headCommit_branchInUse }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_headCommit_alreadyExists", mode := .mocked, run := err_git_headCommit_alreadyExists }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_headCommit_notFound", mode := .mocked, run := err_git_headCommit_notFound }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_headCommit_conflict", mode := .mocked, run := err_git_headCommit_conflict }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_headCommit_timeout", mode := .mocked, run := err_git_headCommit_timeout }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_headCommit_commandFailed", mode := .real, run := err_git_headCommit_commandFailed }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_headCommit_parseError", mode := .mocked, run := err_git_headCommit_parseError }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_headBranch_notARepo", mode := .real, run := err_git_headBranch_notARepo }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_headBranch_invalidRef", mode := .mocked, run := err_git_headBranch_invalidRef }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_headBranch_invalidPath", mode := .real, run := err_git_headBranch_invalidPath }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_headBranch_invalidInput", mode := .real, run := err_git_headBranch_invalidInput }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_headBranch_dirtyWorktree", mode := .mocked, run := err_git_headBranch_dirtyWorktree }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_headBranch_nothingToCommit", mode := .mocked, run := err_git_headBranch_nothingToCommit }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_headBranch_branchInUse", mode := .mocked, run := err_git_headBranch_branchInUse }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_headBranch_alreadyExists", mode := .mocked, run := err_git_headBranch_alreadyExists }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_headBranch_notFound", mode := .mocked, run := err_git_headBranch_notFound }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_headBranch_conflict", mode := .mocked, run := err_git_headBranch_conflict }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_headBranch_timeout", mode := .mocked, run := err_git_headBranch_timeout }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_headBranch_commandFailed", mode := .real, run := err_git_headBranch_commandFailed }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_headBranch_parseError", mode := .mocked, run := err_git_headBranch_parseError }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_headState_notARepo", mode := .real, run := err_git_headState_notARepo }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_headState_invalidRef", mode := .mocked, run := err_git_headState_invalidRef }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_headState_invalidPath", mode := .real, run := err_git_headState_invalidPath }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_headState_invalidInput", mode := .real, run := err_git_headState_invalidInput }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_headState_dirtyWorktree", mode := .mocked, run := err_git_headState_dirtyWorktree }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_headState_nothingToCommit", mode := .mocked, run := err_git_headState_nothingToCommit }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_headState_branchInUse", mode := .mocked, run := err_git_headState_branchInUse }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_headState_alreadyExists", mode := .mocked, run := err_git_headState_alreadyExists }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_headState_notFound", mode := .mocked, run := err_git_headState_notFound }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_headState_conflict", mode := .mocked, run := err_git_headState_conflict }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_headState_timeout", mode := .mocked, run := err_git_headState_timeout }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_headState_commandFailed", mode := .real, run := err_git_headState_commandFailed }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_headState_parseError", mode := .mocked, run := err_git_headState_parseError }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_revParseCommit_notARepo", mode := .real, run := err_git_revParseCommit_notARepo }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_revParseCommit_invalidRef", mode := .real, run := err_git_revParseCommit_invalidRef }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_revParseCommit_invalidPath", mode := .real, run := err_git_revParseCommit_invalidPath }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_revParseCommit_invalidInput", mode := .real, run := err_git_revParseCommit_invalidInput }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_revParseCommit_dirtyWorktree", mode := .mocked, run := err_git_revParseCommit_dirtyWorktree }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_revParseCommit_nothingToCommit", mode := .mocked, run := err_git_revParseCommit_nothingToCommit }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_revParseCommit_branchInUse", mode := .mocked, run := err_git_revParseCommit_branchInUse }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_revParseCommit_alreadyExists", mode := .mocked, run := err_git_revParseCommit_alreadyExists }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_revParseCommit_notFound", mode := .mocked, run := err_git_revParseCommit_notFound }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_revParseCommit_conflict", mode := .mocked, run := err_git_revParseCommit_conflict }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_revParseCommit_timeout", mode := .mocked, run := err_git_revParseCommit_timeout }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_revParseCommit_commandFailed", mode := .real, run := err_git_revParseCommit_commandFailed }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_revParseCommit_parseError", mode := .mocked, run := err_git_revParseCommit_parseError }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_isAncestor_notARepo", mode := .real, run := err_git_isAncestor_notARepo }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_isAncestor_invalidRef", mode := .real, run := err_git_isAncestor_invalidRef }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_isAncestor_invalidPath", mode := .real, run := err_git_isAncestor_invalidPath }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_isAncestor_invalidInput", mode := .real, run := err_git_isAncestor_invalidInput }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_isAncestor_dirtyWorktree", mode := .mocked, run := err_git_isAncestor_dirtyWorktree }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_isAncestor_nothingToCommit", mode := .mocked, run := err_git_isAncestor_nothingToCommit }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_isAncestor_branchInUse", mode := .mocked, run := err_git_isAncestor_branchInUse }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_isAncestor_alreadyExists", mode := .mocked, run := err_git_isAncestor_alreadyExists }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_isAncestor_notFound", mode := .mocked, run := err_git_isAncestor_notFound }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_isAncestor_conflict", mode := .mocked, run := err_git_isAncestor_conflict }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_isAncestor_timeout", mode := .mocked, run := err_git_isAncestor_timeout }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_isAncestor_commandFailed", mode := .real, run := err_git_isAncestor_commandFailed }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_mergeBase_notARepo", mode := .real, run := err_git_mergeBase_notARepo }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_mergeBase_invalidRef", mode := .real, run := err_git_mergeBase_invalidRef }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_mergeBase_invalidPath", mode := .real, run := err_git_mergeBase_invalidPath }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_mergeBase_invalidInput", mode := .real, run := err_git_mergeBase_invalidInput }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_mergeBase_dirtyWorktree", mode := .mocked, run := err_git_mergeBase_dirtyWorktree }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_mergeBase_nothingToCommit", mode := .mocked, run := err_git_mergeBase_nothingToCommit }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_mergeBase_branchInUse", mode := .mocked, run := err_git_mergeBase_branchInUse }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_mergeBase_alreadyExists", mode := .mocked, run := err_git_mergeBase_alreadyExists }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_mergeBase_notFound", mode := .mocked, run := err_git_mergeBase_notFound }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_mergeBase_conflict", mode := .mocked, run := err_git_mergeBase_conflict }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_mergeBase_timeout", mode := .mocked, run := err_git_mergeBase_timeout }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_mergeBase_commandFailed", mode := .real, run := err_git_mergeBase_commandFailed }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_mergeBase_parseError", mode := .mocked, run := err_git_mergeBase_parseError }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_status_notARepo", mode := .real, run := err_git_status_notARepo }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_status_invalidRef", mode := .mocked, run := err_git_status_invalidRef }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_status_invalidPath", mode := .real, run := err_git_status_invalidPath }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_status_invalidInput", mode := .real, run := err_git_status_invalidInput }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_status_dirtyWorktree", mode := .mocked, run := err_git_status_dirtyWorktree }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_status_nothingToCommit", mode := .mocked, run := err_git_status_nothingToCommit }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_status_branchInUse", mode := .mocked, run := err_git_status_branchInUse }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_status_alreadyExists", mode := .mocked, run := err_git_status_alreadyExists }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_status_notFound", mode := .mocked, run := err_git_status_notFound }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_status_conflict", mode := .mocked, run := err_git_status_conflict }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_status_timeout", mode := .mocked, run := err_git_status_timeout }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_status_commandFailed", mode := .real, run := err_git_status_commandFailed }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_status_parseError", mode := .real, run := err_git_status_parseError }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_diffNameStatus_notARepo", mode := .real, run := err_git_diffNameStatus_notARepo }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_diffNameStatus_invalidRef", mode := .real, run := err_git_diffNameStatus_invalidRef }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_diffNameStatus_invalidPath", mode := .real, run := err_git_diffNameStatus_invalidPath }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_diffNameStatus_invalidInput", mode := .real, run := err_git_diffNameStatus_invalidInput }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_diffNameStatus_dirtyWorktree", mode := .mocked, run := err_git_diffNameStatus_dirtyWorktree }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_diffNameStatus_nothingToCommit", mode := .mocked, run := err_git_diffNameStatus_nothingToCommit }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_diffNameStatus_branchInUse", mode := .mocked, run := err_git_diffNameStatus_branchInUse }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_diffNameStatus_alreadyExists", mode := .mocked, run := err_git_diffNameStatus_alreadyExists }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_diffNameStatus_notFound", mode := .mocked, run := err_git_diffNameStatus_notFound }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_diffNameStatus_conflict", mode := .mocked, run := err_git_diffNameStatus_conflict }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_diffNameStatus_timeout", mode := .mocked, run := err_git_diffNameStatus_timeout }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_diffNameStatus_commandFailed", mode := .real, run := err_git_diffNameStatus_commandFailed }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_diffNameStatus_parseError", mode := .real, run := err_git_diffNameStatus_parseError }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_listWorktrees_notARepo", mode := .real, run := err_git_listWorktrees_notARepo }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_listWorktrees_invalidRef", mode := .mocked, run := err_git_listWorktrees_invalidRef }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_listWorktrees_invalidPath", mode := .real, run := err_git_listWorktrees_invalidPath }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_listWorktrees_invalidInput", mode := .real, run := err_git_listWorktrees_invalidInput }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_listWorktrees_dirtyWorktree", mode := .mocked, run := err_git_listWorktrees_dirtyWorktree }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_listWorktrees_nothingToCommit", mode := .mocked, run := err_git_listWorktrees_nothingToCommit }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_listWorktrees_branchInUse", mode := .mocked, run := err_git_listWorktrees_branchInUse }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_listWorktrees_alreadyExists", mode := .mocked, run := err_git_listWorktrees_alreadyExists }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_listWorktrees_notFound", mode := .mocked, run := err_git_listWorktrees_notFound }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_listWorktrees_conflict", mode := .mocked, run := err_git_listWorktrees_conflict }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_listWorktrees_timeout", mode := .mocked, run := err_git_listWorktrees_timeout }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_listWorktrees_commandFailed", mode := .real, run := err_git_listWorktrees_commandFailed }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_listWorktrees_parseError", mode := .real, run := err_git_listWorktrees_parseError }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_showFile_notARepo", mode := .real, run := err_git_showFile_notARepo }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_showFile_invalidRef", mode := .real, run := err_git_showFile_invalidRef }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_showFile_invalidPath", mode := .real, run := err_git_showFile_invalidPath }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_showFile_invalidInput", mode := .real, run := err_git_showFile_invalidInput }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_showFile_dirtyWorktree", mode := .mocked, run := err_git_showFile_dirtyWorktree }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_showFile_nothingToCommit", mode := .mocked, run := err_git_showFile_nothingToCommit }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_showFile_branchInUse", mode := .mocked, run := err_git_showFile_branchInUse }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_showFile_alreadyExists", mode := .mocked, run := err_git_showFile_alreadyExists }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_showFile_notFound", mode := .mocked, run := err_git_showFile_notFound }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_showFile_conflict", mode := .mocked, run := err_git_showFile_conflict }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_showFile_timeout", mode := .mocked, run := err_git_showFile_timeout }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_showFile_commandFailed", mode := .real, run := err_git_showFile_commandFailed }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_showFile_parseError", mode := .mocked, run := err_git_showFile_parseError }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_init_notARepo", mode := .mocked, run := err_git_init_notARepo }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_init_invalidRef", mode := .real, run := err_git_init_invalidRef }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_init_invalidPath", mode := .real, run := err_git_init_invalidPath }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_init_invalidInput", mode := .real, run := err_git_init_invalidInput }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_init_dirtyWorktree", mode := .mocked, run := err_git_init_dirtyWorktree }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_init_nothingToCommit", mode := .mocked, run := err_git_init_nothingToCommit }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_init_branchInUse", mode := .mocked, run := err_git_init_branchInUse }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_init_alreadyExists", mode := .mocked, run := err_git_init_alreadyExists }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_init_notFound", mode := .mocked, run := err_git_init_notFound }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_init_conflict", mode := .mocked, run := err_git_init_conflict }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_init_timeout", mode := .mocked, run := err_git_init_timeout }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_init_commandFailed", mode := .real, run := err_git_init_commandFailed }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_clone_notARepo", mode := .mocked, run := err_git_clone_notARepo }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_clone_invalidRef", mode := .real, run := err_git_clone_invalidRef }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_clone_invalidInput", mode := .real, run := err_git_clone_invalidInput }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_clone_dirtyWorktree", mode := .mocked, run := err_git_clone_dirtyWorktree }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_clone_nothingToCommit", mode := .mocked, run := err_git_clone_nothingToCommit }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_clone_branchInUse", mode := .mocked, run := err_git_clone_branchInUse }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_clone_alreadyExists", mode := .real, run := err_git_clone_alreadyExists }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_clone_notFound", mode := .real, run := err_git_clone_notFound }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_clone_conflict", mode := .mocked, run := err_git_clone_conflict }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_clone_timeout", mode := .mocked, run := err_git_clone_timeout }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_clone_commandFailed", mode := .real, run := err_git_clone_commandFailed }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_add_notARepo", mode := .real, run := err_git_add_notARepo }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_add_invalidRef", mode := .mocked, run := err_git_add_invalidRef }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_add_invalidPath", mode := .real, run := err_git_add_invalidPath }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_add_invalidInput", mode := .real, run := err_git_add_invalidInput }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_add_dirtyWorktree", mode := .mocked, run := err_git_add_dirtyWorktree }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_add_nothingToCommit", mode := .mocked, run := err_git_add_nothingToCommit }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_add_branchInUse", mode := .mocked, run := err_git_add_branchInUse }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_add_alreadyExists", mode := .mocked, run := err_git_add_alreadyExists }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_add_notFound", mode := .real, run := err_git_add_notFound }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_add_conflict", mode := .mocked, run := err_git_add_conflict }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_add_timeout", mode := .mocked, run := err_git_add_timeout }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_add_commandFailed", mode := .real, run := err_git_add_commandFailed }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_commit_notARepo", mode := .real, run := err_git_commit_notARepo }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_commit_invalidRef", mode := .mocked, run := err_git_commit_invalidRef }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_commit_invalidPath", mode := .real, run := err_git_commit_invalidPath }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_commit_invalidInput", mode := .real, run := err_git_commit_invalidInput }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_commit_dirtyWorktree", mode := .mocked, run := err_git_commit_dirtyWorktree }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_commit_nothingToCommit", mode := .real, run := err_git_commit_nothingToCommit }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_commit_branchInUse", mode := .mocked, run := err_git_commit_branchInUse }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_commit_alreadyExists", mode := .mocked, run := err_git_commit_alreadyExists }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_commit_notFound", mode := .mocked, run := err_git_commit_notFound }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_commit_conflict", mode := .real, run := err_git_commit_conflict }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_commit_timeout", mode := .mocked, run := err_git_commit_timeout }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_commit_commandFailed", mode := .real, run := err_git_commit_commandFailed }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_commit_parseError", mode := .mocked, run := err_git_commit_parseError }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_createBranch_notARepo", mode := .real, run := err_git_createBranch_notARepo }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_createBranch_invalidRef", mode := .real, run := err_git_createBranch_invalidRef }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_createBranch_invalidPath", mode := .real, run := err_git_createBranch_invalidPath }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_createBranch_invalidInput", mode := .real, run := err_git_createBranch_invalidInput }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_createBranch_dirtyWorktree", mode := .mocked, run := err_git_createBranch_dirtyWorktree }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_createBranch_nothingToCommit", mode := .mocked, run := err_git_createBranch_nothingToCommit }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_createBranch_branchInUse", mode := .mocked, run := err_git_createBranch_branchInUse }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_createBranch_alreadyExists", mode := .real, run := err_git_createBranch_alreadyExists }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_createBranch_notFound", mode := .mocked, run := err_git_createBranch_notFound }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_createBranch_conflict", mode := .mocked, run := err_git_createBranch_conflict }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_createBranch_timeout", mode := .mocked, run := err_git_createBranch_timeout }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_createBranch_commandFailed", mode := .real, run := err_git_createBranch_commandFailed }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_deleteBranch_notARepo", mode := .real, run := err_git_deleteBranch_notARepo }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_deleteBranch_invalidRef", mode := .real, run := err_git_deleteBranch_invalidRef }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_deleteBranch_invalidPath", mode := .real, run := err_git_deleteBranch_invalidPath }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_deleteBranch_invalidInput", mode := .real, run := err_git_deleteBranch_invalidInput }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_deleteBranch_dirtyWorktree", mode := .mocked, run := err_git_deleteBranch_dirtyWorktree }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_deleteBranch_nothingToCommit", mode := .mocked, run := err_git_deleteBranch_nothingToCommit }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_deleteBranch_branchInUse", mode := .real, run := err_git_deleteBranch_branchInUse }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_deleteBranch_alreadyExists", mode := .mocked, run := err_git_deleteBranch_alreadyExists }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_deleteBranch_notFound", mode := .real, run := err_git_deleteBranch_notFound }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_deleteBranch_conflict", mode := .mocked, run := err_git_deleteBranch_conflict }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_deleteBranch_timeout", mode := .mocked, run := err_git_deleteBranch_timeout }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_deleteBranch_commandFailed", mode := .real, run := err_git_deleteBranch_commandFailed }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_checkout_notARepo", mode := .real, run := err_git_checkout_notARepo }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_checkout_invalidRef", mode := .real, run := err_git_checkout_invalidRef }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_checkout_invalidPath", mode := .real, run := err_git_checkout_invalidPath }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_checkout_invalidInput", mode := .real, run := err_git_checkout_invalidInput }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_checkout_dirtyWorktree", mode := .real, run := err_git_checkout_dirtyWorktree }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_checkout_nothingToCommit", mode := .mocked, run := err_git_checkout_nothingToCommit }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_checkout_branchInUse", mode := .real, run := err_git_checkout_branchInUse }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_checkout_alreadyExists", mode := .mocked, run := err_git_checkout_alreadyExists }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_checkout_notFound", mode := .mocked, run := err_git_checkout_notFound }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_checkout_conflict", mode := .real, run := err_git_checkout_conflict }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_checkout_timeout", mode := .mocked, run := err_git_checkout_timeout }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_checkout_commandFailed", mode := .real, run := err_git_checkout_commandFailed }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_switch_notARepo", mode := .real, run := err_git_switch_notARepo }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_switch_invalidRef", mode := .real, run := err_git_switch_invalidRef }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_switch_invalidPath", mode := .real, run := err_git_switch_invalidPath }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_switch_invalidInput", mode := .real, run := err_git_switch_invalidInput }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_switch_dirtyWorktree", mode := .real, run := err_git_switch_dirtyWorktree }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_switch_nothingToCommit", mode := .mocked, run := err_git_switch_nothingToCommit }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_switch_branchInUse", mode := .real, run := err_git_switch_branchInUse }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_switch_alreadyExists", mode := .real, run := err_git_switch_alreadyExists }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_switch_notFound", mode := .mocked, run := err_git_switch_notFound }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_switch_conflict", mode := .real, run := err_git_switch_conflict }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_switch_timeout", mode := .mocked, run := err_git_switch_timeout }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_switch_commandFailed", mode := .real, run := err_git_switch_commandFailed }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_reset_notARepo", mode := .real, run := err_git_reset_notARepo }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_reset_invalidRef", mode := .real, run := err_git_reset_invalidRef }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_reset_invalidPath", mode := .real, run := err_git_reset_invalidPath }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_reset_invalidInput", mode := .real, run := err_git_reset_invalidInput }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_reset_dirtyWorktree", mode := .mocked, run := err_git_reset_dirtyWorktree }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_reset_nothingToCommit", mode := .mocked, run := err_git_reset_nothingToCommit }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_reset_branchInUse", mode := .mocked, run := err_git_reset_branchInUse }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_reset_alreadyExists", mode := .mocked, run := err_git_reset_alreadyExists }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_reset_notFound", mode := .mocked, run := err_git_reset_notFound }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_reset_conflict", mode := .mocked, run := err_git_reset_conflict }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_reset_timeout", mode := .mocked, run := err_git_reset_timeout }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_reset_commandFailed", mode := .real, run := err_git_reset_commandFailed }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_fetch_notARepo", mode := .real, run := err_git_fetch_notARepo }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_fetch_invalidRef", mode := .mocked, run := err_git_fetch_invalidRef }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_fetch_invalidPath", mode := .real, run := err_git_fetch_invalidPath }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_fetch_invalidInput", mode := .real, run := err_git_fetch_invalidInput }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_fetch_dirtyWorktree", mode := .mocked, run := err_git_fetch_dirtyWorktree }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_fetch_nothingToCommit", mode := .mocked, run := err_git_fetch_nothingToCommit }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_fetch_branchInUse", mode := .mocked, run := err_git_fetch_branchInUse }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_fetch_alreadyExists", mode := .mocked, run := err_git_fetch_alreadyExists }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_fetch_notFound", mode := .mocked, run := err_git_fetch_notFound }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_fetch_conflict", mode := .mocked, run := err_git_fetch_conflict }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_fetch_timeout", mode := .mocked, run := err_git_fetch_timeout }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_fetch_commandFailed", mode := .real, run := err_git_fetch_commandFailed }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_worktreeAdd_notARepo", mode := .real, run := err_git_worktreeAdd_notARepo }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_worktreeAdd_invalidRef", mode := .real, run := err_git_worktreeAdd_invalidRef }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_worktreeAdd_invalidPath", mode := .real, run := err_git_worktreeAdd_invalidPath }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_worktreeAdd_invalidInput", mode := .real, run := err_git_worktreeAdd_invalidInput }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_worktreeAdd_dirtyWorktree", mode := .mocked, run := err_git_worktreeAdd_dirtyWorktree }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_worktreeAdd_nothingToCommit", mode := .mocked, run := err_git_worktreeAdd_nothingToCommit }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_worktreeAdd_branchInUse", mode := .real, run := err_git_worktreeAdd_branchInUse }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_worktreeAdd_alreadyExists", mode := .real, run := err_git_worktreeAdd_alreadyExists }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_worktreeAdd_notFound", mode := .mocked, run := err_git_worktreeAdd_notFound }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_worktreeAdd_conflict", mode := .mocked, run := err_git_worktreeAdd_conflict }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_worktreeAdd_timeout", mode := .mocked, run := err_git_worktreeAdd_timeout }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_worktreeAdd_commandFailed", mode := .real, run := err_git_worktreeAdd_commandFailed }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_worktreeRemove_notARepo", mode := .real, run := err_git_worktreeRemove_notARepo }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_worktreeRemove_invalidRef", mode := .mocked, run := err_git_worktreeRemove_invalidRef }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_worktreeRemove_invalidPath", mode := .real, run := err_git_worktreeRemove_invalidPath }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_worktreeRemove_invalidInput", mode := .real, run := err_git_worktreeRemove_invalidInput }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_worktreeRemove_dirtyWorktree", mode := .real, run := err_git_worktreeRemove_dirtyWorktree }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_worktreeRemove_nothingToCommit", mode := .mocked, run := err_git_worktreeRemove_nothingToCommit }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_worktreeRemove_branchInUse", mode := .mocked, run := err_git_worktreeRemove_branchInUse }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_worktreeRemove_alreadyExists", mode := .mocked, run := err_git_worktreeRemove_alreadyExists }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_worktreeRemove_notFound", mode := .mocked, run := err_git_worktreeRemove_notFound }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_worktreeRemove_conflict", mode := .mocked, run := err_git_worktreeRemove_conflict }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_worktreeRemove_timeout", mode := .mocked, run := err_git_worktreeRemove_timeout }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_worktreeRemove_commandFailed", mode := .real, run := err_git_worktreeRemove_commandFailed }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_withWorktree_notARepo", mode := .real, run := err_git_withWorktree_notARepo }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_withWorktree_invalidRef", mode := .real, run := err_git_withWorktree_invalidRef }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_withWorktree_invalidPath", mode := .real, run := err_git_withWorktree_invalidPath }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_withWorktree_invalidInput", mode := .real, run := err_git_withWorktree_invalidInput }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_withWorktree_dirtyWorktree", mode := .real, run := err_git_withWorktree_dirtyWorktree }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_withWorktree_nothingToCommit", mode := .real, run := err_git_withWorktree_nothingToCommit }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_withWorktree_branchInUse", mode := .real, run := err_git_withWorktree_branchInUse }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_withWorktree_alreadyExists", mode := .real, run := err_git_withWorktree_alreadyExists }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_withWorktree_notFound", mode := .real, run := err_git_withWorktree_notFound }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_withWorktree_conflict", mode := .real, run := err_git_withWorktree_conflict }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_withWorktree_timeout", mode := .mocked, run := err_git_withWorktree_timeout }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_withWorktree_commandFailed", mode := .real, run := err_git_withWorktree_commandFailed }
    :: { testName := "LeanSwe.Git.RuntimeTests.err_git_withWorktree_parseError", mode := .real, run := err_git_withWorktree_parseError }
    :: [])


/-- Execute end-to-end real `git` repository runtime verification tests for `LeanSwe.Git`. -/
def runAll : IO Unit := do
  runIntegrationSmoke
  runExtendedParityAndGuardSmoke
  runLiteralPathspecAndSpoofSmoke
  Core.runRegisteredAssumptions registeredAssumptions
  Core.runRegisteredErrorTests registeredErrorTests
  IO.println "PASS: LeanSwe.Git runtime tests"


end LeanSwe.Git.RuntimeTests
