import LeanSwe.Git.Types
import LeanSwe.Git.Impl
import LeanSwe.Git.Interface
import LeanSwe.Git.SpecTests

set_option Elab.async false
set_option maxRecDepth 4096

namespace LeanSwe.Git.Proofs

open Core
open Core.NondetTest
open LeanSwe.Git
open LeanSwe.Git.Model

/-- Shared SHA-1 constant for secondary revision and 40-hex worktree guard proofs. -/
def secSha1Const : String := String.ofList (List.replicate 40 '1')

/-- Shared 40-hex local branch constant for secondary revision and worktree guard proofs. -/
def secBr40Const : String := String.ofList (List.replicate 40 'f')

/-- Mock CLI state for `test_git_raw_mkApi_secondaryShortShaAnd40HexWorktreeGuards`. -/
def mkSecGuardState (usedInWt symFail : Bool := false) : GitCliMockState :=
  { handler := fun req _ =>
      if req.args == #["rev-parse", "-q", "--verify", secBr40Const ++ "^{commit}"] then
        .ok { exitCode := 1, stdout := ByteArray.empty, stderr := ByteArray.empty }
      else if req.args == #["show-ref", "--verify", "--quiet", "refs/heads/" ++ secBr40Const] then
        .ok { exitCode := 0, stdout := ByteArray.empty, stderr := ByteArray.empty }
      else if req.args == #["worktree", "list", "--porcelain"] then
        let usedBr := if usedInWt then secBr40Const else "main"
        .ok { exitCode := 0, stdout := ("worktree /repo\nbranch refs/heads/" ++ usedBr ++ "\n").toUTF8, stderr := ByteArray.empty }
      else if symFail && req.args == #["symbolic-ref", "HEAD", "refs/heads/" ++ secBr40Const] then
        .ok { exitCode := 128, stdout := ByteArray.empty, stderr := "fatal: cannot update HEAD".toUTF8 }
      else if req.args.toList.contains "--verify" && !req.args.toList.contains "show-ref" then
        .ok { exitCode := 0, stdout := (secSha1Const ++ "\n").toUTF8, stderr := ByteArray.empty }
      else
        .ok { exitCode := 0, stdout := ByteArray.empty, stderr := ByteArray.empty } }

/-- `diffNameStatus` delegates short-SHA `revB?` directly to `git`. -/
theorem secGuard_dfRevBShort :
    let (res, st) := (((Impl.mkApiM mockRawOps).diffNameStatus "/repo" "HEAD" (some "1111111") #[]).run (mkSecGuardState false false))
    res = .ok #[] ∧ st.recordedRequests.getLast? =
      some { cwd := some "/repo", args := #["diff", "--name-status", "--find-renames=100%", "-z", "HEAD", "1111111", "--"] } := by
  constructor <;> cbv

/-- `showFile?` delegates short-SHA `rev` directly to `git`. -/
theorem secGuard_sfShort :
    let (res, st) := (((Impl.mkApiM mockRawOps).showFile? "/repo" "1111111" "f.txt").run (mkSecGuardState false false))
    res = .ok none ∧ st.recordedRequests.getLast? =
      some { cwd := some "/repo", args := #["cat-file", "-t", secSha1Const ++ ":f.txt"] } := by
  constructor <;> cbv

end LeanSwe.Git.Proofs
