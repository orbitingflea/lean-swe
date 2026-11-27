import LeanSwe.Git.Types
import LeanSwe.Git.Impl
import LeanSwe.Git.Interface
import LeanSweProofs.Git.SpecTests

set_option Elab.async false
set_option maxRecDepth 4096

namespace LeanSwe.Git.Proofs

open Core
open Core.NondetTest
open LeanSwe.Git
open LeanSwe.Git.Model

/-- Shared SHA-1 constant for secondary revision and direct `worktreeAdd` delegation proofs. -/
def secSha1Const : String := String.ofList (List.replicate 40 '1')

/-- Shared 40-hex target constant for direct `worktreeAdd` delegation proof. -/
def secBr40Const : String := String.ofList (List.replicate 40 'f')

/-- Mock CLI state for `test_git_raw_mkApi_secondaryShortShaAnd40HexWorktreeGuards`. -/
def mkSecGuardState : GitCliMockState :=
  { handler := fun req _ =>
      if req.args.toList.contains "--verify" && !req.args.toList.contains "show-ref" then
        .ok { exitCode := 0, stdout := (secSha1Const ++ "\n").toUTF8, stderr := ByteArray.empty }
      else
        .ok { exitCode := 0, stdout := ByteArray.empty, stderr := ByteArray.empty } }

/-- `worktreeAdd` delegates a 40-hex target directly to a single `git worktree add` call. -/
theorem secGuard_wa40Direct :
    let (res, st) := (((Impl.mkApiM mockRawOps).worktreeAdd "/repo" { path := "/wt40", target? := some secBr40Const }).run mkSecGuardState)
    res = .ok () ∧ st.recordedRequests =
      [{ cwd := some "/repo", args := #["worktree", "add", "--", "/wt40", secBr40Const] }] := by
  constructor <;> cbv

/-- `diffNameStatus` delegates short-SHA `revB?` directly to `git`. -/
theorem secGuard_dfRevBShort :
    let (res, st) := (((Impl.mkApiM mockRawOps).diffNameStatus "/repo" "HEAD" (some "1111111") #[]).run mkSecGuardState)
    res = .ok #[] ∧ st.recordedRequests.getLast? =
      some { cwd := some "/repo", args := #["diff", "--name-status", "-z", "HEAD", "1111111", "--"] } := by
  constructor <;> cbv

/-- `showFile?` delegates short-SHA `rev` directly to `git`. -/
theorem secGuard_sfShort :
    let (res, st) := (((Impl.mkApiM mockRawOps).showFile? "/repo" "1111111" "f.txt").run mkSecGuardState)
    res = .ok none ∧ st.recordedRequests.getLast? =
      some { cwd := some "/repo", args := #["cat-file", "-t", secSha1Const ++ ":f.txt"] } := by
  constructor <;> cbv

end LeanSwe.Git.Proofs
