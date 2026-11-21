import LeanSwe.Git.Proofs.RevSecondaryGuardsProofs
import LeanSwe.Git.Proofs.WorktreeHexErrKindProofs

set_option Elab.async false
set_option maxRecDepth 4096

namespace LeanSwe.Git.Proofs

open LeanSwe.Git
open LeanSwe.Git.Model

private theorem symFail_step (cwd : String) (st : GitCliMockState) (args : Array String)
    (hCwd : Impl.validateCwd? (some cwd) = .ok ())
    (hArgs : (args.all fun a => !hasNulChar a.toList) = true)
    (out : GitRawOutput)
    (hHand : st.handler { cwd := some cwd, args := args } st.callCount = .ok out) :
    Impl.runGitRaw mockRawOps { cwd := some cwd, args := args } st =
      (.ok out, { st with
        recordedEnvs := st.recordedEnvs ++ [cleanGitEnv st.inheritedEnv #[]]
        recordedRequests := st.recordedRequests ++ [{ cwd := some cwd, args := args }]
        callCount := st.callCount + 1 }) := by
  have hEnv : Impl.validateExtraEnv #[] = .ok () := by cbv
  unfold Impl.runGitRaw
  simp only [hCwd, hEnv, hArgs, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
    bind, StateT.bind, mockRawOps]
  rw [hHand]

/-- Proof that `worktreeAdd` cleans up via `worktree remove --force` when `symbolic-ref` fails on a 40-hex branch. -/
theorem secGuard_wa40SymFail :
    let (res, st) := (((Impl.mkApiM mockRawOps).worktreeAdd "/repo" { path := "/wt40", target? := some secBr40Const }).run (mkSecGuardState false true))
    ∃ e, res = .error e ∧ e.kind = .commandFailed ∧
      st.recordedRequests.getLast? =
        some { cwd := some "/repo", args := #["worktree", "remove", "--force", "--", "/wt40"] } := by
  dsimp only [Impl.mkApiM, StateT.run]
  let st0 : GitCliMockState := mkSecGuardState false true
  let hand := (mkSecGuardState false true).handler
  have hRepo : Impl.validateRepoPath "/repo" = .ok () := by cbv
  have hWt : Impl.validateRepoPath "/wt40" = .ok () := by cbv
  have hCwdRepo : Impl.validateCwd? (some "/repo") = .ok () := by cbv
  have hCwdWt : Impl.validateCwd? (some "/wt40") = .ok () := by cbv
  have hStrict : isValidStrictRevSpec secBr40Const = true := by cbv
  have hCid : isValidCommitIdStr secBr40Const = true := by cbv
  have hLen : (secBr40Const.length == 40) = true := by cbv
  let a1 := #["rev-parse", "-q", "--verify", secBr40Const ++ "^{commit}"]
  have hA1 : (a1.all fun a => !hasNulChar a.toList) = true := by cbv
  let out1 : GitRawOutput := { exitCode := 1, stdout := ByteArray.empty, stderr := ByteArray.empty }
  have hH1' : hand { cwd := some "/repo", args := a1 } 0 = .ok out1 := by cbv
  have hR1 := symFail_step "/repo" st0 a1 hCwdRepo hA1 out1 hH1'
  let st1 : GitCliMockState := { st0 with
    recordedEnvs := st0.recordedEnvs ++ [cleanGitEnv st0.inheritedEnv #[]]
    recordedRequests := st0.recordedRequests ++ [{ cwd := some "/repo", args := a1 }]
    callCount := st0.callCount + 1 }
  let a2 := #["show-ref", "--verify", "--quiet", "refs/heads/" ++ secBr40Const]
  have hA2 : (a2.all fun a => !hasNulChar a.toList) = true := by cbv
  let out2 : GitRawOutput := { exitCode := 0, stdout := ByteArray.empty, stderr := ByteArray.empty }
  have hH2' : hand { cwd := some "/repo", args := a2 } 1 = .ok out2 := by cbv
  have hR2 := symFail_step "/repo" st1 a2 hCwdRepo hA2 out2 hH2'
  let st2 : GitCliMockState := { st1 with
    recordedEnvs := st1.recordedEnvs ++ [cleanGitEnv st1.inheritedEnv #[]]
    recordedRequests := st1.recordedRequests ++ [{ cwd := some "/repo", args := a2 }]
    callCount := st1.callCount + 1 }
  let a3 := #["worktree", "list", "--porcelain"]
  have hA3 : (a3.all fun a => !hasNulChar a.toList) = true := by cbv
  let out3 : GitRawOutput := { exitCode := 0, stdout := "worktree /repo\nbranch refs/heads/main\n".toUTF8, stderr := ByteArray.empty }
  have hH3' : hand { cwd := some "/repo", args := a3 } 2 = .ok out3 := by cbv
  have hR3 := symFail_step "/repo" st2 a3 hCwdRepo hA3 out3 hH3'
  let st3 : GitCliMockState := { st2 with
    recordedEnvs := st2.recordedEnvs ++ [cleanGitEnv st2.inheritedEnv #[]]
    recordedRequests := st2.recordedRequests ++ [{ cwd := some "/repo", args := a3 }]
    callCount := st2.callCount + 1 }
  let a4 := #["worktree", "add", "--detach", "--", "/wt40", "refs/heads/" ++ secBr40Const]
  have hA4 : (a4.all fun a => !hasNulChar a.toList) = true := by cbv
  let out4 : GitRawOutput := { exitCode := 0, stdout := ByteArray.empty, stderr := ByteArray.empty }
  have hH4' : hand { cwd := some "/repo", args := a4 } 3 = .ok out4 := by cbv
  have hR4 := symFail_step "/repo" st3 a4 hCwdRepo hA4 out4 hH4'
  let st4 : GitCliMockState := { st3 with
    recordedEnvs := st3.recordedEnvs ++ [cleanGitEnv st3.inheritedEnv #[]]
    recordedRequests := st3.recordedRequests ++ [{ cwd := some "/repo", args := a4 }]
    callCount := st3.callCount + 1 }
  let a5 := #["symbolic-ref", "HEAD", "refs/heads/" ++ secBr40Const]
  have hA5 : (a5.all fun a => !hasNulChar a.toList) = true := by cbv
  let out5 : GitRawOutput := { exitCode := 128, stdout := ByteArray.empty, stderr := "fatal: cannot update HEAD".toUTF8 }
  have hH5' : hand { cwd := some "/wt40", args := a5 } 4 = .ok out5 := by cbv
  have hR5 := symFail_step "/wt40" st4 a5 hCwdWt hA5 out5 hH5'
  let st5 : GitCliMockState := { st4 with
    recordedEnvs := st4.recordedEnvs ++ [cleanGitEnv st4.inheritedEnv #[]]
    recordedRequests := st4.recordedRequests ++ [{ cwd := some "/wt40", args := a5 }]
    callCount := st4.callCount + 1 }
  let a6 := #["worktree", "remove", "--force", "--", "/wt40"]
  have hA6 : (a6.all fun a => !hasNulChar a.toList) = true := by cbv
  let out6 : GitRawOutput := { exitCode := 0, stdout := ByteArray.empty, stderr := ByteArray.empty }
  have hH6' : hand { cwd := some "/repo", args := a6 } 5 = .ok out6 := by cbv
  have hR6 := symFail_step "/repo" st5 a6 hCwdRepo hA6 out6 hH6'
  let err5 : GitError := Impl.classifyError "symbolic-ref" out5
  have hWtCwd : Impl.joinProbeCwd (some "/repo") "/wt40" = some "/wt40" := by cbv
  have hDestSnd : (Impl.findPorcelainWorktreeDestFlags out3.stdout (Option.map Impl.normalizeWtProbePath (some "/wt40"))).2 = false := by cbv
  have hDestFst : (Impl.findPorcelainWorktreeDestFlags out3.stdout (Option.map Impl.normalizeWtProbePath (some "/wt40"))).1 = false := by cbv
  have hInUseF : ((List.map Impl.trimAsciiWhitespace ((Impl.decodeUtf8Lossy out3.stdout).splitOn "\n")).contains ("branch refs/heads/" ++ secBr40Const)) = false := by cbv
  have hEx1 : (out1.exitCode == 0) = false := rfl
  have hEx2 : (out2.exitCode != 0) = false := rfl
  have hEx3 : (out3.exitCode == 0) = true := rfl
  have hEx4 : (out4.exitCode == 0) = true := rfl
  have hEx5 : (out5.exitCode == 0) = false := rfl
  have hEx6 : (out6.exitCode == 0) = true := rfl
  unfold Impl.worktreeAddImpl Impl.worktreeAddMaybe40HexBranch Impl.runGitChecked
  simp only [hRepo, hWt, Bool.false_eq_true, ↓reduceIte, Bool.and_false, Option.isSome_none,
    hStrict, Bool.not_false, Bool.true_and, hCid, hLen, Array.isEmpty_empty, bind, StateT.bind, pure]
  rw [show Impl.runGitRaw mockRawOps { cwd := some "/repo", args := a1 } st0 = _ from hR1]
  simp only [hEx1, Bool.false_eq_true, ↓reduceIte, bind, StateT.bind]
  rw [show Impl.runGitRaw mockRawOps { cwd := some "/repo", args := a2 } st1 = _ from hR2]
  simp only [hEx2, Bool.false_eq_true, ↓reduceIte, bind, StateT.bind]
  rw [show Impl.runGitRaw mockRawOps { cwd := some "/repo", args := a3 } st2 = _ from hR3]
  simp only [hEx3, ↓reduceIte, StateT.pure, pure, hWtCwd, hDestSnd, hDestFst, hInUseF, Bool.false_and, Bool.false_eq_true, bind, StateT.bind]
  rw [show (#["worktree", "add"] ++ #[] ++ #["--detach", "--", "/wt40", "refs/heads/" ++ secBr40Const]) = a4 from rfl]
  rw [show Impl.runGitRaw mockRawOps { cwd := some "/repo", args := a4 } st3 = _ from hR4]
  simp only [hEx4, ↓reduceIte, StateT.pure, pure, bind, StateT.bind]
  rw [show Impl.runGitRaw mockRawOps { cwd := some "/wt40", args := a5 } st4 = _ from hR5]
  simp only [hEx5, Bool.false_eq_true, ↓reduceIte, StateT.pure, pure, bind, StateT.bind]
  rw [show Impl.runGitRaw mockRawOps { cwd := some "/repo", args := a6 } st5 = _ from hR6]
  simp only [hEx6, ↓reduceIte, StateT.pure, pure]
  refine ⟨err5, rfl, symRefErr_kind, ?_⟩
  simp only [st5, st4, st3, st2, st1, st0, a6, mkSecGuardState]
  rfl

end LeanSwe.Git.Proofs
