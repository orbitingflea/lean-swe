import LeanSwe.LinuxSyscall.Process.Proofs.ModelSoundnessHelpers

namespace LeanSwe.LinuxSyscall.Process

private theorem isTransient_ECHILD : isKernelNonFdTransient Errno.ECHILD = false := rfl
private theorem isTransient_EINTR : isKernelNonFdTransient Errno.EINTR = true := rfl
private theorem isSeccomp_ECHILD : isSeccompSynthesizableErrno Errno.ECHILD = true := rfl
private theorem isSeccomp_EINTR : isSeccompSynthesizableErrno Errno.EINTR = true := rfl

private theorem modelOps_waitpid_none_sound (s : ProcessSysState) (pid : Int32) (flags : WaitFlags)
    (hval : flags.isValid = true)
    (hminF : (pid == Int32.minValue) = false)
    (hempF : (matchingUnreapedChildren s pid flags).isEmpty = false)
    (hfind : pickImmediateWaitResult s.procs (matchingUnreapedChildren s pid flags) flags = none) :
    let r := (execProcessReq modelOps (.waitpid pid flags)).run s
    allowedStep s (.waitpid pid flags) r.1 = some r.2 := by
  have hnoc : hasConfirmedWaitable s.procs (matchingUnreapedChildren s pid flags) flags = false :=
    pickImmediateWaitResult_none_implies_not_hasConfirmedWaitable s.procs _ flags hfind
  dsimp only [execProcessReq, modelOps, allowedStep, validateReqBeforeKernel, allowedStepWaitpid, evalModelWaitpid,
    StateT.run, get, getThe, MonadStateOf.get, StateT.get, set, StateT.set,
    pure, Pure.pure, StateT.pure, bind, Bind.bind, StateT.bind]
  simp only [hval, Bool.not_true, Bool.false_eq_true, ↓reduceIte, hminF, hempF, hfind]
  by_cases hauto : (s.sigchld == .autoreap && allAutoreapable s.procs (matchingUnreapedChildren s pid flags)) = true
  · simp only [hauto, ↓reduceIte, StateT.pure, pure, Pure.pure]
    have hall : allAutoreapable s.procs (matchingUnreapedChildren s pid flags) = true := by
      cases hs : s.sigchld <;> cases ha : allAutoreapable s.procs (matchingUnreapedChildren s pid flags) <;> simp_all
    by_cases hsec : s.ambientSeccomp = true
    · simp only [isTransient_ECHILD, hsec, isSeccomp_ECHILD, Bool.and_self, Bool.false_eq_true, ↓reduceIte]
    · have hsecF : s.ambientSeccomp = false := Bool.eq_false_iff.mpr hsec
      simp only [isTransient_ECHILD, hsecF, Bool.false_and, Bool.false_eq_true, ↓reduceIte,
        beq_self_eq_true, autoReapEchildState, hall, Option.getD_some]
  · have hautoF : (s.sigchld == .autoreap && allAutoreapable s.procs (matchingUnreapedChildren s pid flags)) = false :=
      Bool.eq_false_iff.mpr hauto
    simp only [hautoF, Bool.false_eq_true, ↓reduceIte]
    by_cases hnh : flags.nohang = true
    · simp only [hnh, ↓reduceIte, StateT.pure, pure, Pure.pure, allowedStepWaitResult, hnoc,
        Bool.not_false, Bool.and_self]
    · have hnhF : flags.nohang = false := Bool.eq_false_iff.mpr hnh
      simp only [hnhF, Bool.false_eq_true, ↓reduceIte]
      cases hb : pickBlockingAutoExit s.procs (matchingUnreapedChildren s pid flags) with
      | some wres =>
        exact isSome_eq_getD (d := s) (pickBlockingAutoExit_sound s (matchingUnreapedChildren s pid flags) flags
          (fun hm => assocGet_matching_mem s pid flags hm) hb)
      | none =>
        simp only [StateT.pure, pure, Pure.pure, isTransient_EINTR, ↓reduceIte]

/-- Soundness of `modelOps.waitpid` against `allowedStep`. -/
theorem modelOps_waitpid_sound (s : ProcessSysState) (pid : Int32) (flags : WaitFlags) :
    let r := (execProcessReq modelOps (.waitpid pid flags)).run s
    allowedStep s (.waitpid pid flags) r.1 = some r.2 := by
  by_cases hval : flags.isValid = true
  · by_cases hmin : (pid == Int32.minValue) = true
    · simp only [execProcessReq, modelOps, allowedStep, validateReqBeforeKernel, allowedStepWaitpid, evalModelWaitpid,
        StateT.run, get, getThe, MonadStateOf.get, StateT.get, set, StateT.set,
        pure, Pure.pure, StateT.pure, bind, Bind.bind, StateT.bind,
        hval, Bool.not_true, Bool.false_eq_true, ↓reduceIte, hmin, beq_self_eq_true, Bool.true_or]
    · have hminF : (pid == Int32.minValue) = false := Bool.eq_false_iff.mpr hmin
      by_cases hemp : (matchingUnreapedChildren s pid flags).isEmpty = true
      · simp only [execProcessReq, modelOps, allowedStep, validateReqBeforeKernel, allowedStepWaitpid, evalModelWaitpid,
          StateT.run, get, getThe, MonadStateOf.get, StateT.get, set, StateT.set,
          pure, Pure.pure, StateT.pure, bind, Bind.bind, StateT.bind,
          hval, Bool.not_true, Bool.false_eq_true, ↓reduceIte, hminF, hemp, beq_self_eq_true, Bool.true_or]
      · have hempF : (matchingUnreapedChildren s pid flags).isEmpty = false := Bool.eq_false_iff.mpr hemp
        cases hfind : pickImmediateWaitResult s.procs (matchingUnreapedChildren s pid flags) flags with
        | some wres =>
          dsimp only [execProcessReq, modelOps, allowedStep, validateReqBeforeKernel, allowedStepWaitpid, evalModelWaitpid,
            StateT.run, get, getThe, MonadStateOf.get, StateT.get, set, StateT.set,
            pure, Pure.pure, StateT.pure, bind, Bind.bind, StateT.bind]
          simp only [hval, Bool.not_true, Bool.false_eq_true, ↓reduceIte, hminF, hempF, hfind]
          exact isSome_eq_getD (d := s) (pickImmediateWaitResult_sound s (matchingUnreapedChildren s pid flags) flags
            (fun hm => assocGet_matching_mem s pid flags hm) hfind)
        | none =>
          exact modelOps_waitpid_none_sound s pid flags hval hminF hempF hfind
  · have hvalF : flags.isValid = false := Bool.eq_false_iff.mpr hval
    simp only [execProcessReq, modelOps, allowedStep, validateReqBeforeKernel, allowedStepWaitpid, evalModelWaitpid,
      StateT.run, get, getThe, MonadStateOf.get, StateT.get, set, StateT.set,
      pure, Pure.pure, StateT.pure, bind, Bind.bind, StateT.bind,
      hvalF, Bool.not_false, ↓reduceIte, beq_self_eq_true, Bool.true_or]

end LeanSwe.LinuxSyscall.Process
