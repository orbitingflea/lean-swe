import LeanSweProofs.LinuxSyscall.Process.Proofs.ModelSoundnessHelpers

namespace LeanSwe.LinuxSyscall.Process

/-- Soundness of `modelOps.getpid` against `allowedStep`. -/
theorem modelOps_getpid_sound (s : ProcessSysState) :
    let r := (execProcessReq modelOps .getpid).run s
    allowedStep s .getpid r.1 = some r.2 := by
  simp only [execProcessReq, outcomeOfU32, modelOps, allowedStep, validateReqBeforeKernel, beq_self_eq_true, ↓reduceIte,
    StateT.run, get, getThe, MonadStateOf.get, StateT.get,
    pure, Pure.pure, StateT.pure, bind, Bind.bind, StateT.bind]

/-- Soundness of `modelOps.getuid` against `allowedStep`. -/
theorem modelOps_getuid_sound (s : ProcessSysState) :
    let r := (execProcessReq modelOps .getuid).run s
    allowedStep s .getuid r.1 = some r.2 := by
  simp only [execProcessReq, outcomeOfU32, modelOps, allowedStep, validateReqBeforeKernel, beq_self_eq_true, ↓reduceIte,
    StateT.run, get, getThe, MonadStateOf.get, StateT.get,
    pure, Pure.pure, StateT.pure, bind, Bind.bind, StateT.bind]

/-- Soundness of `modelOps.pipe2` against `allowedStep`. -/
theorem modelOps_pipe2_sound (s : ProcessSysState) (flags : PipeFlags) :
    let r := (execProcessReq modelOps (.pipe2 flags)).run s
    allowedStep s (.pipe2 flags) r.1 = some r.2 := by
  by_cases hval : flags.isValid = true
  · by_cases hwatch : (flags.notificationPipe && !s.watchQueueSupported) = true
    · simp only [execProcessReq, outcomeOfPiped, modelOps, allowedStep, validateReqBeforeKernel, hval, Bool.not_true,
        Bool.false_eq_true, ↓reduceIte, hwatch, beq_self_eq_true, Bool.true_or, StateT.run, get, getThe,
        MonadStateOf.get, StateT.get, pure, Pure.pure, StateT.pure, bind, Bind.bind, StateT.bind]
    · have hwatchF : (flags.notificationPipe && !s.watchQueueSupported) = false :=
        Bool.eq_false_iff.mpr hwatch
      have hne : (nextFreeHid s.fds s.nextHid != nextFreeHid s.fds s.nextHid + 1) = true :=
        bne_iff_ne.mpr (Nat.ne_of_lt (Nat.lt_succ_self _))
      have hnone1 : assocGet s.fds (nextFreeHid s.fds s.nextHid) = none :=
        assocGet_none_of_ge s.fds _ (fun k v hm => lt_nextFreeHid_of_mem s.fds s.nextHid k v hm)
      have hnone2 : assocGet s.fds (nextFreeHid s.fds s.nextHid + 1) = none :=
        assocGet_none_of_ge s.fds _ (fun k v hm =>
          Nat.lt_trans (lt_nextFreeHid_of_mem s.fds s.nextHid k v hm) (Nat.lt_succ_self _))
      simp only [execProcessReq, outcomeOfPiped, modelOps, allowedStep, validateReqBeforeKernel, hval, Bool.not_true,
        Bool.false_eq_true, ↓reduceIte, hwatchF, hne, hnone1, hnone2, Option.isNone_none, Bool.and_self,
        StateT.run, get, getThe, MonadStateOf.get, StateT.get, set, StateT.set,
        pure, Pure.pure, StateT.pure, bind, Bind.bind, StateT.bind]
  · have hvalF : flags.isValid = false := Bool.eq_false_iff.mpr hval
    simp only [execProcessReq, outcomeOfPiped, modelOps, allowedStep, validateReqBeforeKernel, hvalF, Bool.not_false, ↓reduceIte,
      beq_self_eq_true, Bool.true_or, StateT.run, get, getThe, MonadStateOf.get, StateT.get,
      pure, Pure.pure, StateT.pure, bind, Bind.bind, StateT.bind]

end LeanSwe.LinuxSyscall.Process
