import LeanSweProofs.LinuxSyscall.Process.Model

namespace LeanSwe.LinuxSyscall.Process

private theorem modelOps_kill_ok (s s' : ProcessSysState) (pidOrNegPgid : Int32) (sig : Signal)
    (hpre : validateReqBeforeKernel s (.kill pidOrNegPgid sig) = none)
    (h : evalKill s pidOrNegPgid sig = Except.ok s') :
    (modelOps.kill pidOrNegPgid sig).run s = (Except.ok (), s') := by
  dsimp only [modelOps, StateT.run, get, getThe, MonadStateOf.get, StateT.get,
    set, StateT.set, pure, Pure.pure, StateT.pure, bind, Bind.bind, StateT.bind]
  rw [hpre]
  dsimp only
  rw [h]
  rfl

private theorem modelOps_kill_error (s : ProcessSysState) (pidOrNegPgid : Int32) (sig : Signal) (e : Errno)
    (hpre : validateReqBeforeKernel s (.kill pidOrNegPgid sig) = none)
    (h : evalKill s pidOrNegPgid sig = Except.error e) :
    (modelOps.kill pidOrNegPgid sig).run s =
      (Except.error e, if e == Errno.ESRCH then esrchKillNext s pidOrNegPgid else s) := by
  dsimp only [modelOps, StateT.run, get, getThe, MonadStateOf.get, StateT.get,
    set, StateT.set, pure, Pure.pure, StateT.pure, bind, Bind.bind, StateT.bind]
  rw [hpre]
  dsimp only
  rw [h]
  rfl

private theorem exec_kill_ok (s s' : ProcessSysState) (pidOrNegPgid : Int32) (sig : Signal)
    (hpre : validateReqBeforeKernel s (.kill pidOrNegPgid sig) = none)
    (h : evalKill s pidOrNegPgid sig = Except.ok s') :
    (execProcessReq modelOps (.kill pidOrNegPgid sig)).run s = (ProcessOutcome.unit, s') := by
  have hm : modelOps.kill pidOrNegPgid sig s = (Except.ok (), s') :=
    modelOps_kill_ok s s' pidOrNegPgid sig hpre h
  simp only [execProcessReq, StateT.run, pure, Pure.pure, bind, Bind.bind, StateT.bind]
  rw [hm]
  rfl

private theorem exec_kill_error (s : ProcessSysState) (pidOrNegPgid : Int32) (sig : Signal) (e : Errno)
    (hpre : validateReqBeforeKernel s (.kill pidOrNegPgid sig) = none)
    (h : evalKill s pidOrNegPgid sig = Except.error e) :
    (execProcessReq modelOps (.kill pidOrNegPgid sig)).run s =
      (ProcessOutcome.err e, if e == Errno.ESRCH then esrchKillNext s pidOrNegPgid else s) := by
  have hm : modelOps.kill pidOrNegPgid sig s =
      (Except.error e, if e == Errno.ESRCH then esrchKillNext s pidOrNegPgid else s) :=
    modelOps_kill_error s pidOrNegPgid sig e hpre h
  simp only [execProcessReq, StateT.run, pure, Pure.pure, bind, Bind.bind, StateT.bind]
  rw [hm]
  rfl

private theorem allowedStepKill_ok (s s' : ProcessSysState) (pidOrNegPgid : Int32) (sig : Signal)
    (hpre : validateReqBeforeKernel s (.kill pidOrNegPgid sig) = none)
    (h : evalKill s pidOrNegPgid sig = Except.ok s') :
    allowedStep s (.kill pidOrNegPgid sig) ProcessOutcome.unit = some s' := by
  simp only [allowedStep, hpre, allowedStepKill, h]

private theorem allowedStepKill_error (s : ProcessSysState) (pidOrNegPgid : Int32) (sig : Signal) (e : Errno)
    (hpre : validateReqBeforeKernel s (.kill pidOrNegPgid sig) = none)
    (h : evalKill s pidOrNegPgid sig = Except.error e) :
    allowedStep s (.kill pidOrNegPgid sig) (ProcessOutcome.err e) =
      some (if e == Errno.ESRCH then esrchKillNext s pidOrNegPgid else s) := by
  simp only [allowedStep, hpre, allowedStepKill, h, beq_self_eq_true, ↓reduceIte]

/-- Soundness of `modelOps.kill` against `allowedStep`. -/
theorem modelOps_kill_sound (s : ProcessSysState) (pidOrNegPgid : Int32) (sig : Signal) :
    let r := (execProcessReq modelOps (.kill pidOrNegPgid sig)).run s
    allowedStep s (.kill pidOrNegPgid sig) r.1 = some r.2 := by
  cases hpre : validateReqBeforeKernel s (.kill pidOrNegPgid sig) with
  | some preErr =>
    simp only [execProcessReq, outcomeOfUnit, modelOps, allowedStep, hpre, StateT.run, get, getThe,
      MonadStateOf.get, StateT.get, pure, Pure.pure, StateT.pure, bind, Bind.bind, StateT.bind,
      beq_self_eq_true, ↓reduceIte]
  | none =>
    cases hk : evalKill s pidOrNegPgid sig with
    | ok s' =>
      rw [exec_kill_ok s s' pidOrNegPgid sig hpre hk]
      exact allowedStepKill_ok s s' pidOrNegPgid sig hpre hk
    | error e =>
      rw [exec_kill_error s pidOrNegPgid sig e hpre hk]
      exact allowedStepKill_error s pidOrNegPgid sig e hpre hk

end LeanSwe.LinuxSyscall.Process
