import LeanSwe.LinuxSyscall.Process.Model

namespace LeanSwe.LinuxSyscall.Process

private theorem pidfd_nextFreeHid_ge_hint (fds : List (HandleId × ProcessFdDesc)) (hint : HandleId) :
    hint ≤ nextFreeHid fds hint := by
  induction fds generalizing hint with
  | nil => exact Nat.le_refl _
  | cons p rest ih =>
    rcases p with ⟨k, d⟩
    exact Nat.le_trans (Nat.le_max_left _ _) (ih _)

private theorem pidfd_lt_nextFreeHid_of_mem (fds : List (HandleId × ProcessFdDesc)) (hint k : HandleId)
    (v : ProcessFdDesc) (hmem : (k, v) ∈ fds) :
    k < nextFreeHid fds hint := by
  induction fds generalizing hint with
  | nil => contradiction
  | cons hd tl ih =>
    rcases hd with ⟨k', v'⟩
    cases hmem with
    | head =>
      exact Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.lt_succ_self k) (Nat.le_max_right hint (k + 1)))
        (pidfd_nextFreeHid_ge_hint tl _)
    | tail _ htl => exact ih (max hint (k' + 1)) htl

private theorem pidfd_assocGet_none_of_ge {β : Type} (xs : List (Nat × β)) (h : Nat)
    (hgt : ∀ k v, (k, v) ∈ xs → k < h) :
    assocGet xs h = none := by
  induction xs with
  | nil => rfl
  | cons hd tl ih =>
    rcases hd with ⟨k, v⟩
    have hlt : k < h := hgt k v List.mem_cons_self
    have hne : (k == h) = false := beq_false_of_ne (Nat.ne_of_lt hlt)
    change (if k == h then some v else assocGet tl h) = none
    rw [hne]
    exact ih (fun k' v' hmem => hgt k' v' (List.mem_cons_of_mem _ hmem))

private theorem modelOps_pidfd_open_error (s : ProcessSysState) (pid : UInt32) (flags : PidfdOpenFlags) (e : Errno)
    (h : checkPidfdOpenTarget s pid flags = Except.error e) :
    (modelOps.pidfd_open pid flags).run s =
      (Except.error e, if e == Errno.ESRCH then esrchPidfdOpenNext s pid flags else s) := by
  dsimp only [modelOps, StateT.run, get, getThe, MonadStateOf.get, StateT.get,
    set, StateT.set, pure, Pure.pure, StateT.pure, bind, Bind.bind, StateT.bind]
  rw [h]
  rfl

private theorem modelOps_pidfd_open_ok (s : ProcessSysState) (pid : UInt32) (flags : PidfdOpenFlags)
    (h : checkPidfdOpenTarget s pid flags = Except.ok ()) :
    (modelOps.pidfd_open pid flags).run s =
      let hid := nextFreeHid s.fds s.nextHid
      (Except.ok hid, commitPidfd s hid pid flags.nonblock flags.thread) := by
  dsimp only [modelOps, StateT.run, get, getThe, MonadStateOf.get, StateT.get,
    set, StateT.set, pure, Pure.pure, StateT.pure, bind, Bind.bind, StateT.bind]
  rw [h]
  rfl

private theorem exec_pidfd_open_error (s : ProcessSysState) (pid : UInt32) (flags : PidfdOpenFlags) (e : Errno)
    (h : checkPidfdOpenTarget s pid flags = Except.error e) :
    (execProcessReq modelOps (.pidfd_open pid flags)).run s =
      (ProcessOutcome.err e, if e == Errno.ESRCH then esrchPidfdOpenNext s pid flags else s) := by
  have hm : modelOps.pidfd_open pid flags s =
      (Except.error e, if e == Errno.ESRCH then esrchPidfdOpenNext s pid flags else s) :=
    modelOps_pidfd_open_error s pid flags e h
  simp only [execProcessReq, StateT.run, pure, Pure.pure, bind, Bind.bind, StateT.bind]
  rw [hm]
  rfl

private theorem exec_pidfd_open_ok (s : ProcessSysState) (pid : UInt32) (flags : PidfdOpenFlags)
    (h : checkPidfdOpenTarget s pid flags = Except.ok ()) :
    (execProcessReq modelOps (.pidfd_open pid flags)).run s =
      let hid := nextFreeHid s.fds s.nextHid
      (ProcessOutcome.opened hid, commitPidfd s hid pid flags.nonblock flags.thread) := by
  have hm : modelOps.pidfd_open pid flags s =
      (Except.ok (nextFreeHid s.fds s.nextHid), commitPidfd s (nextFreeHid s.fds s.nextHid) pid flags.nonblock flags.thread) :=
    modelOps_pidfd_open_ok s pid flags h
  simp only [execProcessReq, StateT.run, pure, Pure.pure, bind, Bind.bind, StateT.bind]
  rw [hm]
  rfl

private theorem allowedStepPidfdOpen_error (s : ProcessSysState) (pid : UInt32) (flags : PidfdOpenFlags) (e : Errno)
    (h : checkPidfdOpenTarget s pid flags = Except.error e) :
    allowedStep s (.pidfd_open pid flags) (ProcessOutcome.err e) =
      some (if e == Errno.ESRCH then esrchPidfdOpenNext s pid flags else s) := by
  change allowedStepPidfdOpen s pid flags (ProcessOutcome.err e) =
    some (if e == Errno.ESRCH then esrchPidfdOpenNext s pid flags else s)
  unfold allowedStepPidfdOpen
  rw [h]
  change (if e == e then some (if e == Errno.ESRCH then esrchPidfdOpenNext s pid flags else s) else _) = _
  rw [beq_self_eq_true]
  rfl

private theorem allowedStepPidfdOpen_ok (s : ProcessSysState) (pid : UInt32) (flags : PidfdOpenFlags)
    (h : checkPidfdOpenTarget s pid flags = Except.ok ()) :
    let hid := nextFreeHid s.fds s.nextHid
    allowedStep s (.pidfd_open pid flags) (ProcessOutcome.opened hid) =
      some (commitPidfd s hid pid flags.nonblock flags.thread) := by
  intro hid
  have hnone : assocGet s.fds hid = none :=
    pidfd_assocGet_none_of_ge s.fds hid (fun k v hm => pidfd_lt_nextFreeHid_of_mem s.fds s.nextHid k v hm)
  change allowedStepPidfdOpen s pid flags (ProcessOutcome.opened hid) =
    some (commitPidfd s hid pid flags.nonblock flags.thread)
  unfold allowedStepPidfdOpen
  rw [h]
  change (if (assocGet s.fds hid).isNone then some (commitPidfd s hid pid flags.nonblock flags.thread) else none) = _
  rw [hnone]
  rfl

/-- Soundness of `modelOps.pidfd_open` against `allowedStep`. -/
theorem modelOps_pidfd_open_sound (s : ProcessSysState) (pid : UInt32) (flags : PidfdOpenFlags) :
    let r := (execProcessReq modelOps (.pidfd_open pid flags)).run s
    allowedStep s (.pidfd_open pid flags) r.1 = some r.2 := by
  cases ho : checkPidfdOpenTarget s pid flags with
  | error e =>
    rw [exec_pidfd_open_error s pid flags e ho]
    exact allowedStepPidfdOpen_error s pid flags e ho
  | ok u =>
    cases u
    rw [exec_pidfd_open_ok s pid flags ho]
    exact allowedStepPidfdOpen_ok s pid flags ho

private theorem modelOps_pidfd_send_ok (s s' : ProcessSysState) (hid : HandleId) (sig : Signal) (flags : PidfdSignalFlags)
    (hpre : validateReqBeforeKernel s (.pidfd_send_signal hid sig flags) = none)
    (h : evalPidfdSendSignal s hid sig flags = Except.ok s') :
    (modelOps.pidfd_send_signal hid sig flags).run s = (Except.ok (), s') := by
  dsimp only [modelOps, StateT.run, get, getThe, MonadStateOf.get, StateT.get,
    set, StateT.set, pure, Pure.pure, StateT.pure, bind, Bind.bind, StateT.bind]
  rw [hpre]
  dsimp only
  rw [h]
  rfl

private theorem modelOps_pidfd_send_error (s : ProcessSysState) (hid : HandleId) (sig : Signal) (flags : PidfdSignalFlags) (e : Errno)
    (hpre : validateReqBeforeKernel s (.pidfd_send_signal hid sig flags) = none)
    (h : evalPidfdSendSignal s hid sig flags = Except.error e) :
    (modelOps.pidfd_send_signal hid sig flags).run s =
      (Except.error e, if e == Errno.ESRCH then esrchPidfdSendNext s hid flags else s) := by
  dsimp only [modelOps, StateT.run, get, getThe, MonadStateOf.get, StateT.get,
    set, StateT.set, pure, Pure.pure, StateT.pure, bind, Bind.bind, StateT.bind]
  rw [hpre]
  dsimp only
  rw [h]
  rfl

private theorem exec_pidfd_send_ok (s s' : ProcessSysState) (hid : HandleId) (sig : Signal) (flags : PidfdSignalFlags)
    (hpre : validateReqBeforeKernel s (.pidfd_send_signal hid sig flags) = none)
    (h : evalPidfdSendSignal s hid sig flags = Except.ok s') :
    (execProcessReq modelOps (.pidfd_send_signal hid sig flags)).run s = (ProcessOutcome.unit, s') := by
  have hm : modelOps.pidfd_send_signal hid sig flags s = (Except.ok (), s') :=
    modelOps_pidfd_send_ok s s' hid sig flags hpre h
  simp only [execProcessReq, StateT.run, pure, Pure.pure, bind, Bind.bind, StateT.bind]
  rw [hm]
  rfl

private theorem exec_pidfd_send_error (s : ProcessSysState) (hid : HandleId) (sig : Signal) (flags : PidfdSignalFlags) (e : Errno)
    (hpre : validateReqBeforeKernel s (.pidfd_send_signal hid sig flags) = none)
    (h : evalPidfdSendSignal s hid sig flags = Except.error e) :
    (execProcessReq modelOps (.pidfd_send_signal hid sig flags)).run s =
      (ProcessOutcome.err e, if e == Errno.ESRCH then esrchPidfdSendNext s hid flags else s) := by
  have hm : modelOps.pidfd_send_signal hid sig flags s =
      (Except.error e, if e == Errno.ESRCH then esrchPidfdSendNext s hid flags else s) :=
    modelOps_pidfd_send_error s hid sig flags e hpre h
  simp only [execProcessReq, StateT.run, pure, Pure.pure, bind, Bind.bind, StateT.bind]
  rw [hm]
  rfl

private theorem allowedStepPidfdSend_ok (s s' : ProcessSysState) (hid : HandleId) (sig : Signal) (flags : PidfdSignalFlags)
    (hpre : validateReqBeforeKernel s (.pidfd_send_signal hid sig flags) = none)
    (h : evalPidfdSendSignal s hid sig flags = Except.ok s') :
    allowedStep s (.pidfd_send_signal hid sig flags) ProcessOutcome.unit = some s' := by
  simp only [allowedStep, hpre, allowedStepPidfdSendSignal, h]

private theorem allowedStepPidfdSend_error (s : ProcessSysState) (hid : HandleId) (sig : Signal) (flags : PidfdSignalFlags) (e : Errno)
    (hpre : validateReqBeforeKernel s (.pidfd_send_signal hid sig flags) = none)
    (h : evalPidfdSendSignal s hid sig flags = Except.error e) :
    allowedStep s (.pidfd_send_signal hid sig flags) (ProcessOutcome.err e) =
      some (if e == Errno.ESRCH then esrchPidfdSendNext s hid flags else s) := by
  simp only [allowedStep, hpre, allowedStepPidfdSendSignal, h, beq_self_eq_true, ↓reduceIte]

/-- Soundness of `modelOps.pidfd_send_signal` against `allowedStep`. -/
theorem modelOps_pidfd_send_signal_sound (s : ProcessSysState) (hid : HandleId) (sig : Signal) (flags : PidfdSignalFlags) :
    let r := (execProcessReq modelOps (.pidfd_send_signal hid sig flags)).run s
    allowedStep s (.pidfd_send_signal hid sig flags) r.1 = some r.2 := by
  cases hpre : validateReqBeforeKernel s (.pidfd_send_signal hid sig flags) with
  | some preErr =>
    simp only [execProcessReq, outcomeOfUnit, modelOps, allowedStep, hpre, StateT.run, get, getThe,
      MonadStateOf.get, StateT.get, pure, Pure.pure, StateT.pure, bind, Bind.bind, StateT.bind,
      beq_self_eq_true, ↓reduceIte]
  | none =>
    cases hs : evalPidfdSendSignal s hid sig flags with
    | ok s' =>
      rw [exec_pidfd_send_ok s s' hid sig flags hpre hs]
      exact allowedStepPidfdSend_ok s s' hid sig flags hpre hs
    | error e =>
      rw [exec_pidfd_send_error s hid sig flags e hpre hs]
      exact allowedStepPidfdSend_error s hid sig flags e hpre hs

end LeanSwe.LinuxSyscall.Process
