import Core.Obeys
import LeanSwe.LinuxSyscall.Net.Impl
import LeanSwe.LinuxSyscall.Net.Interface
import LeanSwe.LinuxSyscall.Net.Model.Refines
import LeanSwe.LinuxSyscall.Net.Proofs.HealthyStep

/-!
# Raw-to-Package `Core.ObeysStepFrom` Proofs for `LeanSwe.LinuxSyscall.Net`

Proves wire-decoder round-trips, pre-check safety, and `mkNetOpsM_obeysStepFrom`
for `LeanSwe.LinuxSyscall.Net.Proofs`.
-/

namespace LeanSwe.LinuxSyscall.Net.Proofs

open LeanSwe.LinuxSyscall
open LeanSwe.LinuxSyscall.Net

/-- Unfold `StateT.bind` on `StateM W`. -/
@[simp] theorem stateT_bind_eq {W α β : Type} (x : StateM W α) (f : α → StateM W β) (w : W) :
    StateT.bind x f w = f (x w).1 (x w).2 := rfl

/-- Unfold `StateT.pure` on `StateM W`. -/
@[simp] theorem stateT_pure_eq {W α : Type} (a : α) (w : W) :
    StateT.pure (m := Id) a w = (a, w) := rfl

/-- Unfold `StateT.map` on `StateM W`. -/
@[simp] theorem stateT_map_eq {W α β : Type} (g : α → β) (x : StateM W α) (w : W) :
    StateT.map g x w = (g (x w).1, (x w).2) := rfl

/-- `SockDomain.toTag` round-trips through `Model.decodeRawSockDomain?`. -/
theorem decodeRawSockDomain?_toTag (d : SockDomain) :
    Model.decodeRawSockDomain? d.toTag = some d := by
  cases d <;> rfl

/-- `SockType.toTag` round-trips through `Model.decodeRawSockType?`. -/
theorem decodeRawSockType?_toTag (t : SockType) :
    Model.decodeRawSockType? t.toTag = some t := by
  cases t <;> rfl

/-- `SockFlags.toBits` round-trips through `Model.decodeRawSockFlags?`. -/
theorem decodeRawSockFlags?_toBits (f : SockFlags) :
    Model.decodeRawSockFlags? f.toBits = some f := by
  rcases f with ⟨a, b⟩
  cases a <;> cases b <;> decide

/-- `SockOpt.toTag` round-trips through `Model.decodeRawSockOpt?`. -/
theorem decodeRawSockOpt?_toTag (o : SockOpt) :
    Model.decodeRawSockOpt? o.toTag = some o := by
  cases o <;> rfl

/-- `SetSockOpt.toTag` round-trips through `Model.decodeRawSetSockOpt?`. -/
theorem decodeRawSetSockOpt?_toTag (o : SetSockOpt) :
    Model.decodeRawSetSockOpt? o.toTag = some o := by
  cases o <;> rfl

/-- `MsgFlags.toBits` round-trips through `Model.decodeRawMsgFlags?`. -/
theorem decodeRawMsgFlags?_toBits (f : MsgFlags) :
    Model.decodeRawMsgFlags? f.toBits = some f := by
  rcases f with ⟨a, b, c⟩
  cases a <;> cases b <;> cases c <;> decide

/-- `ShutHow.toTag` round-trips through `Model.decodeRawShutHow?`. -/
theorem decodeRawShutHow?_toTag (h : ShutHow) :
    Model.decodeRawShutHow? h.toTag = some h := by
  cases h <;> rfl

/-- `NetIoctlOp.toRaw` round-trips through `Model.decodeRawNetIoctlOp?`. -/
theorem decodeRawNetIoctlOp?_toRaw (op : NetIoctlOp) :
    Model.decodeRawNetIoctlOp? op.toRaw.1 op.toRaw.2 = some op := by
  cases op <;> rfl

/-- `SockAddr.toRawTuple` round-trips through `SockAddr.ofRawTuple`. -/
theorem sockAddr_ofRawTuple_toRawTuple (sa : SockAddr) :
    SockAddr.ofRawTuple sa.toRawTuple = sa := by
  cases sa <;> rfl

/-- Every `preCheckNet` rejection errno is neither a critical OS fault nor `EINTR`. -/
theorem preCheckNet_safe (req : NetReq) (err : Errno)
    (h : preCheckNet req = some err) :
    Errno.isCriticalOsErrno err = false ∧ (err == Errno.EINTR) = false := by
  unfold preCheckNet validateSocketArgs validateSocketpairArgs at h
  cases req <;> simp only at h
  all_goals
    repeat (first
      | (injection h with hEq; subst hEq; exact ⟨by decide, by decide⟩)
      | split at h
      | cases h)

/-- `emitErr` accepts its own canonical errno without mutating `NetState`. -/
theorem emitErr_self_eq (s : NetState) (e : Errno) (alTr : Bool) :
    emitErr (some (.err e)) s e [] (fun _ => s) alTr none none = some (.err e, s) := by
  unfold emitErr
  dsimp only
  rw [beq_self_eq_true, Bool.true_or]
  rfl

private theorem healthyStep_preCheckNet {env : HealthyEnv} {req : NetReq} {err : Errno}
    (hWf : env.wf = true) (hPre : preCheckNet req = some err) :
    healthyStep env req (.err err) = some env := by
  rcases env with ⟨s, budget⟩
  obtain ⟨hCrit, hEi⟩ := preCheckNet_safe req err hPre
  have hCore : stepNetCore s req (some (.err err)) = some (.err err, s) := by
    unfold stepNetCore; rw [hPre]; exact emitErr_self_eq s err false
  have hAl : allowedStep s req (.err err) = some s := by
    unfold allowedStep; rw [hCore]; rfl
  unfold healthyStep
  simp [hWf, isCriticalFault, hCrit, hAl, isEintrOutcome, hEi]

/-- `Internal.mkNetOpsM` lifts any raw C-ABI bundle obeying `Model.allowedRawStep` to `Model.allowedPkgStep`. -/
theorem mkNetOpsM_obeysStepFrom :
    Core.ObeysStepFrom id HealthyEnv.wf Model.execRawStep Model.allowedRawStep
      HealthyEnv.wf Internal.mkNetOpsM Model.execPkgStep Model.allowedPkgStep := by
  intro W proj raw hRaw w req hWf
  dsimp only [Function.comp, id] at hWf ⊢
  cases req with
  | socket dom st fl proto =>
    cases hVal : validateSocketArgs dom st proto with
    | some e =>
      simp only [Model.execPkgStep, execNetReq, Internal.mkNetOpsM,
        Functor.map, Pure.pure, StateT.run, stateT_pure_eq, stateT_map_eq,
        Model.allowedPkgStep, hVal, outcomeOfOpened]
      exact healthyStep_preCheckNet hWf (by simp [preCheckNet, hVal])
    | none =>
      have hStep := hRaw w (.socket dom.toTag st.toTag fl.toBits proto) hWf
      simp only [Model.execRawStep, Model.allowedRawStep, Model.decodeRawNetReq?,
        Model.execPkgStep, execNetReq, Internal.mkNetOpsM, Functor.map,
        StateT.run, stateT_map_eq, Model.allowedPkgStep, hVal,
        decodeRawSockDomain?_toTag, decodeRawSockType?_toTag, decodeRawSockFlags?_toBits] at hStep ⊢
      rcases hCall : raw.socket dom.toTag st.toTag fl.toBits proto w with ⟨res, w'⟩
      try rw [hCall] at hStep
      cases res <;> simpa [Model.outcomeOfRawOpened, Model.toModelOutcome, outcomeOfOpened] using hStep
  | socketpair dom st fl =>
    cases hVal : validateSocketpairArgs dom st with
    | some e =>
      simp only [Model.execPkgStep, execNetReq, Internal.mkNetOpsM,
        Functor.map, Pure.pure, StateT.run, stateT_pure_eq, stateT_map_eq,
        Model.allowedPkgStep, hVal, outcomeOfPair]
      exact healthyStep_preCheckNet hWf (by simp [preCheckNet, hVal])
    | none =>
      have hStep := hRaw w (.socketpair dom.toTag st.toTag fl.toBits) hWf
      simp only [Model.execRawStep, Model.allowedRawStep, Model.decodeRawNetReq?,
        Model.execPkgStep, execNetReq, Internal.mkNetOpsM, Functor.map,
        StateT.run, stateT_map_eq, Model.allowedPkgStep, hVal,
        decodeRawSockDomain?_toTag, decodeRawSockType?_toTag, decodeRawSockFlags?_toBits] at hStep ⊢
      rcases hCall : raw.socketpair dom.toTag st.toTag fl.toBits w with ⟨res, w'⟩
      try rw [hCall] at hStep
      cases res with
      | ok p => rcases p with ⟨a, b⟩; simpa [Model.outcomeOfRawPair, Model.toModelOutcome, outcomeOfPair] using hStep
      | error e => simpa [Model.outcomeOfRawPair, Model.toModelOutcome, outcomeOfPair] using hStep
  | bind hid addr =>
    cases hVal : addr.isValidTarget with
    | false =>
      simp only [Model.execPkgStep, execNetReq, Internal.mkNetOpsM,
        Functor.map, Pure.pure, StateT.run, stateT_pure_eq, stateT_map_eq,
        Model.allowedPkgStep, hVal, Bool.not_false, ↓reduceIte, outcomeOfUnit]
      exact healthyStep_preCheckNet hWf (by simp [preCheckNet, hVal])
    | true =>
      have hStep := hRaw w (.bind hid addr.toRawTuple) hWf
      simp only [Model.execRawStep, Model.allowedRawStep, Model.decodeRawNetReq?,
        Model.execPkgStep, execNetReq, Internal.mkNetOpsM, Functor.map,
        StateT.run, stateT_map_eq, Model.allowedPkgStep, hVal, Bool.not_true, Bool.false_eq_true,
        ↓reduceIte, sockAddr_ofRawTuple_toRawTuple] at hStep ⊢
      rcases hCall : raw.bind hid addr.toRawTuple w with ⟨res, w'⟩
      try rw [hCall] at hStep
      cases res <;> simpa [Model.outcomeOfRawUnit, Model.toModelOutcome, outcomeOfUnit] using hStep
  | listen hid bl =>
    have hStep := hRaw w (.listen hid bl) hWf
    simp only [Model.execRawStep, Model.allowedRawStep, Model.decodeRawNetReq?,
      Model.execPkgStep, execNetReq, Internal.mkNetOpsM, Functor.map,
      StateT.run, stateT_map_eq, Model.allowedPkgStep] at hStep ⊢
    rcases hCall : raw.listen hid bl w with ⟨res, w'⟩
    try rw [hCall] at hStep
    cases res <;> simpa [Model.outcomeOfRawUnit, Model.toModelOutcome, outcomeOfUnit] using hStep
  | accept4 hid fl =>
    have hStep := hRaw w (.accept4 hid fl.toBits) hWf
    simp only [Model.execRawStep, Model.allowedRawStep, Model.decodeRawNetReq?,
      Model.execPkgStep, execNetReq, Internal.mkNetOpsM, Functor.map, Bind.bind, Pure.pure,
      StateT.run, stateT_bind_eq, stateT_map_eq, Model.allowedPkgStep,
      decodeRawSockFlags?_toBits] at hStep ⊢
    rcases hCall : raw.accept4 hid fl.toBits w with ⟨res, w'⟩
    try rw [hCall] at hStep
    cases res with
    | ok p =>
      rcases p with ⟨cfd, rawSa⟩
      simpa [Model.outcomeOfRawAccepted, Model.toModelOutcome, outcomeOfAccepted] using hStep
    | error e =>
      simpa [Model.outcomeOfRawAccepted, Model.toModelOutcome, outcomeOfAccepted] using hStep
  | connect hid addr =>
    cases hVal : addr.isValidTarget with
    | false =>
      simp only [Model.execPkgStep, execNetReq, Internal.mkNetOpsM,
        Functor.map, Pure.pure, StateT.run, stateT_pure_eq, stateT_map_eq,
        Model.allowedPkgStep, hVal, Bool.not_false, ↓reduceIte, outcomeOfUnit]
      exact healthyStep_preCheckNet hWf (by simp [preCheckNet, hVal])
    | true =>
      have hStep := hRaw w (.connect hid addr.toRawTuple) hWf
      simp only [Model.execRawStep, Model.allowedRawStep, Model.decodeRawNetReq?,
        Model.execPkgStep, execNetReq, Internal.mkNetOpsM, Functor.map,
        StateT.run, stateT_map_eq, Model.allowedPkgStep, hVal, Bool.not_true, Bool.false_eq_true,
        ↓reduceIte, sockAddr_ofRawTuple_toRawTuple] at hStep ⊢
      rcases hCall : raw.connect hid addr.toRawTuple w with ⟨res, w'⟩
      try rw [hCall] at hStep
      cases res <;> simpa [Model.outcomeOfRawUnit, Model.toModelOutcome, outcomeOfUnit] using hStep
  | getsockopt hid opt =>
    have hStep := hRaw w (.getsockopt hid opt.toTag) hWf
    simp only [Model.execRawStep, Model.allowedRawStep, Model.decodeRawNetReq?,
      Model.execPkgStep, execNetReq, Internal.mkNetOpsM, Functor.map,
      StateT.run, stateT_map_eq, Model.allowedPkgStep, decodeRawSockOpt?_toTag] at hStep ⊢
    rcases hCall : raw.getsockopt hid opt.toTag w with ⟨res, w'⟩
    try rw [hCall] at hStep
    cases res <;> simpa [Model.outcomeOfRawU32, Model.toModelOutcome, outcomeOfU32] using hStep
  | setsockopt hid opt val =>
    have hStep := hRaw w (.setsockopt hid opt.toTag val) hWf
    simp only [Model.execRawStep, Model.allowedRawStep, Model.decodeRawNetReq?,
      Model.execPkgStep, execNetReq, Internal.mkNetOpsM, Functor.map,
      StateT.run, stateT_map_eq, Model.allowedPkgStep, decodeRawSetSockOpt?_toTag] at hStep ⊢
    rcases hCall : raw.setsockopt hid opt.toTag val w with ⟨res, w'⟩
    try rw [hCall] at hStep
    cases res <;> simpa [Model.outcomeOfRawUnit, Model.toModelOutcome, outcomeOfUnit] using hStep
  | getsockname hid =>
    have hStep := hRaw w (.getsockname hid) hWf
    simp only [Model.execRawStep, Model.allowedRawStep, Model.decodeRawNetReq?,
      Model.execPkgStep, execNetReq, Internal.mkNetOpsM, Functor.map, Bind.bind, Pure.pure,
      StateT.run, stateT_bind_eq, stateT_map_eq, Model.allowedPkgStep] at hStep ⊢
    rcases hCall : raw.getsockname hid w with ⟨res, w'⟩
    try rw [hCall] at hStep
    cases res <;> simpa [Model.outcomeOfRawAddr, Model.toModelOutcome, outcomeOfAddr] using hStep
  | recvfrom hid maxBytes fl =>
    have hStep := hRaw w (.recvfrom hid maxBytes fl.toBits) hWf
    simp only [Model.execRawStep, Model.allowedRawStep, Model.decodeRawNetReq?,
      Model.execPkgStep, execNetReq, Internal.mkNetOpsM, Functor.map,
      StateT.run, stateT_map_eq, Model.allowedPkgStep, decodeRawMsgFlags?_toBits] at hStep ⊢
    rcases hCall : raw.recvfrom hid maxBytes fl.toBits w with ⟨res, w'⟩
    try rw [hCall] at hStep
    cases res <;> simpa [Model.outcomeOfRawBytes, Model.toModelOutcome, outcomeOfBytes] using hStep
  | sendto hid data fl =>
    have hStep := hRaw w (.sendto hid data fl.toBits) hWf
    simp only [Model.execRawStep, Model.allowedRawStep, Model.decodeRawNetReq?,
      Model.execPkgStep, execNetReq, Internal.mkNetOpsM, Functor.map,
      StateT.run, stateT_map_eq, Model.allowedPkgStep, decodeRawMsgFlags?_toBits] at hStep ⊢
    rcases hCall : raw.sendto hid data fl.toBits w with ⟨res, w'⟩
    try rw [hCall] at hStep
    cases res <;> simpa [Model.outcomeOfRawU32, Model.toModelOutcome, outcomeOfU32] using hStep
  | shutdown hid how =>
    have hStep := hRaw w (.shutdown hid how.toTag) hWf
    simp only [Model.execRawStep, Model.allowedRawStep, Model.decodeRawNetReq?,
      Model.execPkgStep, execNetReq, Internal.mkNetOpsM, Functor.map,
      StateT.run, stateT_map_eq, Model.allowedPkgStep, decodeRawShutHow?_toTag] at hStep ⊢
    rcases hCall : raw.shutdown hid how.toTag w with ⟨res, w'⟩
    try rw [hCall] at hStep
    cases res <;> simpa [Model.outcomeOfRawUnit, Model.toModelOutcome, outcomeOfUnit] using hStep
  | sendmsg hid fds =>
    cases hVal : isValidScmCount fds.size with
    | false =>
      simp only [Model.execPkgStep, execNetReq, Internal.mkNetOpsM,
        Functor.map, Pure.pure, StateT.run, stateT_pure_eq, stateT_map_eq,
        Model.allowedPkgStep, hVal, Bool.not_false, ↓reduceIte, outcomeOfUnit]
      exact healthyStep_preCheckNet hWf (by simp [preCheckNet, hVal])
    | true =>
      have hStep := hRaw w (.sendmsg hid fds) hWf
      simp only [Model.execRawStep, Model.allowedRawStep, Model.decodeRawNetReq?,
        Model.execPkgStep, execNetReq, Internal.mkNetOpsM, Functor.map,
        StateT.run, stateT_map_eq, Model.allowedPkgStep, hVal, Bool.not_true, Bool.false_eq_true,
        ↓reduceIte] at hStep ⊢
      rcases hCall : raw.sendmsg hid fds w with ⟨res, w'⟩
      try rw [hCall] at hStep
      cases res <;> simpa [Model.outcomeOfRawUnit, Model.toModelOutcome, outcomeOfUnit] using hStep
  | recvmsg hid maxFds =>
    cases hVal : isValidScmCount maxFds.toNat with
    | false =>
      simp only [Model.execPkgStep, execNetReq, Internal.mkNetOpsM,
        Functor.map, Pure.pure, StateT.run, stateT_pure_eq, stateT_map_eq,
        Model.allowedPkgStep, hVal, Bool.not_false, ↓reduceIte, outcomeOfFds]
      exact healthyStep_preCheckNet hWf (by simp [preCheckNet, hVal])
    | true =>
      have hStep := hRaw w (.recvmsg hid maxFds) hWf
      simp only [Model.execRawStep, Model.allowedRawStep, Model.decodeRawNetReq?,
        Model.execPkgStep, execNetReq, Internal.mkNetOpsM, Functor.map,
        StateT.run, stateT_map_eq, Model.allowedPkgStep, hVal, Bool.not_true, Bool.false_eq_true,
        ↓reduceIte] at hStep ⊢
      rcases hCall : raw.recvmsg hid maxFds w with ⟨res, w'⟩
      try rw [hCall] at hStep
      cases res <;> simpa [Model.outcomeOfRawFds, Model.toModelOutcome, outcomeOfFds] using hStep
  | ioctl hid op ifn =>
    cases hVal : isValidIfname ifn with
    | false =>
      simp only [Model.execPkgStep, execNetReq, Internal.mkNetOpsM,
        Functor.map, Pure.pure, StateT.run, stateT_pure_eq, stateT_map_eq,
        Model.allowedPkgStep, hVal, Bool.not_false, ↓reduceIte, outcomeOfU32]
      exact healthyStep_preCheckNet hWf (by simp [preCheckNet, hVal])
    | true =>
      have hStep := hRaw w (.ioctl hid op.toRaw.1 op.toRaw.2 ifn) hWf
      simp only [Model.execRawStep, Model.allowedRawStep, Model.decodeRawNetReq?,
        Model.execPkgStep, execNetReq, Internal.mkNetOpsM, Functor.map,
        StateT.run, stateT_map_eq, Model.allowedPkgStep, hVal, Bool.not_true, Bool.false_eq_true,
        ↓reduceIte, decodeRawNetIoctlOp?_toRaw] at hStep ⊢
      rcases hCall : raw.ioctl hid op.toRaw.1 op.toRaw.2 ifn w with ⟨res, w'⟩
      try rw [hCall] at hStep
      cases res <;> simpa [Model.outcomeOfRawU32, Model.toModelOutcome, outcomeOfU32] using hStep

end LeanSwe.LinuxSyscall.Net.Proofs
