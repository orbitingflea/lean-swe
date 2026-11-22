import LeanSwe.ProcessSandbox.Host.SysBridge
import LeanSwe.ProcessSandbox.Proofs.HostBwrapProofs

namespace LeanSwe.ProcessSandbox.Proofs.HostBridge

open LeanSwe.LinuxSyscall
open LeanSwe.ProcessSandbox.Raw
open LeanSwe.ProcessSandbox.Host.SysBridge

/-- `allocHandleIdPure` only yields IDs satisfying `isValidSandboxHandleId` and advances `nextId` monotonically. -/
theorem allocHandleIdPure_valid {fd fwdTask : Type} (st : HostTableState fd fwdTask) (hid : Nat)
    (st' : HostTableState fd fwdTask) (h : allocHandleIdPure st = (some hid, st')) :
    isValidSandboxHandleId hid = true ∧ st'.nextId = hid + 1 ∧
      countsPure st' = countsPure st := by
  unfold allocHandleIdPure at h
  dsimp only at h
  split at h
  · next hval =>
    cases h
    exact ⟨hval, rfl, rfl⟩
  · cases h

/-- `insertPlanPure` followed by `detachPlanPure` restores exact `countsPure` and returns the inserted slot. -/
theorem plan_insert_detach_conserves {fd fwdTask : Type}
    (st : HostTableState fd fwdTask) (slot : PlanSlotM fd) (hid : Nat)
    (st1 : HostTableState fd fwdTask)
    (hins : insertPlanPure st slot = (some hid, st1)) :
    isValidSandboxHandleId hid = true ∧
    (countsPure st1).openPlans = (countsPure st).openPlans + 1 ∧
    (countsPure st1).activeBoxes = (countsPure st).activeBoxes ∧
    (countsPure st1).activeForwarders = (countsPure st).activeForwarders ∧
    (detachPlanPure st1 hid).1.isSome = true ∧
    countsPure (detachPlanPure st1 hid).2 = countsPure st := by
  unfold insertPlanPure at hins
  cases ha : allocHandleIdPure st with
  | mk hid? st0 =>
    rw [ha] at hins
    cases hid? with
    | none => cases hins
    | some h =>
      cases hins
      have ⟨hval, _, hc0⟩ := allocHandleIdPure_valid st hid st0 ha
      have hp : st0.plans.length = st.plans.length := congrArg SandboxResourceCounts.openPlans hc0
      have hb : st0.boxes.length = st.boxes.length := congrArg SandboxResourceCounts.activeBoxes hc0
      have hf : st0.forwarders.length = st.forwarders.length := congrArg SandboxResourceCounts.activeForwarders hc0
      refine ⟨hval, ?_, ?_, ?_, ?_, ?_⟩
      · simp [countsPure, hp]
      · simp [countsPure, hb]
      · simp [countsPure, hf]
      · simp [detachPlanPure, assocRemove]
      · simp [detachPlanPure, assocRemove, countsPure, hp, hb, hf]

/-- `insertBoxPure` followed by `detachBoxPure` restores exact `countsPure` and returns the inserted box slot. -/
theorem box_insert_detach_conserves {fd fwdTask : Type}
    (st : HostTableState fd fwdTask) (slot : BoxSlotM fd) (hid : Nat)
    (st1 : HostTableState fd fwdTask)
    (hins : insertBoxPure st slot = (some hid, st1)) :
    isValidSandboxHandleId hid = true ∧
    (countsPure st1).openPlans = (countsPure st).openPlans ∧
    (countsPure st1).activeBoxes = (countsPure st).activeBoxes + 1 ∧
    (countsPure st1).activeForwarders = (countsPure st).activeForwarders ∧
    (detachBoxPure st1 hid).1.isSome = true ∧
    countsPure (detachBoxPure st1 hid).2 = countsPure st := by
  unfold insertBoxPure at hins
  cases ha : allocHandleIdPure st with
  | mk hid? st0 =>
    rw [ha] at hins
    cases hid? with
    | none => cases hins
    | some h =>
      cases hins
      have ⟨hval, _, hc0⟩ := allocHandleIdPure_valid st hid st0 ha
      have hp : st0.plans.length = st.plans.length := congrArg SandboxResourceCounts.openPlans hc0
      have hb : st0.boxes.length = st.boxes.length := congrArg SandboxResourceCounts.activeBoxes hc0
      have hf : st0.forwarders.length = st.forwarders.length := congrArg SandboxResourceCounts.activeForwarders hc0
      refine ⟨hval, ?_, ?_, ?_, ?_, ?_⟩
      · simp [countsPure, hp]
      · simp [countsPure, hb]
      · simp [countsPure, hf]
      · simp [detachBoxPure, assocRemove]
      · simp [detachBoxPure, assocRemove, countsPure, hp, hb, hf]

/-- `insertFwdPure` followed by `detachFwdPure` restores exact `countsPure` and returns the inserted forwarder slot. -/
theorem fwd_insert_detach_conserves {fd fwdTask : Type}
    (st : HostTableState fd fwdTask) (slot : ForwarderSlotM fwdTask) (hid : Nat)
    (st1 : HostTableState fd fwdTask)
    (hins : insertFwdPure st slot = (some hid, st1)) :
    isValidSandboxHandleId hid = true ∧
    (countsPure st1).openPlans = (countsPure st).openPlans ∧
    (countsPure st1).activeBoxes = (countsPure st).activeBoxes ∧
    (countsPure st1).activeForwarders = (countsPure st).activeForwarders + 1 ∧
    (detachFwdPure st1 hid).1.isSome = true ∧
    countsPure (detachFwdPure st1 hid).2 = countsPure st := by
  unfold insertFwdPure at hins
  cases ha : allocHandleIdPure st with
  | mk hid? st0 =>
    rw [ha] at hins
    cases hid? with
    | none => cases hins
    | some h =>
      cases hins
      have ⟨hval, _, hc0⟩ := allocHandleIdPure_valid st hid st0 ha
      have hp : st0.plans.length = st.plans.length := congrArg SandboxResourceCounts.openPlans hc0
      have hb : st0.boxes.length = st.boxes.length := congrArg SandboxResourceCounts.activeBoxes hc0
      have hf : st0.forwarders.length = st.forwarders.length := congrArg SandboxResourceCounts.activeForwarders hc0
      refine ⟨hval, ?_, ?_, ?_, ?_, ?_⟩
      · simp [countsPure, hp]
      · simp [countsPure, hb]
      · simp [countsPure, hf]
      · simp [detachFwdPure, assocRemove]
      · simp [detachFwdPure, assocRemove, countsPure, hp, hb, hf]

/-- `takeBoxIoPure` preserves `countsPure` and rejects any second call on the same handle (`readStarted` single-use gate). -/
theorem takeBoxIoPure_single_use {fd fwdTask : Type}
    (st : HostTableState fd fwdTask) (hid : Nat) (slot : BoxSlotM fd)
    (hfresh : slot.readStarted = false) :
    let st1 : HostTableState fd fwdTask := { st with boxes := (hid, slot) :: st.boxes }
    let (r1, st2) := takeBoxIoPure st1 hid
    let (r2, st3) := takeBoxIoPure st2 hid
    r1.isSome = true ∧ r2 = none ∧ countsPure st2 = countsPure st1 ∧ countsPure st3 = countsPure st1 := by
  simp [takeBoxIoPure, assocFind, countsPure, hfresh]

/-- `takeBoxListenersPure` enforces exact `expectedCount` match, preserves `countsPure`, and rejects any second call (`fwdsTaken` single-use gate). -/
theorem takeBoxListenersPure_single_use {fd fwdTask : Type}
    (st : HostTableState fd fwdTask) (hid : Nat) (slot : BoxSlotM fd)
    (hfresh : slot.fwdsTaken = false) :
    let st1 : HostTableState fd fwdTask := { st with boxes := (hid, slot) :: st.boxes }
    let (r1, st2) := takeBoxListenersPure st1 hid slot.listenerFds.size
    let (r2, st3) := takeBoxListenersPure st2 hid slot.listenerFds.size
    r1 = some slot.listenerFds ∧ r2 = none ∧ countsPure st2 = countsPure st1 ∧ countsPure st3 = countsPure st1 := by
  simp [takeBoxListenersPure, assocFind, countsPure, hfresh]

/-- `nextCgSeqPure` strictly increments `cgSeq` while leaving all resource counts unchanged. -/
theorem nextCgSeqPure_preserves_counts {fd fwdTask : Type} (st : HostTableState fd fwdTask) :
    let (seq, st') := nextCgSeqPure st
    seq = st.cgSeq ∧ st'.cgSeq = st.cgSeq + 1 ∧ countsPure st' = countsPure st := by
  exact ⟨rfl, rfl, rfl⟩

/-- Every handle-consuming `SysBridge` operation rejects invalid handle IDs (`isValidSandboxHandleId hid = false`) with `.invalidInput` and a non-empty message without touching state. -/
theorem invalid_handle_rejected_early {m : Type → Type} [Monad m] {fd fwdTask : Type}
    (deps : HostSysDepsM m fd fwdTask) (tbl : HostTableOpsM m fd fwdTask)
    (fuel ioFuel : Nat) (hid : Nat) (hinv : isValidSandboxHandleId hid = false) :
    (∃ e, closePlanPure deps tbl { handleId := hid } = pure (.error e) ∧ e.kind = .invalidInput ∧ e.message ≠ "") ∧
    (∃ e, spawnBoxPure deps tbl fuel { handleId := hid } = pure (.error e) ∧ e.kind = .invalidInput ∧ e.message ≠ "") ∧
    (∃ e, startPortForwardersPure deps tbl { handleId := hid, pid := 1, pgid := 1, pidfd := 0 } #[] =
      pure (.error e) ∧ e.kind = .invalidInput ∧ e.message ≠ "") ∧
    (∃ e, stopPortForwardersPure deps tbl { handleId := hid, boxHandleId := 0 } =
      pure (.error e) ∧ e.kind = .invalidInput ∧ e.message ≠ "") ∧
    (∃ e, readBoxOutputPure deps tbl fuel ioFuel { handleId := hid, pid := 1, pgid := 1, pidfd := 0 } ByteArray.empty 100 none =
      pure (.error e) ∧ e.kind = .invalidInput ∧ e.message ≠ "") ∧
    (∃ e, killProcessGroupPure deps tbl fuel { handleId := hid, pid := 1, pgid := 1, pidfd := 0 } =
      pure (.error e) ∧ e.kind = .invalidInput ∧ e.message ≠ "") ∧
    (∃ e, pidfdKillPure deps tbl fuel { handleId := hid, pid := 1, pgid := 1, pidfd := 0 } =
      pure (.error e) ∧ e.kind = .invalidInput ∧ e.message ≠ "") ∧
    (∃ e, reapBoxPure deps tbl fuel { handleId := hid, pid := 1, pgid := 1, pidfd := 0 } =
      pure (.error e) ∧ e.kind = .invalidInput ∧ e.message ≠ "") := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact ⟨Internal.mapRawError (.invalidArgument none none "invalid plan handle"),
      by simp [closePlanPure, hinv], rfl, by decide⟩
  · exact ⟨Internal.mapRawError (.invalidArgument none none "invalid plan handle"),
      by simp [spawnBoxPure, hinv], rfl, by decide⟩
  · exact ⟨Internal.mapRawError (.invalidArgument none none "invalid box handle"),
      by simp [startPortForwardersPure, hinv], rfl, by decide⟩
  · exact ⟨Internal.mapRawError (.invalidArgument none none "invalid forwarder handle"),
      by simp [stopPortForwardersPure, hinv], rfl, by decide⟩
  · exact ⟨Internal.mapRawError (.invalidArgument none none "invalid box handle"),
      by simp [readBoxOutputPure, hinv], rfl, by decide⟩
  · exact ⟨Internal.mapRawError (.invalidArgument none none "invalid box handle"),
      by simp [killProcessGroupPure, hinv], rfl, by decide⟩
  · exact ⟨Internal.mapRawError (.invalidArgument none none "invalid box handle"),
      by simp [pidfdKillPure, hinv], rfl, by decide⟩
  · exact ⟨Internal.mapRawError (.invalidArgument none none "invalid box handle"),
      by simp [reapBoxPure, hinv], rfl, by decide⟩

/-- `hostSeccompArchPure` fails closed with `.unavailable` on non-Linux hosts without performing syscalls. -/
theorem hostSeccompArchPure_nonLinux {m : Type → Type} [Monad m] {fd fwdTask : Type}
    (deps : HostSysDepsM m fd fwdTask) (h : deps.isLinux = false) :
    ∃ err, hostSeccompArchPure deps = pure (.error err) ∧ err.kind = .unavailable ∧ err.message ≠ "" := by
  unfold hostSeccompArchPure
  rw [h, HostBwrap.detectHostAuditArch_nonLinux]
  exact ⟨_, rfl, rfl, by decide⟩

/-- `preflightPure` fails closed with `.unavailable` on non-Linux hosts without performing syscalls. -/
theorem preflightPure_nonLinux {m : Type → Type} [Monad m] {fd fwdTask : Type}
    (deps : HostSysDepsM m fd fwdTask) (tbl : HostTableOpsM m fd fwdTask)
    (fuel : Nat) (req : PreflightReq) (h : deps.isLinux = false) :
    ∃ err, preflightPure deps tbl fuel req = pure (.error err) ∧ err.kind = .unavailable ∧ err.message ≠ "" := by
  exact ⟨Internal.mapRawError (.unavailable none "ProcessSandbox requires Linux"),
    by simp [preflightPure, h], rfl, by decide⟩

end LeanSwe.ProcessSandbox.Proofs.HostBridge
