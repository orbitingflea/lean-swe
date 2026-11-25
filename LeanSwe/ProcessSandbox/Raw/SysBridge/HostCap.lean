import LeanSwe.ProcessSandbox.Raw.Model.Refines
import LeanSwe.ProcessSandbox.Raw.SysBridge

namespace LeanSwe.ProcessSandbox.Raw.SysBridge

open LeanSwe.ProcessSandbox.Raw

/-- Convert a public `Model.RawPlanRecord` to an internal `PlanSlotM Nat`. -/
def toSysPlanSlot (r : Model.RawPlanRecord) : PlanSlotM Nat :=
  { plan := r.plan, planMemfd := r.planMemfd, initMemfd := r.initMemfd, hostsMemfd := r.hostsMemfd }

/-- Convert an internal `PlanSlotM Nat` to a public `Model.RawPlanRecord`. -/
def fromSysPlanSlot (s : PlanSlotM Nat) : Model.RawPlanRecord :=
  { plan := s.plan, planMemfd := s.planMemfd, initMemfd := s.initMemfd, hostsMemfd := s.hostsMemfd }

/-- Convert a public `Model.RawBoxRecord` to an internal `BoxSlotM Nat`. -/
def toSysBoxSlot (r : Model.RawBoxRecord) : BoxSlotM Nat :=
  { pid := r.pid, pgid := r.pgid, pidfd := r.pidfd,
    stdinFd? := r.stdinFd?, stdoutFd? := r.stdoutFd?, stderrFd? := r.stderrFd?,
    statusFd? := r.statusFd?, goFd? := r.goFd?,
    readStarted := r.readStarted, fwdsTaken := r.fwdsTaken, listenerFds := r.listenerFds,
    cgroupDir := r.cgroupDir, program := r.program, cwd := r.cwd }

/-- Convert an internal `BoxSlotM Nat` to a public `Model.RawBoxRecord`. -/
def fromSysBoxSlot (s : BoxSlotM Nat) : Model.RawBoxRecord :=
  { pid := s.pid, pgid := s.pgid, pidfd := s.pidfd,
    stdinFd? := s.stdinFd?, stdoutFd? := s.stdoutFd?, stderrFd? := s.stderrFd?,
    statusFd? := s.statusFd?, goFd? := s.goFd?,
    readStarted := s.readStarted, fwdsTaken := s.fwdsTaken, listenerFds := s.listenerFds,
    cgroupDir := s.cgroupDir, program := s.program, cwd := s.cwd }

/-- Convert a public `Model.RawFwdRecord` to an internal `ForwarderSlotM Nat`. -/
def toSysFwdSlot (r : Model.RawFwdRecord) : ForwarderSlotM Nat :=
  { boxHandleId := r.boxHandleId, taskHandle := r.taskHandle }

/-- Convert an internal `ForwarderSlotM Nat` to a public `Model.RawFwdRecord`. -/
def fromSysFwdSlot (s : ForwarderSlotM Nat) : Model.RawFwdRecord :=
  { boxHandleId := s.boxHandleId, taskHandle := s.taskHandle }

/-- Convert a public `Model.RawTableState` to an internal `HostTableState Nat Nat`. -/
def toSysTable (t : Model.RawTableState) : HostTableState Nat Nat :=
  { nextId := t.nextId
    cgSeq := t.cgSeq
    plans := t.plans.map fun (k, v) => (k, toSysPlanSlot v)
    boxes := t.boxes.map fun (k, v) => (k, toSysBoxSlot v)
    forwarders := t.fwds.map fun (k, v) => (k, toSysFwdSlot v) }

/-- Convert an internal `HostTableState Nat Nat` to a public `Model.RawTableState`. -/
def fromSysTable (t : HostTableState Nat Nat) : Model.RawTableState :=
  { nextId := t.nextId
    cgSeq := t.cgSeq
    plans := t.plans.map fun (k, v) => (k, fromSysPlanSlot v)
    boxes := t.boxes.map fun (k, v) => (k, fromSysBoxSlot v)
    fwds := t.forwarders.map fun (k, v) => (k, fromSysFwdSlot v) }

/-- Project `Model.RawHostCapM m` onto internal `HostSysDepsM m Nat Nat`. -/
def toHostSysDeps {m : Type → Type} (cap : Model.RawHostCapM m) :
    HostSysDepsM m Nat Nat where
  files := cap.files
  net := cap.net
  poll := cap.poll
  proc := cap.proc
  sandbox := cap.sandbox
  timeRand := cap.timeRand
  passwd := cap.passwd
  postFork := cap.postFork
  isLinux := cap.isLinux
  target := cap.target
  getEnvPath := cap.getEnvPath
  getEnvHome := cap.getEnvHome
  startFwdTask := cap.startFwdTask
  stopFwdTask := cap.stopFwdTask

/-- Project `Model.RawHostCapM m` handle-table hooks onto internal `HostTableOpsM m Nat Nat`. -/
def toHostTableOps {m : Type → Type} [Monad m] (cap : Model.RawHostCapM m) :
    HostTableOpsM m Nat Nat where
  insertPlan slot := do
    let st ← cap.modifyTable fun s => fromSysTable (insertPlanPure (toSysTable s) slot).2
    return (insertPlanPure (toSysTable st) slot).1
  findPlan hid := do
    let st ← cap.getTable
    return assocFind hid (toSysTable st).plans
  detachPlan hid := do
    let st ← cap.modifyTable fun s => fromSysTable (detachPlanPure (toSysTable s) hid).2
    return (detachPlanPure (toSysTable st) hid).1
  insertBox slot := do
    let st ← cap.modifyTable fun s => fromSysTable (insertBoxPure (toSysTable s) slot).2
    return (insertBoxPure (toSysTable st) slot).1
  findBoxKillInfo hid := do
    let st ← cap.getTable
    return (assocFind hid (toSysTable st).boxes).map fun b => (b.pgid, b.pidfd)
  takeBoxListeners hid expected := do
    let st ← cap.modifyTable fun s => fromSysTable (takeBoxListenersPure (toSysTable s) hid expected).2
    return (takeBoxListenersPure (toSysTable st) hid expected).1
  takeBoxIo hid := do
    let st ← cap.modifyTable fun s => fromSysTable (takeBoxIoPure (toSysTable s) hid).2
    return (takeBoxIoPure (toSysTable st) hid).1
  detachBox hid := do
    let st ← cap.modifyTable fun s => fromSysTable (detachBoxPure (toSysTable s) hid).2
    return (detachBoxPure (toSysTable st) hid).1
  insertFwd slot := do
    let st ← cap.modifyTable fun s => fromSysTable (insertFwdPure (toSysTable s) slot).2
    return (insertFwdPure (toSysTable st) slot).1
  detachFwd hid := do
    let st ← cap.modifyTable fun s => fromSysTable (detachFwdPure (toSysTable s) hid).2
    return (detachFwdPure (toSysTable st) hid).1
  nextCgSeq := do
    let st ← cap.modifyTable fun s => fromSysTable (nextCgSeqPure (toSysTable s)).2
    return (nextCgSeqPure (toSysTable st)).1
  counts := do
    let st ← cap.getTable
    return countsPure (toSysTable st)

/-- Construct `RawProcessSandboxOpsM m` from a public `Model.RawHostCapM m`. -/
def mkOpsFromHostCapM {m : Type → Type} [Monad m]
    (cap : Model.RawHostCapM m) : RawProcessSandboxOpsM m :=
  mkRawOpsM (toHostSysDeps cap) (toHostTableOps cap)

end LeanSwe.ProcessSandbox.Raw.SysBridge
