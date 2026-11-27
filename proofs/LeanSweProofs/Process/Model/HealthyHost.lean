import LeanSwe.LinuxSyscall.Common.Types
import LeanSweProofs.LinuxSyscall.Common.Model
import LeanSwe.LinuxSyscall.Process.Types
import LeanSweProofs.LinuxSyscall.Process.Model
import LeanSwe.LinuxSyscall.Files.Types
import LeanSweProofs.LinuxSyscall.Files.Model
import LeanSwe.LinuxSyscall.Poll.Types
import LeanSwe.LinuxSyscall.TimeRand.Types
import LeanSweProofs.LinuxSyscall.TimeRand.Model
import LeanSwe.PostFork.Types
import LeanSwe.Process.Types
import LeanSwe.Process.Types.Internal
import LeanSweProofs.Process.Model

/-!
Healthy-OS capability boundary and world-state specification for `LeanSwe.Process`
covering `Impl + SysBridge` end-to-end over imported dependency interfaces
(`LinuxSyscall.{Process,Files,Poll,TimeRand}`, `PostFork`, and `EnvVars`).
-/

namespace LeanSwe.Process.Model

open LeanSwe.LinuxSyscall
open LeanSwe.Process

export LeanSwe.Process.Internal
  (ProcSlotM ProcTableState ProcTableOpsM ProcessHostCapsM HealthyHostCapsM)

/-- Pure step inserting `slot` into `ProcTableState`, returning `(handleId, nextState)`. -/
def insertHostSlotPure {fd : Type} (st : ProcTableState fd) (slot : ProcSlotM fd) :
    Nat × ProcTableState fd :=
  let hid := st.nextId
  (hid, { nextId := hid + 1, slots := (hid, slot) :: st.slots })

/-- Lookup helper over association list `slots`. -/
def findHostSlotPure {fd : Type} (hid : Nat) : List (Nat × ProcSlotM fd) → Option (ProcSlotM fd)
  | [] => none
  | (k, v) :: rest => if k == hid then some v else findHostSlotPure hid rest

/-- Pure step detaching pipe descriptors from `hid` for `awaitOutput`. -/
def takeHostSlotIoPure {fd : Type} (st : ProcTableState fd) (hid : Nat) :
    Option (UInt32 × Option fd × Option fd × Option fd) × ProcTableState fd :=
  match findHostSlotPure hid st.slots with
  | none => (none, st)
  | some slot =>
    let slots' := st.slots.map fun (k, s) =>
      if k == hid then (k, { s with stdinFd? := none, stdoutFd? := none, stderrFd? := none })
      else (k, s)
    (some (slot.pid, slot.stdinFd?, slot.stdoutFd?, slot.stderrFd?), { st with slots := slots' })

/-- Pure step updating `waited` on `hid` if still present (`false` if absent). -/
def markHostWaitedPure {fd : Type} (st : ProcTableState fd) (hid : Nat) (waited : Bool) :
    Bool × ProcTableState fd :=
  match findHostSlotPure hid st.slots with
  | none => (false, st)
  | some _ =>
    let slots' := st.slots.map fun (k, s) =>
      if k == hid then (k, { s with waited := s.waited || waited }) else (k, s)
    (true, { st with slots := slots' })

/-- Remove first matching `hid` from association list `slots`. -/
def removeHostSlotList {fd : Type} (hid : Nat) :
    List (Nat × ProcSlotM fd) → Option (ProcSlotM fd) × List (Nat × ProcSlotM fd)
  | [] => (none, [])
  | (k, v) :: rest =>
    if k == hid then
      (some v, rest)
    else
      let (found?, rest') := removeHostSlotList hid rest
      (found?, (k, v) :: rest')

/-- Pure step detaching `hid` completely from `ProcTableState`. -/
def detachHostSlotPure {fd : Type} (st : ProcTableState fd) (hid : Nat) :
    Option (ProcSlotM fd) × ProcTableState fd :=
  let (found?, slots') := removeHostSlotList hid st.slots
  (found?, { st with slots := slots' })

/-- Pure `StateM S` instantiation of `ProcTableOpsM` via lens `(getTbl, setTbl)`. -/
def stateHostTableOps {S fd : Type}
    (getTbl : S → ProcTableState fd)
    (setTbl : S → ProcTableState fd → S) : ProcTableOpsM (StateM S) fd where
  insertSlot slot := modifyGet fun s =>
    let (hid, t') := insertHostSlotPure (getTbl s) slot
    (hid, setTbl s t')
  takeSlotIo hid := modifyGet fun s =>
    let (res, t') := takeHostSlotIoPure (getTbl s) hid
    (res, setTbl s t')
  markWaited hid waited := modifyGet fun s =>
    let (ok, t') := markHostWaitedPure (getTbl s) hid waited
    (ok, setTbl s t')
  lookupPgid hid := do
    let s ← get
    return (findHostSlotPure hid (getTbl s).slots).map (·.pgid)
  detachSlot hid := modifyGet fun s =>
    let (res, t') := detachHostSlotPure (getTbl s) hid
    (res, setTbl s t')
  activeCount := do
    let s ← get
    return (getTbl s).slots.length

/-- Pure healthy-OS world state combining Linux process, files, time, ambient env, and active slot table. -/
structure ProcessHostWorld where
  /-- Healthy Linux process environment. -/
  proc : LinuxSyscall.Process.HealthyEnv := LinuxSyscall.Process.HealthyEnv.initial
  /-- Healthy Linux filesystem environment. -/
  files : LinuxSyscall.Files.HealthyEnv := LinuxSyscall.Files.HealthyEnv.initial
  /-- Healthy Linux clock/random environment. -/
  time : LinuxSyscall.TimeRand.HealthyEnv := LinuxSyscall.TimeRand.HealthyEnv.initial
  /-- Ambient raw `environ(7)` entries. -/
  ambientEnv : Array ByteArray := #["PATH=/bin:/usr/bin".toUTF8]
  /-- Active process handle slot table. -/
  tbl : ProcTableState LinuxSyscall.Files.HandleId := {}

instance : Inhabited ProcessHostWorld where
  default := {}

/-- Project a `(handleId, ProcSlotM)` entry into a public `ProcessHandleEntry`. -/
def hostSlotToEntry (p : Nat × ProcSlotM LinuxSyscall.Files.HandleId) : ProcessHandleEntry :=
  { handleId := p.1
    pid := Int.ofNat p.2.pid.toNat
    pgid := Int.ofNat p.2.pgid.toNat
    ioConsumed := p.2.stdinFd?.isNone && p.2.stdoutFd?.isNone && p.2.stderrFd?.isNone
    waited := p.2.waited }

/-- Project `ProcessHostWorld` to abstract `ProcessModelState`. -/
def hostWorldToProcessState (w : ProcessHostWorld) : ProcessModelState :=
  { nextHandleId := w.tbl.nextId
    activeHandles := w.tbl.slots.map hostSlotToEntry }

/-- Maximum positive 32-bit Linux PID/PGID bound (`0x7fffffff`). -/
def maxLinuxPidModel : UInt32 := 0x7fffffff

/-- Well-formedness check on a single `ProcSlotM` requiring valid Linux PID/PGID bounds. -/
def hostSlotWf (s : ProcSlotM LinuxSyscall.Files.HandleId) : Bool :=
  decide (1 ≤ s.pid ∧ s.pid ≤ maxLinuxPidModel ∧
    1 ≤ s.pgid ∧ s.pgid ≤ maxLinuxPidModel)

/-- Total well-formedness guard on `ProcessHostWorld` for `Core.ObeysStepFrom`. -/
def hostWorldWf (w : ProcessHostWorld) : Bool :=
  w.proc.wf &&
  w.files.wf &&
  w.time.wf &&
  w.tbl.slots.all (fun p => hostSlotWf p.2) &&
  processStateWf (hostWorldToProcessState w)

/-- Request sum covering all `ProcTableOpsM` operations. -/
inductive HostTableReq where
  /-- Insert a new handle slot. -/
  | insertSlot (slot : ProcSlotM LinuxSyscall.Files.HandleId)
  /-- Detach pipe descriptors for I/O streaming. -/
  | takeSlotIo (hid : Nat)
  /-- Update `waited` flag on a handle slot. -/
  | markWaited (hid : Nat) (waited : Bool)
  /-- Look up `pgid` for a handle slot. -/
  | lookupPgid (hid : Nat)
  /-- Detach and return the slot for `hid`. -/
  | detachSlot (hid : Nat)
  /-- Query active handle slot count. -/
  | activeCount
  deriving BEq, DecidableEq, Inhabited

/-- Output sum for `HostTableReq`. -/
inductive HostTableOut where
  /-- Allocated handle ID from `insertSlot`. -/
  | hid (id : Nat)
  /-- Detached slot I/O tuple from `takeSlotIo`. -/
  | slotIo (res : Option (UInt32 × Option LinuxSyscall.Files.HandleId × Option LinuxSyscall.Files.HandleId × Option LinuxSyscall.Files.HandleId))
  /-- Success flag from `markWaited`. -/
  | flag (ok : Bool)
  /-- Optional PGID from `lookupPgid`. -/
  | pgid (res : Option UInt32)
  /-- Detached slot from `detachSlot`. -/
  | slot (res : Option (ProcSlotM LinuxSyscall.Files.HandleId))
  /-- Active slot count from `activeCount`. -/
  | count (n : Nat)
  deriving Inhabited

/-- Execute one `HostTableReq` against `ProcTableOpsM (StateM W) LinuxSyscall.Files.HandleId`. -/
def execHostTableReq {W : Type}
    (tbl : ProcTableOpsM (StateM W) LinuxSyscall.Files.HandleId) :
    HostTableReq → StateM W HostTableOut
  | .insertSlot slot => .hid <$> tbl.insertSlot slot
  | .takeSlotIo hid => .slotIo <$> tbl.takeSlotIo hid
  | .markWaited hid waited => .flag <$> tbl.markWaited hid waited
  | .lookupPgid hid => .pgid <$> tbl.lookupPgid hid
  | .detachSlot hid => .slot <$> tbl.detachSlot hid
  | .activeCount => .count <$> tbl.activeCount

/-- Pure deterministic relation for `HostTableReq` over `ProcTableState`. -/
def allowedHostTableStep (t : ProcTableState LinuxSyscall.Files.HandleId)
    (req : HostTableReq) (out : HostTableOut)
    (t' : ProcTableState LinuxSyscall.Files.HandleId) : Prop :=
  match req, out with
  | .insertSlot slot, .hid id =>
    let r := insertHostSlotPure t slot
    id = r.1 ∧ t' = r.2
  | .takeSlotIo hid, .slotIo res =>
    let r := takeHostSlotIoPure t hid
    res = r.1 ∧ t' = r.2
  | .markWaited hid waited, .flag ok =>
    let r := markHostWaitedPure t hid waited
    ok = r.1 ∧ t' = r.2
  | .lookupPgid hid, .pgid res =>
    res = (findHostSlotPure hid t.slots).map (·.pgid) ∧ t' = t
  | .detachSlot hid, .slot res =>
    let r := detachHostSlotPure t hid
    res = r.1 ∧ t' = r.2
  | .activeCount, .count n =>
    n = t.slots.length ∧ t' = t
  | _, _ => False

/-- Scoped `LinuxSyscall.Process` request sum covering operations consumed by `Process.SysBridge`. -/
inductive HostProcReq where
  /-- `pipe2(2)` syscall request. -/
  | pipe2 (flags : LinuxSyscall.Process.PipeFlags)
  /-- `waitpid(2)` syscall request. -/
  | waitpid (pid : Int32) (flags : LinuxSyscall.Process.WaitFlags)
  /-- `kill(2)` syscall request. -/
  | kill (target : Int32) (sig : LinuxSyscall.Process.Signal)

/-- Embed `HostProcReq` into `LinuxSyscall.Process.ProcessReq`. -/
def HostProcReq.toProcessReq : HostProcReq → LinuxSyscall.Process.ProcessReq
  | .pipe2 flags => .pipe2 flags
  | .waitpid pid flags => .waitpid pid flags
  | .kill target sig => .kill target sig

/-- Scoped `LinuxSyscall.Files` request sum covering operations consumed by `Process.SysBridge`. -/
inductive HostFilesReq where
  /-- `close(2)` syscall request. -/
  | close (hid : LinuxSyscall.Files.HandleId)
  /-- `read(2)` syscall request. -/
  | read (hid : LinuxSyscall.Files.HandleId) (maxBytes : UInt32)
  /-- `write(2)` syscall request. -/
  | write (hid : LinuxSyscall.Files.HandleId) (data : ByteArray)
  /-- `fstatat(2)` syscall request. -/
  | fstatat (dir : Option LinuxSyscall.Files.HandleId) (path : ByteArray) (flags : LinuxSyscall.Files.AtFlags)
  /-- `faccessat(2)` syscall request. -/
  | faccessat (dir : Option LinuxSyscall.Files.HandleId) (path : ByteArray)
      (mask : LinuxSyscall.Files.AccessModeMask) (flags : LinuxSyscall.Files.AtFlags)
  /-- `fcntl(2)` syscall request. -/
  | fcntl (hid : LinuxSyscall.Files.HandleId) (cmd : LinuxSyscall.Files.FcntlCmd)

/-- Embed `HostFilesReq` into `LinuxSyscall.Files.FilesReq`. -/
def HostFilesReq.toFilesReq : HostFilesReq → LinuxSyscall.Files.FilesReq
  | .close hid => .close hid
  | .read hid maxBytes => .read hid maxBytes
  | .write hid data => .write hid data
  | .fstatat dir path flags => .fstatat dir path flags
  | .faccessat dir path mask flags => .faccessat dir path mask flags
  | .fcntl hid cmd => .fcntl hid cmd

/-- Single-step request sum covering all imported OS capabilities in `HealthyHostCapsM`. -/
inductive HostCapStepReq where
  /-- Curated `LinuxSyscall.Process` syscall consumed by `Process.SysBridge`. -/
  | proc (req : HostProcReq)
  /-- Curated `LinuxSyscall.Files` syscall consumed by `Process.SysBridge`. -/
  | files (req : HostFilesReq)
  /-- Curated `LinuxSyscall.Poll.ppoll` syscall. -/
  | poll (entries : Array (LinuxSyscall.Files.HandleId × Poll.PollEvents)) (timeout? : Option Poll.Timespec)
  /-- Curated `LinuxSyscall.TimeRand` syscall. -/
  | timeRand (req : LinuxSyscall.TimeRand.TimeRandReq)
  /-- Verified `PostFork.spawn` child launch. -/
  | postFork (spec : PostFork.ChildSpecM LinuxSyscall.Files.HandleId)
  /-- Ambient `environ(7)` byte snapshot (`EnvVars.listEnvironBytes`). -/
  | listAmbientEnv
  /-- Active process handle table operation. -/
  | table (req : HostTableReq)

instance : Inhabited HostCapStepReq where
  default := .listAmbientEnv

/-- Single-step output sum for `HostCapStepReq`. -/
inductive HostCapStepOut where
  /-- Decoded `LinuxSyscall.Process` outcome. -/
  | proc (out : LinuxSyscall.Process.ProcessOutcome)
  /-- Decoded `LinuxSyscall.Files` outcome. -/
  | files (out : LinuxSyscall.Files.FilesOutcome)
  /-- Result of `ppoll`. -/
  | poll (res : Except Errno (Array Poll.PollEvents))
  /-- Decoded `LinuxSyscall.TimeRand` outcome. -/
  | timeRand (out : LinuxSyscall.TimeRand.TimeRandOutcome)
  /-- Result of `PostFork.spawn`. -/
  | postFork (res : Except PostFork.PostForkError PostFork.SpawnedChild)
  /-- Ambient `environ(7)` byte entries. -/
  | env (entries : Array ByteArray)
  /-- Result of `HostTableReq`. -/
  | table (out : HostTableOut)
  deriving Inhabited

/-- Execute one `HostCapStepReq` against `HealthyHostCapsM (StateM W)`. -/
def execHostCapStep {W : Type} (cap : HealthyHostCapsM (StateM W)) :
    HostCapStepReq → StateM W HostCapStepOut
  | .proc req => .proc <$> LinuxSyscall.Process.execProcessReq cap.proc req.toProcessReq
  | .files req => .files <$> LinuxSyscall.Files.execFilesReq cap.files req.toFilesReq
  | .poll entries timeout? => .poll <$> cap.poll.ppoll entries timeout?
  | .timeRand req => .timeRand <$> LinuxSyscall.TimeRand.execTimeRandReq cap.timeRand req
  | .postFork spec => .postFork <$> cap.postFork.spawn spec
  | .listAmbientEnv => .env <$> cap.listEnvironBytes
  | .table req => .table <$> execHostTableReq cap.table req

/-- Request well-formedness check ensuring inserted handle slots satisfy Linux PID/PGID bounds. -/
def hostCapReqWf : HostCapStepReq → Bool
  | .table (.insertSlot slot) => hostSlotWf slot
  | _ => true

/-- Healthy-OS relational single-step specification for `HealthyHostCapsM` over `ProcessHostWorld`. -/
def allowedHostCapStep (w : ProcessHostWorld) (req : HostCapStepReq) (out : HostCapStepOut)
    (w' : ProcessHostWorld) : Prop :=
  hostWorldWf w = true ∧
  (hostCapReqWf req = true → hostWorldWf w' = true) ∧
  match req, out with
  | .proc r, .proc o =>
    LinuxSyscall.Process.healthyStep w.proc r.toProcessReq o = some w'.proc ∧
    w'.time = w.time ∧
    w'.ambientEnv = w.ambientEnv ∧
    w'.tbl = w.tbl
  | .files r, .files o =>
    LinuxSyscall.Files.healthyStep w.files r.toFilesReq o = some w'.files ∧
    w'.proc = w.proc ∧
    w'.time = w.time ∧
    w'.ambientEnv = w.ambientEnv ∧
    w'.tbl = w.tbl ∧
    (∀ hid cap bs, r = .read hid cap → o = .bytes bs → bs.size ≤ cap.toNat) ∧
    (∀ hid data n, r = .write hid data → o = .u32 n → n.toNat ≤ data.size)
  | .poll entries _, .poll res =>
    w'.proc = w.proc ∧
    w'.files = w.files ∧
    w'.ambientEnv = w.ambientEnv ∧
    w'.tbl = w.tbl ∧
    match res with
    | .ok revents => revents.size = entries.size
    | .error e => Errno.isCriticalOsErrno e = false
  | .timeRand r, .timeRand o =>
    LinuxSyscall.TimeRand.healthyStep w.time r o = some w'.time ∧
    w'.proc = w.proc ∧
    w'.files = w.files ∧
    w'.ambientEnv = w.ambientEnv ∧
    w'.tbl = w.tbl
  | .postFork spec, .postFork res =>
    w'.time = w.time ∧
    w'.ambientEnv = w.ambientEnv ∧
    w'.tbl = w.tbl ∧
    match res with
    | .ok child =>
      1 ≤ child.pid ∧
      child.pid ≤ maxLinuxPidModel ∧
      (spec.processGroup = .newGroup → child.pgid = some child.pid)
    | .error err =>
      (∀ e, err.errno = some e → Errno.isCriticalOsErrno e = false) ∧
      (∀ cf, err.childFailure = some cf → Errno.isCriticalOsErrno cf.errno = false)
  | .listAmbientEnv, .env entries =>
    w' = w ∧ entries = w.ambientEnv
  | .table r, .table o =>
    w'.proc = w.proc ∧
    w'.files = w.files ∧
    w'.time = w.time ∧
    w'.ambientEnv = w.ambientEnv ∧
    allowedHostTableStep w.tbl r o w'.tbl
  | _, _ => False

/-- Package-level `ProcessApiM` step specification over `ProcessHostWorld`. -/
def allowedPkgHostStep (w : ProcessHostWorld) (req : PkgStepReq) (out : PkgStepOut)
    (w' : ProcessHostWorld) : Prop :=
  hostWorldWf w = true ∧
  hostWorldWf w' = true ∧
  allowedPkgStep (hostWorldToProcessState w) req out (hostWorldToProcessState w')

end LeanSwe.Process.Model
