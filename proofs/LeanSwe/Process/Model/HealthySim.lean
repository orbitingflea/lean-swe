import LeanSwe.LinuxSyscall.Common.Types
import LeanSwe.LinuxSyscall.Common.Model
import LeanSwe.LinuxSyscall.Process.Types
import LeanSwe.LinuxSyscall.Process.Model
import LeanSwe.LinuxSyscall.Files.Types
import LeanSwe.LinuxSyscall.Files.Model
import LeanSwe.LinuxSyscall.Poll.Types
import LeanSwe.LinuxSyscall.TimeRand.Types
import LeanSwe.LinuxSyscall.TimeRand.Model
import LeanSwe.PostFork.Types
import LeanSwe.Process.Types
import LeanSwe.Process.Types.Internal

/-!
# Pure Healthy-Kernel Simulation Model for `LeanSwe.Process`

Spec-locked internal simulation state (`HealthySimFd`, `HealthySimState`), static VFS table
(`healthySimInodes`), projections (`toSimProcState`, `toSimFilesState`, `toSimTimeState`,
`projSimProc`, `projSimFiles`, `projSimTime`), and `SysDepsM` transition model (`healthySimDeps`)
over `LinuxSyscall.{Process,Files,TimeRand}.Model` under `LeanSwe.Process.Model.Internal`.
-/

namespace LeanSwe.Process.Model.Internal

open LeanSwe.LinuxSyscall
open LeanSwe.Process
open LeanSwe.Process.Internal (SysDepsM ProcTableState)

/-- Pipe/device descriptor state tracked by `HealthySimState`, projecting into `Files.OpenDesc`. -/
structure HealthySimFd where
  /-- `true` for read-end pipe descriptors (`rdonly`), `false` for write-end pipe descriptors (`wronly`). -/
  isReader : Bool := true
  /-- When `true` on a read pipe, non-blocking `read` yields `EAGAIN` (simulating an open writer that never writes). -/
  hangMode : Bool := false
  /-- `O_NONBLOCK` status flag (`fcntl F_SETFL`). -/
  nonblock : Bool := false
  /-- `O_APPEND` status flag (`fcntl F_SETFL`). -/
  append : Bool := false
  /-- `FD_CLOEXEC` descriptor flag (`fcntl F_SETFD`). -/
  cloexec : Bool := true
  /-- Current read cursor into `payload`. -/
  offset : Nat := 0
  /-- Queued output bytes on a readable pipe. -/
  payload : ByteArray := ByteArray.empty
  deriving DecidableEq, Inhabited

/-- Construct a simulated `Files.VNode` with aliased kernel ID for `HealthySimState`. -/
def mkSimVNode (ino : Nat) (data : Files.InodeData) (mode : Mode) (nlink : Nat := 1) : Files.VNode :=
  { data := data
    mode := mode
    nlink := nlink
    kernelId := { dev? := some 1, ino? := some (UInt64.ofNat ino), allowAlias := true }
    origin := .hostDynamic }

/-- Static 10-inode VFS table backing `HealthySimState` (`0 = /`, `1 = /bin`, `2..6 = /bin/{true,exit1,hang,bigout,sig9}`, `7 = /dev/null` sink, `8 = dynamic read stream`, `9 = hang pipe source`). -/
def healthySimInodes : List (Files.InodeId × Files.VNode) :=
  [ (0, mkSimVNode 0 (.dir { children := [("bin".toUTF8, 1)], parentIno := 0, lifecycle := .live }) 0o755 2),
    (1, mkSimVNode 1 (.dir {
          children := [
            ("true".toUTF8, 2),
            ("exit1".toUTF8, 3),
            ("hang".toUTF8, 4),
            ("bigout".toUTF8, 5),
            ("sig9".toUTF8, 6)
          ],
          parentIno := 0,
          lifecycle := .live }) 0o755 2),
    (2, mkSimVNode 2 (.reg {}) 0o755 1),
    (3, mkSimVNode 3 (.reg {}) 0o755 1),
    (4, mkSimVNode 4 (.reg {}) 0o755 1),
    (5, mkSimVNode 5 (.reg {}) 0o755 1),
    (6, mkSimVNode 6 (.reg {}) 0o755 1),
    (7, mkSimVNode 7 (.charDev .nullDev) 0o666 1),
    (8, mkSimVNode 8 (.reg {}) 0o600 1),
    (9, mkSimVNode 9 (.charDev .generic) 0o600 1) ]

/-- Map a `HealthySimFd` to its corresponding `LinuxSyscall.Files.OpenDesc` over `healthySimInodes`. -/
def toSimOpenDesc (d : HealthySimFd) : Files.OpenDesc :=
  { ino := if !d.isReader then 7 else if d.hangMode then 9 else 8
    access := if d.isReader then .rdonly else .wronly
    append := d.append
    nonblock := d.nonblock
    cloexec := d.cloexec
    pos := .byteOffset d.offset }

/-- Project `simFds` into a well-formed `LinuxSyscall.Files.FilesState` with `ambientSeccomp = false`. -/
def toSimFilesState (simFds : List (Files.HandleId × HealthySimFd)) : Files.FilesState :=
  { inodes := healthySimInodes
    fds := simFds.map (fun (k, d) => (k, toSimOpenDesc d))
    cwdPath := .bound "/".toUTF8
    rootIno := 0
    cwdIno := 0
    ambientSeccomp := false
    nextIno := 10
    nextHid := 100 }

/-- Map optional zombie status to `ProcessSysState.procs` for a single isolated child PID `100`. -/
def child100Procs (child100? : Option LinuxSyscall.Process.ZombieStatus) :
    List (UInt32 × LinuxSyscall.Process.ProcEntry) :=
  match child100? with
  | none => []
  | some z => [(100, { pgid := 100, role := .child .sigchld false, lifecycle := .zombie z })]

/-- Concrete healthy-kernel simulation state backed by `ProcessSysState`, `FilesState`, and `TimeRandState`. -/
structure HealthySimState where
  /-- Active `SysBridge` process slot table. -/
  tbl : ProcTableState Files.HandleId := {}
  /-- Tracked `ProcessSysState` descriptor table. -/
  procFds : List (LinuxSyscall.Process.HandleId × LinuxSyscall.Process.ProcessFdDesc) := []
  /-- Next `ProcessSysState` descriptor hint. -/
  procNextHid : LinuxSyscall.Process.HandleId := 10
  /-- Optional spawned child `pid = 100` zombie status. -/
  child100? : Option LinuxSyscall.Process.ZombieStatus := none
  /-- Open pipe descriptors projected into `FilesState`. -/
  simFds : List (Files.HandleId × HealthySimFd) := []
  /-- Monotonic/realtime clock and CRNG state (projected with `ambientSeccomp := false`). -/
  timeState : TimeRand.TimeRandState := TimeRand.TimeRandState.initial
  deriving Inhabited

/-- Update the active `SysBridge` process slot table in `HealthySimState`. -/
def setSimTbl (s : HealthySimState) (t : ProcTableState Files.HandleId) : HealthySimState :=
  { s with tbl := t }

/-- Project `HealthySimState` into `LinuxSyscall.Process.ProcessSysState` (`ambientSeccomp = false`). -/
def toSimProcState (s : HealthySimState) : LinuxSyscall.Process.ProcessSysState :=
  { LinuxSyscall.Process.ProcessSysState.initial with
    procs := child100Procs s.child100?
    fds := s.procFds
    nextHid := s.procNextHid }

/-- Project `HealthySimState` into `LinuxSyscall.TimeRand.TimeRandState` (`ambientSeccomp = false`). -/
def toSimTimeState (s : HealthySimState) : TimeRand.TimeRandState :=
  { s.timeState with ambientSeccomp := false }

/-- `HealthyEnv` projection for `LinuxSyscall.Process`. -/
def projSimProc (s : HealthySimState) : LinuxSyscall.Process.HealthyEnv :=
  { state := toSimProcState s, eintrBudget := 0 }

/-- `HealthyEnv` projection for `LinuxSyscall.Files`. -/
def projSimFiles (s : HealthySimState) : Files.HealthyEnv :=
  { state := toSimFilesState s.simFds, eintrBudget := 0 }

/-- `HealthyEnv` projection for `LinuxSyscall.TimeRand`. -/
def projSimTime (s : HealthySimState) : TimeRand.HealthyEnv :=
  { state := toSimTimeState s, eintrBudget := 0 }

/-- Upper bound across association-list keys in `xs` starting from `init`. -/
def maxKey {β : Type} (xs : List (Nat × β)) (init : Nat) : Nat :=
  xs.foldl (fun m x => Nat.max m x.1) init

/-- Genuine `healthyStep`-refining `SysDepsM` witness over `HealthySimState`. -/
def healthySimDeps : SysDepsM (StateM HealthySimState) Files.HandleId where
  proc :=
    { pipe2 := fun flags => modifyGet fun s =>
        if !flags.isValid then
          (.error Errno.EINVAL, s)
        else if flags.notificationPipe then
          (.error Errno.ENOPKG, s)
        else
          let base := Nat.max (maxKey s.procFds s.procNextHid) (maxKey s.simFds 10)
          let rHid : Files.HandleId := base + 1
          let wHid : Files.HandleId := base + 2
          let ps' := LinuxSyscall.Process.commitPipeFds (toSimProcState s) rHid wHid flags
          let rDesc : HealthySimFd :=
            { isReader := true, nonblock := flags.nonblock, cloexec := flags.cloexec }
          let wDesc : HealthySimFd :=
            { isReader := false, nonblock := flags.nonblock, cloexec := flags.cloexec }
          (.ok (rHid, wHid),
           { s with
             procFds := ps'.fds
             procNextHid := ps'.nextHid
             simFds := (wHid, wDesc) :: (rHid, rDesc) :: s.simFds })
      waitpid := fun pid flags => modifyGet fun s =>
        let (res, ps') := (LinuxSyscall.Process.modelOps.waitpid pid flags).run (toSimProcState s)
        (res, { s with child100? := if ps'.procs.isEmpty then none else s.child100? })
      kill := fun target sig => modifyGet fun s =>
        let (res, _) := (LinuxSyscall.Process.modelOps.kill target sig).run (toSimProcState s)
        (res, s)
      pidfd_open := fun pid flags => modifyGet fun s =>
        let (res, ps') := (LinuxSyscall.Process.modelOps.pidfd_open pid flags).run (toSimProcState s)
        (res, { s with procFds := ps'.fds, procNextHid := ps'.nextHid })
      pidfd_send_signal := fun hid sig flags => modifyGet fun s =>
        let (res, _) := (LinuxSyscall.Process.modelOps.pidfd_send_signal hid sig flags).run (toSimProcState s)
        (res, s)
      getpid := modifyGet fun s =>
        let (res, _) := LinuxSyscall.Process.modelOps.getpid.run (toSimProcState s)
        (res, s)
      getuid := modifyGet fun s =>
        let (res, _) := LinuxSyscall.Process.modelOps.getuid.run (toSimProcState s)
        (res, s) }
  files :=
    { openat := fun _ _ _ _ => pure (.error Errno.ENOENT)
      openat2 := fun _ _ _ => pure (.error Errno.ENOENT)
      close := fun hid => modifyGet fun s =>
        match Files.assocGet s.simFds hid with
        | none => (.error Errno.EBADF, s)
        | some _ => (.ok (), { s with simFds := Files.assocErase s.simFds hid })
      read := fun hid maxBytes => modifyGet fun s =>
        match Files.assocGet s.simFds hid with
        | none => (.error Errno.EBADF, s)
        | some d =>
          if !d.isReader then
            (.error Errno.EBADF, s)
          else if d.hangMode then
            if d.nonblock then (.error Errno.EAGAIN, s)
            else (.ok ByteArray.empty, s)
          else
            let cap := Nat.min maxBytes.toNat MAX_READ_BYTES.toNat
            let avail := d.payload.size - d.offset
            let takeN := Nat.min cap avail
            if takeN == 0 then
              (.ok ByteArray.empty, s)
            else
              let chunk := d.payload.extract d.offset (d.offset + takeN)
              let d' := { d with offset := d.offset + chunk.size }
              (.ok chunk, { s with simFds := Files.assocSet s.simFds hid d' })
      write := fun hid data => modifyGet fun s =>
        match Files.assocGet s.simFds hid with
        | none => (.error Errno.EBADF, s)
        | some d =>
          if d.isReader then
            (.error Errno.EBADF, s)
          else
            let n := Nat.min data.size MAX_READ_BYTES.toNat
            (.ok (UInt32.ofNat n), s)
      fstat := fun hid => modifyGet fun s =>
        let (out, _) := Files.evalModel (toSimFilesState s.simFds) (.fstat hid)
        let res := match out with
          | .statted st => .ok st
          | .err e => .error e
          | _ => .error Errno.EINVAL
        (res, s)
      fstatat := fun dir path flags => modifyGet fun s =>
        let (out, _) := Files.evalModel (toSimFilesState s.simFds) (.fstatat dir path flags)
        let res := match out with
          | .statted st => .ok st
          | .err e => .error e
          | _ => .error Errno.EINVAL
        (res, s)
      faccessat := fun dir path mask flags => modifyGet fun s =>
        let (out, _) := Files.evalModel (toSimFilesState s.simFds) (.faccessat dir path mask flags)
        let res := match out with
          | .unit => .ok ()
          | .err e => .error e
          | _ => .error Errno.EINVAL
        (res, s)
      mkdirat := fun _ _ _ => pure (.error Errno.EACCES)
      unlinkat := fun _ _ _ => pure (.error Errno.EACCES)
      renameat2 := fun _ _ _ _ _ => pure (.error Errno.EACCES)
      symlinkat := fun _ _ _ => pure (.error Errno.EACCES)
      readlinkat := fun _ _ _ => pure (.error Errno.ENOENT)
      getdents64 := fun _ _ => pure (.error Errno.EBADF)
      fchmodat := fun _ _ _ => pure (.error Errno.EACCES)
      fchmod := fun _ _ => pure (.error Errno.EBADF)
      flock := fun _ _ => pure (.error Errno.EBADF)
      fcntl := fun hid cmd => modifyGet fun s =>
        match Files.assocGet s.simFds hid with
        | none => (.error Errno.EBADF, s)
        | some d =>
          match cmd with
          | .getFl => (.ok (Files.encodeOpenStatusFlags (toSimOpenDesc d)), s)
          | .setFl nb ap =>
            (.ok 0, { s with simFds := Files.assocSet s.simFds hid { d with nonblock := nb, append := ap } })
          | .getFd => (.ok (if d.cloexec then 1 else 0), s)
          | .setFd clo =>
            (.ok 0, { s with simFds := Files.assocSet s.simFds hid { d with cloexec := clo } })
          | .addSeals _ =>
            if d.isReader then (.error Errno.EPERM, s)
            else (.error Errno.EINVAL, s)
          | .getSeals =>
            if d.isReader && !d.hangMode then (.ok 1, s)
            else (.error Errno.EINVAL, s)
      fsync := fun _ => pure (.ok ())
      getcwd := fun _ => pure (.ok "/".toUTF8)
      lseek := fun _ _ _ => pure (.error Errno.ESPIPE)
      reopenReadOnly := fun _ => pure (.error Errno.EBADF)
      dupStdio := fun _ => pure (.error Errno.EBADF) }
  poll :=
    { ppoll := fun entries timeout? => modifyGet fun s =>
        let evOf (fd : Files.HandleId) (req : Poll.PollEvents) : Poll.PollEvents :=
          match s.simFds.find? (fun p => p.1 == fd) with
          | none => { pollnval := true }
          | some (_, d) =>
            if d.isReader && d.hangMode then {}
            else { pollin := req.pollin, pollout := req.pollout }
        let revents := entries.map fun (fd, req) => evOf fd req
        let anyReady := revents.any (fun ev => ev.pollin || ev.pollout || ev.pollhup || ev.pollerr || ev.pollnval)
        if anyReady then
          (.ok revents, s)
        else
          match timeout? with
          | none => (.ok revents, s)
          | some ts =>
            let (_, ts') := (TimeRand.modelOps.clock_nanosleep .monotonic false
              { sec := ts.sec, nsec := ts.nsec }).run (toSimTimeState s)
            (.ok revents, { s with timeState := ts' })
      eventfd2 := fun _ _ => pure (.error Errno.ENOSYS) }
  timeRand :=
    { clock_gettime := fun clk => modifyGet fun s =>
        let (res, ts') := (TimeRand.modelOps.clock_gettime clk).run (toSimTimeState s)
        (res, { s with timeState := ts' })
      clock_nanosleep := fun clk abs req => modifyGet fun s =>
        let (res, ts') := (TimeRand.modelOps.clock_nanosleep clk abs req).run (toSimTimeState s)
        (res, { s with timeState := ts' })
      getrandom := fun len flags => modifyGet fun s =>
        let (res, ts') := (TimeRand.modelOps.getrandom len flags).run (toSimTimeState s)
        (res, { s with timeState := ts' }) }
  postFork :=
    { spawn := fun spec => modifyGet fun s =>
        let outReadFd : Files.HandleId :=
          match spec.stdio with
          | .redirect _ (.handle outW) _ _ => outW - 1
          | _ => 0
        let zStatus : LinuxSyscall.Process.ZombieStatus :=
          if spec.path == "/bin/sig9" then .signaled 9 false
          else if spec.path == "/bin/exit1" then .exited 1
          else .exited 0
        let simFds' := s.simFds.map fun (k, d) =>
          (k,
           if k == outReadFd && d.isReader then
             if spec.path == "/bin/hang" then
               { d with hangMode := true, offset := 0, payload := ByteArray.empty }
             else if spec.path == "/bin/bigout" then
               { d with hangMode := false, offset := 0, payload := "0123456789abcdef".toUTF8 }
             else
               { d with hangMode := false, offset := 0, payload := ByteArray.empty }
           else d)
        (.ok { pid := 100, pgid := some 100 },
         { s with
           child100? := some zStatus
           simFds := simFds' })
      spawnWithBarrier := fun _ => pure (.error { kind := .invalidInput, message := "unused" })
      releaseBarrier := fun _ => pure (.error { kind := .invalidInput, message := "unused" })
      abortBarrier := fun _ => pure (.error { kind := .invalidInput, message := "unused" }) }
  listAmbientEnv := pure (.ok #["PATH=/bin:/usr/bin".toUTF8])

end LeanSwe.Process.Model.Internal
