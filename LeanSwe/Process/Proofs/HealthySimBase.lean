import LeanSwe.LinuxSyscall.Process.Proofs
import LeanSwe.LinuxSyscall.Files.Proofs
import LeanSwe.LinuxSyscall.TimeRand.Proofs
import LeanSwe.Process.SysBridge
import LeanSwe.Process.Proofs.HealthyStep

/-!
# Genuine `healthyStep` Simulation Witness for `LeanSwe.Process.SysBridge`

Constructs `HealthySimState` and `healthySimDeps` directly over `LinuxSyscall.Process`,
`LinuxSyscall.Files` (with genuine `evalModel`-backed `fstat`, `fstatat`, and `faccessat`),
and `LinuxSyscall.TimeRand.modelOps`, and proves `RefinesHealthySysDeps` via
`refinesHealthySysDeps_of_components` (deriving `close` FD erasure from canonical
`Files.healthyStep` without `.close`/`EBUSY`).
-/

namespace LeanSwe.Process.Proofs

open LeanSwe.LinuxSyscall
open LeanSwe.Process.SysBridge

local instance : Repr ByteArray where
  reprPrec b _ := s!"ByteArray(len={b.size})"

@[simp] private theorem stateM_modifyGet_run {S α : Type} (f : S → α × S) (s : S) :
    (modifyGet f : StateM S α).run s = f s := rfl

@[simp] private theorem stateM_pure_run {S α : Type} (a : α) (s : S) :
    (pure a : StateM S α).run s = (a, s) := rfl

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
  deriving Repr, DecidableEq, Inhabited

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

private theorem le_foldl_max {β : Type} (xs : List (Nat × β)) (init : Nat) :
    init ≤ maxKey xs init := by
  unfold maxKey
  induction xs generalizing init with
  | nil => exact Nat.le_refl _
  | cons hd tl ih =>
    simp only [List.foldl_cons]
    exact Nat.le_trans (Nat.le_max_left init hd.1) (ih (Nat.max init hd.1))

/-- Every key present in `xs.map Prod.fst` is bounded above by `maxKey xs init`. -/
theorem mem_fst_le_maxKey {β : Type} (xs : List (Nat × β)) (init k : Nat)
    (hMem : k ∈ xs.map Prod.fst) :
    k ≤ maxKey xs init := by
  unfold maxKey
  induction xs generalizing init with
  | nil => simp at hMem
  | cons hd tl ih =>
    rcases hd with ⟨k', v⟩
    simp only [List.map_cons, List.mem_cons] at hMem
    simp only [List.foldl_cons]
    rcases hMem with rfl | hRest
    · exact Nat.le_trans (Nat.le_max_right init k) (le_foldl_max tl (Nat.max init k))
    · exact ih (Nat.max init k') hRest

/-- Genuine `healthyStep`-refining `SysDepsM` witness over `HealthySimState`. -/
def healthySimDeps : SysDepsM (StateM HealthySimState) Files.HandleId where
  proc :=
    { pipe2 := fun flags => modifyGet fun s =>
        if !flags.isValid then
          (.error Errno.EINVAL, s)
        else if flags.notificationPipe then
          (.error LinuxSyscall.Process.errnoENOPKG, s)
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


private theorem proc_assocGet_none_of_gt_maxKey {β : Type} (xs : List (Nat × β)) (init k : Nat)
    (hGt : maxKey xs init < k) :
    LinuxSyscall.Process.assocGet xs k = none := by
  induction xs with
  | nil => rfl
  | cons hd tl ih =>
    rcases hd with ⟨k', v⟩
    have hkLe : k' ≤ maxKey ((k', v) :: tl) init :=
      mem_fst_le_maxKey ((k', v) :: tl) init k' List.mem_cons_self
    have hNe : (k' == k) = false := beq_false_of_ne (by omega)
    simp only [LinuxSyscall.Process.assocGet, hNe, Bool.false_eq_true, ↓reduceIte]
    apply ih
    have hTlLe : maxKey tl init ≤ maxKey ((k', v) :: tl) init := by
      unfold maxKey
      simp only [List.foldl_cons]
      suffices ∀ (ys : List (Nat × β)) (a b : Nat), a ≤ b →
          ys.foldl (fun m x => Nat.max m x.1) a ≤ ys.foldl (fun m x => Nat.max m x.1) b from
        this tl init (Nat.max init k') (Nat.le_max_left _ _)
      intro ys
      induction ys with
      | nil => intro a b hab; exact hab
      | cons y ys' ihy =>
        intro a b hab
        simp only [List.foldl_cons]
        exact ihy (Nat.max a y.1) (Nat.max b y.1)
          (Nat.max_le.mpr ⟨Nat.le_trans hab (Nat.le_max_left _ _), Nat.le_max_right _ _⟩)
    omega

private def child100Entry (z : LinuxSyscall.Process.ZombieStatus) : LinuxSyscall.Process.ProcEntry :=
  { pgid := 100, role := .child .sigchld false, lifecycle := .zombie z }

private theorem deliverSignalToEntry_zombie
    (ps : LinuxSyscall.Process.ProcessSysState) (pid : UInt32) (sig : LinuxSyscall.Process.Signal)
    (z : LinuxSyscall.Process.ZombieStatus) (ts : Bool)
    (a c g arb : Std.TreeSet UInt32 compare) :
    LinuxSyscall.Process.deliverSignalToEntry ps pid sig (child100Entry z) ts a c g arb =
      child100Entry z := by
  unfold LinuxSyscall.Process.deliverSignalToEntry
  dsimp only [child100Entry]
  simp only [Bool.false_and, Bool.false_eq_true, ↓reduceIte, ite_self]

private theorem reapThreadGroup_child100
    (ps : LinuxSyscall.Process.ProcessSysState) (z : LinuxSyscall.Process.ZombieStatus)
    (hProcs : ps.procs = [(100, child100Entry z)]) :
    (LinuxSyscall.Process.reapThreadGroup ps 100).procs = [] := by
  unfold LinuxSyscall.Process.reapThreadGroup
  rw [hProcs]
  cases z <;> rfl

private theorem evalModelWaitpid_child100
    (s : HealthySimState) (pid : Int32) (flags : LinuxSyscall.Process.WaitFlags) :
    let ps := toSimProcState s
    let (res, ps') := LinuxSyscall.Process.evalModelWaitpid ps pid flags
    (∀ e, res = .error e → Errno.isCriticalOsErrno e = false ∧ e ≠ Errno.EINTR) ∧
    toSimProcState { s with child100? := if ps'.procs.isEmpty then none else s.child100? } = ps' := by
  dsimp only
  cases hCh : s.child100? with
  | none =>
    have hSame : toSimProcState { s with child100? := none } = toSimProcState s := by
      simp only [toSimProcState, hCh]
    unfold LinuxSyscall.Process.evalModelWaitpid
    have hPsProcs : (toSimProcState s).procs = [] := by simp [toSimProcState, child100Procs, hCh]
    split
    · exact ⟨(fun e h => by injection h with hE; subst hE; decide),
        by simp [toSimProcState, child100Procs, hCh]⟩
    · split
      · exact ⟨(fun e h => by injection h with hE; subst hE; decide),
          by simp [toSimProcState, child100Procs, hCh]⟩
      · have hMatch : LinuxSyscall.Process.matchingUnreapedChildren (toSimProcState s) pid flags = [] := by
          simp [LinuxSyscall.Process.matchingUnreapedChildren,
            LinuxSyscall.Process.matchingUnreapedChildrenGo, hPsProcs]
        rw [hMatch]
        exact ⟨(fun e h => by injection h with hE; subst hE; decide),
          by simp [toSimProcState, child100Procs, hCh]⟩
  | some z =>
    have hPsProcs : (toSimProcState s).procs = [(100, child100Entry z)] := by
      simp [toSimProcState, child100Procs, child100Entry, hCh]
    unfold LinuxSyscall.Process.evalModelWaitpid
    split
    · exact ⟨(fun e h => by injection h with hE; subst hE; decide),
        by simp [toSimProcState, child100Procs, hCh]⟩
    · split
      · exact ⟨(fun e h => by injection h with hE; subst hE; decide),
          by simp [toSimProcState, child100Procs, hCh]⟩
      · have hM := LinuxSyscall.Process.matchingUnreapedChildren (toSimProcState s) pid flags
        have hCases : LinuxSyscall.Process.matchingUnreapedChildren (toSimProcState s) pid flags = [] ∨
            LinuxSyscall.Process.matchingUnreapedChildren (toSimProcState s) pid flags = [(100, child100Entry z)] := by
          unfold LinuxSyscall.Process.matchingUnreapedChildren
            LinuxSyscall.Process.matchingUnreapedChildrenGo
          rw [hPsProcs]
          have hNotSeen : ({} : Std.TreeSet UInt32 compare).contains 100 = false := rfl
          dsimp only
          simp only [hNotSeen, Bool.false_eq_true, ↓reduceIte]
          split
          · exact Or.inr rfl
          · exact Or.inl rfl
        rcases hCases with hEmpty | hOne
        · rw [hEmpty]
          dsimp only [List.isEmpty_nil, ↓reduceIte]
          exact ⟨(fun e h => by injection h with hE; subst hE; decide),
            by simp [toSimProcState, child100Procs, hCh]⟩
        · have hPick : LinuxSyscall.Process.pickImmediateWaitResult (toSimProcState s).procs
              [(100, child100Entry z)] flags = some (z.toWaitResult 100) := by
            unfold LinuxSyscall.Process.pickImmediateWaitResult
              LinuxSyscall.Process.pickImmediateWaitResultSet
              LinuxSyscall.Process.pickImmediateWaitStep
            cases z <;> rfl
          simp only [hOne, List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte, hPick]
          refine ⟨(fun _ h => by cases h), ?_⟩
          cases hStep : LinuxSyscall.Process.allowedStepWaitResult (toSimProcState s)
              [(100, child100Entry z)] flags (z.toWaitResult 100) with
          | none =>
            simp only [Option.getD, List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte,
              toSimProcState, child100Procs, hCh]
          | some psNext =>
            have hEqReap : psNext = LinuxSyscall.Process.reapThreadGroup (toSimProcState s) 100 := by
              cases z with
              | exited zc =>
                change LinuxSyscall.Process.waitChildStep (toSimProcState s) 100
                  (child100Entry (.exited zc)) flags (.exited 100 zc) = some psNext at hStep
                simp only [LinuxSyscall.Process.waitChildStep, child100Entry,
                  bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, beq_self_eq_true,
                  Option.some.injEq] at hStep
                exact hStep.symm
              | signaled zs zcore =>
                change LinuxSyscall.Process.waitChildStep (toSimProcState s) 100
                  (child100Entry (.signaled zs zcore)) flags
                  (.signaled 100 (LinuxSyscall.Process.normalizeWaitSig zs) zcore) = some psNext at hStep
                unfold LinuxSyscall.Process.waitChildStep child100Entry at hStep
                dsimp only at hStep
                split at hStep
                · cases hStep
                · split at hStep
                  · injection hStep with hE; exact hE.symm
                  · cases hStep
            subst hEqReap
            have hRE : (LinuxSyscall.Process.reapThreadGroup (toSimProcState s) 100).procs = [] :=
              reapThreadGroup_child100 (toSimProcState s) z hPsProcs
            simp only [Option.getD, hRE, List.isEmpty_nil, ↓reduceIte]
            unfold LinuxSyscall.Process.reapThreadGroup
            rw [show LinuxSyscall.Process.markThreadGroupLifecycleGo 100 .reaped (toSimProcState s).procs {} [] = [] from hRE]
            rfl

private theorem evalKill_child100
    (ps : LinuxSyscall.Process.ProcessSysState) (target : Int32) (sig : LinuxSyscall.Process.Signal)
    (hProcs : ps.procs = [] ∨ ∃ z, ps.procs = [(100, child100Entry z)]) :
    (∀ e, LinuxSyscall.Process.evalKill ps target sig = .error e →
      Errno.isCriticalOsErrno e = false ∧ e ≠ Errno.EINTR ∧
      (e = Errno.ESRCH → LinuxSyscall.Process.esrchKillNext ps target = ps)) ∧
    (∀ st, LinuxSyscall.Process.evalKill ps target sig = .ok st → st = ps) := by
  have hReapSingle : ∀ pid, LinuxSyscall.Process.reapExitDeadSingleTarget ps pid = ps := by
    intro pid
    unfold LinuxSyscall.Process.reapExitDeadSingleTarget
    dsimp only
    split
    · rfl
    · rcases hProcs with hNil | ⟨z, hOne⟩
      · rw [hNil]; rfl
      · rw [hOne]
        by_cases hp : (100 == pid) = true
        · simp only [LinuxSyscall.Process.assocGet, hp, ↓reduceIte, child100Entry]; rfl
        · have hpF : (100 == pid) = false := Bool.eq_false_iff.mpr hp
          simp only [LinuxSyscall.Process.assocGet, hpF, Bool.false_eq_true, ↓reduceIte]
  have hNonLead : ∀ pid, LinuxSyscall.Process.nonLeaderEsrch? ps pid = none := by
    intro pid
    unfold LinuxSyscall.Process.nonLeaderEsrch?
    dsimp only
    split
    · rfl
    · rcases hProcs with hNil | ⟨z, hOne⟩
      · rw [hNil]; rfl
      · rw [hOne]
        by_cases hp : (100 == pid) = true
        · simp only [LinuxSyscall.Process.assocGet, hp, ↓reduceIte, child100Entry]
        · have hpF : (100 == pid) = false := Bool.eq_false_iff.mpr hp
          simp only [LinuxSyscall.Process.assocGet, hpF, Bool.false_eq_true, ↓reduceIte]
  have hReapGrp : ∀ pred, LinuxSyscall.Process.reapExitDeadGroup ps pred = ps := by
    intro pred
    unfold LinuxSyscall.Process.reapExitDeadGroup LinuxSyscall.Process.reapActiveLeadersWhere
    rcases hProcs with hNil | ⟨z, hOne⟩
    · rw [hNil]; rfl
    · rw [hOne]
      have hNotDead : ((child100Entry z).lifecycle == .exitDead) = false := by cases z <;> rfl
      unfold LinuxSyscall.Process.collectActivePidSetGo
      dsimp only
      have hNS : ({} : Std.TreeSet UInt32 compare).contains 100 = false := rfl
      simp only [hNS, hNotDead, Bool.and_false, Bool.false_eq_true, ↓reduceIte]
      rfl
  have hEsrch : LinuxSyscall.Process.esrchKillNext ps target = ps := by
    unfold LinuxSyscall.Process.esrchKillNext
    split
    · split
      · dsimp only; rw [hReapSingle, hNonLead]; rfl
      · split
        · exact hReapGrp _
        · split
          · exact hReapGrp _
          · rfl
    · rfl
  have hApply : ∀ pred, LinuxSyscall.Process.applySignalWhere ps ps.procs pred sig = ps.procs := by
    intro pred
    unfold LinuxSyscall.Process.applySignalWhere
    rcases hProcs with hNil | ⟨z, hOne⟩
    · rw [hNil]; rfl
    · rw [hOne]
      unfold LinuxSyscall.Process.applySignalWhereGo
      have hNS : ({} : Std.TreeSet UInt32 compare).contains 100 = false := rfl
      simp only [hNS, Bool.false_eq_true, ↓reduceIte]
      split
      · simp only [deliverSignalToEntry_zombie]; rfl
      · rfl
  have hGroup : ∀ pgid,
      (∀ e, LinuxSyscall.Process.evalKillProcessGroup ps pgid sig = .error e →
        Errno.isCriticalOsErrno e = false ∧ e ≠ Errno.EINTR) ∧
      (∀ st, LinuxSyscall.Process.evalKillProcessGroup ps pgid sig = .ok st → st = ps) := by
    intro pgid
    unfold LinuxSyscall.Process.evalKillProcessGroup
    dsimp only
    split
    · exact ⟨(fun e h => by injection h with hE; subst hE; decide), (fun _ h => by cases h)⟩
    · split
      · exact ⟨(fun e h => by injection h with hE; subst hE; decide), (fun _ h => by cases h)⟩
      · split
        · exact ⟨(fun e h => by injection h with hE; subst hE; decide), (fun _ h => by cases h)⟩
        · split
          · exact ⟨(fun e h => by injection h with hE; subst hE; decide), (fun _ h => by cases h)⟩
          · refine ⟨(fun _ h => by cases h), fun st hOk => ?_⟩
            injection hOk with hEq; subst hEq
            rw [hApply]
  have hSingle : ∀ tpid,
      (∀ e, LinuxSyscall.Process.deliverSignalToTarget ps tpid sig false = .error e →
        Errno.isCriticalOsErrno e = false ∧ e ≠ Errno.EINTR) ∧
      (∀ st, LinuxSyscall.Process.deliverSignalToTarget ps tpid sig false = .ok st → st = ps) := by
    intro tpid
    unfold LinuxSyscall.Process.deliverSignalToTarget
    dsimp only
    split
    · exact ⟨(fun e h => by injection h with hE; subst hE; decide), (fun _ h => by cases h)⟩
    · split
      · split
        · exact ⟨(fun e h => by injection h with hE; subst hE; decide), (fun _ h => by cases h)⟩
        · exact ⟨(fun _ h => by cases h), fun st h => by injection h with hE; exact hE.symm⟩
      · rcases hProcs with hNil | ⟨z, hOne⟩
        · rw [hNil]; dsimp only [LinuxSyscall.Process.assocGet]
          exact ⟨(fun e h => by injection h with hE; subst hE; decide), (fun _ h => by cases h)⟩
        · rw [hOne]
          by_cases hEqPid : (100 == tpid) = true
          · have hT : tpid = 100 := (beq_iff_eq.mp hEqPid).symm
            subst hT
            simp only [LinuxSyscall.Process.assocGet, beq_self_eq_true, ↓reduceIte, child100Entry]
            split
            · exact ⟨(fun e h => by injection h with hE; subst hE; decide), (fun _ h => by cases h)⟩
            · split
              · exact ⟨(fun e h => by injection h with hE; subst hE; decide), (fun _ h => by cases h)⟩
              · split
                · exact ⟨(fun e h => by injection h with hE; subst hE; decide), (fun _ h => by cases h)⟩
                · refine ⟨(fun _ h => by cases h), fun st hOk => ?_⟩
                  injection hOk with hEq; subst hEq
                  cases ps with
                  | mk a b c d e f g h i j k l =>
                    simp only at hOne ⊢
                    subst hOne
                    dsimp only [LinuxSyscall.Process.assocSet, LinuxSyscall.Process.assocSetAux]
                    have hDel := deliverSignalToEntry_zombie
                      { selfPid := a, selfPgid := b, selfUid := c, sigchld := d,
                        ambientIgnoredSigs := e, closedPidNamespace := f,
                        ambientSeccomp := g, watchQueueSupported := h,
                        pidfdThreadSupported := i, procs := [(100, child100Entry z)],
                        fds := k, nextHid := l }
                      100 sig z false
                      (LinuxSyscall.Process.collectActiveSubthreadTgids [(100, child100Entry z)])
                      (LinuxSyscall.Process.collectControlledSubthreadTgids [(100, child100Entry z)])
                      (LinuxSyscall.Process.collectGroupExitSubthreadTgids [(100, child100Entry z)])
                      (LinuxSyscall.Process.collectArbitraryRunningSubthreadTgids [(100, child100Entry z)])
                    simp only [child100Entry] at hDel ⊢
                    rw [hDel]
                    rfl
          · have hNePid : (100 == tpid) = false := Bool.eq_false_iff.mpr hEqPid
            simp only [LinuxSyscall.Process.assocGet, hNePid, Bool.false_eq_true, ↓reduceIte]
            exact ⟨(fun e h => by injection h with hE; subst hE; decide), (fun _ h => by cases h)⟩
  unfold LinuxSyscall.Process.evalKill
  refine ⟨?_, ?_⟩
  · intro e hErr
    split at hErr
    · injection hErr with hE; subst hE; exact ⟨by decide, by decide, fun _ => hEsrch⟩
    · split at hErr
      · injection hErr with hE; subst hE; exact ⟨by decide, by decide, fun _ => hEsrch⟩
      · split at hErr
        · have h := (hSingle target.toUInt32).1 e hErr; exact ⟨h.1, h.2, fun _ => hEsrch⟩
        · split at hErr
          · have h := (hGroup _).1 e hErr; exact ⟨h.1, h.2, fun _ => hEsrch⟩
          · split at hErr
            · dsimp only at hErr
              split at hErr
              · injection hErr with hE; subst hE; exact ⟨by decide, by decide, fun _ => hEsrch⟩
              · split at hErr
                · injection hErr with hE; subst hE; exact ⟨by decide, by decide, fun _ => hEsrch⟩
                · cases hErr
            · have h := (hGroup _).1 e hErr; exact ⟨h.1, h.2, fun _ => hEsrch⟩
  · intro st hOk
    split at hOk
    · cases hOk
    · split at hOk
      · cases hOk
      · split at hOk
        · exact (hSingle target.toUInt32).2 st hOk
        · split at hOk
          · exact (hGroup _).2 st hOk
          · split at hOk
            · dsimp only at hOk
              split at hOk
              · cases hOk
              · split at hOk
                · cases hOk
                · injection hOk with hEq; subst hEq; rw [hApply]
            · exact (hGroup _).2 st hOk

/-- `healthySimDeps.proc` refines canonical `LinuxSyscall.Process.healthyStep` via `projSimProc`. -/
theorem healthySimDeps_proc_refinesHealthy :
    RefinesHealthyProcOpsAt projSimProc id healthySimDeps.proc where
  pipe2_healthy s flags _ := by
    dsimp only [healthySimDeps, stateM_modifyGet_run, projSimProc, id]
    by_cases hVal : flags.isValid = true
    · by_cases hNotif : flags.notificationPipe = true
      · simp only [hVal, Bool.not_true, Bool.false_eq_true, ↓reduceIte, hNotif,
          Except.map, LinuxSyscall.Process.outcomeOfPiped]
        unfold LinuxSyscall.Process.healthyStep LinuxSyscall.Process.HealthyEnv.wf
          LinuxSyscall.Process.isCriticalFault LinuxSyscall.Process.isEintrOutcome
          LinuxSyscall.Process.allowedStep LinuxSyscall.Process.validateReqBeforeKernel
        have hCrit65 : Errno.isCriticalOsErrno LinuxSyscall.Process.errnoENOPKG = false := by decide
        have hNeEi65 : (LinuxSyscall.Process.errnoENOPKG == Errno.EINTR) = false := by decide
        simp [toSimProcState, LinuxSyscall.Process.ProcessSysState.initial, hVal, hNotif,
          hCrit65, hNeEi65]
      · have hNotifF : flags.notificationPipe = false := Bool.eq_false_iff.mpr hNotif
        simp only [hVal, Bool.not_true, Bool.false_eq_true, ↓reduceIte, hNotifF,
          Except.map, LinuxSyscall.Process.outcomeOfPiped]
        let base := Nat.max (maxKey s.procFds s.procNextHid) (maxKey s.simFds 10)
        have hLeB : maxKey s.procFds s.procNextHid ≤ base := Nat.le_max_left _ _
        have hNoneR : LinuxSyscall.Process.assocGet s.procFds (base + 1) = none :=
          proc_assocGet_none_of_gt_maxKey s.procFds s.procNextHid (base + 1) (by omega)
        have hNoneW : LinuxSyscall.Process.assocGet s.procFds (base + 2) = none :=
          proc_assocGet_none_of_gt_maxKey s.procFds s.procNextHid (base + 2) (by omega)
        have hNe : ((base + 1 : Files.HandleId) != (base + 2 : Files.HandleId)) = true :=
          bne_iff_ne.mpr (by omega)
        unfold LinuxSyscall.Process.healthyStep LinuxSyscall.Process.HealthyEnv.wf
          LinuxSyscall.Process.isCriticalFault LinuxSyscall.Process.isEintrOutcome
          LinuxSyscall.Process.allowedStep LinuxSyscall.Process.validateReqBeforeKernel
        dsimp only
        have hSec : (toSimProcState s).ambientSeccomp = false := rfl
        have hFds : (toSimProcState s).fds = s.procFds := rfl
        rw [hSec]
        simp only [Bool.not_false, Bool.not_true, Bool.or_self, Bool.false_eq_true, ↓reduceIte]
        rw [hVal, hNotifF, hFds, hNe, hNoneR, hNoneW]
        simp [LinuxSyscall.Process.commitPipeFds, toSimProcState, LinuxSyscall.Process.ProcessSysState.initial]
    · have hValF : flags.isValid = false := Bool.eq_false_iff.mpr hVal
      simp only [hValF, Bool.not_false, ↓reduceIte, Except.map, LinuxSyscall.Process.outcomeOfPiped]
      unfold LinuxSyscall.Process.healthyStep LinuxSyscall.Process.HealthyEnv.wf
        LinuxSyscall.Process.isCriticalFault LinuxSyscall.Process.isEintrOutcome
        LinuxSyscall.Process.allowedStep LinuxSyscall.Process.validateReqBeforeKernel
      simp [toSimProcState, LinuxSyscall.Process.ProcessSysState.initial, hValF,
        Errno.isCriticalOsErrno, Errno.EINVAL, Errno.EINTR, Errno.ENOMEM, Errno.EIO, Errno.ENFILE]
  waitpid_healthy s pid flags _ := by
    have hSound := LinuxSyscall.Process.modelOps_execProcessReq_sound (toSimProcState s) (.waitpid pid flags)
    have hPres := evalModelWaitpid_child100 s pid flags
    dsimp only [healthySimDeps, stateM_modifyGet_run, projSimProc]
    have hWaitRun : (LinuxSyscall.Process.modelOps.waitpid pid flags).run (toSimProcState s) =
        LinuxSyscall.Process.evalModelWaitpid (toSimProcState s) pid flags := by
      dsimp only [LinuxSyscall.Process.modelOps, Bind.bind, Pure.pure, StateT.bind, StateT.pure, StateT.run,
        get, MonadState.get, getThe, MonadStateOf.get, StateT.get,
        set, MonadState.set, MonadStateOf.set, StateT.set]
    rw [hWaitRun]
    dsimp only at hPres
    cases hEv : LinuxSyscall.Process.evalModelWaitpid (toSimProcState s) pid flags with
    | mk res ps' =>
      have hExecEv : (LinuxSyscall.Process.execProcessReq LinuxSyscall.Process.modelOps (.waitpid pid flags)).run
          (toSimProcState s) =
          (match res with | .ok wr => .waited wr | .error e => .err e, ps') := by
        have hWaitFn : LinuxSyscall.Process.modelOps.waitpid pid flags (toSimProcState s) = (res, ps') :=
          hWaitRun.trans hEv
        unfold LinuxSyscall.Process.execProcessReq StateT.run
        dsimp only [Bind.bind, StateT.bind]
        rw [hWaitFn]
        cases res <;> rfl
      rw [hExecEv] at hSound
      rw [hEv] at hPres
      obtain ⟨hNoCrit, hStEq⟩ := hPres
      dsimp only at hSound ⊢
      unfold LinuxSyscall.Process.healthyStep LinuxSyscall.Process.HealthyEnv.wf
        LinuxSyscall.Process.isCriticalFault LinuxSyscall.Process.isEintrOutcome
      have hSec : (toSimProcState s).ambientSeccomp = false := rfl
      cases res with
      | ok wr =>
        dsimp only [LinuxSyscall.Process.outcomeOfWaited] at hSound ⊢
        rw [hSec, hSound, hStEq]
        rfl
      | error e =>
        obtain ⟨hCrit, hNeEi⟩ := hNoCrit e rfl
        dsimp only [LinuxSyscall.Process.outcomeOfWaited] at hSound hStEq ⊢
        simp only [hSec, hCrit, hSound, beq_false_of_ne hNeEi, hStEq,
          Bool.not_false, Bool.not_true, Bool.or_self, Bool.false_eq_true, ↓reduceIte]
  kill_healthy s target sig _ := by
    have hSound := LinuxSyscall.Process.modelOps_execProcessReq_sound (toSimProcState s) (.kill target sig)
    have hProcsShape : (toSimProcState s).procs = [] ∨ ∃ z, (toSimProcState s).procs = [(100, child100Entry z)] := by
      cases hCh : s.child100? with
      | none => exact Or.inl (by simp [toSimProcState, child100Procs, hCh])
      | some z => exact Or.inr ⟨z, by simp [toSimProcState, child100Procs, child100Entry, hCh]⟩
    have hExecKill : (LinuxSyscall.Process.execProcessReq LinuxSyscall.Process.modelOps (.kill target sig)).run
        (toSimProcState s) =
        (match ((LinuxSyscall.Process.modelOps.kill target sig).run (toSimProcState s)).1 with
         | .ok () => .unit | .error e => .err e,
         ((LinuxSyscall.Process.modelOps.kill target sig).run (toSimProcState s)).2) := by
      unfold LinuxSyscall.Process.execProcessReq StateT.run
      dsimp only [Bind.bind, StateT.bind]
      cases LinuxSyscall.Process.modelOps.kill target sig (toSimProcState s) with
      | mk a _ => cases a <;> rfl
    rw [hExecKill] at hSound
    dsimp only at hSound
    dsimp only [healthySimDeps, stateM_modifyGet_run, projSimProc]
    obtain ⟨res, ps', hEvRun⟩ : ∃ res ps',
        (LinuxSyscall.Process.modelOps.kill target sig).run (toSimProcState s) = (res, ps') :=
      ⟨_, _, rfl⟩
    rw [hEvRun] at hSound ⊢
    have hSound2 : LinuxSyscall.Process.allowedStep (toSimProcState s) (.kill target sig)
        (match res with | .ok () => .unit | .error e => .err e) = some ps' := by
      cases res <;> exact hSound
    have hRun : LinuxSyscall.Process.modelOps.kill target sig (toSimProcState s) = (res, ps') := hEvRun
    dsimp only
    unfold LinuxSyscall.Process.healthyStep LinuxSyscall.Process.HealthyEnv.wf
      LinuxSyscall.Process.isCriticalFault LinuxSyscall.Process.isEintrOutcome
    have hSec : (toSimProcState s).ambientSeccomp = false := rfl
    have hKillUnf : LinuxSyscall.Process.modelOps.kill target sig (toSimProcState s) =
        match LinuxSyscall.Process.validateReqBeforeKernel (toSimProcState s) (.kill target sig) with
        | some e => (.error e, toSimProcState s)
        | none =>
          match LinuxSyscall.Process.evalKill (toSimProcState s) target sig with
          | .ok st => (.ok (), st)
          | .error e =>
            (.error e,
             if e == Errno.ESRCH then LinuxSyscall.Process.esrchKillNext (toSimProcState s) target
             else toSimProcState s) := by
      unfold LinuxSyscall.Process.modelOps
      dsimp only [Bind.bind, Pure.pure, StateT.bind, StateT.pure,
        get, MonadState.get, getThe, MonadStateOf.get, StateT.get,
        set, MonadState.set, MonadStateOf.set, StateT.set]
      cases LinuxSyscall.Process.validateReqBeforeKernel (toSimProcState s) (.kill target sig) with
      | some _ => rfl
      | none =>
        dsimp only
        cases LinuxSyscall.Process.evalKill (toSimProcState s) target sig with
        | ok _ => rfl
        | error e =>
          cases (e == Errno.ESRCH) <;> rfl
    rw [hKillUnf] at hRun
    cases hPre : LinuxSyscall.Process.validateReqBeforeKernel (toSimProcState s) (.kill target sig) with
    | some preE =>
      rw [hPre] at hRun
      injection hRun with hR hS
      subst hR hS
      have hPreEq : preE = Errno.EINVAL := by
        unfold LinuxSyscall.Process.validateReqBeforeKernel at hPre
        dsimp only at hPre
        split at hPre
        · injection hPre with hEq; exact hEq.symm
        · cases hPre
      subst hPreEq
      dsimp only [LinuxSyscall.Process.outcomeOfUnit] at hSound2 ⊢
      have hCrit22 : Errno.isCriticalOsErrno Errno.EINVAL = false := by decide
      have hNeEi22 : (Errno.EINVAL == Errno.EINTR) = false := by decide
      simp [hSec, hCrit22, hSound2, hNeEi22]
    | none =>
      rw [hPre] at hRun
      dsimp only at hRun
      obtain ⟨hKillErr, hKillOk⟩ := evalKill_child100 (toSimProcState s) target sig hProcsShape
      cases hEv : LinuxSyscall.Process.evalKill (toSimProcState s) target sig with
      | ok st =>
        rw [hEv] at hRun
        injection hRun with hR hS
        subst hR hS
        have hEq := hKillOk st hEv
        subst hEq
        dsimp only [LinuxSyscall.Process.outcomeOfUnit] at hSound2 ⊢
        rw [hSec, hSound2]
        rfl
      | error e =>
        rw [hEv] at hRun
        injection hRun with hR hS
        subst hR
        obtain ⟨hCrit, hNeEi, hEsrchEq⟩ := hKillErr e hEv
        have hNextEq : ps' = toSimProcState s := by
          rw [← hS]
          split
          · next hIs => exact hEsrchEq (beq_iff_eq.mp hIs)
          · rfl
        subst hNextEq
        dsimp only [LinuxSyscall.Process.outcomeOfUnit] at hSound2 ⊢
        simp [hSec, hCrit, hSound2, beq_false_of_ne hNeEi]

end LeanSwe.Process.Proofs
