import Std.Data.HashMap
import LeanSwe.LinuxSyscall.Common.Types
import LeanSwe.LinuxSyscall.Files.Interface
import LeanSwe.LinuxSyscall.Net.Interface
import LeanSwe.LinuxSyscall.Poll.Interface
import LeanSwe.LinuxSyscall.Process.Interface
import LeanSwe.LinuxSyscall.Sandbox.Interface
import LeanSwe.LinuxSyscall.TimeRand.Interface
import LeanSwe.LinuxSyscall.Passwd.Interface
import LeanSwe.PostFork.Interface
import LeanSwe.EnvVars.Raw.Interface
import LeanSwe.ProcessSandbox.Raw.Model.Refines
import LeanSwe.ProcessSandbox.Raw.SysBridge.Forwarder

namespace LeanSwe.ProcessSandbox.Raw.SysBridge

open LeanSwe.LinuxSyscall
open LeanSwe.ProcessSandbox.Raw

/-- Mutable host runtime state holding the active `Model.RawTableState` plus `Nat`-keyed `RawFd` and `IoForwarderHandle` maps. -/
structure IoHostState where
  /-- Public handle-table state mirrored by `Model.RawHostCapM`. -/
  table : Model.RawTableState := {}
  /-- Next fresh positive `Nat` descriptor key. -/
  nextFdId : Nat := 1
  /-- Active `Nat -> RawFd` descriptor map. -/
  fds : Std.HashMap Nat RawFd := {}
  /-- Next fresh positive `Nat` forwarder task key. -/
  nextFwdId : Nat := 1
  /-- Active `Nat -> IoForwarderHandle` task map. -/
  fwds : Std.HashMap Nat Forwarder.IoForwarderHandle := {}

instance : Inhabited IoHostState := ⟨{}⟩

/-- Map any uncaught `IO.Error` to a positive Linux `Errno` fallback. -/
def ioErrorToErrno : IO.Error → Errno
  | .noFileOrDirectory _ c _ | .noSuchThing _ c _ => if c == 0 then Errno.ENOENT else c
  | .permissionDenied _ c _ => if c == 0 then Errno.EACCES else c
  | .invalidArgument _ c _ => if c == 0 then Errno.EINVAL else c
  | .unsupportedOperation c _ | .unsatisfiedConstraints c _ => if c == 0 then Errno.ENOSYS else c
  | .resourceExhausted _ c _ => if c == 0 then Errno.ENOMEM else c
  | .interrupted _ c _ => if c == 0 then Errno.EINTR else c
  | .alreadyExists _ c _ => if c == 0 then Errno.EEXIST else c
  | .resourceBusy c _ => if c == 0 then Errno.EBUSY else c
  | .timeExpired c _ => if c == 0 then Errno.ETIMEDOUT else c
  | _ => Errno.EIO

/-- Execute `act : IO α`, converting any thrown `IO.Error` via `fallback` in `BaseIO` so the resulting `IO` action never throws. -/
def catchIoTotal {α : Type} (act : IO α) (fallback : IO.Error → α) : IO α :=
  (act.catchExceptions fun err => pure (fallback err) : BaseIO α)

/-- Execute `act : IO (Except Errno α)`, converting any thrown `IO.Error` into `.error (ioErrorToErrno err)`. -/
def catchErrno {α : Type} (act : IO (Except Errno α)) : IO (Except Errno α) :=
  catchIoTotal act (fun err => .error (ioErrorToErrno err))

/-- Execute `act : IO (Except PostForkError α)`, converting any thrown `IO.Error` into `.error` with `.sysError`. -/
def catchPf {α : Type} (act : IO (Except PostFork.PostForkError α)) :
    IO (Except PostFork.PostForkError α) :=
  catchIoTotal act fun err =>
    .error { kind := .sysError, errno := some (ioErrorToErrno err), message := toString err }

private def allocFd (ref : IO.Ref IoHostState) (rfd : RawFd) : IO Nat :=
  (ref.modifyGet fun st =>
    let id := st.nextFdId
    (id, { st with nextFdId := id + 1, fds := st.fds.insert id rfd }) : BaseIO _)

private def allocFdPair (ref : IO.Ref IoHostState) (p : RawFd × RawFd) : IO (Nat × Nat) :=
  (ref.modifyGet fun st =>
    let i0 := st.nextFdId
    let i1 := i0 + 1
    ((i0, i1), { st with nextFdId := i1 + 1, fds := (st.fds.insert i0 p.1).insert i1 p.2 }) : BaseIO _)

private def allocFdArray (ref : IO.Ref IoHostState) (rfds : Array RawFd) : IO (Array Nat) :=
  (ref.modifyGet fun st =>
    let (ids, nextId, fds') := rfds.foldl
      (fun (acc, nid, mp) rfd => (acc.push nid, nid + 1, mp.insert nid rfd))
      (#[], st.nextFdId, st.fds)
    (ids, { st with nextFdId := nextId, fds := fds' }) : BaseIO _)

private def takeFd (ref : IO.Ref IoHostState) (id : Nat) : IO (Option RawFd) :=
  (ref.modifyGet fun st =>
    (st.fds.get? id, { st with fds := st.fds.erase id }) : BaseIO _)

private def eraseFdArray (ref : IO.Ref IoHostState) (ids : Array Nat) : IO Unit :=
  (ref.modify fun st =>
    { st with fds := ids.foldl (fun mp id => mp.erase id) st.fds } : BaseIO _)

private def withFd {α : Type} (ref : IO.Ref IoHostState) (id : Nat)
    (k : RawFd → IO (Except Errno α)) : IO (Except Errno α) := do
  match (← (ref.get : BaseIO _)).fds.get? id with
  | some rfd => k rfd
  | none => return .error Errno.EBADF

private def resolveOptFd (fds : Std.HashMap Nat RawFd) : Option Nat → Except Errno (Option RawFd)
  | none => .ok none
  | some id =>
    match fds.get? id with
    | some rfd => .ok (some rfd)
    | none => .error Errno.EBADF

private def withOptFd {α : Type} (ref : IO.Ref IoHostState) (optId : Option Nat)
    (k : Option RawFd → IO (Except Errno α)) : IO (Except Errno α) := do
  match resolveOptFd (← (ref.get : BaseIO _)).fds optId with
  | .ok optRfd => k optRfd
  | .error e => return .error e

private def bindAllocFd (ref : IO.Ref IoHostState)
    (act : IO (Except Errno RawFd)) : IO (Except Errno Nat) := do
  match ← act with
  | .error e => return .error e
  | .ok rfd => return .ok (← allocFd ref rfd)

private def bindAllocFdPair (ref : IO.Ref IoHostState)
    (act : IO (Except Errno (RawFd × RawFd))) : IO (Except Errno (Nat × Nat)) := do
  match ← act with
  | .error e => return .error e
  | .ok p => return .ok (← allocFdPair ref p)

private def resolveFdArray (ref : IO.Ref IoHostState)
    (ids : Array Nat) : IO (Except Errno (Array RawFd)) := do
  let fds := (← (ref.get : BaseIO _)).fds
  return ids.mapM fun id =>
    match fds.get? id with
    | some rfd => .ok rfd
    | none => .error Errno.EBADF

/-- Build exception-total `FilesOpsM IO Nat` backed by `ref` and `Files.defaultOps`. -/
def mkIoFilesOps (ref : IO.Ref IoHostState) : Files.FilesOpsM IO Nat where
  openat dir p fl m := catchErrno (withOptFd ref dir fun rDir => bindAllocFd ref (Files.defaultOps.openat rDir p fl m))
  openat2 dir p how := catchErrno (withOptFd ref dir fun rDir => bindAllocFd ref (Files.defaultOps.openat2 rDir p how))
  close fd := catchErrno do
    match ← takeFd ref fd with
    | some rfd => Files.defaultOps.close rfd
    | none => return .error Errno.EBADF
  read fd maxB := catchErrno (withFd ref fd (Files.defaultOps.read · maxB))
  write fd bs := catchErrno (withFd ref fd (Files.defaultOps.write · bs))
  fstat fd := catchErrno (withFd ref fd Files.defaultOps.fstat)
  fstatat dir p fl := catchErrno (withOptFd ref dir (Files.defaultOps.fstatat · p fl))
  faccessat dir p mk fl := catchErrno (withOptFd ref dir (Files.defaultOps.faccessat · p mk fl))
  mkdirat dir p m := catchErrno (withOptFd ref dir (Files.defaultOps.mkdirat · p m))
  unlinkat dir p rm := catchErrno (withOptFd ref dir (Files.defaultOps.unlinkat · p rm))
  renameat2 oDir oP nDir nP fl := catchErrno do
    let fds := (← (ref.get : BaseIO _)).fds
    match resolveOptFd fds oDir, resolveOptFd fds nDir with
    | .ok rOld, .ok rNew => Files.defaultOps.renameat2 rOld oP rNew nP fl
    | .error e, _ => return .error e
    | _, .error e => return .error e
  symlinkat tgt dir lp := catchErrno (withOptFd ref dir (Files.defaultOps.symlinkat tgt · lp))
  readlinkat dir p cap := catchErrno (withOptFd ref dir (Files.defaultOps.readlinkat · p cap))
  getdents64 fd cap := catchErrno (withFd ref fd (Files.defaultOps.getdents64 · cap))
  fchmodat dir p m := catchErrno (withOptFd ref dir (Files.defaultOps.fchmodat · p m))
  fchmod fd m := catchErrno (withFd ref fd (Files.defaultOps.fchmod · m))
  flock fd op := catchErrno (withFd ref fd (Files.defaultOps.flock · op))
  fcntl fd cmd := catchErrno (withFd ref fd (Files.defaultOps.fcntl · cmd))
  fsync fd := catchErrno (withFd ref fd Files.defaultOps.fsync)
  getcwd cap := catchErrno (Files.defaultOps.getcwd cap)
  lseek fd off wh := catchErrno (withFd ref fd (Files.defaultOps.lseek · off wh))
  reopenReadOnly fd := catchErrno (withFd ref fd fun rfd => bindAllocFd ref (Files.defaultOps.reopenReadOnly rfd))
  dupStdio slot := catchErrno (bindAllocFd ref (Files.defaultOps.dupStdio slot))

private def mkIoNetOps (ref : IO.Ref IoHostState) : Net.NetOpsM IO Nat where
  socket dom st fl proto := catchErrno (bindAllocFd ref (Net.defaultOps.socket dom st fl proto))
  socketpair dom st fl := catchErrno (bindAllocFdPair ref (Net.defaultOps.socketpair dom st fl))
  bind fd sa := catchErrno (withFd ref fd (Net.defaultOps.bind · sa))
  listen fd bl := catchErrno (withFd ref fd (Net.defaultOps.listen · bl))
  accept4 fd fl := catchErrno (withFd ref fd fun rfd => do
    match ← Net.defaultOps.accept4 rfd fl with
    | .error e => return .error e
    | .ok (cfd, sa) => return .ok (← allocFd ref cfd, sa))
  connect fd sa := catchErrno (withFd ref fd (Net.defaultOps.connect · sa))
  getsockopt fd opt := catchErrno (withFd ref fd (Net.defaultOps.getsockopt · opt))
  setsockopt fd opt v := catchErrno (withFd ref fd (Net.defaultOps.setsockopt · opt v))
  getsockname fd := catchErrno (withFd ref fd Net.defaultOps.getsockname)
  recvfrom fd maxB fl := catchErrno (withFd ref fd (Net.defaultOps.recvfrom · maxB fl))
  sendto fd bs fl := catchErrno (withFd ref fd (Net.defaultOps.sendto · bs fl))
  shutdown fd how := catchErrno (withFd ref fd (Net.defaultOps.shutdown · how))
  sendmsg fd fds := catchErrno (withFd ref fd fun rfd => do
    match ← resolveFdArray ref fds with
    | .error e => return .error e
    | .ok rfds => Net.defaultOps.sendmsg rfd rfds)
  recvmsg fd maxFds := catchErrno (withFd ref fd fun rfd => do
    match ← Net.defaultOps.recvmsg rfd maxFds with
    | .error e => return .error e
    | .ok rfds => return .ok (← allocFdArray ref rfds))
  ioctl fd op ifn := catchErrno (withFd ref fd (Net.defaultOps.ioctl · op ifn))

private def mkIoPollOps (ref : IO.Ref IoHostState) : Poll.PollOpsM IO Nat where
  ppoll entries timeout? := catchErrno do
    if let some ts := timeout? then
      if !ts.isValid then return .error Errno.EINVAL
    if entries.size > Poll.MAX_POLL_NFDS then return .error Errno.EINVAL
    let fds := (← (ref.get : BaseIO _)).fds
    match entries.mapM (fun (id, ev) => (fun r => (r, ev)) <$> fds.get? id) with
    | some rawEntries => Poll.defaultOps.ppoll rawEntries timeout?
    | none =>
      let valid := entries.foldl
        (fun acc (id, ev) => match fds.get? id with | some r => acc.push (r, ev) | none => acc) #[]
      match ← Poll.defaultOps.ppoll valid (some { sec := 0, nsec := 0 }) with
      | .error e => return .error e
      | .ok validRevs =>
        let (out, _) := entries.foldl
          (fun (acc, idx) (id, _) =>
            match fds.get? id with
            | some _ => (acc.push (validRevs.getD idx {}), idx + 1)
            | none => (acc.push { pollnval := true }, idx))
          (#[], 0)
        return .ok out
  eventfd2 initval fl := catchErrno (bindAllocFd ref (Poll.defaultOps.eventfd2 initval fl))

/-- Build exception-total `ProcessOpsM IO Nat` backed by `ref` and `LinuxSyscall.Process.defaultOps`. -/
def mkIoProcOps (ref : IO.Ref IoHostState) : LinuxSyscall.Process.ProcessOpsM IO Nat where
  pipe2 fl := catchErrno (bindAllocFdPair ref (LinuxSyscall.Process.defaultOps.pipe2 fl))
  waitpid pid fl := catchErrno (LinuxSyscall.Process.defaultOps.waitpid pid fl)
  kill pid sig := catchErrno (LinuxSyscall.Process.defaultOps.kill pid sig)
  pidfd_open pid fl := catchErrno (bindAllocFd ref (LinuxSyscall.Process.defaultOps.pidfd_open pid fl))
  pidfd_send_signal fd sig fl := catchErrno (withFd ref fd (LinuxSyscall.Process.defaultOps.pidfd_send_signal · sig fl))
  getpid := catchErrno LinuxSyscall.Process.defaultOps.getpid
  getuid := catchErrno LinuxSyscall.Process.defaultOps.getuid

/-- Build exception-total `SandboxOpsM IO Nat` backed by `ref` and `Sandbox.defaultOps`. -/
def mkIoSandboxOps (ref : IO.Ref IoHostState) : Sandbox.SandboxOpsM IO Nat where
  landlockCreateRuleset attr? fl := catchErrno do
    match ← Sandbox.defaultOps.landlockCreateRuleset attr? fl with
    | .error e => return .error e
    | .ok (.version v) => return .ok (.version v)
    | .ok (.ruleset rfd) => return .ok (.ruleset (← allocFd ref rfd))
  landlockAddRule rs rule := catchErrno (withFd ref rs fun rRs =>
    match rule with
    | .pathBeneath parentFd acc =>
      withFd ref parentFd fun rParent => Sandbox.defaultOps.landlockAddRule rRs (.pathBeneath rParent acc)
    | .netPort port acc => Sandbox.defaultOps.landlockAddRule rRs (.netPort port acc))
  landlockRestrictSelf rs := catchErrno (withFd ref rs Sandbox.defaultOps.landlockRestrictSelf)
  seccomp op fl bs := catchErrno (Sandbox.defaultOps.seccomp op fl bs)
  prctl op := catchErrno (Sandbox.defaultOps.prctl op)
  setrlimit res cur mx := catchErrno (Sandbox.defaultOps.setrlimit res cur mx)
  memfdCreate name fl := catchErrno (bindAllocFd ref (Sandbox.defaultOps.memfdCreate name fl))

/-- Build exception-total `TimeRandOpsM IO` backed by `TimeRand.defaultOps`. -/
def mkIoTimeRandOps : TimeRand.TimeRandOpsM IO where
  clock_gettime clk := catchErrno (TimeRand.defaultOps.clock_gettime clk)
  clock_nanosleep clk a ts := catchErrno (TimeRand.defaultOps.clock_nanosleep clk a ts)
  getrandom n fl := catchErrno (TimeRand.defaultOps.getrandom n fl)

/-- Build exception-total `PasswdOpsM IO` backed by `Passwd.defaultOps`. -/
def mkIoPasswdOps : Passwd.PasswdOpsM IO where
  getpwuid uid := catchErrno (Passwd.defaultOps.getpwuid uid)
  getpwnam nm := catchErrno (Passwd.defaultOps.getpwnam nm)

private def badPfFdErr : PostFork.PostForkError :=
  { kind := .sysError, errno := some Errno.EBADF, message := "closed or unknown descriptor handle" }

private def mapPfFdRef (fds : Std.HashMap Nat RawFd) :
    PostFork.FdRef Nat → Except PostFork.PostForkError (PostFork.FdRef RawFd)
  | .raw n => .ok (.raw n)
  | .handle id =>
    match fds.get? id with
    | some rfd => .ok (.handle rfd)
    | none => .error badPfFdErr

private def mapPfArgToken (fds : Std.HashMap Nat RawFd) :
    PostFork.ArgToken Nat → Except PostFork.PostForkError (PostFork.ArgToken RawFd)
  | .lit s => .ok (.lit s)
  | .fdDecimal r => PostFork.ArgToken.fdDecimal <$> mapPfFdRef fds r
  | .prefixedFd pre r suf => (fun r' => PostFork.ArgToken.prefixedFd pre r' suf) <$> mapPfFdRef fds r

private def mapPfStdio (fds : Std.HashMap Nat RawFd) :
    PostFork.StdioPlan Nat → Except PostFork.PostForkError (PostFork.StdioPlan RawFd)
  | .inherit => .ok .inherit
  | .redirect i o e cl => do
    return .redirect (← mapPfFdRef fds i) (← mapPfFdRef fds o) (← mapPfFdRef fds e) cl

private def mapPfPolicy (fds : Std.HashMap Nat RawFd) :
    PostFork.FdPolicy Nat → Except PostFork.PostForkError (PostFork.FdPolicy RawFd)
  | .inheritNonCloexec ks => do return .inheritNonCloexec (← ks.mapM (mapPfFdRef fds))
  | .closeAllAbove2Except ks => do return .closeAllAbove2Except (← ks.mapM (mapPfFdRef fds))

private def mapPfChildSpec (fds : Std.HashMap Nat RawFd)
    (s : PostFork.ChildSpecM Nat) : Except PostFork.PostForkError PostFork.ChildSpec := do
  let argv ← s.argv.mapM (mapPfArgToken fds)
  let stdio ← mapPfStdio fds s.stdio
  let fdPolicy ← mapPfPolicy fds s.fdPolicy
  let closeFds ← s.closeFds.mapM (mapPfFdRef fds)
  return {
    path := s.path, argv := argv, cwd := s.cwd, env := s.env, rawEnv := s.rawEnv,
    stdio := stdio, fdPolicy := fdPolicy, closeFds := closeFds,
    processGroup := s.processGroup, sigpipe := s.sigpipe, forkMode := s.forkMode }

private def takePendingChild (ref : IO.Ref IoHostState)
    (p : PostFork.PendingChildM Nat) : IO (Option PostFork.PendingChild) :=
  (ref.modifyGet fun st =>
    if p.syncWrite == p.errRead then (none, st)
    else
      match st.fds.get? p.syncWrite, st.fds.get? p.errRead with
      | some rSw, some rEr =>
        (some { pid := p.pid, pgid := p.pgid, syncWrite := rSw, errRead := rEr },
         { st with fds := (st.fds.erase p.syncWrite).erase p.errRead })
      | _, _ => (none, st) : BaseIO _)

/-- Build exception-total `PostForkOpsM IO Nat` backed by `ref` and `PostFork.defaultOps`. -/
def mkIoPostForkOps (ref : IO.Ref IoHostState) : PostFork.PostForkOpsM IO Nat where
  spawn spec := catchPf do
    match mapPfChildSpec (← (ref.get : BaseIO _)).fds spec with
    | .error e => return .error e
    | .ok rSpec => PostFork.defaultOps.spawn rSpec
  spawnWithBarrier spec := catchPf do
    match mapPfChildSpec (← (ref.get : BaseIO _)).fds spec with
    | .error e => return .error e
    | .ok rSpec =>
      match ← PostFork.defaultOps.spawnWithBarrier rSpec with
      | .error e => return .error e
      | .ok pc =>
        let (swId, erId) ← allocFdPair ref (pc.syncWrite, pc.errRead)
        return .ok { pid := pc.pid, pgid := pc.pgid, syncWrite := swId, errRead := erId }
  releaseBarrier pc := catchPf do
    match ← takePendingChild ref pc with
    | some rPc => PostFork.defaultOps.releaseBarrier rPc
    | none => return .error badPfFdErr
  abortBarrier pc := catchPf do
    match ← takePendingChild ref pc with
    | some rPc => PostFork.defaultOps.abortBarrier rPc
    | none => return .error badPfFdErr

/-- Construct a concrete, exception-total `Model.RawHostCapM IO` capability bundle backed by `ref` and `LinuxSyscall.*`, `PostFork`, `EnvVars.Raw`, and `Forwarder`. -/
def mkIoHostCap (ref : IO.Ref IoHostState) : Model.RawHostCapM IO where
  files := mkIoFilesOps ref
  net := mkIoNetOps ref
  poll := mkIoPollOps ref
  proc := mkIoProcOps ref
  sandbox := mkIoSandboxOps ref
  timeRand := mkIoTimeRandOps
  passwd := mkIoPasswdOps
  postFork := mkIoPostForkOps ref
  isLinux := !System.Platform.isWindows && !System.Platform.isOSX
  target := System.Platform.target
  getEnvPath := catchIoTotal (do
    match ← EnvVars.Raw.getEnv "PATH" with
    | .ok (some s) => return some s.toUTF8
    | _ => return none) (fun _ => none)
  getEnvHome := catchIoTotal (do
    match ← EnvVars.Raw.getEnv "HOME" with
    | .ok v? => return v?
    | .error _ => return none) (fun _ => none)
  startFwdTask listenerIds hostPorts := catchErrno do
    match ← resolveFdArray ref listenerIds with
    | .error e => return .error e
    | .ok rawListeners =>
      match ← Forwarder.startIoForwarder rawListeners hostPorts with
      | .error e => return .error e
      | .ok rawFwd =>
        eraseFdArray ref listenerIds
        let tid ← (ref.modifyGet fun st =>
          let id := st.nextFwdId
          (id, { st with nextFwdId := id + 1, fwds := st.fwds.insert id rawFwd }) : BaseIO _)
        return .ok tid
  stopFwdTask tid := catchIoTotal (do
    let rawFwd? ← (ref.modifyGet fun st =>
      (st.fwds.get? tid, { st with fwds := st.fwds.erase tid }) : BaseIO _)
    match rawFwd? with
    | some rawFwd => Forwarder.stopIoForwarder rawFwd
    | none => pure ()) (fun _ => ())
  getTable := catchIoTotal (do return (← (ref.get : BaseIO _)).table) (fun _ => {})
  modifyTable f := catchIoTotal
    ((ref.modifyGet fun st => (st.table, { st with table := f st.table }) : BaseIO _))
    (fun _ => {})

end LeanSwe.ProcessSandbox.Raw.SysBridge
