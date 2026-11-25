import LeanSwe.LinuxSyscall.Common.Types
import LeanSwe.LinuxSyscall.Files.Types
import LeanSwe.LinuxSyscall.Files.Interface
import LeanSwe.LinuxSyscall.Net.Types
import LeanSwe.LinuxSyscall.Poll.Types
import LeanSwe.LinuxSyscall.Process.Types
import LeanSwe.LinuxSyscall.Process.Interface
import LeanSwe.LinuxSyscall.TimeRand.Types
import LeanSwe.PostFork.Types
import LeanSwe.ProcessSandbox.Raw.Types
import LeanSwe.ProcessSandbox.Raw.Impl
import LeanSwe.ProcessSandbox.Raw.SysBridge.Cgroup
import LeanSwe.ProcessSandbox.Raw.SysBridge.Bwrap
import LeanSwe.ProcessSandbox.Raw.SysBridge.StreamIo
import LeanSwe.ProcessSandbox.Raw.SysBridge.State

namespace LeanSwe.ProcessSandbox.Raw.SysBridge

open LeanSwe.LinuxSyscall
open LeanSwe.ProcessSandbox.Raw
open LeanSwe.ProcessSandbox.Raw.SysBridge.Cgroup
open LeanSwe.ProcessSandbox.Raw.SysBridge.Bwrap
open LeanSwe.ProcessSandbox.Raw.SysBridge.StreamIo

/-- Precheck every user bind-mount `hostPath` via `stat` before creating cgroups or spawning `bwrap`. -/
def precheckHostMounts {m : Type → Type} [Monad m] {fd : Type}
    (files : Files.FilesOpsM m fd) (eintrFuel : Nat) :
    List SandboxMount → m (Except SandboxError Unit)
  | [] => pure (.ok ())
  | mnt :: rest => do
    match mountHostPath? mnt with
    | none => precheckHostMounts files eintrFuel rest
    | some hp =>
      match ← retryEintr (files.fstatat none hp.toUTF8 {}) eintrFuel with
      | .error e => return .error (mapPathErrnoToSandboxError hp "host mount path error" e)
      | .ok _ => precheckHostMounts files eintrFuel rest

/-- Best-effort teardown of a partially spawned box after `releaseBarrier` succeeded. -/
def rollbackRunningChild {m : Type → Type} [Monad m] {fd : Type}
    (files : Files.FilesOpsM m fd) (proc : LinuxSyscall.Process.ProcessOpsM m fd)
    (timeRand : TimeRand.TimeRandOpsM m)
    (childPid : UInt32) (pidfd? : Option fd) (cgDir : String) (eintrFuel : Nat) : m Unit := do
  let _ ← killBoxPg proc childPid eintrFuel
  match pidfd? with
  | some pfd =>
    let _ ← killBoxPidfd proc pfd eintrFuel
    pure ()
  | none => pure ()
  if !cgDir.isEmpty then
    let _ ← writeTextFile files (cgroupSubfile cgDir "cgroup.kill") "1" eintrFuel
  if childPid > 0 && childPid ≤ LinuxSyscall.Process.MAX_LINUX_PID then
    let _ ← LinuxSyscall.Process.waitpidReapLoop proc childPid.toInt32 eintrFuel
    pure ()
  Files.closeOpt files pidfd?
  let _ ← cleanupCgroupDir files timeRand cgDir CGROUP_POLL_STEPS CGROUP_RMDIR_STEPS eintrFuel
  pure ()

/-- Optionally allocate the `AF_UNIX` `SOCK_SEQPACKET` control socketpair when `nFwds > 0`. -/
def allocCtrlSocketpair {m : Type → Type} [Monad m] {fd : Type}
    (net : Net.NetOpsM m fd) (nFwds eintrFuel : Nat) :
    m (Except Errno (Option (fd × fd))) := do
  if nFwds > 0 then
    match ← retryEintr (net.socketpair .unix .seqpacket { cloexec := true }) eintrFuel with
    | .ok pair => return .ok (some pair)
    | .error e => return .error e
  else
    return .ok none

/-- Verify `cgroup.kill` write access and configure optional `memory` and `pids.max` limits on `cgDir`. -/
def setupSpawnCgroupLimits {m : Type → Type} [Monad m] {fd : Type}
    (files : Files.FilesOpsM m fd) (cgDir : String) (limits : SandboxLimits) (eintrFuel : Nat) :
    m (Option (Errno × String)) := do
  match ← retryEintr (files.faccessat none (cgroupSubfile cgDir "cgroup.kill").toUTF8 { write := true } {}) eintrFuel with
  | .error e => return some (e, "direct cgroup v2 cgroup.kill unavailable")
  | .ok () =>
    let checkPids : m (Option (Errno × String)) :=
      match limits.pidsMax with
      | none => pure none
      | some pMax => do
        match ← configureCgroupPids files cgDir (toString (cappedPidsMax pMax)) eintrFuel with
        | .ok () => pure none
        | .error e => pure (some (e, s!"failed to set direct cgroup v2 pids.max: {Errno.name e}"))
    match limits.memoryMaxBytes with
    | none => checkPids
    | some memMax =>
      match ← configureCgroupMemory files cgDir (toString memMax) eintrFuel with
      | .ok () => checkPids
      | .error (fname, e) => return some (e, s!"failed to set direct cgroup v2 {fname}: {Errno.name e}")

/-- Receive `nFwds` bound listener descriptors over `ctrlR?` when port forwarding is configured. -/
def recvPortListenerFds {m : Type → Type} [Monad m] {fd : Type}
    (files : Files.FilesOpsM m fd) (net : Net.NetOpsM m fd) (poll : Poll.PollOpsM m fd)
    (ctrlR? : Option fd) (statusR : fd) (nFwds : Nat) :
    m (Except Errno (Array fd)) := do
  match ctrlR? with
  | some cr =>
    let r ← recvFdsScm files net poll cr statusR nFwds
    Files.closeOpt files (some cr)
    return r
  | none => return .ok #[]

/-- Pure capability-parameterized implementation of `RawProcessSandboxOpsM.spawnBox`. -/
def spawnBoxPure {m : Type → Type} [Monad m] {fd fwdTask : Type}
    (deps : HostSysDepsM m fd fwdTask) (tbl : HostTableOpsM m fd fwdTask)
    (eintrFuel : Nat) (ph : PlanHandle) : m (Except SandboxError BoxHandle) := do
  if !isValidSandboxHandleId ph.handleId then
    return .error (Internal.mapRawError (.invalidArgument none none "invalid plan handle"))
  match ← tbl.findPlan ph.handleId with
  | none =>
    return .error (Internal.mapRawError (.invalidArgument none (some Errno.EINVAL) "invalid or closed plan handle"))
  | some pslot =>
    let plan := pslot.plan
    match ← precheckHostMounts deps.files eintrFuel plan.userMounts.toList with
    | .error e => return .error e
    | .ok () =>
      match ← resolveBwrapPath deps.files deps.getEnvPath eintrFuel with
      | none =>
        return .error (Internal.mapRawError (.unavailable (some Errno.ENOENT) "bwrap executable not found in PATH"))
      | some bwrapPath =>
        match ← retryEintr (deps.proc.pipe2 { cloexec := true }) eintrFuel with
        | .error e => return .error (Internal.mapRawError (.ioError none e "pipe2 failed"))
        | .ok (inR, inW) =>
          match ← retryEintr (deps.proc.pipe2 { cloexec := true }) eintrFuel with
          | .error e =>
            Files.closeOpt deps.files (some inR); Files.closeOpt deps.files (some inW)
            return .error (Internal.mapRawError (.ioError none e "pipe2 failed"))
          | .ok (outR, outW) =>
            match ← retryEintr (deps.proc.pipe2 { cloexec := true }) eintrFuel with
            | .error e =>
              Files.closeOpt deps.files (some inR); Files.closeOpt deps.files (some inW)
              Files.closeOpt deps.files (some outR); Files.closeOpt deps.files (some outW)
              return .error (Internal.mapRawError (.ioError none e "pipe2 failed"))
            | .ok (errR, errW) =>
              let closeStdioPipes : m Unit := do
                Files.closeOpt deps.files (some inR); Files.closeOpt deps.files (some inW)
                Files.closeOpt deps.files (some outR); Files.closeOpt deps.files (some outW)
                Files.closeOpt deps.files (some errR); Files.closeOpt deps.files (some errW)
              match ← retryEintr (deps.files.reopenReadOnly pslot.initMemfd) eintrFuel with
              | .error e =>
                closeStdioPipes
                return .error (Internal.mapRawError (.ioError none e "failed to reopen sealed init memfd"))
              | .ok initFd =>
                match ← retryEintr (deps.files.reopenReadOnly pslot.hostsMemfd) eintrFuel with
                | .error e =>
                  Files.closeOpt deps.files (some initFd); closeStdioPipes
                  return .error (Internal.mapRawError (.ioError none e "failed to reopen sealed hosts memfd"))
                | .ok hostsFd =>
                  match ← retryEintr (deps.files.reopenReadOnly pslot.planMemfd) eintrFuel with
                  | .error e =>
                    Files.closeOpt deps.files (some hostsFd); Files.closeOpt deps.files (some initFd); closeStdioPipes
                    return .error (Internal.mapRawError (.ioError none e "failed to reopen sealed plan memfd"))
                  | .ok planFd =>
                    let closeBaseFds : m Unit := do
                      Files.closeOpt deps.files (some planFd)
                      Files.closeOpt deps.files (some hostsFd)
                      Files.closeOpt deps.files (some initFd)
                      closeStdioPipes
                    match ← retryEintr (deps.proc.pipe2 { cloexec := true }) eintrFuel with
                    | .error e =>
                      closeBaseFds
                      return .error (Internal.mapRawError (.ioError none e "pipe2 failed"))
                    | .ok (statusR, statusW) =>
                      match ← retryEintr (deps.proc.pipe2 { cloexec := true }) eintrFuel with
                      | .error e =>
                        Files.closeOpt deps.files (some statusR); Files.closeOpt deps.files (some statusW); closeBaseFds
                        return .error (Internal.mapRawError (.ioError none e "pipe2 failed"))
                      | .ok (goR, goW) =>
                        let nFwds := plan.portForwards.size
                        let ctrlRes ← allocCtrlSocketpair deps.net nFwds eintrFuel
                        match ctrlRes with
                        | .error e =>
                          Files.closeOpt deps.files (some goR); Files.closeOpt deps.files (some goW)
                          Files.closeOpt deps.files (some statusR); Files.closeOpt deps.files (some statusW)
                          closeBaseFds
                          return .error (Internal.mapRawError (.ioError none e "socketpair failed"))
                        | .ok ctrlPair? =>
                          let ctrlR? := ctrlPair?.map Prod.fst
                          let ctrlW? := ctrlPair?.map Prod.snd
                          let closeAllPreFork : m Unit := do
                            Files.closeOpt deps.files ctrlR?; Files.closeOpt deps.files ctrlW?
                            Files.closeOpt deps.files (some goR); Files.closeOpt deps.files (some goW)
                            Files.closeOpt deps.files (some statusR); Files.closeOpt deps.files (some statusW)
                            closeBaseFds
                          match ← deps.proc.getpid with
                          | .error e =>
                            closeAllPreFork
                            return .error (Internal.mapRawError (.unavailable (some e) "getpid failed"))
                          | .ok hostPid =>
                            let seq ← tbl.nextCgSeq
                            match ← createSiblingCgroup deps.files hostPid seq eintrFuel with
                            | .error e =>
                              closeAllPreFork
                              return .error (Internal.mapRawError (.unavailable (some e) s!"failed to create direct cgroup v2 directory: {Errno.name e}"))
                            | .ok cgDir =>
                              let cgSetupErr? ← setupSpawnCgroupLimits deps.files cgDir plan.limits eintrFuel
                              match cgSetupErr? with
                              | some (e, msg) =>
                                closeAllPreFork
                                let _ ← cleanupCgroupDir deps.files deps.timeRand cgDir CGROUP_POLL_STEPS CGROUP_RMDIR_STEPS eintrFuel
                                return .error (Internal.mapRawError (.unavailable (some e) msg))
                              | none =>
                                let baseKeep : Array (PostFork.FdRef fd) :=
                                  #[.handle statusW, .handle goR, .handle initFd, .handle hostsFd, .handle planFd]
                                let keepFds := match ctrlW? with
                                  | some cw => baseKeep.push (.handle cw)
                                  | none => baseKeep
                                let baseClose : Array (PostFork.FdRef fd) :=
                                  #[.handle inW, .handle outR, .handle errR, .handle statusR, .handle goW]
                                let closeFds := match ctrlR? with
                                  | some cr => baseClose.push (.handle cr)
                                  | none => baseClose
                                let childSpec : PostFork.ChildSpecM fd := {
                                  path := bwrapPath
                                  argv := buildSpawnBwrapArgv bwrapPath plan initFd hostsFd planFd statusW goR ctrlW?
                                  stdio := .redirect (.handle inR) (.handle outW) (.handle errW) false
                                  fdPolicy := .closeAllAbove2Except keepFds
                                  closeFds := closeFds
                                  processGroup := .newGroup
                                  sigpipe := .resetDefault
                                  forkMode := .immortalThread
                                }
                                match ← deps.postFork.spawnWithBarrier childSpec with
                                | .error pfErr =>
                                  closeAllPreFork
                                  let _ ← cleanupCgroupDir deps.files deps.timeRand cgDir CGROUP_POLL_STEPS CGROUP_RMDIR_STEPS eintrFuel
                                  return .error (Internal.mapRawError (.unavailable pfErr.errno s!"failed to fork bwrap: {pfErr.message}"))
                                | .ok pending =>
                                  let closeChildSides : m Unit := do
                                    Files.closeOpt deps.files (some initFd)
                                    Files.closeOpt deps.files (some hostsFd)
                                    Files.closeOpt deps.files (some planFd)
                                    Files.closeOpt deps.files (some inR)
                                    Files.closeOpt deps.files (some outW)
                                    Files.closeOpt deps.files (some errW)
                                    Files.closeOpt deps.files (some statusW)
                                    Files.closeOpt deps.files (some goR)
                                    Files.closeOpt deps.files ctrlW?
                                  let closeParentSides : m Unit := do
                                    Files.closeOpt deps.files (some inW)
                                    Files.closeOpt deps.files (some outR)
                                    Files.closeOpt deps.files (some errR)
                                    Files.closeOpt deps.files (some statusR)
                                    Files.closeOpt deps.files (some goW)
                                    Files.closeOpt deps.files ctrlR?
                                  match ← retryEintr (deps.proc.pidfd_open pending.pid {}) eintrFuel with
                                  | .error e =>
                                    let _ ← deps.postFork.abortBarrier pending
                                    closeChildSides; closeParentSides
                                    let _ ← cleanupCgroupDir deps.files deps.timeRand cgDir CGROUP_POLL_STEPS CGROUP_RMDIR_STEPS eintrFuel
                                    return .error (Internal.mapRawError (.unavailable (some e) s!"pidfd_open failed: {Errno.name e}"))
                                  | .ok pidfd =>
                                    match ← writeTextFile deps.files (cgroupSubfile cgDir "cgroup.procs") (toString pending.pid) eintrFuel with
                                    | .error e =>
                                      let _ ← deps.postFork.abortBarrier pending
                                      Files.closeOpt deps.files (some pidfd)
                                      closeChildSides; closeParentSides
                                      let _ ← cleanupCgroupDir deps.files deps.timeRand cgDir CGROUP_POLL_STEPS CGROUP_RMDIR_STEPS eintrFuel
                                      return .error (Internal.mapRawError (.unavailable (some e) s!"failed to attach child to cgroup.procs: {Errno.name e}"))
                                    | .ok () =>
                                      let relRes ← deps.postFork.releaseBarrier pending
                                      closeChildSides
                                      match relRes with
                                      | .error pfErr =>
                                        Files.closeOpt deps.files (some pidfd)
                                        closeParentSides
                                        let _ ← cleanupCgroupDir deps.files deps.timeRand cgDir CGROUP_POLL_STEPS CGROUP_RMDIR_STEPS eintrFuel
                                        return .error (Internal.mapRawError (.unavailable pfErr.errno s!"execvp bwrap failed: {pfErr.message}"))
                                      | .ok child =>
                                        let recvRes ← recvPortListenerFds deps.files deps.net deps.poll ctrlR? statusR nFwds
                                        match recvRes with
                                        | .error e =>
                                          let snip ← drainStderrSnippet deps.files errR
                                          Files.closeOpt deps.files (some inW); Files.closeOpt deps.files (some outR)
                                          Files.closeOpt deps.files (some errR); Files.closeOpt deps.files (some statusR)
                                          Files.closeOpt deps.files (some goW)
                                          rollbackRunningChild deps.files deps.proc deps.timeRand child.pid (some pidfd) cgDir eintrFuel
                                          let msg := if snip.isEmpty then "failed to receive box port listener descriptors" else s!"sandbox setup failed: {snip}"
                                          return .error (Internal.mapRawError (.unavailable (some e) msg))
                                        | .ok listenerFds =>
                                          let (smsg?, readErr?) ← readInitStatusBlocking deps.files statusR ByteArray.empty 64
                                          match smsg? with
                                          | some msg =>
                                            if msg.kind == PS_STATUS_READY then
                                              let pgid := child.pgid.getD child.pid
                                              if child.pid == 0 || child.pid > LinuxSyscall.Process.MAX_LINUX_PID || pgid == 0 || pgid > LinuxSyscall.Process.MAX_LINUX_PID then
                                                closeFdArray deps.files listenerFds
                                                Files.closeOpt deps.files (some inW); Files.closeOpt deps.files (some outR)
                                                Files.closeOpt deps.files (some errR); Files.closeOpt deps.files (some statusR)
                                                Files.closeOpt deps.files (some goW)
                                                rollbackRunningChild deps.files deps.proc deps.timeRand child.pid (some pidfd) cgDir eintrFuel
                                                return .error (Internal.mapRawError (.unavailable none "invalid child pid/pgid"))
                                              let bslot : BoxSlotM fd := {
                                                pid := child.pid
                                                pgid := pgid
                                                pidfd := pidfd
                                                stdinFd? := some inW
                                                stdoutFd? := some outR
                                                stderrFd? := some errR
                                                statusFd? := some statusR
                                                goFd? := some goW
                                                listenerFds := listenerFds
                                                cgroupDir := cgDir
                                                program := plan.program
                                                cwd := plan.cwd
                                              }
                                              match ← tbl.insertBox bslot with
                                              | none =>
                                                closeFdArray deps.files listenerFds
                                                Files.closeOpt deps.files (some inW); Files.closeOpt deps.files (some outR)
                                                Files.closeOpt deps.files (some errR); Files.closeOpt deps.files (some statusR)
                                                Files.closeOpt deps.files (some goW)
                                                rollbackRunningChild deps.files deps.proc deps.timeRand child.pid (some pidfd) cgDir eintrFuel
                                                return .error (Internal.mapRawError (.ioError none Errno.ENOMEM "box handle table exhausted"))
                                              | some bhid =>
                                                return .ok {
                                                  handleId := bhid
                                                  pid := Int.ofNat child.pid.toNat
                                                  pgid := Int.ofNat pgid.toNat
                                                  pidfd := 0
                                                }
                                            else
                                              let snip ← drainStderrSnippet deps.files errR
                                              let eCode : Errno :=
                                                if msg.kind == PS_STATUS_INIT_ERR && msg.value != 0 then
                                                  msg.value.toUInt32
                                                else
                                                  readErr?.getD Errno.EPERM
                                              closeFdArray deps.files listenerFds
                                              Files.closeOpt deps.files (some inW); Files.closeOpt deps.files (some outR)
                                              Files.closeOpt deps.files (some errR); Files.closeOpt deps.files (some statusR)
                                              Files.closeOpt deps.files (some goW)
                                              rollbackRunningChild deps.files deps.proc deps.timeRand child.pid (some pidfd) cgDir eintrFuel
                                              let msgTxt := if snip.isEmpty then s!"sandbox init failed before execvp: {Errno.name eCode}" else s!"sandbox init failed before execvp: {snip}"
                                              return .error (Internal.mapRawError (.unavailable (some eCode) msgTxt))
                                          | none =>
                                            let snip ← drainStderrSnippet deps.files errR
                                            let eCode : Errno := readErr?.getD Errno.EPERM
                                            closeFdArray deps.files listenerFds
                                            Files.closeOpt deps.files (some inW); Files.closeOpt deps.files (some outR)
                                            Files.closeOpt deps.files (some errR); Files.closeOpt deps.files (some statusR)
                                            Files.closeOpt deps.files (some goW)
                                            rollbackRunningChild deps.files deps.proc deps.timeRand child.pid (some pidfd) cgDir eintrFuel
                                            let msgTxt := if snip.isEmpty then s!"sandbox init failed before execvp: {Errno.name eCode}" else s!"sandbox init failed before execvp: {snip}"
                                            return .error (Internal.mapRawError (.unavailable (some eCode) msgTxt))

end LeanSwe.ProcessSandbox.Raw.SysBridge
