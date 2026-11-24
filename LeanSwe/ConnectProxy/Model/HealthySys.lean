import LeanSwe.LinuxSyscall.Common.Types
import LeanSwe.LinuxSyscall.Files.Model
import LeanSwe.LinuxSyscall.Net.Model
import LeanSwe.LinuxSyscall.Poll.Model
import LeanSwe.LinuxSyscall.Dns.Model
import LeanSwe.LinuxSyscall.TimeRand.Model
import LeanSwe.NetRelay.Types
import LeanSwe.ConnectProxy.Types
import LeanSwe.ConnectProxy.Model.RelayState
import LeanSwe.ConnectProxy.Model.BridgeState

namespace LeanSwe.ConnectProxy.Internal.SysBridge

open LeanSwe.LinuxSyscall

/-- Observational syscall audit log for stating end-to-end invariants over any `CProxySysOpsM`. -/
structure SysAuditTrace (fd : Type) where
  /-- Descriptors returned by `net.socket`, `net.socketpair`, or `net.accept4` in allocation order. -/
  openedFds : Array fd := #[]
  /-- Descriptors passed to `files.close` in call order. -/
  closedFds : Array fd := #[]
  /-- Socket addresses passed to `net.bind` in call order. -/
  boundAddrs : Array Net.SockAddr := #[]
  /-- Hostnames passed to `dns.getaddrinfo` in call order. -/
  dnsQueries : Array String := #[]
  /-- Socket addresses passed to `net.connect` in call order. -/
  dialedAddrs : Array Net.SockAddr := #[]
  /-- Ordered bytes returned by `net.recvfrom` across calls. -/
  recvBytes : Array UInt8 := #[]
  /-- Ordered bytes accepted by `net.sendto` across calls. -/
  sentBytes : Array UInt8 := #[]
  /-- Non-`EINTR` `Errno` outcomes returned by `net.accept4`, `net.recvfrom`, or `net.sendto`. -/
  netErrs : Array Errno := #[]
  /-- Set to `true` when `net.sendto` on a non-empty buffer returns `.ok 0`. -/
  sawZeroSend : Bool := false
  /-- Per-call `poll.ppoll` outcomes (`none` on `.ok`, `some e` on `.error e`). -/
  pollOutcomes : Array (Option Errno) := #[]
  deriving BEq, DecidableEq, Inhabited

/-- Lift a `StateM W` action to `StateM (W × SysAuditTrace fd)` while updating the audit trace on result. -/
def liftTraceOp {W fd α : Type}
    (act : StateM W α)
    (upd : α → SysAuditTrace fd → SysAuditTrace fd := fun _ tr => tr) :
    StateM (W × SysAuditTrace fd) α := fun (w, tr) =>
  let (r, w') := act.run w
  (r, (w', upd r tr))

/-- Wrap any `sys : CProxySysOpsM (StateM W) fd` with pure non-interfering syscall trace recording. -/
def instrumentSysOps {W fd : Type}
    (sys : CProxySysOpsM (StateM W) fd) :
    CProxySysOpsM (StateM (W × SysAuditTrace fd)) fd :=
  { files :=
      { openat := fun d p fl m => liftTraceOp (sys.files.openat d p fl m)
        openat2 := fun d p how => liftTraceOp (sys.files.openat2 d p how)
        close := fun h => liftTraceOp (sys.files.close h) (fun _ tr => { tr with closedFds := tr.closedFds.push h })
        read := fun h n => liftTraceOp (sys.files.read h n)
        write := fun h bs => liftTraceOp (sys.files.write h bs)
        fstat := fun h => liftTraceOp (sys.files.fstat h)
        fstatat := fun d p fl => liftTraceOp (sys.files.fstatat d p fl)
        faccessat := fun d p m fl => liftTraceOp (sys.files.faccessat d p m fl)
        mkdirat := fun d p m => liftTraceOp (sys.files.mkdirat d p m)
        unlinkat := fun d p rd => liftTraceOp (sys.files.unlinkat d p rd)
        renameat2 := fun od op nd np fl => liftTraceOp (sys.files.renameat2 od op nd np fl)
        symlinkat := fun t d lp => liftTraceOp (sys.files.symlinkat t d lp)
        readlinkat := fun d p c => liftTraceOp (sys.files.readlinkat d p c)
        getdents64 := fun h c => liftTraceOp (sys.files.getdents64 h c)
        fchmodat := fun d p m => liftTraceOp (sys.files.fchmodat d p m)
        fchmod := fun h m => liftTraceOp (sys.files.fchmod h m)
        flock := fun h op => liftTraceOp (sys.files.flock h op)
        fcntl := fun h cmd => liftTraceOp (sys.files.fcntl h cmd)
        fsync := fun h => liftTraceOp (sys.files.fsync h)
        getcwd := fun c => liftTraceOp (sys.files.getcwd c)
        lseek := fun h off wh => liftTraceOp (sys.files.lseek h off wh)
        reopenReadOnly := fun h => liftTraceOp (sys.files.reopenReadOnly h)
        dupStdio := fun sl => liftTraceOp (sys.files.dupStdio sl) }
    net :=
      { socket := fun dom st fl p =>
          liftTraceOp (sys.net.socket dom st fl p) fun r tr =>
            match r with
            | .ok h => { tr with openedFds := tr.openedFds.push h }
            | .error _ => tr
        socketpair := fun dom st fl =>
          liftTraceOp (sys.net.socketpair dom st fl) fun r tr =>
            match r with
            | .ok (h0, h1) => { tr with openedFds := (tr.openedFds.push h0).push h1 }
            | .error _ => tr
        bind := fun h sa =>
          liftTraceOp (sys.net.bind h sa) fun _ tr =>
            { tr with boundAddrs := tr.boundAddrs.push sa }
        listen := fun h bl => liftTraceOp (sys.net.listen h bl)
        accept4 := fun h fl =>
          liftTraceOp (sys.net.accept4 h fl) fun r tr =>
            match r with
            | .ok (cfd, _) => { tr with openedFds := tr.openedFds.push cfd }
            | .error e => if e == Errno.EINTR then tr else { tr with netErrs := tr.netErrs.push e }
        connect := fun h sa =>
          liftTraceOp (sys.net.connect h sa) fun _ tr =>
            { tr with dialedAddrs := tr.dialedAddrs.push sa }
        getsockopt := fun h opt => liftTraceOp (sys.net.getsockopt h opt)
        setsockopt := fun h opt val => liftTraceOp (sys.net.setsockopt h opt val)
        getsockname := fun h => liftTraceOp (sys.net.getsockname h)
        recvfrom := fun h n fl =>
          liftTraceOp (sys.net.recvfrom h n fl) fun r tr =>
            match r with
            | .ok bs =>
              let k := Nat.min bs.size n.toNat
              let accepted := if k == bs.size then bs.data else (bs.extract 0 k).data
              { tr with recvBytes := tr.recvBytes ++ accepted }
            | .error e => if e == Errno.EINTR then tr else { tr with netErrs := tr.netErrs.push e }
        sendto := fun h bs fl =>
          liftTraceOp (sys.net.sendto h bs fl) fun r tr =>
            match r with
            | .ok n =>
              let k := Nat.min n.toNat bs.size
              let accepted := if k == bs.size then bs.data else (bs.extract 0 k).data
              let zeroSend := tr.sawZeroSend || (n == 0 && bs.size > 0)
              { tr with sentBytes := tr.sentBytes ++ accepted, sawZeroSend := zeroSend }
            | .error e => if e == Errno.EINTR then tr else { tr with netErrs := tr.netErrs.push e }
        shutdown := fun h how => liftTraceOp (sys.net.shutdown h how)
        sendmsg := fun h fds => liftTraceOp (sys.net.sendmsg h fds)
        recvmsg := fun h maxFds => liftTraceOp (sys.net.recvmsg h maxFds)
        ioctl := fun h req ifn => liftTraceOp (sys.net.ioctl h req ifn) }
    poll :=
      { ppoll := fun fds to? =>
          liftTraceOp (sys.poll.ppoll fds to?) fun r tr =>
            match r with
            | .ok _ => { tr with pollOutcomes := tr.pollOutcomes.push none }
            | .error e => { tr with pollOutcomes := tr.pollOutcomes.push (some e) }
        eventfd2 := fun iv fl => liftTraceOp (sys.poll.eventfd2 iv fl) }
    dns :=
      { getaddrinfo := fun host hints =>
          liftTraceOp (sys.dns.getaddrinfo host hints) fun _ tr =>
            { tr with dnsQueries := tr.dnsQueries.push host } }
    timeRand :=
      { clock_gettime := fun clk => liftTraceOp (sys.timeRand.clock_gettime clk)
        clock_nanosleep := fun clk abs ts => liftTraceOp (sys.timeRand.clock_nanosleep clk abs ts)
        getrandom := fun n fl => liftTraceOp (sys.timeRand.getrandom n fl) } }

end LeanSwe.ConnectProxy.Internal.SysBridge

namespace LeanSwe.ConnectProxy.Internal.HealthySys

open LeanSwe.LinuxSyscall
open LeanSwe.ConnectProxy
open LeanSwe.ConnectProxy.Internal
open LeanSwe.ConnectProxy.Internal.SysBridge

/-- Combined healthy OS world state for `ConnectProxy` relational specs (`Files` + `Net` + `Poll` + `Dns` + `TimeRand` + `SyncProxyTable` + unconstrained nondeterministic `auxTag`). -/
structure HealthySysWorld where
  /-- `Files` healthy environment (`LinuxSyscall.Files.HealthyEnv`). -/
  filesEnv : Files.HealthyEnv := Files.HealthyEnv.initial
  /-- `Net` healthy environment (`LinuxSyscall.Net.HealthyEnv`). -/
  netEnv : Net.HealthyEnv := Net.HealthyEnv.initial
  /-- `Poll` healthy environment (`LinuxSyscall.Poll.HealthyEnv`). -/
  pollEnv : Poll.HealthyEnv := Poll.HealthyEnv.initial
  /-- `Dns` healthy environment (`LinuxSyscall.Dns.HealthyEnv`). -/
  dnsEnv : Dns.HealthyEnv := Dns.HealthyEnv.initial
  /-- `TimeRand` healthy environment (`LinuxSyscall.TimeRand.HealthyEnv`). -/
  timeEnv : TimeRand.HealthyEnv := TimeRand.HealthyEnv.initial 0 0 true
  /-- Unconstrained auxiliary state allowing arbitrary healthy adversarial/nondeterministic schedules. -/
  auxTag : Nat := 0
  /-- Active synchronous proxy table owned by `mkSyncRawOps`. -/
  proxyTable : SyncProxyTable Nat := {}
  deriving Inhabited

/-- Combined well-formedness check across all 5 subsystem environments. -/
def HealthySysWorld.wf (w : HealthySysWorld) : Bool :=
  w.filesEnv.wf && w.netEnv.wf && w.pollEnv.wf && w.dnsEnv.wf && w.timeEnv.wf

/-- Universal relational healthy refinement for `CProxySysOpsM (StateM W) Nat` over arbitrary world `W`. -/
def RefinesHealthyCProxySysAt {W : Type}
    (projFiles : W → Files.HealthyEnv)
    (projNet : W → Net.HealthyEnv)
    (projPoll : W → Poll.HealthyEnv)
    (projDns : W → Dns.HealthyEnv)
    (projTime : W → TimeRand.HealthyEnv)
    (getTable : W → SyncProxyTable Nat)
    (setTable : W → SyncProxyTable Nat → W)
    (sys : CProxySysOpsM (StateM W) Nat) : Prop :=
  let worldWf (w : W) : Prop :=
    (projFiles w).wf = true ∧ (projNet w).wf = true ∧ (projPoll w).wf = true ∧
    (projDns w).wf = true ∧ (projTime w).wf = true
  let fdsNodup (w : W) : Prop := ((projFiles w).state.fds.map Prod.fst).Nodup
  (∀ w h, worldWf w →
    let (r, w') := (sys.files.close h).run w
    Files.healthyStep (projFiles w) (.close h) (Files.outcomeOfUnit r) = some (projFiles w') ∧
    worldWf w' ∧ getTable w' = getTable w) ∧
  (∀ w req, worldWf w →
    let (out, w') := (Net.execNetReq sys.net req).run w
    Net.healthyStep (projNet w) req out = some (projNet w') ∧
    worldWf w' ∧ getTable w' = getTable w ∧ (fdsNodup w → fdsNodup w')) ∧
  (∀ w req, worldWf w →
    let (out, w') := (Poll.execPollReq sys.poll req).run w
    Poll.healthyStep (projPoll w) req out = some (projPoll w') ∧
    worldWf w' ∧ getTable w' = getTable w ∧ (fdsNodup w → fdsNodup w')) ∧
  (∀ w req, worldWf w →
    let (out, w') := (Dns.execDnsReq sys.dns req).run w
    Dns.healthyStep (projDns w) req out = some (projDns w') ∧
    worldWf w' ∧ getTable w' = getTable w ∧ (fdsNodup w → fdsNodup w')) ∧
  (∀ w req, worldWf w →
    let (out, w') := (TimeRand.execTimeRandReq sys.timeRand req).run w
    TimeRand.healthyStep (projTime w) req out = some (projTime w') ∧
    worldWf w' ∧ getTable w' = getTable w ∧ (fdsNodup w → fdsNodup w')) ∧
  (∀ w t, getTable (setTable w t) = t) ∧
  (∀ w t, (worldWf w → worldWf (setTable w t)) ∧ (fdsNodup w → fdsNodup (setTable w t)))

/-- Relational healthy OS world refinement instantiated at `HealthySysWorld`. -/
def RefinesHealthyCProxySys (sys : CProxySysOpsM (StateM HealthySysWorld) Nat) : Prop :=
  RefinesHealthyCProxySysAt
    (·.filesEnv) (·.netEnv) (·.pollEnv) (·.dnsEnv) (·.timeEnv)
    (·.proxyTable) (fun w t => { w with proxyTable := t })
    sys

/-- Return all open descriptors currently owned by `slot`. -/
def slotOpenFds {fd dnsJob : Type} (slot : ClientSlot fd dnsJob) : List fd :=
  match slot.phase with
  | .handshake cfd _ _ => [cfd]
  | .dns cfd _ _ _ => [cfd]
  | .connecting cfd ufd .. => [ufd, cfd]
  | .relay st =>
    (match st.clientFd? with | some c => [c] | none => []) ++
    (match st.upstreamFd? with | some u => [u] | none => [])
  | .closingReply cfd? .. =>
    match cfd? with | some c => [c] | none => []
  | .done => []

/-- Entrypoint bundle tested by `ConnectProxy`'s `RefinesHealthy*` `SpecTests` and `SpecMutants`. -/
structure SysBridgeTarget where
  /-- Create `127.0.0.1` loopback listener + wakeup socketpair. -/
  createListener :
    CProxySysOpsM (StateM (HealthySysWorld × SysAuditTrace Nat)) Nat →
    ValidProxyConfig →
    StateM (HealthySysWorld × SysAuditTrace Nat) (Except ProxyError (Nat × Nat × Nat × UInt16))
  /-- Stage-1 complete-head gate + Stage-2 DNS/dial pipeline. -/
  handleCompleteHeadSync :
    CProxySysOpsM (StateM (HealthySysWorld × SysAuditTrace Nat)) Nat →
    ProxyLimits →
    (ByteArray → HeadDecision) →
    (String → UInt16 → Array IpAddr → ResolveDecision) →
    ClientSlot Nat Unit →
    Array ConnectEvent →
    Nat →
    ByteArray →
    ByteArray →
    StateM (HealthySysWorld × SysAuditTrace Nat) (ClientSlot Nat Unit × Array ConnectEvent)
  /-- Concurrency-bounded `accept4` admission loop. -/
  acceptNewClients :
    CProxySysOpsM (StateM (HealthySysWorld × SysAuditTrace Nat)) Nat →
    ProxyLimits →
    Nat →
    Nat →
    Array (ClientSlot Nat Unit) →
    StateM (HealthySysWorld × SysAuditTrace Nat) (Array (ClientSlot Nat Unit))
  /-- Listener `POLLIN` interest gate (`slots.size < maxConcurrentTunnels`). -/
  listenPollinEnabled : Nat → Nat → Bool
  /-- Synchronous `ppoll` batch builder (`wakeR`, `listenFd`, per-slot poll requests, and relative timeout). -/
  buildPollBatchSync :
    Nat → Nat → Nat → Nat → Array (ClientSlot Nat Unit) →
    Array (Nat × Poll.PollEvents) × Array (Option Nat × Option Nat) × Option Poll.Timespec
  /-- Non-blocking handshake reader (`maxHeaderBytes` cap). -/
  stepHandshakeSync :
    CProxySysOpsM (StateM (HealthySysWorld × SysAuditTrace Nat)) Nat →
    ProxyLimits →
    (ByteArray → HeadDecision) →
    (String → UInt16 → Array IpAddr → ResolveDecision) →
    ClientSlot Nat Unit →
    Array ConnectEvent →
    Nat → ByteArray → Nat → Poll.PollEvents → Nat →
    StateM (HealthySysWorld × SysAuditTrace Nat) (ClientSlot Nat Unit × Array ConnectEvent)
  /-- Non-blocking `recvfrom` loop into `RingBuf`. -/
  recvIntoRing :
    Net.NetOpsM (StateM (HealthySysWorld × SysAuditTrace Nat)) Nat →
    Nat → Nat → NetRelay.RingBuf →
    StateM (HealthySysWorld × SysAuditTrace Nat) (Option (NetRelay.RingBuf × Bool))
  /-- Non-blocking `sendto` loop draining `RingBuf`. -/
  flushRingNonblock :
    Net.NetOpsM (StateM (HealthySysWorld × SysAuditTrace Nat)) Nat →
    Nat → Nat → NetRelay.RingBuf →
    StateM (HealthySysWorld × SysAuditTrace Nat) (Option NetRelay.RingBuf)
  /-- One non-blocking bidirectional tunnel relay tick (`pendingPrefix`, `c2u`, `u2c`, half-close, peer reset drain). -/
  stepBidirectionalRelay :
    CProxySysOpsM (StateM (HealthySysWorld × SysAuditTrace Nat)) Nat →
    Relay.RelayState Nat → Poll.PollEvents → Poll.PollEvents →
    StateM (HealthySysWorld × SysAuditTrace Nat) (Relay.RelayState Nat)
  /-- Synchronous single-slot transition (`stepSlotM` instantiated over `StateM`). -/
  stepSlotSync :
    CProxySysOpsM (StateM (HealthySysWorld × SysAuditTrace Nat)) Nat →
    ProxyLimits →
    (ByteArray → HeadDecision) →
    (String → UInt16 → Array IpAddr → ResolveDecision) →
    ClientSlot Nat Unit →
    Array ConnectEvent →
    Poll.PollEvents → Poll.PollEvents → Nat →
    StateM (HealthySysWorld × SysAuditTrace Nat) (ClientSlot Nat Unit × Array ConnectEvent)
  /-- Synchronous server loop tick (`pollAndStepTickM` instantiated over `StateM`). -/
  pollAndStepTickSync :
    CProxySysOpsM (StateM (HealthySysWorld × SysAuditTrace Nat)) Nat →
    ProxyLimits →
    (ByteArray → HeadDecision) →
    (String → UInt16 → Array IpAddr → ResolveDecision) →
    Bool →
    Nat → Nat →
    Array (ClientSlot Nat Unit) →
    Array ConnectEvent →
    StateM (HealthySysWorld × SysAuditTrace Nat) (SysBridge.PollTickOutcome Nat Unit)
  /-- Synchronous single-threaded `RawConnectProxyOpsM` stand-in builder (`SysBridge.mkSyncRawOps`) over instrumented `HealthySysWorld`.
      Formal FD-conservation proofs target this stand-in; the concurrent `IO` task/socketpair driver (`mkIoRawOps` / `runIoProxyLoop` / `teardownIoLoopState`) is verified by runtime, mutation, and stress tests. -/
  mkRawOps :
    CProxySysOpsM (StateM (HealthySysWorld × SysAuditTrace Nat)) Nat →
    RawConnectProxyOpsM (StateM (HealthySysWorld × SysAuditTrace Nat))

end LeanSwe.ConnectProxy.Internal.HealthySys
