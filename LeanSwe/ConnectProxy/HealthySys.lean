import LeanSwe.LinuxSyscall.Common.Types
import LeanSwe.LinuxSyscall.Files.Model
import LeanSwe.LinuxSyscall.Net.Model
import LeanSwe.LinuxSyscall.Poll.Model
import LeanSwe.LinuxSyscall.Dns.Model
import LeanSwe.LinuxSyscall.TimeRand.Model
import LeanSwe.ConnectProxy.Types
import LeanSwe.ConnectProxy.Model
import LeanSwe.ConnectProxy.Relay
import LeanSwe.ConnectProxy.SysBridge

namespace LeanSwe.ConnectProxy.HealthySys

open LeanSwe.LinuxSyscall
open LeanSwe.ConnectProxy
open LeanSwe.ConnectProxy.Model
open LeanSwe.ConnectProxy.SysBridge

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
    Nat → Nat → Relay.RingBuf →
    StateM (HealthySysWorld × SysAuditTrace Nat) (Option (Relay.RingBuf × Bool))
  /-- Non-blocking `sendto` loop draining `RingBuf`. -/
  flushRingNonblock :
    Net.NetOpsM (StateM (HealthySysWorld × SysAuditTrace Nat)) Nat →
    Nat → Nat → Relay.RingBuf →
    StateM (HealthySysWorld × SysAuditTrace Nat) (Option Relay.RingBuf)
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

/-- Canonical `SysBridgeTarget` wired directly to `SysBridge` and `Relay`.
    Note: `mkRawOps` binds the synchronous single-threaded stand-in `SysBridge.mkSyncRawOps` for formal FD-conservation and `healthyStep` proofs; concurrent `IO` DNS-task/socketpair orchestration (`mkIoRawOps` / `runIoProxyLoop` / `teardownIoLoopState`) is verified separately via runtime, mutation, and stress tests. -/
def realBridgeTarget : SysBridgeTarget :=
  { createListener := fun sys vcfg => SysBridge.createListener sys vcfg
    handleCompleteHeadSync := fun sys limits onHead onResolved slot evs cfd head pipe =>
      SysBridge.handleCompleteHead sys limits onHead onResolved
        (SysBridge.startDnsSync sys limits onResolved) slot evs cfd head pipe
    acceptNewClients := fun sys limits lfd now slots =>
      SysBridge.acceptNewClients sys limits lfd now slots
    listenPollinEnabled := fun cur maxT => (SysBridge.listenPollEvents cur maxT).pollin
    buildPollBatchSync := fun wakeR lfd maxT nowMs slots =>
      SysBridge.buildPollBatchSync wakeR lfd maxT nowMs slots
    stepHandshakeSync := fun sys limits onHead onResolved slot evs cfd hb dl rev now =>
      SysBridge.stepHandshake sys limits onHead onResolved
        (SysBridge.startDnsSync sys limits onResolved) slot evs cfd hb dl rev now
    recvIntoRing := fun net fd fuel rb => Relay.recvIntoRing net fd fuel rb
    flushRingNonblock := fun net fd fuel rb => Relay.flushRingNonblock net fd fuel rb
    stepBidirectionalRelay := fun sys st cRev uRev =>
      Relay.stepBidirectionalRelay sys.net sys.closeFd st cRev uRev
    stepSlotSync := fun sys limits onHead onResolved slot evs cRev uRev nowMs =>
      SysBridge.stepSyncSlot sys limits onHead onResolved slot evs cRev uRev nowMs
    pollAndStepTickSync := fun sys limits onHead onResolved stopFlag wakeR lfd slots evs =>
      SysBridge.pollAndStepTickSync sys limits onHead onResolved stopFlag wakeR lfd slots evs
    mkRawOps := fun sys =>
      SysBridge.mkSyncRawOps sys (fun wt => wt.1.proxyTable)
        (fun (w, tr) tbl => ({ w with proxyTable := tbl }, tr)) }

end LeanSwe.ConnectProxy.HealthySys
