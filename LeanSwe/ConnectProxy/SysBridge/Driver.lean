import Core.ConcOps
import LeanSwe.LinuxSyscall.Common.Types
import LeanSwe.LinuxSyscall.Files.Types
import LeanSwe.LinuxSyscall.Net.Types
import LeanSwe.LinuxSyscall.Poll.Types
import LeanSwe.LinuxSyscall.Dns.Types
import LeanSwe.LinuxSyscall.TimeRand.Types
import LeanSwe.NetRelay.Interface
import LeanSwe.ConnectProxy.Types
import LeanSwe.ConnectProxy.Model
import LeanSwe.ConnectProxy.Model.BridgeState
import LeanSwe.ConnectProxy.SysBridge

namespace LeanSwe.ConnectProxy.SysBridge.Driver

open LeanSwe.LinuxSyscall
open LeanSwe.ConnectProxy
open LeanSwe.ConnectProxy.Model
open LeanSwe.ConnectProxy.SysBridge

/-- Shared cancellation, completion, and result state for one off-thread DNS lookup job. -/
structure DnsJobState where
  /-- Set to `true` when the owning client disconnects or the proxy tears down. -/
  cancelled : Bool := false
  /-- Set to `true` in the worker `finally` block strictly before closing `dnsW`. -/
  done : Bool := false
  /-- Completed `getaddrinfo` result (`some (.ok ips)` or `some (.error msg)`). -/
  result? : Option (Except String (Array IpAddr)) := none

/-- Handle to one off-thread DNS lookup job built locally over `Core.ConcOpsM`'s general `Ref`
    and `TaskHandle` primitives. The event loop exclusively owns `dnsR`; the worker task
    exclusively owns `dnsW` and closes it inside `tryFinally'` after setting `done := true`. -/
structure ConcDnsJob (fd : Type) (Ref : Type → Type) (TaskHandle : Type → Type) where
  /-- Shared cancellation, completion, and result cell. -/
  stateRef : Ref DnsJobState
  /-- Dedicated background task executing `getaddrinfo` and closing `dnsW`. -/
  task : TaskHandle Unit
  /-- Loop-owned read end of the per-job `AF_UNIX` `SOCK_STREAM` wakeup socketpair. -/
  dnsR : fd

/-- Wrap `sys` so `accept4` records transient resource exhaustion (`isAcceptResourceErrno`) in `hitLimitRef`. -/
def sysWithAcceptWatch {m : Type → Type} [Monad m] {fd : Type}
    (sys : CProxySysOpsM m fd) (conc : Core.ConcOpsM m)
    (hitLimitRef : conc.Ref Bool) : CProxySysOpsM m fd :=
  { sys with
    net :=
      { sys.net with
        accept4 := fun lfd fl => do
          let r ← sys.net.accept4 lfd fl
          if let .error e := r then
            if isAcceptResourceErrno e then
              conc.writeRef hitLimitRef true
          return r } }

/-- Return `true` iff DNS job `dj` has finished (either `stateRef.done` or `conc.hasFinished`). -/
def isDnsJobDoneM {m : Type → Type} [Monad m] {fd : Type}
    (conc : Core.ConcOpsM m) (dj : ConcDnsJob fd conc.Ref conc.TaskHandle) : m Bool := do
  let st ← conc.readRef dj.stateRef
  if st.done then
    return true
  else
    conc.hasFinished dj.task

/-- Mark a DNS job cancelled without blocking and close its loop-owned wakeup reader `dnsR`. -/
def cancelAndCloseDnsM {m : Type → Type} [Monad m] {fd : Type}
    (sys : CProxySysOpsM m fd) (conc : Core.ConcOpsM m)
    (dj : ConcDnsJob fd conc.Ref conc.TaskHandle) : m Unit := do
  conc.modifyRef dj.stateRef fun st => { st with cancelled := true }
  sys.closeFd dj.dnsR

/-- Retain only still-running detached DNS jobs, closing `dnsR` on completed jobs. -/
def pruneFinishedDnsM {m : Type → Type} [Monad m] {fd : Type}
    (sys : CProxySysOpsM m fd) (conc : Core.ConcOpsM m) :
    List (ConcDnsJob fd conc.Ref conc.TaskHandle) →
    Array (ConcDnsJob fd conc.Ref conc.TaskHandle) →
    m (Array (ConcDnsJob fd conc.Ref conc.TaskHandle))
  | [], acc => pure acc
  | dj :: rest, acc => do
    if ← isDnsJobDoneM conc dj then
      sys.closeFd dj.dnsR
      pruneFinishedDnsM sys conc rest acc
    else
      pruneFinishedDnsM sys conc rest (acc.push dj)

/-- Cancel and close every detached DNS job during teardown without blocking on worker threads. -/
def cancelAllDnsM {m : Type → Type} [Monad m] {fd : Type}
    (sys : CProxySysOpsM m fd) (conc : Core.ConcOpsM m) :
    List (ConcDnsJob fd conc.Ref conc.TaskHandle) → m Unit
  | [] => pure ()
  | dj :: rest => do
    cancelAndCloseDnsM sys conc dj
    cancelAllDnsM sys conc rest

/-- Spawn a per-job wakeup `socketpair` and dedicated background DNS lookup task using
    `conc.spawnTask`, `conc.tryCatchMsg`, and `[MonadFinally m]`. On `socketpair` resource
    exhaustion, responds with HTTP `503` without leaking descriptors. -/
def startDnsM {m : Type → Type} [Monad m] [MonadFinally m] {fd : Type}
    (sys : CProxySysOpsM m fd)
    (conc : Core.ConcOpsM m)
    (limits : ProxyLimits)
    (slot : ClientSlot fd (ConcDnsJob fd conc.Ref conc.TaskHandle))
    (events : Array ConnectEvent)
    (clientFd : fd)
    (host : String) (port : UInt16) :
    m (ClientSlot fd (ConcDnsJob fd conc.Ref conc.TaskHandle) × Array ConnectEvent) := do
  match ← retryEintr
      (sys.net.socketpair .unix .stream { nonblock := true, cloexec := true })
      MAX_EINTR_RETRIES with
  | .error e =>
    let msg := s!"dns wakeup socketpair failed: errno {e}"
    let (slot1, events1) :=
      emitSlotEvent slot events
        { host := some host, port := some port, outcome := .failed, reason := some msg }
    let slot2 ← enterClosingReply sys limits slot1 clientFd 503
    return (slot2, events1)
  | .ok (dnsR, dnsW) =>
    let jobRef ← conc.mkRef ({} : DnsJobState)
    let dnsTask ← conc.spawnTask do
      let _ ← tryFinally'
        (do
          match ← conc.tryCatchMsg (sys.dns.getaddrinfo host { family := .any, sockType := .stream }) with
          | .error msg =>
            let reason := if msg.isEmpty then "dns resolution failed" else msg
            conc.modifyRef jobRef fun st =>
              if st.cancelled then st else { st with result? := some (.error reason) }
          | .ok res =>
            let mapped : Except String (Array IpAddr) :=
              match res with
              | .error dnsErr =>
                .error (if dnsErr.message.isEmpty then "dns resolution failed" else dnsErr.message)
              | .ok addrs =>
                .ok (filterUnscopedDnsAddrs addrs)
            conc.modifyRef jobRef fun st =>
              if st.cancelled then st else { st with result? := some mapped })
        (fun _ => do
          conc.modifyRef jobRef fun st =>
            let st1 :=
              if st.cancelled || st.result?.isSome then st
              else { st with result? := some (.error "dns resolution failed") }
            { st1 with done := true }
          sys.closeFd dnsW)
      pure ()
    let dj : ConcDnsJob fd conc.Ref conc.TaskHandle :=
      { stateRef := jobRef, task := dnsTask, dnsR := dnsR }
    return ({ slot with phase := .dns clientFd host port dj }, events)

/-- Poll an active `.dns` slot job, closing its loop-owned `dnsR` once a result or completion is
    observed. -/
def pollDnsM {m : Type → Type} [Monad m] {fd : Type}
    (sys : CProxySysOpsM m fd)
    (conc : Core.ConcOpsM m)
    (dj : ConcDnsJob fd conc.Ref conc.TaskHandle) :
    m (Option (Except String (Array IpAddr))) := do
  let st ← conc.readRef dj.stateRef
  match st.result? with
  | some mapped =>
    sys.closeFd dj.dnsR
    return some mapped
  | none =>
    if st.done || (← conc.hasFinished dj.task) then
      sys.closeFd dj.dnsR
      return some (.error "dns resolution failed")
    else
      return none

/-- Detach a cancelled `.dns` job on mid-lookup client disconnect, closing `dnsR` immediately if
    already completed or appending it to `dnsTasksRef` so `ppoll` watches `dnsR` until `dnsW` closes. -/
def detachDnsM {m : Type → Type} [Monad m] {fd : Type}
    (sys : CProxySysOpsM m fd)
    (conc : Core.ConcOpsM m)
    (dnsTasksRef : conc.Ref (Array (ConcDnsJob fd conc.Ref conc.TaskHandle)))
    (dj : ConcDnsJob fd conc.Ref conc.TaskHandle) : m Unit := do
  let alreadyDone ←
    conc.modifyGetRef dj.stateRef fun st => (st.done, { st with cancelled := true })
  if alreadyDone || (← conc.hasFinished dj.task) then
    sys.closeFd dj.dnsR
  else
    conc.modifyRef dnsTasksRef fun js => js.push dj

/-- Filter detached DNS jobs after `ppoll` returns extra watch revents, closing `dnsR` on
    signalled or finished jobs. -/
def reapExtraDnsListM {m : Type → Type} [Monad m] {fd : Type}
    (sys : CProxySysOpsM m fd)
    (conc : Core.ConcOpsM m)
    (extraRevs : Array Poll.PollEvents) :
    Nat →
    List (ConcDnsJob fd conc.Ref conc.TaskHandle) →
    Array (ConcDnsJob fd conc.Ref conc.TaskHandle) →
    m (Array (ConcDnsJob fd conc.Ref conc.TaskHandle))
  | _, [], kept => pure kept
  | idx, dj :: rest, kept => do
    let ev := extraRevs[idx]?.getD {}
    let signalled := ev.pollin || ev.pollhup || ev.pollerr || ev.pollnval
    if signalled || (← isDnsJobDoneM conc dj) then
      sys.closeFd dj.dnsR
      reapExtraDnsListM sys conc extraRevs (idx + 1) rest kept
    else
      reapExtraDnsListM sys conc extraRevs (idx + 1) rest (kept.push dj)

/-- Tear down every active slot, every detached DNS job, and `listenFd` (atomically recording
    closure in `listenClosedFlag` and clearing live tracking refs) without blocking on in-flight
    DNS tasks. -/
def teardownLoopM {m : Type → Type} [Monad m] {fd : Type}
    (sys : CProxySysOpsM m fd)
    (conc : Core.ConcOpsM m)
    (slotsRef : conc.Ref (Array (ClientSlot fd (ConcDnsJob fd conc.Ref conc.TaskHandle))))
    (dnsTasksRef : conc.Ref (Array (ConcDnsJob fd conc.Ref conc.TaskHandle)))
    (listenClosedFlag : conc.Ref Bool)
    (listenFd : fd)
    (slots : Array (ClientSlot fd (ConcDnsJob fd conc.Ref conc.TaskHandle)))
    (dnsTasks : Array (ConcDnsJob fd conc.Ref conc.TaskHandle))
    (events : Array ConnectEvent) : m (Array ConnectEvent) := do
  conc.writeRef slotsRef #[]
  conc.writeRef dnsTasksRef #[]
  let finalEvents ←
    teardownAllSlotsList sys (cancelAndCloseDnsM sys conc) slots.toList events
  cancelAllDnsM sys conc dnsTasks.toList
  let alreadyClosed ← conc.modifyGetRef listenClosedFlag (fun c => (c, true))
  if !alreadyClosed then
    sys.closeFd listenFd
  return finalEvents

/-- Emergency teardown invoked on abnormal loop exit: atomically drains `slotsRef` and
    `dnsTasksRef`, closes every active client/upstream/DNS-wakeup FD, cancels active DNS jobs, and
    closes `listenFd` if not yet closed. -/
def teardownTrackedM {m : Type → Type} [Monad m] {fd : Type}
    (sys : CProxySysOpsM m fd)
    (conc : Core.ConcOpsM m)
    (slotsRef : conc.Ref (Array (ClientSlot fd (ConcDnsJob fd conc.Ref conc.TaskHandle))))
    (dnsTasksRef : conc.Ref (Array (ConcDnsJob fd conc.Ref conc.TaskHandle)))
    (listenClosedFlag : conc.Ref Bool)
    (listenFd : fd) : m Unit := do
  let slots ← conc.modifyGetRef slotsRef (fun s => (s, #[]))
  let dnsTasks ← conc.modifyGetRef dnsTasksRef (fun d => (d, #[]))
  let _ ← teardownAllSlotsList sys (cancelAndCloseDnsM sys conc) slots.toList #[]
  cancelAllDnsM sys conc dnsTasks.toList
  let alreadyClosed ← conc.modifyGetRef listenClosedFlag (fun c => (c, true))
  if !alreadyClosed then
    sys.closeFd listenFd

/-- Fuel-bounded `ConcOpsM`-polymorphic proxy event loop wrapping the verified `pollAndStepTickM`
    kernel, watching both active `.dns` slots and detached in-flight DNS jobs via per-job `dnsR`
    and keeping `slotsRef`/`dnsTasksRef` synchronized across ticks for exception-safe teardown. -/
def runProxyLoopM {m : Type → Type} [Monad m] [MonadFinally m] {fd : Type}
    (sys : CProxySysOpsM m fd)
    (conc : Core.ConcOpsM m)
    (vcfg : ValidProxyConfig)
    (onHead : ByteArray → HeadDecision)
    (onResolved : String → UInt16 → Array IpAddr → ResolveDecision)
    (stopFlag listenClosedFlag : conc.Ref Bool)
    (slotsRef : conc.Ref (Array (ClientSlot fd (ConcDnsJob fd conc.Ref conc.TaskHandle))))
    (dnsTasksRef : conc.Ref (Array (ConcDnsJob fd conc.Ref conc.TaskHandle)))
    (listenFd wakeR : fd) :
    Nat →
    Array (ClientSlot fd (ConcDnsJob fd conc.Ref conc.TaskHandle)) →
    Array (ConcDnsJob fd conc.Ref conc.TaskHandle) →
    Nat →
    Array ConnectEvent →
    m (Array ConnectEvent)
  | 0, slots, dnsTasks, _, events =>
    teardownLoopM sys conc slotsRef dnsTasksRef listenClosedFlag listenFd slots dnsTasks events
  | fuel' + 1, slots, dnsTasks, acceptBackoffUntilMs, events => do
    if ← conc.readRef stopFlag then
      teardownLoopM sys conc slotsRef dnsTasksRef listenClosedFlag listenFd slots dnsTasks events
    else
      let liveDns0 ← pruneFinishedDnsM sys conc dnsTasks.toList (Array.emptyWithCapacity dnsTasks.size)
      conc.writeRef slotsRef slots
      conc.writeRef dnsTasksRef liveDns0
      let curBackoff :=
        if liveDns0.size < dnsTasks.size then 0 else acceptBackoffUntilMs
      let prevLoad := slots.size + liveDns0.size
      let extraDnsFds := liveDns0.map (·.dnsR)
      let hitAcceptLimitRef ← conc.mkRef false
      let tickOut ← pollAndStepTickM (sysWithAcceptWatch sys conc hitAcceptLimitRef)
        vcfg.config.limits onHead onResolved
        (conc.readRef stopFlag)
        (fun _ => pure false)
        (startDnsM sys conc vcfg.config.limits)
        (pollDnsM sys conc)
        (detachDnsM sys conc dnsTasksRef)
        wakeR listenFd slots events
        liveDns0.size curBackoff
        (do
          let cur ← conc.readRef dnsTasksRef
          let pruned ← pruneFinishedDnsM sys conc cur.toList (Array.emptyWithCapacity cur.size)
          conc.writeRef dnsTasksRef pruned
          return pruned.size)
        (fun dj => pure (some dj.dnsR))
        true
        extraDnsFds
        (fun extraRevs => do
          let kept ← reapExtraDnsListM sys conc extraRevs 0 liveDns0.toList
            (Array.emptyWithCapacity liveDns0.size)
          conc.writeRef dnsTasksRef kept)
      match tickOut with
      | .retryEintr =>
        let curTasks ← conc.readRef dnsTasksRef
        runProxyLoopM sys conc vcfg onHead onResolved stopFlag listenClosedFlag slotsRef dnsTasksRef
          listenFd wakeR fuel' slots curTasks curBackoff events
      | .stopOrFatal =>
        let curTasks ← conc.readRef dnsTasksRef
        teardownLoopM sys conc slotsRef dnsTasksRef listenClosedFlag listenFd slots curTasks events
      | .stepped acceptedSlots nextEvents =>
        conc.writeRef slotsRef acceptedSlots
        let curTasks ← conc.readRef dnsTasksRef
        let nextDnsTasks ←
          pruneFinishedDnsM sys conc curTasks.toList (Array.emptyWithCapacity curTasks.size)
        conc.writeRef dnsTasksRef nextDnsTasks
        let hitAcceptLimit ← conc.readRef hitAcceptLimitRef
        let nowAfter ← monoNowMs sys
        let postStepLoad := acceptedSlots.size + nextDnsTasks.size
        let nextBackoff : Nat :=
          if hitAcceptLimit then
            nowAfter + ACCEPT_EMFILE_BACKOFF_MS
          else if postStepLoad < prevLoad || nowAfter >= curBackoff then
            0
          else
            curBackoff
        runProxyLoopM sys conc vcfg onHead onResolved stopFlag listenClosedFlag slotsRef dnsTasksRef
          listenFd wakeR fuel' acceptedSlots nextDnsTasks nextBackoff nextEvents

/-- Scoped polymorphic `withProxy` execution parameterized directly over `CProxySysOpsM m fd` and
    `Core.ConcOpsM m` for an already-validated `ValidProxyConfig`. Wraps listener creation, worker
    loop execution (with `teardownTrackedM` on abnormal loop exit), and finalizer shutdown in
    `conc.tryCatchMsg` / `tryFinally'` so host exceptions convert to `ProxyError` and never leak
    active sockets, DNS wakeup FDs, or listener/wakeup descriptors. -/
def withProxyM {m : Type → Type} [Monad m] [MonadFinally m] {fd : Type} {α : Type}
    (sys : CProxySysOpsM m fd)
    (conc : Core.ConcOpsM m)
    (vcfg : ValidProxyConfig)
    (action : RunningProxy → m (Except ProxyError α)) :
    m (Except ProxyError (α × Array ConnectEvent)) := do
  match ← conc.tryCatchMsg (createListener sys vcfg) with
  | .error msg => return .error (Model.mapRawErrorPure (.userError msg))
  | .ok (.error err) => return .error err
  | .ok (.ok (listenFd, wakeR, wakeW, boundPort)) =>
    let onHead := Model.decideConnectHead vcfg.config
    let onResolved := Model.decideResolvedIps vcfg.config.ipPolicy
    match ← conc.tryCatchMsg (do
        let stopFlag ← conc.mkRef false
        let listenClosedFlag ← conc.mkRef false
        let slotsRef ← conc.mkRef (#[] : Array (ClientSlot fd (ConcDnsJob fd conc.Ref conc.TaskHandle)))
        let dnsTasksRef ← conc.mkRef (#[] : Array (ConcDnsJob fd conc.Ref conc.TaskHandle))
        let loopTask ← conc.spawnTask (do
          match ← conc.tryCatchMsg
              (runProxyLoopM sys conc vcfg onHead onResolved stopFlag listenClosedFlag
                slotsRef dnsTasksRef listenFd wakeR LOOP_FUEL #[] #[] 0 #[]) with
          | .ok evs => return (Except.ok evs : Except String (Array ConnectEvent))
          | .error msg =>
            let _ ← conc.tryCatchMsg
              (teardownTrackedM sys conc slotsRef dnsTasksRef listenClosedFlag listenFd)
            return (Except.error msg : Except String (Array ConnectEvent)))
        pure (stopFlag, listenClosedFlag, loopTask)) with
    | .error msg =>
      let _ ← conc.tryCatchMsg (do
        sys.closeFd listenFd
        sys.closeFd wakeR
        sys.closeFd wakeW)
      return .error (Model.mapRawErrorPure (.userError msg))
    | .ok (stopFlag, listenClosedFlag, loopTask) =>
      let (actRes, stopRes) ←
        tryFinally'
          (action { handleId := 1, port := boundPort })
          (fun _ =>
            conc.tryCatchMsg (do
              let (waitRes, _) ←
                tryFinally'
                  (do
                    conc.writeRef stopFlag true
                    let _ ← retryEintr
                      (sys.net.sendto wakeW (ByteArray.mk #[1]) { nosignal := true, dontwait := true })
                      MAX_EINTR_RETRIES
                    conc.waitTask loopTask)
                  (fun _ => do
                    let alreadyClosed ← conc.modifyGetRef listenClosedFlag (fun c => (c, true))
                    if !alreadyClosed then
                      sys.closeFd listenFd
                    sys.closeFd wakeR
                    sys.closeFd wakeW)
              match waitRes with
              | .error msg => return (Except.error msg : Except String (Array ConnectEvent))
              | .ok inner => return inner))
      match actRes, stopRes with
      | .error ae, _ => return .error ae
      | .ok _, .error msg => return .error (Model.mapRawErrorPure (.userError msg))
      | .ok _, .ok (.error msg) => return .error (Model.mapRawErrorPure (.userError msg))
      | .ok a, .ok (.ok evs) => return .ok (a, evs)

end LeanSwe.ConnectProxy.SysBridge.Driver
