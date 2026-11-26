import Core.ConcOps
import LeanSwe.LinuxSyscall.Common.Types
import LeanSwe.LinuxSyscall.Files.Types
import LeanSwe.LinuxSyscall.Net.Types
import LeanSwe.LinuxSyscall.Poll.Types
import LeanSwe.NetRelay.Types
import LeanSwe.NetRelay.Interface
import LeanSwe.ProcessSandbox.Raw.Types.Internal

namespace LeanSwe.ProcessSandbox.Raw.SysBridge.Forwarder

open LeanSwe.LinuxSyscall
open LeanSwe.NetRelay
open LeanSwe.ProcessSandbox.Raw

/-- Maximum number of simultaneous active TCP port-forward relay connections per box (`128`). -/
def MAX_RELAY_SLOTS : Nat := 128

/-- Maximum connections accepted per listener in a single `ppoll` tick (`256`). -/
def MAX_ACCEPT_BATCH : Nat := 256

/-- Structural poll-loop fuel bound for the host TCP port-forwarder task (`2^64`). -/
def FORWARDER_LOOP_FUEL : Nat := UInt64.size

/-- One active bidirectional non-blocking TCP relay between a box-accepted socket and host `127.0.0.1:hostPort`. -/
structure ForwardRelayConn (fd : Type) where
  /-- Accepted socket originating inside the sandbox's network namespace. -/
  boxFd : fd
  /-- Connected or connecting socket targeting host `127.0.0.1:hostPort`. -/
  hostFd : fd
  /-- Target host loopback TCP port. -/
  hostPort : UInt16
  /-- `true` while non-blocking `connect(2)` on `hostFd` is awaiting `POLLOUT` + `SO_ERROR`. -/
  hostConnecting : Bool := false
  /-- `true` once `boxFd` has delivered inbound EOF. -/
  boxEofIn : Bool := false
  /-- `true` once `hostFd` has delivered inbound EOF. -/
  hostEofIn : Bool := false
  /-- `true` once `shutdown(boxFd, SHUT_WR)` has been invoked. -/
  boxShutdownWr : Bool := false
  /-- `true` once `shutdown(hostFd, SHUT_WR)` has been invoked. -/
  hostShutdownWr : Bool := false
  /-- Box-to-host `16 KiB` FIFO ring buffer from `LeanSwe.NetRelay`. -/
  b2h : RingBuf := {}
  /-- Host-to-box `16 KiB` FIFO ring buffer from `LeanSwe.NetRelay`. -/
  h2b : RingBuf := {}

/-- Compute requested `PollEvents` for `c.boxFd` (`isEmpty = true` omits the descriptor from `ppoll`). -/
def ForwardRelayConn.boxPollEvents {fd : Type} (c : ForwardRelayConn fd) : Poll.PollEvents :=
  { pollin := !c.boxEofIn && c.b2h.writeAvail > 0
    pollout := !c.h2b.isEmpty }

/-- Compute requested `PollEvents` for `c.hostFd` (`isEmpty = true` omits the descriptor from `ppoll`). -/
def ForwardRelayConn.hostPollEvents {fd : Type} (c : ForwardRelayConn fd) : Poll.PollEvents :=
  if c.hostConnecting then
    { pollout := true }
  else
    { pollin := !c.hostEofIn && c.h2b.writeAvail > 0
      pollout := !c.b2h.isEmpty }

/-- Close both endpoints of `c`. -/
def closeForwardRelay {m : Type → Type} [Monad m] {fd : Type}
    (closeFd : fd → m Unit) (c : ForwardRelayConn fd) : m Unit := do
  closeFd c.boxFd
  closeFd c.hostFd

/-- Close every active relay connection in `relays`. -/
def closeAllRelays {m : Type → Type} [Monad m] {fd : Type}
    (closeFd : fd → m Unit) (relays : Array (ForwardRelayConn fd)) : m Unit := do
  for c in relays do
    closeForwardRelay closeFd c

/-- Complete pending non-blocking `connect(2)` via `SO_ERROR` when `hostConnecting` and `hRev` signals completion. -/
def stepRelayConnect {m : Type → Type} [Monad m] {fd : Type}
    (net : Net.NetOpsM m fd) (c : ForwardRelayConn fd) (hRev : Poll.PollEvents) :
    m (Option (ForwardRelayConn fd)) := do
  if c.hostConnecting && (hRev.pollout || hRev.pollerr || hRev.pollhup) then
    match ← net.getsockopt c.hostFd .error with
    | .ok 0 => return some { c with hostConnecting := false }
    | _ => return none
  else
    return some c

/-- Non-blocking inbound box-to-host ring read step for `stepForwardRelay`. -/
def stepRelayRecvBox {m : Type → Type} [Monad m] {fd : Type}
    (net : Net.NetOpsM m fd) (c1 : ForwardRelayConn fd) (bRev : Poll.PollEvents) :
    m (Option (ForwardRelayConn fd)) :=
  if !c1.boxEofIn && (bRev.pollin || bRev.pollhup || bRev.pollerr) then do
    match ← recvIntoRing net c1.boxFd MAX_RELAY_IO_STEPS c1.b2h with
    | none => pure none
    | some (b2h', eof') => pure (some { c1 with b2h := b2h', boxEofIn := c1.boxEofIn || eof' })
  else
    pure (some c1)

/-- Non-blocking inbound host-to-box ring read step for `stepForwardRelay`. -/
def stepRelayRecvHost {m : Type → Type} [Monad m] {fd : Type}
    (net : Net.NetOpsM m fd) (c2 : ForwardRelayConn fd) (hRev : Poll.PollEvents) :
    m (Option (ForwardRelayConn fd)) :=
  if !c2.hostConnecting && !c2.hostEofIn && (hRev.pollin || hRev.pollhup || hRev.pollerr) then do
    match ← recvIntoRing net c2.hostFd MAX_RELAY_IO_STEPS c2.h2b with
    | none => pure none
    | some (h2b', eof') => pure (some { c2 with h2b := h2b', hostEofIn := c2.hostEofIn || eof' })
  else
    pure (some c2)

/-- Flush `rb` via `flushRingNonblock` when non-empty, or return `some rb` when empty. -/
def flushRingIfNonEmpty {m : Type → Type} [Monad m] {fd : Type}
    (net : Net.NetOpsM m fd) (targetFd : fd) (rb : RingBuf) : m (Option RingBuf) :=
  if !rb.isEmpty then flushRingNonblock net targetFd MAX_RELAY_IO_STEPS rb
  else pure (some rb)

/-- Non-blocking outbound box-to-host ring flush and half-close step for `stepForwardRelay`. -/
def stepRelayFlushHost {m : Type → Type} [Monad m] {fd : Type}
    (net : Net.NetOpsM m fd) (c3 : ForwardRelayConn fd) :
    m (Option (ForwardRelayConn fd)) :=
  if !c3.hostConnecting then do
    match ← flushRingIfNonEmpty net c3.hostFd c3.b2h with
    | none => pure none
    | some b2h' =>
      let c3a := { c3 with b2h := b2h' }
      if c3a.boxEofIn && c3a.b2h.isEmpty && !c3a.hostShutdownWr then do
        let _ ← shutdownWrClean net c3a.hostFd MAX_RELAY_IO_STEPS
        pure (some { c3a with hostShutdownWr := true })
      else
        pure (some c3a)
  else
    pure (some c3)

/-- Perform `shutdownWrClean` on `c.boxFd` when `c.hostEofIn && c.h2b.isEmpty && !c.boxShutdownWr`. -/
def maybeShutdownBoxWr {m : Type → Type} [Monad m] {fd : Type}
    (net : Net.NetOpsM m fd) (c : ForwardRelayConn fd) : m (ForwardRelayConn fd) :=
  if c.hostEofIn && c.h2b.isEmpty && !c.boxShutdownWr then do
    let _ ← shutdownWrClean net c.boxFd MAX_RELAY_IO_STEPS
    pure { c with boxShutdownWr := true }
  else
    pure c

/-- Advance one poll tick for a single `ForwardRelayConn`, reusing `LeanSwe.NetRelay` `16 KiB` ring operations and directional `SHUT_WR` half-close. -/
def stepForwardRelay {m : Type → Type} [Monad m] {fd : Type}
    (net : Net.NetOpsM m fd) (closeFd : fd → m Unit)
    (c0 : ForwardRelayConn fd) (bRev hRev : Poll.PollEvents) :
    m (Option (ForwardRelayConn fd)) :=
  if bRev.pollnval || hRev.pollnval then do
    closeForwardRelay closeFd c0
    pure none
  else do
    match ← stepRelayConnect net c0 hRev with
    | none =>
      closeForwardRelay closeFd c0
      pure none
    | some c1 =>
      match ← stepRelayRecvBox net c1 bRev with
      | none =>
        closeForwardRelay closeFd c1
        pure none
      | some c2 =>
        match ← stepRelayRecvHost net c2 hRev with
        | none =>
          closeForwardRelay closeFd c2
          pure none
        | some c3 =>
          match ← stepRelayFlushHost net c3 with
          | none =>
            closeForwardRelay closeFd c3
            pure none
          | some c4 =>
            match ← flushRingIfNonEmpty net c4.boxFd c4.h2b with
            | none =>
              closeForwardRelay closeFd c4
              pure none
            | some h2b' =>
              let c6 ← maybeShutdownBoxWr net { c4 with h2b := h2b' }
              if c6.boxEofIn && c6.b2h.isEmpty && c6.hostEofIn && c6.h2b.isEmpty then do
                closeForwardRelay closeFd c6
                pure none
              else
                pure (some c6)

/-- Accept pending connections on one handed-off listener socket up to `MAX_RELAY_SLOTS` and initiate non-blocking `connect(127.0.0.1:hostPort)`. -/
def acceptOnListenerLoop {m : Type → Type} [Monad m] {fd : Type}
    (net : Net.NetOpsM m fd) (closeFd : fd → m Unit)
    (lfd : fd) (hostPort : UInt16) :
    Nat → Array (ForwardRelayConn fd) → m (Array (ForwardRelayConn fd))
  | 0, relays => pure relays
  | fuel + 1, relays => do
    if relays.size ≥ MAX_RELAY_SLOTS then
      return relays
    match ← net.accept4 lfd { nonblock := true, cloexec := true } with
    | .error e =>
      if e == Errno.EINTR then
        acceptOnListenerLoop net closeFd lfd hostPort fuel relays
      else
        return relays
    | .ok (bfd, _) =>
      match ← net.socket .inet .stream { nonblock := true, cloexec := true } 0 with
      | .error _ =>
        closeFd bfd
        acceptOnListenerLoop net closeFd lfd hostPort fuel relays
      | .ok hfd =>
        let targetAddr := Net.SockAddr.ipv4 Net.INADDR_LOOPBACK hostPort
        match ← net.connect hfd targetAddr with
        | .ok () =>
          let conn : ForwardRelayConn fd :=
            { boxFd := bfd, hostFd := hfd, hostPort := hostPort, hostConnecting := false }
          acceptOnListenerLoop net closeFd lfd hostPort fuel (relays.push conn)
        | .error e =>
          if e == Errno.EINPROGRESS then
            let conn : ForwardRelayConn fd :=
              { boxFd := bfd, hostFd := hfd, hostPort := hostPort, hostConnecting := true }
            acceptOnListenerLoop net closeFd lfd hostPort fuel (relays.push conn)
          else
            closeFd hfd
            closeFd bfd
            acceptOnListenerLoop net closeFd lfd hostPort fuel relays

/-- Poll-entry layout mapping indices in the `ppoll` request array back to listeners and active relays. -/
structure ForwarderPollPlan (fd : Type) where
  /-- Descriptor/event pairs passed to `ppoll` (entry `0` is always `wakeR`). -/
  entries : Array (fd × Poll.PollEvents)
  /-- Indices in `entries` paired with `(listenerFd, hostPort)` (empty when `relays.size ≥ MAX_RELAY_SLOTS`). -/
  listenerIndices : Array (Nat × fd × UInt16)
  /-- Optional `(boxPollIdx?, hostPollIdx?)` for each relay in `relays`. -/
  relayIndices : Array (Option Nat × Option Nat)

/-- Construct the `ppoll` descriptor list for one forwarder tick, suppressing listener `POLLIN` when `relays.size ≥ MAX_RELAY_SLOTS`. -/
def buildForwarderPollPlan {fd : Type} (wakeR : fd)
    (listeners : Array (fd × UInt16)) (relays : Array (ForwardRelayConn fd)) :
    ForwarderPollPlan fd :=
  let initEntries : Array (fd × Poll.PollEvents) := #[(wakeR, { pollin := true })]
  let (entries1, listenerIndices) :=
    if relays.size < MAX_RELAY_SLOTS then
      listeners.foldl
        (fun (acc : Array (fd × Poll.PollEvents) × Array (Nat × fd × UInt16)) (lp : fd × UInt16) =>
          let (es, lis) := acc
          (es.push (lp.1, { pollin := true }), lis.push (es.size, lp.1, lp.2)))
        (initEntries, #[])
    else
      (initEntries, #[])
  let (entries2, relayIndices) :=
    relays.foldl
      (fun (acc : Array (fd × Poll.PollEvents) × Array (Option Nat × Option Nat)) (c : ForwardRelayConn fd) =>
        let (es0, ris) := acc
        let bev := c.boxPollEvents
        let (es1, bIdx?) :=
          if !bev.isEmpty then (es0.push (c.boxFd, bev), some es0.size) else (es0, none)
        let hev := c.hostPollEvents
        let (es2, hIdx?) :=
          if !hev.isEmpty then (es1.push (c.hostFd, hev), some es1.size) else (es1, none)
        (es2, ris.push (bIdx?, hIdx?)))
      (entries1, Array.emptyWithCapacity relays.size)
  { entries := entries2, listenerIndices := listenerIndices, relayIndices := relayIndices }

/-- Outcome of a single forwarder poll tick. -/
inductive ForwarderTickResult (fd : Type) where
  /-- Stop requested, wakeup socket signaled, or fatal `ppoll` error. -/
  | stop
  /-- `ppoll` was interrupted by `EINTR`; retry with unchanged relays. -/
  | retryEintr
  /-- Tick completed cleanly with updated active `relays`. -/
  | stepped (relays : Array (ForwardRelayConn fd))

/-- Advance all active relays across indices `0 .. relays.size - 1` using `stepForwardRelay`. -/
def stepRelaysAt {m : Type → Type} [Monad m] {fd : Type}
    (net : Net.NetOpsM m fd) (closeFd : fd → m Unit)
    (relays : Array (ForwardRelayConn fd))
    (relayIndices : Array (Option Nat × Option Nat))
    (revents : Array Poll.PollEvents) :
    Nat → Array (ForwardRelayConn fd) → m (Array (ForwardRelayConn fd))
  | 0, acc => pure acc
  | rem + 1, acc => do
    let i := relays.size - (rem + 1)
    if h : i < relays.size then
      let c := relays[i]
      let (bIdx?, hIdx?) := relayIndices[i]?.getD (none, none)
      let bRev := match bIdx? with | some idx => revents[idx]?.getD {} | none => {}
      let hRev := match hIdx? with | some idx => revents[idx]?.getD {} | none => {}
      match ← stepForwardRelay net closeFd c bRev hRev with
      | some c' => stepRelaysAt net closeFd relays relayIndices revents rem (acc.push c')
      | none => stepRelaysAt net closeFd relays relayIndices revents rem acc
    else
      pure acc

/-- Execute one `ppoll` tick of the host TCP forwarder (wake check, listener accept, and bidirectional relay steps). -/
def stepForwarderTick {m : Type → Type} [Monad m] {fd : Type}
    (net : Net.NetOpsM m fd) (poll : Poll.PollOpsM m fd) (closeFd : fd → m Unit)
    (checkStop : m Bool) (wakeR : fd) (listeners : Array (fd × UInt16))
    (relays : Array (ForwardRelayConn fd)) : m (ForwarderTickResult fd) := do
  if ← checkStop then
    return .stop
  let plan := buildForwarderPollPlan wakeR listeners relays
  match ← poll.ppoll plan.entries none with
  | .error e =>
    if e == Errno.EINTR then return .retryEintr else return .stop
  | .ok revents =>
    let wakeRev : Poll.PollEvents := revents[0]?.getD {}
    if wakeRev.pollin || wakeRev.pollhup || wakeRev.pollerr || wakeRev.pollnval then
      return .stop
    if ← checkStop then
      return .stop
    let mut nextRelays ←
      stepRelaysAt net closeFd relays plan.relayIndices revents relays.size
        (Array.emptyWithCapacity relays.size)
    for (lIdx, lfd, hport) in plan.listenerIndices do
      let lRev : Poll.PollEvents := revents[lIdx]?.getD {}
      if lRev.pollin && nextRelays.size < MAX_RELAY_SLOTS then
        nextRelays ← acceptOnListenerLoop net closeFd lfd hport MAX_ACCEPT_BATCH nextRelays
    return .stepped nextRelays

/-- Fuel-bounded host TCP forwarder event loop closing all active relays before returning. -/
def runForwarderLoop {m : Type → Type} [Monad m] {fd : Type}
    (net : Net.NetOpsM m fd) (poll : Poll.PollOpsM m fd) (closeFd : fd → m Unit)
    (checkStop : m Bool) (wakeR : fd) (listeners : Array (fd × UInt16)) :
    Array (ForwardRelayConn fd) → Nat → m Unit
  | relays, 0 => closeAllRelays closeFd relays
  | relays, fuel + 1 => do
    match ← stepForwarderTick net poll closeFd checkStop wakeR listeners relays with
    | .stop => closeAllRelays closeFd relays
    | .retryEintr => runForwarderLoop net poll closeFd checkStop wakeR listeners relays fuel
    | .stepped relays' => runForwarderLoop net poll closeFd checkStop wakeR listeners relays' fuel

/-- Start a dedicated TCP port-forwarder task over `(listenerFds, hostPorts)` with `socketpair` wakeup using `conc : Core.ConcOpsM m`. -/
def startForwarderM {m : Type → Type} [Monad m] {fd : Type}
    (files : Files.FilesOpsM m fd) (net : Net.NetOpsM m fd) (poll : Poll.PollOpsM m fd)
    (conc : Core.ConcOpsM m) (listenerFds : Array fd) (hostPorts : Array UInt16) :
    m (Except Errno (ConcForwarderHandle fd conc.Ref conc.TaskHandle)) := do
  match ← retryEintr
      (net.socketpair .unix .stream { nonblock := true, cloexec := true })
      DEFAULT_EINTR_FUEL with
  | .error e => return .error e
  | .ok (wakeR, wakeW) =>
    let stopRequested ← conc.mkRef false
    let wakeWRef ← conc.mkRef (some wakeW)
    let listeners := listenerFds.zip hostPorts
    let closeFd : fd → m Unit := fun h => do
      let _ ← files.close h
      pure ()
    let task ← conc.spawnTask do
      let _ ← conc.tryCatchMsg
        (runForwarderLoop net poll closeFd
          (conc.readRef stopRequested) wakeR listeners #[] FORWARDER_LOOP_FUEL)
      pure ()
    return .ok {
      stopRequested := stopRequested
      wakeR := wakeR
      wakeWRef := wakeWRef
      listenerFds := listenerFds
      task := task
    }

/-- Signal `h`, wait for its dedicated forwarder task to terminate and close all relay sockets, then close `wakeR` and all listener descriptors. -/
def stopForwarderM {m : Type → Type} [Monad m] {fd : Type}
    (files : Files.FilesOpsM m fd) (net : Net.NetOpsM m fd)
    (conc : Core.ConcOpsM m) (h : ConcForwarderHandle fd conc.Ref conc.TaskHandle) :
    m Unit := do
  conc.writeRef h.stopRequested true
  let wakeW? ← conc.modifyGetRef h.wakeWRef fun w => (w, none)
  match wakeW? with
  | some w =>
    let _ ← retryEintr
      (net.sendto w (ByteArray.mk #[1]) { nosignal := true, dontwait := true })
      DEFAULT_EINTR_FUEL
    let _ ← files.close w
    pure ()
  | none => pure ()
  let _ ← conc.waitTask h.task
  let closeFd : fd → m Unit := fun d => do
    let _ ← files.close d
    pure ()
  closeFd h.wakeR
  for lfd in h.listenerFds do
    closeFd lfd

end LeanSwe.ProcessSandbox.Raw.SysBridge.Forwarder
