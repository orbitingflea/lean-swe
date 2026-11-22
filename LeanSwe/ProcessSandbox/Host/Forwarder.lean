import LeanSwe.LinuxSyscall.Common.Types
import LeanSwe.LinuxSyscall.Files.Types
import LeanSwe.LinuxSyscall.Net.Types
import LeanSwe.LinuxSyscall.Poll.Types
import LeanSwe.LinuxSyscall.Files.Interface
import LeanSwe.LinuxSyscall.Net.Interface
import LeanSwe.LinuxSyscall.Poll.Interface
import LeanSwe.NetRelay.Types
import LeanSwe.NetRelay.Interface

namespace LeanSwe.ProcessSandbox.Host.Forwarder

open LeanSwe.LinuxSyscall
open LeanSwe.NetRelay

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

/-- Advance one poll tick for a single `ForwardRelayConn`, reusing `LeanSwe.NetRelay` `16 KiB` ring operations and directional `SHUT_WR` half-close. -/
def stepForwardRelay {m : Type → Type} [Monad m] {fd : Type}
    (net : Net.NetOpsM m fd) (closeFd : fd → m Unit)
    (c0 : ForwardRelayConn fd) (bRev hRev : Poll.PollEvents) :
    m (Option (ForwardRelayConn fd)) := do
  if bRev.pollnval || hRev.pollnval then
    closeForwardRelay closeFd c0
    return none
  match ← stepRelayConnect net c0 hRev with
  | none =>
    closeForwardRelay closeFd c0
    return none
  | some c1 =>
    let c2? ←
      if !c1.boxEofIn && (bRev.pollin || bRev.pollhup || bRev.pollerr) then
        match ← recvIntoRing net c1.boxFd MAX_RELAY_IO_STEPS c1.b2h with
        | none => pure none
        | some (b2h', eof') => pure (some { c1 with b2h := b2h', boxEofIn := c1.boxEofIn || eof' })
      else
        pure (some c1)
    match c2? with
    | none =>
      closeForwardRelay closeFd c1
      return none
    | some c2 =>
      let c3? ←
        if !c2.hostConnecting && !c2.hostEofIn && (hRev.pollin || hRev.pollhup || hRev.pollerr) then
          match ← recvIntoRing net c2.hostFd MAX_RELAY_IO_STEPS c2.h2b with
          | none => pure none
          | some (h2b', eof') => pure (some { c2 with h2b := h2b', hostEofIn := c2.hostEofIn || eof' })
        else
          pure (some c2)
      match c3? with
      | none =>
        closeForwardRelay closeFd c2
        return none
      | some c3 =>
        let c4? ←
          if !c3.hostConnecting then
            let b2hRes? ←
              if !c3.b2h.isEmpty then
                flushRingNonblock net c3.hostFd MAX_RELAY_IO_STEPS c3.b2h
              else
                pure (some c3.b2h)
            match b2hRes? with
            | none => pure none
            | some b2h' =>
              let c3a := { c3 with b2h := b2h' }
              if c3a.boxEofIn && c3a.b2h.isEmpty && !c3a.hostShutdownWr then
                let _ ← shutdownWrClean net c3a.hostFd MAX_RELAY_IO_STEPS
                pure (some { c3a with hostShutdownWr := true })
              else
                pure (some c3a)
          else
            pure (some c3)
        match c4? with
        | none =>
          closeForwardRelay closeFd c3
          return none
        | some c4 =>
          let h2bRes? ←
            if !c4.h2b.isEmpty then
              flushRingNonblock net c4.boxFd MAX_RELAY_IO_STEPS c4.h2b
            else
              pure (some c4.h2b)
          match h2bRes? with
          | none =>
            closeForwardRelay closeFd c4
            return none
          | some h2b' =>
            let c5 := { c4 with h2b := h2b' }
            let c6 ←
              if c5.hostEofIn && c5.h2b.isEmpty && !c5.boxShutdownWr then do
                let _ ← shutdownWrClean net c5.boxFd MAX_RELAY_IO_STEPS
                pure { c5 with boxShutdownWr := true }
              else
                pure c5
            if c6.boxEofIn && c6.b2h.isEmpty && c6.hostEofIn && c6.h2b.isEmpty then
              closeForwardRelay closeFd c6
              return none
            else
              return some c6

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
    let wakeRev := revents[0]?.getD {}
    if wakeRev.pollin || wakeRev.pollhup || wakeRev.pollerr || wakeRev.pollnval then
      return .stop
    if ← checkStop then
      return .stop
    let mut nextRelays : Array (ForwardRelayConn fd) := Array.emptyWithCapacity relays.size
    for h : i in [0 : relays.size] do
      let c := relays[i]
      let (bIdx?, hIdx?) := plan.relayIndices[i]?.getD (none, none)
      let bRev := match bIdx? with | some idx => revents[idx]?.getD {} | none => {}
      let hRev := match hIdx? with | some idx => revents[idx]?.getD {} | none => {}
      match ← stepForwardRelay net closeFd c bRev hRev with
      | some c' => nextRelays := nextRelays.push c'
      | none => pure ()
    for (lIdx, lfd, hport) in plan.listenerIndices do
      let lRev := revents[lIdx]?.getD {}
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

/-- Live `IO` handle for a dedicated host-side TCP port-forwarder task and its wakeup `socketpair`. -/
structure IoForwarderHandle where
  /-- Flag checked by the forwarder loop before and after `ppoll`. -/
  stopRequested : IO.Ref Bool
  /-- Read end of the wakeup `socketpair` (closed after `IO.wait`). -/
  wakeR : RawFd
  /-- Write end of the wakeup `socketpair` (signaled and closed on stop). -/
  wakeWRef : IO.Ref (Option RawFd)
  /-- Handed-off box listener descriptors (closed after `IO.wait`). -/
  listenerFds : Array RawFd
  /-- Dedicated OS task executing `runForwarderLoop`. -/
  task : Task (Except IO.Error Unit)

/-- Start a dedicated `IO` TCP port-forwarder task over `(listenerFds, hostPorts)` with `socketpair` wakeup. -/
def startIoForwarder (listenerFds : Array RawFd) (hostPorts : Array UInt16) :
    IO (Except Errno IoForwarderHandle) := do
  match ← retryEintr
      (Net.defaultOps.socketpair .unix .stream { nonblock := true, cloexec := true })
      DEFAULT_EINTR_FUEL with
  | .error e => return .error e
  | .ok (wakeR, wakeW) =>
    let stopRequested ← IO.mkRef false
    let wakeWRef ← IO.mkRef (some wakeW)
    let listeners := listenerFds.zip hostPorts
    let closeFd : RawFd → IO Unit := fun h => do
      let _ ← Files.defaultOps.close h
      pure ()
    let task ← IO.asTask (prio := .dedicated) do
      runForwarderLoop Net.defaultOps Poll.defaultOps closeFd
        stopRequested.get wakeR listeners #[] FORWARDER_LOOP_FUEL
    return .ok {
      stopRequested := stopRequested
      wakeR := wakeR
      wakeWRef := wakeWRef
      listenerFds := listenerFds
      task := task
    }

/-- Signal `h`, wait for its dedicated forwarder task to terminate and close all relay sockets, then close `wakeR` and all listener descriptors. -/
def stopIoForwarder (h : IoForwarderHandle) : IO Unit := do
  h.stopRequested.set true
  let wakeW? ← h.wakeWRef.modifyGet fun w => (w, none)
  match wakeW? with
  | some w =>
    let _ ← retryEintr
      (Net.defaultOps.sendto w (ByteArray.mk #[1]) { nosignal := true, dontwait := true })
      DEFAULT_EINTR_FUEL
    let _ ← Files.defaultOps.close w
    pure ()
  | none => pure ()
  let _ ← IO.wait h.task
  let closeFd : RawFd → IO Unit := fun d => do
    let _ ← Files.defaultOps.close d
    pure ()
  closeFd h.wakeR
  for lfd in h.listenerFds do
    closeFd lfd

end LeanSwe.ProcessSandbox.Host.Forwarder
