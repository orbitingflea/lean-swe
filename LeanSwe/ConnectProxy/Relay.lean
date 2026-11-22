import LeanSwe.LinuxSyscall.Common.Types
import LeanSwe.LinuxSyscall.Net.Types
import LeanSwe.LinuxSyscall.Poll.Types
import LeanSwe.NetRelay.Types
import LeanSwe.NetRelay.Interface

namespace LeanSwe.ConnectProxy.Relay

open LeanSwe.LinuxSyscall
open LeanSwe.LinuxSyscall.Net
open LeanSwe.LinuxSyscall.Poll
open LeanSwe.NetRelay

export LeanSwe.NetRelay (RING_CAP MAX_RELAY_IO_STEPS RingBuf)

/-- Static HTTP `200 Connection Established` response header bytes. -/
def reply200Bytes : ByteArray :=
  asciiBytes ['H', 'T', 'T', 'P', '/', '1', '.', '1', ' ', '2', '0', '0', ' ',
    'C', 'o', 'n', 'n', 'e', 'c', 't', 'i', 'o', 'n', ' ',
    'E', 's', 't', 'a', 'b', 'l', 'i', 's', 'h', 'e', 'd', '\r', '\n', '\r', '\n']

/-- Static HTTP `403 Forbidden` response header bytes. -/
def reply403Bytes : ByteArray :=
  asciiBytes ['H', 'T', 'T', 'P', '/', '1', '.', '1', ' ', '4', '0', '3', ' ',
    'F', 'o', 'r', 'b', 'i', 'd', 'd', 'e', 'n', '\r', '\n',
    'C', 'o', 'n', 't', 'e', 'n', 't', '-', 'L', 'e', 'n', 'g', 't', 'h', ':', ' ', '0',
    '\r', '\n', '\r', '\n']

/-- Static HTTP `502 Bad Gateway` response header bytes. -/
def reply502Bytes : ByteArray :=
  asciiBytes ['H', 'T', 'T', 'P', '/', '1', '.', '1', ' ', '5', '0', '2', ' ',
    'B', 'a', 'd', ' ', 'G', 'a', 't', 'e', 'w', 'a', 'y', '\r', '\n',
    'C', 'o', 'n', 't', 'e', 'n', 't', '-', 'L', 'e', 'n', 'g', 't', 'h', ':', ' ', '0',
    '\r', '\n', '\r', '\n']

/-- Static HTTP `503 Service Unavailable` response header bytes. -/
def reply503Bytes : ByteArray :=
  asciiBytes ['H', 'T', 'T', 'P', '/', '1', '.', '1', ' ', '5', '0', '3', ' ',
    'S', 'e', 'r', 'v', 'i', 'c', 'e', ' ', 'U', 'n', 'a', 'v', 'a', 'i', 'l', 'a', 'b', 'l', 'e', '\r', '\n',
    'C', 'o', 'n', 't', 'e', 'n', 't', '-', 'L', 'e', 'n', 'g', 't', 'h', ':', ' ', '0',
    '\r', '\n', '\r', '\n']

/-- Bidirectional TCP tunnel state with pipelined handshake tail and half-close tracking. -/
structure RelayState (fd : Type) where
  /-- Open client socket descriptor (`none` once closed). -/
  clientFd? : Option fd := none
  /-- Open upstream socket descriptor (`none` once closed). -/
  upstreamFd? : Option fd := none
  /-- Coalesced client payload bytes received after `\r\n\r\n` during handshake. -/
  pendingPrefix : ByteArray := ByteArray.empty
  /-- Offset of already-forwarded bytes within `pendingPrefix`. -/
  pendingOff : Nat := 0
  /-- Client-to-upstream `16 KiB` FIFO buffer. -/
  c2u : RingBuf := {}
  /-- Upstream-to-client `16 KiB` FIFO buffer (seeded with `200 Connection Established`). -/
  u2c : RingBuf := {}
  /-- `true` once client `recvfrom` has returned `0` (`EOF`). -/
  cEof : Bool := false
  /-- `true` once upstream `recvfrom` has returned `0` (`EOF`). -/
  uEof : Bool := false
  /-- `true` once `shutdown(clientFd, .wr)` has completed. -/
  cWrClosed : Bool := false
  /-- `true` once `shutdown(upstreamFd, .wr)` has completed. -/
  uWrClosed : Bool := false

/-- Initialize a `RelayState` with `200 Connection Established` queued to the client and any pipelined client tail queued to upstream. -/
def RelayState.init {fd : Type} (clientFd upstreamFd : fd) (pipelinedPrefix : ByteArray) : RelayState fd :=
  { clientFd? := some clientFd
    upstreamFd? := some upstreamFd
    pendingPrefix := pipelinedPrefix
    pendingOff := 0
    c2u := {}
    u2c := ({} : RingBuf).push reply200Bytes
    cEof := false
    uEof := false
    cWrClosed := false
    uWrClosed := false }

/-- Return `true` iff all pipelined post-`\r\n\r\n` handshake bytes have been flushed to `upstreamFd`. -/
def RelayState.prefixFlushed {fd : Type} (st : RelayState fd) : Bool :=
  st.pendingOff >= st.pendingPrefix.size

/-- Return `true` iff both client and upstream descriptors have been closed. -/
def RelayState.isClosed {fd : Type} (st : RelayState fd) : Bool :=
  st.clientFd?.isNone && st.upstreamFd?.isNone

/-- Compute requested `PollEvents` for `st.clientFd?` (`isEmpty = true` omits the descriptor from `ppoll`). -/
def RelayState.clientPollEvents {fd : Type} (st : RelayState fd) : PollEvents :=
  { pollin := (st.prefixFlushed || st.uWrClosed || st.upstreamFd?.isNone) && !st.cEof &&
      (st.uWrClosed || st.upstreamFd?.isNone || st.c2u.writeAvail > 0)
    pollout := !st.u2c.isEmpty && !st.cWrClosed }

/-- Compute requested `PollEvents` for `st.upstreamFd?` (`isEmpty = true` omits the descriptor from `ppoll`). -/
def RelayState.upstreamPollEvents {fd : Type} (st : RelayState fd) : PollEvents :=
  { pollin := !st.uEof && st.u2c.writeAvail > 0
    pollout := (!st.prefixFlushed || !st.c2u.isEmpty) && !st.uWrClosed }

/-- Close both endpoints of `st` and return the cleared `RelayState`. -/
def closeRelayBoth {m : Type → Type} [Monad m] {fd : Type}
    (closeFd : fd → m Unit) (st : RelayState fd) : m (RelayState fd) := do
  closeOptFd closeFd st.clientFd?
  closeOptFd closeFd st.upstreamFd?
  return { st with
    clientFd? := none
    upstreamFd? := none
    pendingPrefix := ByteArray.empty
    pendingOff := 0 }

/-- Phase 1 of `stepBidirectionalRelay`: flush pending pipelined client bytes before regular upstream writes. -/
def stepRelayPrefix {m : Type → Type} [Monad m] {fd : Type}
    (net : NetOpsM m fd) (st0 : RelayState fd) (uRev : PollEvents) : m (RelayState fd) := do
  if !st0.prefixFlushed && !st0.uWrClosed && (uRev.pollout || uRev.pollerr || uRev.pollhup) then
    match st0.upstreamFd? with
    | some ufd =>
      match ← flushBytesNonblock net ufd st0.pendingPrefix MAX_RELAY_IO_STEPS st0.pendingOff with
      | none =>
        return { st0 with
          pendingPrefix := ByteArray.empty
          pendingOff := 0
          c2u := {}
          uWrClosed := true }
      | some nextOff =>
        if nextOff >= st0.pendingPrefix.size then
          return { st0 with pendingPrefix := ByteArray.empty, pendingOff := 0 }
        else
          return { st0 with pendingOff := nextOff }
    | none => return st0
  else
    return st0

/-- Phase 2 of `stepBidirectionalRelay`: drain readable client bytes into `c2u` (or discard unread upload bytes once upstream write closes so `closeFd` sends `FIN` rather than `TCP RST`). -/
def stepRelayClientRx {m : Type → Type} [Monad m] {fd : Type}
    (net : NetOpsM m fd) (st1 : RelayState fd) (cRev : PollEvents) : m (Option (RelayState fd)) := do
  if !st1.cEof && (cRev.pollin || cRev.pollhup || cRev.pollerr) then
    if st1.uWrClosed || st1.upstreamFd?.isNone then
      match st1.clientFd? with
      | some cfd =>
        let eof' ← drainDeadPeerRx net cfd MAX_RELAY_IO_STEPS
        return some { st1 with cEof := st1.cEof || eof' }
      | none => return some st1
    else if st1.prefixFlushed && st1.c2u.writeAvail > 0 then
      match st1.clientFd? with
      | some cfd =>
        match ← recvIntoRing net cfd MAX_RELAY_IO_STEPS st1.c2u with
        | none => return none
        | some (c2u', eof') => return some { st1 with c2u := c2u', cEof := st1.cEof || eof' }
      | none => return some st1
    else
      return some st1
  else
    return some st1

/-- Phase 3 of `stepBidirectionalRelay`: drain readable upstream bytes into `u2c` (including unread payload before `TCP RST`). -/
def stepRelayUpstreamRx {m : Type → Type} [Monad m] {fd : Type}
    (net : NetOpsM m fd) (st2 : RelayState fd) (uRev : PollEvents) : m (Option (RelayState fd)) := do
  if !st2.uEof && st2.u2c.writeAvail > 0 &&
      (uRev.pollin || uRev.pollhup || uRev.pollerr) then
    match st2.upstreamFd? with
    | some ufd =>
      match ← recvIntoRing net ufd MAX_RELAY_IO_STEPS st2.u2c with
      | none => return none
      | some (u2c', eof') => return some { st2 with u2c := u2c', uEof := st2.uEof || eof' }
    | none => return some st2
  else
    return some st2

/-- Phase 4 of `stepBidirectionalRelay`: flush `c2u` ring buffer toward upstream, tolerating peer write closure without losing `u2c`. -/
def stepRelayUpstreamTx {m : Type → Type} [Monad m] {fd : Type}
    (net : NetOpsM m fd) (st3 : RelayState fd) (uRev : PollEvents) : m (RelayState fd) := do
  if st3.prefixFlushed && !st3.c2u.isEmpty && !st3.uWrClosed &&
      (uRev.pollout || uRev.pollerr || uRev.pollhup) then
    match st3.upstreamFd? with
    | some ufd =>
      match ← flushRingNonblock net ufd MAX_RELAY_IO_STEPS st3.c2u with
      | none => return { st3 with c2u := {}, uWrClosed := true }
      | some c2u' => return { st3 with c2u := c2u' }
    | none => return st3
  else
    return st3

/-- Phase 5 of `stepBidirectionalRelay`: flush `u2c` ring buffer toward client. -/
def stepRelayClientTx {m : Type → Type} [Monad m] {fd : Type}
    (net : NetOpsM m fd) (st4 : RelayState fd) (cRev : PollEvents) : m (Option (RelayState fd)) := do
  if !st4.u2c.isEmpty && !st4.cWrClosed &&
      (cRev.pollout || cRev.pollerr || cRev.pollhup) then
    match st4.clientFd? with
    | some cfd =>
      match ← flushRingNonblock net cfd MAX_RELAY_IO_STEPS st4.u2c with
      | none =>
        if st4.prefixFlushed && st4.c2u.isEmpty then
          return none
        else
          return some { st4 with u2c := {}, uEof := true, cWrClosed := true }
      | some u2c' => return some { st4 with u2c := u2c' }
    | none => return some st4
  else
    return some st4

/-- Phase 6 of `stepBidirectionalRelay`: propagate client `EOF` via `shutdown(ufd, .wr)` once `c2u` and `pendingPrefix` drain. -/
def stepRelayShutdownUpstream {m : Type → Type} [Monad m] {fd : Type}
    (net : NetOpsM m fd) (st5 : RelayState fd) : m (Option (RelayState fd)) := do
  if st5.cEof && st5.prefixFlushed && st5.c2u.isEmpty && !st5.uWrClosed then
    match st5.upstreamFd? with
    | some ufd =>
      if ← shutdownWrClean net ufd MAX_RELAY_IO_STEPS then
        return some { st5 with uWrClosed := true }
      else
        return none
    | none => return some { st5 with uWrClosed := true }
  else
    return some st5

/-- Phase 7 of `stepBidirectionalRelay`: propagate upstream `EOF` via `shutdown(cfd, .wr)` once `u2c` drains. -/
def stepRelayShutdownClient {m : Type → Type} [Monad m] {fd : Type}
    (net : NetOpsM m fd) (st6 : RelayState fd) : m (Option (RelayState fd)) := do
  if st6.uEof && st6.u2c.isEmpty && !st6.cWrClosed then
    match st6.clientFd? with
    | some cfd =>
      if ← shutdownWrClean net cfd MAX_RELAY_IO_STEPS then
        return some { st6 with cWrClosed := true }
      else
        return none
    | none => return some { st6 with cWrClosed := true }
  else
    return some st6

/-- Close `optFd` iff `done = true`, returning the remaining open descriptor option. -/
def reapIdleFd {m : Type → Type} [Monad m] {fd : Type}
    (closeFd : fd → m Unit) (optFd : Option fd) (done : Bool) : m (Option fd) := do
  match optFd with
  | some d =>
    if done then
      closeFd d
      return none
    else
      return some d
  | none => return none

/-- Phase 8 of `stepBidirectionalRelay`: close any side whose read and write directions have both completed. -/
def stepRelayReapIdle {m : Type → Type} [Monad m] {fd : Type}
    (closeFd : fd → m Unit) (st7 : RelayState fd) : m (RelayState fd) := do
  let clientFd' ← reapIdleFd closeFd st7.clientFd? (st7.cEof && st7.cWrClosed)
  let upstreamFd' ← reapIdleFd closeFd st7.upstreamFd? (st7.uEof && st7.uWrClosed)
  return { st7 with clientFd? := clientFd', upstreamFd? := upstreamFd' }

/-- Advance one poll tick of bidirectional TCP relay, preserving pipelined prefix ordering, directional half-close, and unread response bytes across peer `TCP RST`. -/
def stepBidirectionalRelay {m : Type → Type} [Monad m] {fd : Type}
    (net : NetOpsM m fd) (closeFd : fd → m Unit)
    (st0 : RelayState fd) (cRev uRev : PollEvents) : m (RelayState fd) := do
  if cRev.pollnval || uRev.pollnval then
    closeRelayBoth closeFd st0
  else
    let st1 ← stepRelayPrefix net st0 uRev
    match ← stepRelayClientRx net st1 cRev with
    | none => closeRelayBoth closeFd st1
    | some st2 =>
      match ← stepRelayUpstreamRx net st2 uRev with
      | none => closeRelayBoth closeFd st2
      | some st3 =>
        let st4 ← stepRelayUpstreamTx net st3 uRev
        match ← stepRelayClientTx net st4 cRev with
        | none => closeRelayBoth closeFd st4
        | some st5 =>
          match ← stepRelayShutdownUpstream net st5 with
          | none => closeRelayBoth closeFd st5
          | some st6 =>
            match ← stepRelayShutdownClient net st6 with
            | none => closeRelayBoth closeFd st6
            | some st7 =>
              stepRelayReapIdle closeFd st7

end LeanSwe.ConnectProxy.Relay
