import LeanSwe.LinuxSyscall.Common.Types
import LeanSwe.LinuxSyscall.Net.Types
import LeanSwe.LinuxSyscall.Poll.Types
import LeanSwe.NetRelay.Types
import LeanSwe.NetRelay.Model
import LeanSwe.ConnectProxy.Model.RelayState

/-!
Pure spec-passing reference `NetRelay` and `ConnectProxy.Relay` helpers over `.Types` and `.Model`
for single-bug `ConnectProxy` specification mutants.
-/

namespace LeanSwe.ConnectProxy.SpecMutants

open LeanSwe.LinuxSyscall
open LeanSwe.LinuxSyscall.Net
open LeanSwe.LinuxSyscall.Poll
open LeanSwe.NetRelay
open LeanSwe.NetRelay.Model
open LeanSwe.ConnectProxy.Internal.Relay (RelayState)

/-- Contiguous unread byte slice ready for `sendto`. -/
def refRingBufFrontSlice (rb : RingBuf) : ByteArray :=
  let n := Nat.min (ringBufLen rb) rb.cap
  if n == 0 then
    ByteArray.empty
  else if rb.off == 0 && rb.buf.size == n then
    rb.buf
  else
    rb.buf.extract rb.off (rb.off + n)

/-- Append up to `writeAvail` bytes of `chunk` to `rb` while preserving `rb.cap`. -/
def refRingBufPush (rb : RingBuf) (chunk : ByteArray) : RingBuf :=
  let active := refRingBufFrontSlice rb
  let avail := rb.cap - active.size
  let takeN := Nat.min chunk.size avail
  if takeN == 0 then
    { buf := active, off := 0, cap := rb.cap }
  else
    let part := if takeN == chunk.size then chunk else chunk.extract 0 takeN
    let combined := if active.size == 0 then part else active ++ part
    { buf := combined, off := 0, cap := rb.cap }

/-- Close an optional descriptor if present. -/
def refCloseOptFd {m : Type → Type} [Monad m] {fd : Type}
    (closeFd : fd → m Unit) : Option fd → m Unit
  | some f => closeFd f
  | none => pure ()

/-- Non-blocking `sendto` loop advancing `off` across `bytes` until complete, `EAGAIN`, or hard error (`none`). -/
def refFlushBytesNonblock {m : Type → Type} [Monad m] {fd : Type}
    (net : NetOpsM m fd) (f : fd) (bytes : ByteArray) : Nat → Nat → m (Option Nat)
  | 0, off => pure (some off)
  | fuel + 1, off => do
    if off >= bytes.size then
      return some off
    else
      let slice := if off == 0 then bytes else bytes.extract off bytes.size
      match ← net.sendto f slice { nosignal := true, dontwait := true } with
      | .ok n =>
        if n == 0 then return some off
        else refFlushBytesNonblock net f bytes fuel (off + Nat.min n.toNat slice.size)
      | .error e =>
        if e == Errno.EINTR then refFlushBytesNonblock net f bytes fuel off
        else if e == Errno.EAGAIN then return some off
        else return none

/-- Non-blocking `recvfrom` loop filling `rb` until full, `EOF`/peer-reset, `EAGAIN`, or invalid-FD error (`none`). -/
def refRecvIntoRing {m : Type → Type} [Monad m] {fd : Type}
    (net : NetOpsM m fd) (f : fd) : Nat → RingBuf → m (Option (RingBuf × Bool))
  | 0, rb => pure (some (rb, false))
  | fuel + 1, rb => do
    let avail := ringBufWriteAvail rb
    if avail == 0 then
      return some (rb, false)
    else
      let reqCap := Nat.min avail MAX_READ_BYTES.toNat
      match ← net.recvfrom f (UInt32.ofNat reqCap) { dontwait := true } with
      | .ok bs =>
        if bs.size == 0 then
          return some (rb, true)
        else
          let chunk := if bs.size <= reqCap then bs else bs.extract 0 reqCap
          refRecvIntoRing net f fuel (refRingBufPush rb chunk)
      | .error e =>
        if e == Errno.EINTR then refRecvIntoRing net f fuel rb
        else if e == Errno.EAGAIN then return some (rb, false)
        else if e == Errno.EBADF || e == Errno.EINVAL || e == Errno.ENOTSOCK then return none
        else return some (rb, true)

/-- Non-blocking `sendto` loop draining `rb` until empty, `EAGAIN`, or hard error (`none`). -/
def refFlushRingNonblock {m : Type → Type} [Monad m] {fd : Type}
    (net : NetOpsM m fd) (f : fd) : Nat → RingBuf → m (Option RingBuf)
  | 0, rb => pure (some rb)
  | fuel + 1, rb => do
    if ringBufIsEmpty rb then
      return some rb
    else
      let slice := refRingBufFrontSlice rb
      match ← net.sendto f slice { nosignal := true, dontwait := true } with
      | .ok n =>
        if n == 0 then return some rb
        else refFlushRingNonblock net f fuel (ringBufConsumeModel rb n.toNat)
      | .error e =>
        if e == Errno.EINTR then refFlushRingNonblock net f fuel rb
        else if e == Errno.EAGAIN then return some rb
        else return none

/-- Execute `shutdown(f, .wr)` retrying `EINTR` and tolerating already-disconnected peers. -/
def refShutdownWrClean {m : Type → Type} [Monad m] {fd : Type}
    (net : NetOpsM m fd) (f : fd) : Nat → m Bool
  | 0 => pure false
  | fuel + 1 => do
    match ← net.shutdown f .wr with
    | .ok () => return true
    | .error e =>
      if e == Errno.EINTR then refShutdownWrClean net f fuel
      else if e == Errno.ENOTCONN || e == Errno.ECONNRESET || e == Errno.EPIPE then return true
      else return false

/-- Drain unread inbound bytes from `f` after the peer write side has closed. -/
def refDrainDeadPeerRx {m : Type → Type} [Monad m] {fd : Type}
    (net : NetOpsM m fd) (f : fd) : Nat → m Bool
  | 0 => pure false
  | fuel + 1 => do
    match ← net.recvfrom f 4096 { dontwait := true } with
    | .ok bs =>
      if bs.size == 0 then return true else refDrainDeadPeerRx net f fuel
    | .error e =>
      if e == Errno.EINTR then refDrainDeadPeerRx net f fuel
      else if e == Errno.EAGAIN then return false
      else return true

/-- Compute requested `PollEvents` for `st.clientFd?`. -/
def refClientPollEvents {fd : Type} (st : RelayState fd) : PollEvents :=
  { pollin := (st.prefixFlushed || st.uWrClosed || st.upstreamFd?.isNone) && !st.cEof &&
      (st.uWrClosed || st.upstreamFd?.isNone || ringBufWriteAvail st.c2u > 0)
    pollout := !ringBufIsEmpty st.u2c && !st.cWrClosed }

/-- Compute requested `PollEvents` for `st.upstreamFd?`. -/
def refUpstreamPollEvents {fd : Type} (st : RelayState fd) : PollEvents :=
  { pollin := !st.uEof && ringBufWriteAvail st.u2c > 0
    pollout := (!st.prefixFlushed || !ringBufIsEmpty st.c2u) && !st.uWrClosed }

/-- Static HTTP `403 Forbidden` response header bytes. -/
def refReply403Bytes : ByteArray :=
  asciiBytes ['H', 'T', 'T', 'P', '/', '1', '.', '1', ' ', '4', '0', '3', ' ',
    'F', 'o', 'r', 'b', 'i', 'd', 'd', 'e', 'n', '\r', '\n',
    'C', 'o', 'n', 't', 'e', 'n', 't', '-', 'L', 'e', 'n', 'g', 't', 'h', ':', ' ', '0',
    '\r', '\n', '\r', '\n']

/-- Static HTTP `502 Bad Gateway` response header bytes. -/
def refReply502Bytes : ByteArray :=
  asciiBytes ['H', 'T', 'T', 'P', '/', '1', '.', '1', ' ', '5', '0', '2', ' ',
    'B', 'a', 'd', ' ', 'G', 'a', 't', 'e', 'w', 'a', 'y', '\r', '\n',
    'C', 'o', 'n', 't', 'e', 'n', 't', '-', 'L', 'e', 'n', 'g', 't', 'h', ':', ' ', '0',
    '\r', '\n', '\r', '\n']

/-- Static HTTP `503 Service Unavailable` response header bytes. -/
def refReply503Bytes : ByteArray :=
  asciiBytes ['H', 'T', 'T', 'P', '/', '1', '.', '1', ' ', '5', '0', '3', ' ',
    'S', 'e', 'r', 'v', 'i', 'c', 'e', ' ', 'U', 'n', 'a', 'v', 'a', 'i', 'l', 'a', 'b', 'l', 'e', '\r', '\n',
    'C', 'o', 'n', 't', 'e', 'n', 't', '-', 'L', 'e', 'n', 'g', 't', 'h', ':', ' ', '0',
    '\r', '\n', '\r', '\n']

/-- Close both endpoints of `st` and return the cleared `RelayState`. -/
def refCloseRelayBoth {m : Type → Type} [Monad m] {fd : Type}
    (closeFd : fd → m Unit) (st : RelayState fd) : m (RelayState fd) := do
  refCloseOptFd closeFd st.clientFd?
  refCloseOptFd closeFd st.upstreamFd?
  return { st with
    clientFd? := none
    upstreamFd? := none
    pendingPrefix := ByteArray.empty
    pendingOff := 0 }

private def stepRelayPrefixRef {m : Type → Type} [Monad m] {fd : Type}
    (net : NetOpsM m fd) (st0 : RelayState fd) (uRev : PollEvents) : m (RelayState fd) := do
  if !st0.prefixFlushed && !st0.uWrClosed && (uRev.pollout || uRev.pollerr || uRev.pollhup) then
    match st0.upstreamFd? with
    | some ufd =>
      match ← refFlushBytesNonblock net ufd st0.pendingPrefix MAX_RELAY_IO_STEPS st0.pendingOff with
      | none =>
        return { st0 with pendingPrefix := ByteArray.empty, pendingOff := 0, c2u := {}, uWrClosed := true }
      | some nextOff =>
        if nextOff >= st0.pendingPrefix.size then
          return { st0 with pendingPrefix := ByteArray.empty, pendingOff := 0 }
        else
          return { st0 with pendingOff := nextOff }
    | none => return st0
  else
    return st0

private def stepRelayClientRxRef {m : Type → Type} [Monad m] {fd : Type}
    (net : NetOpsM m fd) (st1 : RelayState fd) (cRev : PollEvents) : m (Option (RelayState fd)) := do
  if !st1.cEof && (cRev.pollin || cRev.pollhup || cRev.pollerr) then
    if st1.uWrClosed || st1.upstreamFd?.isNone then
      match st1.clientFd? with
      | some cfd =>
        let eof' ← refDrainDeadPeerRx net cfd MAX_RELAY_IO_STEPS
        return some { st1 with cEof := st1.cEof || eof' }
      | none => return some st1
    else if st1.prefixFlushed && ringBufWriteAvail st1.c2u > 0 then
      match st1.clientFd? with
      | some cfd =>
        match ← refRecvIntoRing net cfd MAX_RELAY_IO_STEPS st1.c2u with
        | none => return none
        | some (c2u', eof') => return some { st1 with c2u := c2u', cEof := st1.cEof || eof' }
      | none => return some st1
    else return some st1
  else return some st1

private def stepRelayUpstreamRxRef {m : Type → Type} [Monad m] {fd : Type}
    (net : NetOpsM m fd) (st2 : RelayState fd) (uRev : PollEvents) : m (Option (RelayState fd)) := do
  if !st2.uEof && ringBufWriteAvail st2.u2c > 0 && (uRev.pollin || uRev.pollhup || uRev.pollerr) then
    match st2.upstreamFd? with
    | some ufd =>
      match ← refRecvIntoRing net ufd MAX_RELAY_IO_STEPS st2.u2c with
      | none => return none
      | some (u2c', eof') => return some { st2 with u2c := u2c', uEof := st2.uEof || eof' }
    | none => return some st2
  else return some st2

private def stepRelayUpstreamTxRef {m : Type → Type} [Monad m] {fd : Type}
    (net : NetOpsM m fd) (st3 : RelayState fd) (uRev : PollEvents) : m (RelayState fd) := do
  if st3.prefixFlushed && !ringBufIsEmpty st3.c2u && !st3.uWrClosed &&
      (uRev.pollout || uRev.pollerr || uRev.pollhup) then
    match st3.upstreamFd? with
    | some ufd =>
      match ← refFlushRingNonblock net ufd MAX_RELAY_IO_STEPS st3.c2u with
      | none => return { st3 with c2u := {}, uWrClosed := true }
      | some c2u' => return { st3 with c2u := c2u' }
    | none => return st3
  else return st3

private def stepRelayClientTxRef {m : Type → Type} [Monad m] {fd : Type}
    (net : NetOpsM m fd) (st4 : RelayState fd) (cRev : PollEvents) : m (Option (RelayState fd)) := do
  if !ringBufIsEmpty st4.u2c && !st4.cWrClosed &&
      (cRev.pollout || cRev.pollerr || cRev.pollhup) then
    match st4.clientFd? with
    | some cfd =>
      match ← refFlushRingNonblock net cfd MAX_RELAY_IO_STEPS st4.u2c with
      | none =>
        if st4.prefixFlushed && ringBufIsEmpty st4.c2u then return none
        else return some { st4 with u2c := {}, uEof := true, cWrClosed := true }
      | some u2c' => return some { st4 with u2c := u2c' }
    | none => return some st4
  else return some st4

private def stepRelayShutdownUpstreamRef {m : Type → Type} [Monad m] {fd : Type}
    (net : NetOpsM m fd) (st5 : RelayState fd) : m (Option (RelayState fd)) := do
  if st5.cEof && st5.prefixFlushed && ringBufIsEmpty st5.c2u && !st5.uWrClosed then
    match st5.upstreamFd? with
    | some ufd =>
      if ← refShutdownWrClean net ufd MAX_RELAY_IO_STEPS then
        return some { st5 with uWrClosed := true }
      else return none
    | none => return some { st5 with uWrClosed := true }
  else return some st5

private def stepRelayShutdownClientRef {m : Type → Type} [Monad m] {fd : Type}
    (net : NetOpsM m fd) (st6 : RelayState fd) : m (Option (RelayState fd)) := do
  if st6.uEof && ringBufIsEmpty st6.u2c && !st6.cWrClosed then
    match st6.clientFd? with
    | some cfd =>
      if ← refShutdownWrClean net cfd MAX_RELAY_IO_STEPS then
        return some { st6 with cWrClosed := true }
      else return none
    | none => return some { st6 with cWrClosed := true }
  else return some st6

private def reapIdleFdRef {m : Type → Type} [Monad m] {fd : Type}
    (closeFd : fd → m Unit) (optFd : Option fd) (done : Bool) : m (Option fd) := do
  match optFd with
  | some d => if done then closeFd d; return none else return some d
  | none => return none

/-- Advance one poll tick of bidirectional TCP relay. -/
def refStepBidirectionalRelay {m : Type → Type} [Monad m] {fd : Type}
    (net : NetOpsM m fd) (closeFd : fd → m Unit)
    (st0 : RelayState fd) (cRev uRev : PollEvents) : m (RelayState fd) := do
  if cRev.pollnval || uRev.pollnval then
    refCloseRelayBoth closeFd st0
  else
    let st1 ← stepRelayPrefixRef net st0 uRev
    match ← stepRelayClientRxRef net st1 cRev with
    | none => refCloseRelayBoth closeFd st1
    | some st2 =>
      match ← stepRelayUpstreamRxRef net st2 uRev with
      | none => refCloseRelayBoth closeFd st2
      | some st3 =>
        let st4 ← stepRelayUpstreamTxRef net st3 uRev
        match ← stepRelayClientTxRef net st4 cRev with
        | none => refCloseRelayBoth closeFd st4
        | some st5 =>
          match ← stepRelayShutdownUpstreamRef net st5 with
          | none => refCloseRelayBoth closeFd st5
          | some st6 =>
            match ← stepRelayShutdownClientRef net st6 with
            | none => refCloseRelayBoth closeFd st6
            | some st7 =>
              let clientFd' ← reapIdleFdRef closeFd st7.clientFd? (st7.cEof && st7.cWrClosed)
              let upstreamFd' ← reapIdleFdRef closeFd st7.upstreamFd? (st7.uEof && st7.uWrClosed)
              return { st7 with clientFd? := clientFd', upstreamFd? := upstreamFd' }

end LeanSwe.ConnectProxy.SpecMutants
