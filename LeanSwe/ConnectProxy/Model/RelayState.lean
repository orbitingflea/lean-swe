import LeanSwe.LinuxSyscall.Common.Types
import LeanSwe.NetRelay.Types

namespace LeanSwe.ConnectProxy.Internal.Relay

open LeanSwe.LinuxSyscall
open LeanSwe.NetRelay

/-- Static HTTP `200 Connection Established` response header bytes. -/
def reply200Bytes : ByteArray :=
  asciiBytes ['H', 'T', 'T', 'P', '/', '1', '.', '1', ' ', '2', '0', '0', ' ',
    'C', 'o', 'n', 'n', 'e', 'c', 't', 'i', 'o', 'n', ' ',
    'E', 's', 't', 'a', 'b', 'l', 'i', 's', 'h', 'e', 'd', '\r', '\n', '\r', '\n']

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
    u2c := { buf := reply200Bytes, off := 0, cap := RING_CAP }
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

end LeanSwe.ConnectProxy.Internal.Relay
