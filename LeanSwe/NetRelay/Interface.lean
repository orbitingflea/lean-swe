import LeanSwe.LinuxSyscall.Common.Types
import LeanSwe.LinuxSyscall.Net.Types
import LeanSwe.NetRelay.Types
import LeanSwe.NetRelay.Impl

namespace LeanSwe.NetRelay

open LeanSwe.LinuxSyscall.Net

/-- Number of unread bytes currently buffered in `rb`. -/
@[inline] def RingBuf.len (rb : RingBuf) : Nat :=
  Internal.ringBufLen rb

/-- Return `true` iff `rb` holds zero unread bytes. -/
@[inline] def RingBuf.isEmpty (rb : RingBuf) : Bool :=
  Internal.ringBufIsEmpty rb

/-- Remaining capacity in bytes (`0 .. rb.cap`) available for `push`. -/
@[inline] def RingBuf.writeAvail (rb : RingBuf) : Nat :=
  Internal.ringBufWriteAvail rb

/-- Logical FIFO list of unread bytes in `rb` (clamped at `rb.cap`). -/
@[inline] def RingBuf.toList (rb : RingBuf) : List UInt8 :=
  Internal.ringBufToList rb

/-- Contiguous unread byte slice ready for `sendto`. -/
@[inline] def RingBuf.frontSlice (rb : RingBuf) : ByteArray :=
  Internal.ringBufFrontSlice rb

/-- Append up to `rb.writeAvail` bytes of `chunk` to the tail of `rb`, compacting any consumed prefix while preserving `rb.cap`. -/
@[inline] def RingBuf.push (rb : RingBuf) (chunk : ByteArray) : RingBuf :=
  Internal.ringBufPush rb chunk

/-- Advance the read cursor by `n` bytes, resetting `buf` when fully drained while preserving `rb.cap`. -/
@[inline] def RingBuf.consume (rb : RingBuf) (n : Nat) : RingBuf :=
  Internal.ringBufConsume rb n

/-- Close an optional descriptor if present. -/
@[inline] def closeOptFd {m : Type → Type} [Monad m] {fd : Type}
    (closeFd : fd → m Unit) (optFd : Option fd) : m Unit :=
  Internal.closeOptFd closeFd optFd

/-- Non-blocking `sendto` loop advancing `off` across `bytes` until complete, `EAGAIN`, or hard error (`none`). -/
@[inline] def flushBytesNonblock {m : Type → Type} [Monad m] {fd : Type}
    (net : NetOpsM m fd) (f : fd) (bytes : ByteArray) (fuel off : Nat) : m (Option Nat) :=
  Internal.flushBytesNonblock net f bytes fuel off

/-- Non-blocking `recvfrom` loop filling `rb` until full, `EOF`/peer-reset (`eof = true`), `EAGAIN`, or invalid-descriptor error (`none`). -/
@[inline] def recvIntoRing {m : Type → Type} [Monad m] {fd : Type}
    (net : NetOpsM m fd) (f : fd) (fuel : Nat) (rb : RingBuf) : m (Option (RingBuf × Bool)) :=
  Internal.recvIntoRing net f fuel rb

/-- Non-blocking `sendto` loop draining `rb` until empty, `EAGAIN`, or hard error (`none`). -/
@[inline] def flushRingNonblock {m : Type → Type} [Monad m] {fd : Type}
    (net : NetOpsM m fd) (f : fd) (fuel : Nat) (rb : RingBuf) : m (Option RingBuf) :=
  Internal.flushRingNonblock net f fuel rb

/-- Execute `shutdown(f, .wr)` retrying `EINTR` and tolerating already-disconnected peers (`ENOTCONN`/`ECONNRESET`/`EPIPE`). -/
@[inline] def shutdownWrClean {m : Type → Type} [Monad m] {fd : Type}
    (net : NetOpsM m fd) (f : fd) (fuel : Nat) : m Bool :=
  Internal.shutdownWrClean net f fuel

/-- Drain unread inbound bytes from `f` after the peer write side has closed, returning `true` on `EOF` or socket error. -/
@[inline] def drainDeadPeerRx {m : Type → Type} [Monad m] {fd : Type}
    (net : NetOpsM m fd) (f : fd) (fuel : Nat) : m Bool :=
  Internal.drainDeadPeerRx net f fuel

end LeanSwe.NetRelay
