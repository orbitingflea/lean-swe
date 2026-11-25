import LeanSwe.LinuxSyscall.Common.Types
import LeanSwe.LinuxSyscall.Files.Types
import LeanSwe.LinuxSyscall.Net.Types
import LeanSwe.NetRelay.Types

namespace LeanSwe.NetRelay.Internal

open LeanSwe.LinuxSyscall
open LeanSwe.LinuxSyscall.Net
open LeanSwe.NetRelay

/-- Number of unread bytes currently buffered in `rb`. -/
def ringBufLen (rb : RingBuf) : Nat :=
  rb.buf.size - rb.off

/-- Return `true` iff `rb` holds zero unread bytes. -/
def ringBufIsEmpty (rb : RingBuf) : Bool :=
  ringBufLen rb == 0

/-- Remaining capacity in bytes (`0 .. rb.cap`) available for `push`. -/
def ringBufWriteAvail (rb : RingBuf) : Nat :=
  rb.cap - Nat.min (ringBufLen rb) rb.cap

/-- Logical FIFO list of unread bytes in `rb` (clamped at `rb.cap`). -/
def ringBufToList (rb : RingBuf) : List UInt8 :=
  (rb.buf.data.toList.drop rb.off).take rb.cap

/-- Contiguous unread byte slice ready for `sendto`. -/
def ringBufFrontSlice (rb : RingBuf) : ByteArray :=
  let n := Nat.min (ringBufLen rb) rb.cap
  if n == 0 then
    ByteArray.empty
  else if rb.off == 0 && rb.buf.size == n then
    rb.buf
  else
    rb.buf.extract rb.off (rb.off + n)

/-- Append up to `rb.writeAvail` bytes of `chunk` to the tail of `rb`, compacting any consumed prefix while preserving `rb.cap`. -/
def ringBufPush (rb : RingBuf) (chunk : ByteArray) : RingBuf :=
  let active := ringBufFrontSlice rb
  let avail := rb.cap - active.size
  let takeN := Nat.min chunk.size avail
  if takeN == 0 then
    { buf := active, off := 0, cap := rb.cap }
  else
    let part := if takeN == chunk.size then chunk else chunk.extract 0 takeN
    let combined := if active.size == 0 then part else active ++ part
    { buf := combined, off := 0, cap := rb.cap }

/-- Advance the read cursor by `n` bytes, resetting `buf` when fully drained while preserving `rb.cap`. -/
def ringBufConsume (rb : RingBuf) (n : Nat) : RingBuf :=
  let activeLen := Nat.min (ringBufLen rb) rb.cap
  if n >= activeLen then
    { buf := ByteArray.empty, off := 0, cap := rb.cap }
  else
    { buf := rb.buf, off := rb.off + n, cap := rb.cap }

/-- Concrete `RingBufApi` bundling the internal `RingBuf` operations. -/
def defaultRingBufApi : RingBufApi :=
  { len := ringBufLen
  , isEmpty := ringBufIsEmpty
  , writeAvail := ringBufWriteAvail
  , toList := ringBufToList
  , frontSlice := ringBufFrontSlice
  , push := ringBufPush
  , consume := ringBufConsume }

/-- Close an optional descriptor if present. -/
def closeOptFd {m : Type → Type} [Monad m] {fd : Type}
    (closeFd : fd → m Unit) : Option fd → m Unit
  | some f => closeFd f
  | none => pure ()

/-- Non-blocking `sendto` loop advancing `off` across `bytes` until complete, `EAGAIN`, or hard error (`none`). -/
def flushBytesNonblock {m : Type → Type} [Monad m] {fd : Type}
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
        else flushBytesNonblock net f bytes fuel (off + Nat.min n.toNat slice.size)
      | .error e =>
        if e == Errno.EINTR then
          flushBytesNonblock net f bytes fuel off
        else if e == Errno.EAGAIN then
          return some off
        else
          return none

/-- Non-blocking `recvfrom` loop filling `rb` until full, `EOF`/peer-reset (`eof = true`), `EAGAIN`, or invalid-descriptor error (`none`). -/
def recvIntoRing {m : Type → Type} [Monad m] {fd : Type}
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
          recvIntoRing net f fuel (ringBufPush rb chunk)
      | .error e =>
        if e == Errno.EINTR then
          recvIntoRing net f fuel rb
        else if e == Errno.EAGAIN then
          return some (rb, false)
        else if e == Errno.EBADF || e == Errno.EINVAL || e == Errno.ENOTSOCK then
          return none
        else
          return some (rb, true)

/-- Non-blocking `sendto` loop draining `rb` until empty, `EAGAIN`, or hard error (`none`). -/
def flushRingNonblock {m : Type → Type} [Monad m] {fd : Type}
    (net : NetOpsM m fd) (f : fd) : Nat → RingBuf → m (Option RingBuf)
  | 0, rb => pure (some rb)
  | fuel + 1, rb => do
    if ringBufIsEmpty rb then
      return some rb
    else
      let slice := ringBufFrontSlice rb
      match ← net.sendto f slice { nosignal := true, dontwait := true } with
      | .ok n =>
        if n == 0 then return some rb
        else flushRingNonblock net f fuel (ringBufConsume rb n.toNat)
      | .error e =>
        if e == Errno.EINTR then
          flushRingNonblock net f fuel rb
        else if e == Errno.EAGAIN then
          return some rb
        else
          return none

/-- Execute `shutdown(f, .wr)` retrying `EINTR` and tolerating already-disconnected peers (`ENOTCONN`/`ECONNRESET`/`EPIPE`). -/
def shutdownWrClean {m : Type → Type} [Monad m] {fd : Type}
    (net : NetOpsM m fd) (f : fd) : Nat → m Bool
  | 0 => pure false
  | fuel + 1 => do
    match ← net.shutdown f .wr with
    | .ok () => return true
    | .error e =>
      if e == Errno.EINTR then
        shutdownWrClean net f fuel
      else if e == Errno.ENOTCONN || e == Errno.ECONNRESET || e == Errno.EPIPE then
        return true
      else
        return false

/-- Drain unread inbound bytes from `f` after the peer write side has closed, returning `true` on `EOF` or socket error. -/
def drainDeadPeerRx {m : Type → Type} [Monad m] {fd : Type}
    (net : NetOpsM m fd) (f : fd) : Nat → m Bool
  | 0 => pure false
  | fuel + 1 => do
    match ← net.recvfrom f 4096 { dontwait := true } with
    | .ok bs =>
      if bs.size == 0 then return true else drainDeadPeerRx net f fuel
    | .error e =>
      if e == Errno.EINTR then drainDeadPeerRx net f fuel
      else if e == Errno.EAGAIN then return false
      else return true

/-- Build a `RelayApi` bundle over arbitrary monadic raw socket and descriptor capabilities. -/
def mkRelayApiM {m : Type → Type} [Monad m] (raw : RelayRawOps m) : RelayApi m :=
  { closeOptFd := closeOptFd (fun fd => do let _ ← raw.files.close fd; pure ())
  , flushBytesNonblock := flushBytesNonblock raw.net
  , recvIntoRing := recvIntoRing raw.net
  , flushRingNonblock := flushRingNonblock raw.net
  , shutdownWrClean := shutdownWrClean raw.net
  , drainDeadPeerRx := drainDeadPeerRx raw.net }

end LeanSwe.NetRelay.Internal
