import LeanSwe.LinuxSyscall.Common.Types
import LeanSwe.LinuxSyscall.Files.Types
import LeanSwe.LinuxSyscall.Net.Types

namespace LeanSwe.NetRelay

/-- Default fixed byte capacity (`16 KiB`) for directional TCP relay ring buffers. -/
def RING_CAP : Nat := 16384

/-- Per-poll-tick non-blocking I/O iteration bound preventing unbounded spin with structural fuel. -/
def MAX_RELAY_IO_STEPS : Nat := 256

/-- Bounded FIFO byte queue (`len ≤ cap`) for non-blocking stream relay. -/
structure RingBuf where
  /-- Backing byte slice containing unread bytes in `off .. buf.size`. -/
  buf : ByteArray := ByteArray.empty
  /-- Read cursor offset into `buf`. -/
  off : Nat := 0
  /-- Configured byte capacity of the ring buffer (defaults to `RING_CAP`). -/
  cap : Nat := RING_CAP
  deriving DecidableEq, BEq, Inhabited

/-- Abstract bundle of pure `RingBuf` operations for specification testing. -/
structure RingBufApi where
  /-- Number of unread bytes currently buffered. -/
  len : RingBuf → Nat
  /-- Return `true` iff zero unread bytes are buffered. -/
  isEmpty : RingBuf → Bool
  /-- Remaining capacity in bytes (`0 .. cap`) available for `push`. -/
  writeAvail : RingBuf → Nat
  /-- Logical FIFO byte list clamped at `cap`. -/
  toList : RingBuf → List UInt8
  /-- Contiguous unread byte slice ready for `sendto`. -/
  frontSlice : RingBuf → ByteArray
  /-- Append up to `writeAvail` bytes of a chunk while compacting any consumed prefix and preserving `cap`. -/
  push : RingBuf → ByteArray → RingBuf
  /-- Advance the read cursor by `n` bytes, compacting when drained and preserving `cap`. -/
  consume : RingBuf → Nat → RingBuf

/-- Raw socket and file-descriptor capabilities consumed by `NetRelay` loops over descriptor `Nat`. -/
structure RelayRawOps (m : Type → Type) where
  /-- Non-blocking socket syscall interface over `Nat` descriptors. -/
  net : LinuxSyscall.Net.NetOpsM m Nat
  /-- Filesystem descriptor syscall interface over `Nat` descriptors (used to close descriptors). -/
  files : LinuxSyscall.Files.FilesOpsM m Nat

/-- Parameterized bundle of monadic non-blocking stream relay helpers. -/
structure RelayApi (m : Type → Type) where
  /-- Close an optional descriptor if present. -/
  closeOptFd : Option Nat → m Unit
  /-- Flush `bytes` starting at `off` in non-blocking mode across `EINTR`/`EAGAIN`/short writes. -/
  flushBytesNonblock : Nat → ByteArray → Nat → Nat → m (Option Nat)
  /-- Receive non-blocking bytes into a bounded `RingBuf` with `EINTR`/`EAGAIN`/`EOF` handling. -/
  recvIntoRing : Nat → Nat → RingBuf → m (Option (RingBuf × Bool))
  /-- Drain a `RingBuf` via non-blocking `sendto` across `EINTR`/`EAGAIN`/short writes. -/
  flushRingNonblock : Nat → Nat → RingBuf → m (Option RingBuf)
  /-- Issue `shutdown(fd, .wr)` retrying `EINTR` and tolerating already-disconnected peers. -/
  shutdownWrClean : Nat → Nat → m Bool
  /-- Discard unread inbound bytes from a descriptor whose peer write side has closed. -/
  drainDeadPeerRx : Nat → Nat → m Bool

end LeanSwe.NetRelay
