import LeanSwe.LinuxSyscall.Common.Types
import LeanSwe.LinuxSyscall.Files.Types
import LeanSwe.LinuxSyscall.Net.Types
import LeanSwe.NetRelay.Types

namespace LeanSwe.NetRelay.Model

open LeanSwe.LinuxSyscall
open LeanSwe.LinuxSyscall.Net
open LeanSwe.NetRelay

/-- Remaining byte capacity in a bounded FIFO list of capacity `cap`. -/
def fifoWriteAvail (cap : Nat) (xs : List UInt8) : Nat :=
  cap - Nat.min xs.length cap

/-- Append up to `cap - min xs.length cap` bytes of `chunk` to a bounded FIFO list. -/
def fifoPush (cap : Nat) (xs chunk : List UInt8) : List UInt8 :=
  xs.take cap ++ chunk.take (cap - (xs.take cap).length)

/-- Consume `n` leading bytes from a FIFO list. -/
def fifoConsume (xs : List UInt8) (n : Nat) : List UInt8 :=
  xs.drop n

/-- Pure specification for `RingBuf.len`. -/
def ringBufLen (rb : RingBuf) : Nat :=
  rb.buf.size - rb.off

/-- Pure specification for `RingBuf.isEmpty`. -/
def ringBufIsEmpty (rb : RingBuf) : Bool :=
  ringBufLen rb == 0

/-- Pure specification for `RingBuf.writeAvail`. -/
def ringBufWriteAvail (rb : RingBuf) : Nat :=
  rb.cap - Nat.min (ringBufLen rb) rb.cap

/-- Pure logical FIFO byte list of `rb` clamped at `rb.cap`. -/
def ringBufToList (rb : RingBuf) : List UInt8 :=
  (rb.buf.data.toList.drop rb.off).take rb.cap

/-- Pure specification for `RingBuf.frontSlice`. -/
def ringBufFrontSlice (rb : RingBuf) : ByteArray :=
  ByteArray.mk (ringBufToList rb).toArray

/-- Allowed outcome relation for `RingBuf.push`: preserves `cap`, respects capacity bound, and appends in FIFO order via `fifoPush`. -/
def allowedRingBufPush (rb : RingBuf) (chunk : ByteArray) (out : RingBuf) : Prop :=
  out.cap = rb.cap ∧
    ringBufLen out ≤ rb.cap ∧
    ringBufToList out = fifoPush rb.cap (ringBufToList rb) chunk.data.toList

/-- Pure reference step for `RingBuf.consume` preserving `rb.cap`. -/
def ringBufConsumeModel (rb : RingBuf) (n : Nat) : RingBuf :=
  let activeLen := Nat.min (ringBufLen rb) rb.cap
  if n >= activeLen then
    { buf := ByteArray.empty, off := 0, cap := rb.cap }
  else
    { buf := rb.buf, off := rb.off + n, cap := rb.cap }

/-- Return `true` iff `e` indicates a fatal descriptor error for non-blocking `recvfrom`. -/
def isFatalRxErrno (e : Errno) : Bool :=
  e == Errno.EBADF || e == Errno.EINVAL || e == Errno.ENOTSOCK

/-- Return `true` iff `e` represents a benign already-closed peer state during `shutdown(SHUT_WR)`. -/
def isBenignShutdownErrno (e : Errno) : Bool :=
  e == Errno.ENOTCONN || e == Errno.ECONNRESET || e == Errno.EPIPE

/-- Abstract raw trace state tracking socket side effects for `NetRelay` step refinement. -/
structure RelayTraceState where
  /-- Well-formedness flag propagated across raw socket steps. -/
  wf : Bool := true
  /-- Sequence of closed descriptors in call order. -/
  closedFds : List Nat := []
  /-- Cumulative received bytes delivered by `recvfrom`. -/
  rxLog : List UInt8 := []
  /-- Cumulative transmitted bytes accepted by `sendto`. -/
  txLog : List UInt8 := []
  /-- Cumulative `Errno` failures observed from socket operations. -/
  errLog : List Errno := []
  /-- Descriptors on which `shutdown(.wr)` returned `.ok ()`. -/
  shutdownWrFds : List Nat := []
  deriving DecidableEq, BEq, Inhabited

/-- Well-formedness guard for `RelayTraceState`. -/
def relayStepWf (s : RelayTraceState) : Bool :=
  s.wf

/-- Raw socket call dispatch request for `Core.ObeysStepFrom`. -/
inductive RelayRawReq where
  /-- Close descriptor `fd`. -/
  | closeFd (fd : Nat)
  /-- Non-blocking `recvfrom fd maxBytes flags`. -/
  | recvfrom (fd : Nat) (maxBytes : UInt32) (flags : MsgFlags)
  /-- Non-blocking `sendto fd bs flags`. -/
  | sendto (fd : Nat) (bs : ByteArray) (flags : MsgFlags)
  /-- Half-close descriptor `fd` with mode `how`. -/
  | shutdown (fd : Nat) (how : ShutHow)
  deriving Inhabited

/-- Tagged return value for `RelayRawReq`. -/
inductive RelayRawOut where
  /-- Result of `closeFd`. -/
  | closed (res : Except Errno Unit)
  /-- Result of `recvfrom`. -/
  | bytes (res : Except Errno ByteArray)
  /-- Result of `sendto`. -/
  | sent (res : Except Errno UInt32)
  /-- Result of `shutdown`. -/
  | shut (res : Except Errno Unit)
  deriving Inhabited

/-- Dispatch a `RelayRawReq` through a `RelayRawOps` capability bundle. -/
def execRawStep {W : Type} (raw : RelayRawOps (StateM W)) : RelayRawReq → StateM W RelayRawOut
  | .closeFd fd => .closed <$> raw.files.close fd
  | .recvfrom fd maxBytes flags => .bytes <$> raw.net.recvfrom fd maxBytes flags
  | .sendto fd bs flags => .sent <$> raw.net.sendto fd bs flags
  | .shutdown fd how => .shut <$> raw.net.shutdown fd how

/-- Allowed single-step transition relation for raw socket operations in `RelayTraceState`. -/
def allowedRawStep (s : RelayTraceState) (req : RelayRawReq) (out : RelayRawOut)
    (s' : RelayTraceState) : Prop :=
  s'.wf = true ∧
  match req, out with
  | .closeFd fd, .closed _ =>
    s'.closedFds = s.closedFds ++ [fd] ∧
      s'.rxLog = s.rxLog ∧ s'.txLog = s.txLog ∧
      s'.errLog = s.errLog ∧ s'.shutdownWrFds = s.shutdownWrFds
  | .recvfrom _ maxBytes _, .bytes (.ok bs) =>
    bs.size ≤ maxBytes.toNat ∧
      s'.closedFds = s.closedFds ∧
      s'.rxLog = s.rxLog ++ bs.data.toList ∧
      s'.txLog = s.txLog ∧ s'.errLog = s.errLog ∧ s'.shutdownWrFds = s.shutdownWrFds
  | .recvfrom _ _ _, .bytes (.error e) =>
    s'.closedFds = s.closedFds ∧ s'.rxLog = s.rxLog ∧ s'.txLog = s.txLog ∧
      s'.errLog = s.errLog ++ [e] ∧ s'.shutdownWrFds = s.shutdownWrFds
  | .sendto _ bs _, .sent (.ok n) =>
    n.toNat ≤ bs.size ∧
      s'.closedFds = s.closedFds ∧ s'.rxLog = s.rxLog ∧
      s'.txLog = s.txLog ++ bs.data.toList.take n.toNat ∧
      s'.errLog = s.errLog ∧ s'.shutdownWrFds = s.shutdownWrFds
  | .sendto _ _ _, .sent (.error e) =>
    s'.closedFds = s.closedFds ∧ s'.rxLog = s.rxLog ∧ s'.txLog = s.txLog ∧
      s'.errLog = s.errLog ++ [e] ∧ s'.shutdownWrFds = s.shutdownWrFds
  | .shutdown fd .wr, .shut (.ok ()) =>
    s'.closedFds = s.closedFds ∧ s'.rxLog = s.rxLog ∧ s'.txLog = s.txLog ∧
      s'.errLog = s.errLog ∧ s'.shutdownWrFds = s.shutdownWrFds ++ [fd]
  | .shutdown _ _, .shut (.ok ()) =>
    s'.closedFds = s.closedFds ∧ s'.rxLog = s.rxLog ∧ s'.txLog = s.txLog ∧
      s'.errLog = s.errLog ∧ s'.shutdownWrFds = s.shutdownWrFds
  | .shutdown _ _, .shut (.error e) =>
    s'.closedFds = s.closedFds ∧ s'.rxLog = s.rxLog ∧ s'.txLog = s.txLog ∧
      s'.errLog = s.errLog ++ [e] ∧ s'.shutdownWrFds = s.shutdownWrFds
  | _, _ => False

/-- Package-level request dispatch covering all six monadic `NetRelay` helpers. -/
inductive RelayPkgReq where
  /-- Invoke `closeOptFd fd?`. -/
  | closeOptFd (fd? : Option Nat)
  /-- Invoke `flushBytesNonblock fd bytes fuel off`. -/
  | flushBytesNonblock (fd : Nat) (bytes : ByteArray) (fuel off : Nat)
  /-- Invoke `recvIntoRing fd fuel rb`. -/
  | recvIntoRing (fd fuel : Nat) (rb : RingBuf)
  /-- Invoke `flushRingNonblock fd fuel rb`. -/
  | flushRingNonblock (fd fuel : Nat) (rb : RingBuf)
  /-- Invoke `shutdownWrClean fd fuel`. -/
  | shutdownWrClean (fd fuel : Nat)
  /-- Invoke `drainDeadPeerRx fd fuel`. -/
  | drainDeadPeerRx (fd fuel : Nat)
  deriving Inhabited

/-- Tagged return value for `RelayPkgReq`. -/
inductive RelayPkgOut where
  /-- Result of `closeOptFd`. -/
  | unit
  /-- Result of `flushBytesNonblock`. -/
  | optNat (v : Option Nat)
  /-- Result of `recvIntoRing`. -/
  | optRecv (v : Option (RingBuf × Bool))
  /-- Result of `flushRingNonblock`. -/
  | optBuf (v : Option RingBuf)
  /-- Result of `shutdownWrClean` or `drainDeadPeerRx`. -/
  | flag (b : Bool)
  deriving Inhabited

/-- Dispatch a `RelayPkgReq` through a `RelayApi` capability bundle. -/
def execPkgStep {W : Type} (api : RelayApi (StateM W)) : RelayPkgReq → StateM W RelayPkgOut
  | .closeOptFd fd? => do api.closeOptFd fd?; return .unit
  | .flushBytesNonblock fd bytes fuel off => .optNat <$> api.flushBytesNonblock fd bytes fuel off
  | .recvIntoRing fd fuel rb => .optRecv <$> api.recvIntoRing fd fuel rb
  | .flushRingNonblock fd fuel rb => .optBuf <$> api.flushRingNonblock fd fuel rb
  | .shutdownWrClean fd fuel => .flag <$> api.shutdownWrClean fd fuel
  | .drainDeadPeerRx fd fuel => .flag <$> api.drainDeadPeerRx fd fuel

/-- Allowed package-level transition relation encoding exact FIFO byte conservation, capacity preservation, and error propagation across all six `NetRelay` helpers. -/
def allowedPkgStep (s : RelayTraceState) (req : RelayPkgReq) (out : RelayPkgOut)
    (s' : RelayTraceState) : Prop :=
  s'.wf = true ∧
  match req, out with
  | .closeOptFd fd?, .unit =>
    s'.closedFds = s.closedFds ++ fd?.toList ∧
      s'.rxLog = s.rxLog ∧ s'.txLog = s.txLog ∧
      s'.errLog = s.errLog ∧ s'.shutdownWrFds = s.shutdownWrFds
  | .flushBytesNonblock _ bytes _ off, .optNat (some nextOff) =>
    off ≤ nextOff ∧ nextOff ≤ max off bytes.size ∧
      s'.closedFds = s.closedFds ∧ s'.rxLog = s.rxLog ∧
      s'.txLog = s.txLog ++ (bytes.data.toList.drop off).take (nextOff - off) ∧
      s'.shutdownWrFds = s.shutdownWrFds
  | .flushBytesNonblock _ _ _ _, .optNat none =>
    s'.closedFds = s.closedFds ∧ s'.rxLog = s.rxLog ∧ s'.shutdownWrFds = s.shutdownWrFds ∧
      ∃ errTail, s'.errLog = s.errLog ++ errTail ∧
        ∃ e ∈ errTail, e ≠ Errno.EINTR ∧ e ≠ Errno.EAGAIN
  | .recvIntoRing _ _ rb, .optRecv (some (rb', _eof)) =>
    rb'.cap = rb.cap ∧
      s'.closedFds = s.closedFds ∧ s'.txLog = s.txLog ∧ s'.shutdownWrFds = s.shutdownWrFds ∧
      (∃ rxTail, s'.rxLog = s.rxLog ++ rxTail ∧
        ringBufToList rb' = ringBufToList rb ++ rxTail)
  | .recvIntoRing _ _ _, .optRecv none =>
    s'.closedFds = s.closedFds ∧ s'.txLog = s.txLog ∧ s'.shutdownWrFds = s.shutdownWrFds ∧
      ∃ errTail, s'.errLog = s.errLog ++ errTail ∧
        ∃ e ∈ errTail, isFatalRxErrno e = true
  | .flushRingNonblock _ _ rb, .optBuf (some rb') =>
    rb'.cap = rb.cap ∧
      s'.closedFds = s.closedFds ∧ s'.rxLog = s.rxLog ∧ s'.shutdownWrFds = s.shutdownWrFds ∧
      ∃ txTail, s'.txLog = s.txLog ++ txTail ∧
        (ringBufLen rb ≤ rb.cap →
          ringBufLen rb' ≤ rb.cap ∧ txTail ++ ringBufToList rb' = ringBufToList rb)
  | .flushRingNonblock _ _ _, .optBuf none =>
    s'.closedFds = s.closedFds ∧ s'.rxLog = s.rxLog ∧ s'.shutdownWrFds = s.shutdownWrFds ∧
      ∃ errTail, s'.errLog = s.errLog ++ errTail ∧
        ∃ e ∈ errTail, e ≠ Errno.EINTR ∧ e ≠ Errno.EAGAIN
  | .shutdownWrClean fd _, .flag true =>
    s'.closedFds = s.closedFds ∧ s'.rxLog = s.rxLog ∧ s'.txLog = s.txLog ∧
      ((s'.shutdownWrFds = s.shutdownWrFds ++ [fd]) ∨
        (s'.shutdownWrFds = s.shutdownWrFds ∧
          ∃ errTail, s'.errLog = s.errLog ++ errTail ∧
            ∃ e ∈ errTail, isBenignShutdownErrno e = true))
  | .shutdownWrClean _ _, .flag false =>
    s'.closedFds = s.closedFds ∧ s'.rxLog = s.rxLog ∧ s'.txLog = s.txLog ∧
      s'.shutdownWrFds = s.shutdownWrFds
  | .drainDeadPeerRx _ fuel, .flag b =>
    (b = true → fuel > 0) ∧
      s'.closedFds = s.closedFds ∧ s'.txLog = s.txLog ∧ s'.shutdownWrFds = s.shutdownWrFds ∧
      ∃ rxTail, s'.rxLog = s.rxLog ++ rxTail
  | _, _ => False

end LeanSwe.NetRelay.Model
