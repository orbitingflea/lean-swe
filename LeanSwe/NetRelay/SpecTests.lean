import Core.NondetTest
import LeanSwe.LinuxSyscall.Common.Types
import LeanSwe.LinuxSyscall.Files.Types
import LeanSwe.LinuxSyscall.Net.Types
import LeanSwe.NetRelay.Types
import LeanSwe.NetRelay.Model

namespace LeanSwe.NetRelay

open Core (NondetTest)
open Core.NondetTest
open LeanSwe.LinuxSyscall
open LeanSwe.LinuxSyscall.Net
open LeanSwe.NetRelay.Model

/-- Type alias for a polymorphic `RelayApi` constructor accepted by specification tests. -/
abbrev RelayApiBuilder :=
  {m : Type → Type} → [Monad m] → RelayRawOps m → RelayApi m

private structure ScriptState where
  rxQueue : List (Except Errno ByteArray) := []
  txQueue : List (Except Errno UInt32) := []
  shutQueue : List (Except Errno Unit) := []
  sentBytes : List UInt8 := []
  rxReqs : List UInt32 := []
  closed : List Nat := []

private def scriptedRawOps : RelayRawOps (StateM ScriptState) :=
  let noNet {α : Type} : StateM ScriptState (Except Errno α) := pure (.error Errno.ENOSYS)
  { net :=
      { socket := fun _ _ _ _ => noNet
      , socketpair := fun _ _ _ => noNet
      , bind := fun _ _ => noNet
      , listen := fun _ _ => noNet
      , accept4 := fun _ _ => noNet
      , connect := fun _ _ => noNet
      , getsockopt := fun _ _ => noNet
      , setsockopt := fun _ _ _ => noNet
      , getsockname := fun _ => noNet
      , recvfrom := fun _ maxBytes _ => do
          let s ← get
          let s' := { s with rxReqs := s.rxReqs ++ [maxBytes] }
          match s'.rxQueue with
          | hd :: tl => set { s' with rxQueue := tl }; return hd
          | [] => set s'; return .error Errno.EAGAIN
      , sendto := fun _ bs _ => do
          let s ← get
          match s.txQueue with
          | hd :: tl =>
            match hd with
            | .ok n =>
              set { s with txQueue := tl, sentBytes := s.sentBytes ++ bs.data.toList.take n.toNat }
              return .ok n
            | .error e =>
              set { s with txQueue := tl }
              return .error e
          | [] => return .error Errno.EAGAIN
      , shutdown := fun _ _ => do
          let s ← get
          match s.shutQueue with
          | hd :: tl => set { s with shutQueue := tl }; return hd
          | [] => return .ok ()
      , sendmsg := fun _ _ => noNet
      , recvmsg := fun _ _ => noNet
      , ioctl := fun _ _ _ => noNet }
  , files :=
      { openat := fun _ _ _ _ => noNet
      , openat2 := fun _ _ _ => noNet
      , close := fun fd => do modify (fun s => { s with closed := s.closed ++ [fd] }); return .ok ()
      , read := fun _ _ => noNet
      , write := fun _ _ => noNet
      , fstat := fun _ => noNet
      , fstatat := fun _ _ _ => noNet
      , faccessat := fun _ _ _ _ => noNet
      , mkdirat := fun _ _ _ => noNet
      , unlinkat := fun _ _ _ => noNet
      , renameat2 := fun _ _ _ _ _ => noNet
      , symlinkat := fun _ _ _ => noNet
      , readlinkat := fun _ _ _ => noNet
      , getdents64 := fun _ _ => noNet
      , fchmodat := fun _ _ _ => noNet
      , fchmod := fun _ _ => noNet
      , flock := fun _ _ => noNet
      , fcntl := fun _ _ => noNet
      , fsync := fun _ => noNet
      , getcwd := fun _ => noNet
      , lseek := fun _ _ _ => noNet
      , reopenReadOnly := fun _ => noNet
      , dupStdio := fun _ => noNet } }

/-- Pure `RingBuf` operations preserve arbitrary `rb.cap`, match the bounded FIFO list model, compact cleanly on `push`, and clamp unread slices to `rb.cap`. -/
def test_netRelay_ringBuf_pushAndViewLaws
    {runner} [NondetTest runner] (api : RingBufApi) : runner Unit := do
  let rb ← nondet RingBuf
  let chunk ← nondet ByteArray
  NondetTest.assert (api.len rb = ringBufLen rb)
  NondetTest.assert (api.isEmpty rb = ringBufIsEmpty rb)
  NondetTest.assert (api.writeAvail rb = ringBufWriteAvail rb)
  NondetTest.assert (api.toList rb = ringBufToList rb)
  NondetTest.assert ((api.frontSlice rb).data.toList = ringBufToList rb)
  NondetTest.assert ((api.frontSlice rb).size ≤ rb.cap)
  let rb' := api.push rb chunk
  NondetTest.assert (rb'.cap = rb.cap)
  NondetTest.assert (api.len rb' ≤ rb.cap)
  NondetTest.assert (api.toList rb' = fifoPush rb.cap (ringBufToList rb) chunk.data.toList)

/-- On any well-formed `RingBuf` (`len ≤ cap`), `consume` preserves `cap`, maintains `len ≤ cap`, and drops exact leading bytes from the FIFO stream. -/
def test_netRelay_ringBuf_consumePreservesCapAndFifo
    {runner} [NondetTest runner] (api : RingBufApi) : runner Unit := do
  let rb ← nondet RingBuf
  let n ← nondet Nat
  assume (ringBufLen rb ≤ rb.cap)
  let rb' := api.consume rb n
  NondetTest.assert (rb'.cap = rb.cap)
  NondetTest.assert (ringBufLen rb' ≤ rb.cap)
  NondetTest.assert (api.toList rb' = fifoConsume (ringBufToList rb) n)

/-- `recvIntoRing` retries `EINTR`, preserves buffered bytes across `ECONNRESET`/`EOF`, preserves arbitrary `rb.cap`, clamps `recvfrom` lengths, stops on `EAGAIN`, and returns `none` on fatal descriptor errors. -/
def test_netRelay_recvIntoRing_eintrCapAndErrors
    {runner} [NondetTest runner] (mkApi : RelayApiBuilder) : runner Unit := do
  let api := mkApi scriptedRawOps
  let rbSmall : RingBuf := { cap := 3 }
  let (r1, s1) := (api.recvIntoRing 7 8 rbSmall).run
    { rxQueue := [.error Errno.EINTR, .ok (ByteArray.mk #[10, 20]),
                  .ok (ByteArray.mk #[30, 40]), .ok (ByteArray.mk #[50])] }
  NondetTest.assert (match r1 with
    | some (rb', eof) =>
      eof = false ∧ rb'.cap = 3 ∧ ringBufToList rb' = [10, 20, 30] ∧
        s1.rxReqs = [3, 3, 1]
    | none => False)
  let (r2, _) := (api.recvIntoRing 7 8 { cap := 5 }).run
    { rxQueue := [.ok (ByteArray.mk #[65]), .error Errno.EINTR,
                  .error Errno.ECONNRESET] }
  NondetTest.assert (match r2 with
    | some (rb', eof) => eof = true ∧ rb'.cap = 5 ∧ ringBufToList rb' = [65]
    | none => False)
  let (r3, _) := (api.recvIntoRing 7 4 { cap := 4 }).run
    { rxQueue := [.error Errno.EBADF] }
  NondetTest.assert (r3 = none)
  let (r4, s4) := (api.recvIntoRing 7 4 { cap := 0 }).run
    { rxQueue := [.ok (ByteArray.mk #[99])] }
  NondetTest.assert (match r4 with
    | some (rb', eof) => eof = false ∧ rb'.cap = 0 ∧ s4.rxReqs = []
    | none => False)

/-- `flushRingNonblock` retries `EINTR`, drains partial `sendto` writes preserving byte order and `rb.cap`, stops on `EAGAIN`, and fails (`none`) on hard errors. -/
def test_netRelay_flushRingNonblock_shortWritesAndEintr
    {runner} [NondetTest runner] (mkApi : RelayApiBuilder) : runner Unit := do
  let api := mkApi scriptedRawOps
  let rb0 : RingBuf := { buf := ByteArray.mk #[1, 2, 3, 4], off := 0, cap := 7 }
  let (r1, s1) := (api.flushRingNonblock 7 8 rb0).run
    { txQueue := [.error Errno.EINTR, .ok 1, .error Errno.EINTR, .ok 2, .error Errno.EAGAIN] }
  NondetTest.assert (match r1 with
    | some rb' => rb'.cap = 7 ∧ ringBufToList rb' = [4] ∧ s1.sentBytes = [1, 2, 3]
    | none => False)
  let (r2, _) := (api.flushRingNonblock 7 4 rb0).run
    { txQueue := [.error Errno.EPIPE] }
  NondetTest.assert (r2 = none)

/-- `flushBytesNonblock`, `shutdownWrClean`, `drainDeadPeerRx`, and `closeOptFd` handle `EINTR`, `EAGAIN`, short writes, benign disconnect errnos, and optional close cleanly. -/
def test_netRelay_flushBytesShutdownDrainAndClose
    {runner} [NondetTest runner] (mkApi : RelayApiBuilder) : runner Unit := do
  let api := mkApi scriptedRawOps
  let bytes := ByteArray.mk #[7, 8, 9, 10]
  let (fb1, sf1) := (api.flushBytesNonblock 3 bytes 8 1).run
    { txQueue := [.error Errno.EINTR, .ok 2, .error Errno.EAGAIN] }
  NondetTest.assert (fb1 = some 3 ∧ sf1.sentBytes = [8, 9])
  let (fb2, _) := (api.flushBytesNonblock 3 bytes 4 0).run
    { txQueue := [.error Errno.EPIPE] }
  NondetTest.assert (fb2 = none)
  let (sh1, _) := (api.shutdownWrClean 3 4).run
    { shutQueue := [.error Errno.EINTR, .error Errno.ENOTCONN] }
  let (sh2, _) := (api.shutdownWrClean 3 4).run
    { shutQueue := [.error Errno.EBADF] }
  NondetTest.assert (sh1 = true ∧ sh2 = false)
  let (dr1, _) := (api.drainDeadPeerRx 3 4).run
    { rxQueue := [.error Errno.EINTR, .ok (ByteArray.mk #[1]), .ok ByteArray.empty] }
  let (dr2, _) := (api.drainDeadPeerRx 3 4).run
    { rxQueue := [.error Errno.EAGAIN] }
  NondetTest.assert (dr1 = true ∧ dr2 = false)
  let (_, sc1) := (api.closeOptFd (some 11)).run {}
  let (_, sc2) := (api.closeOptFd none).run {}
  NondetTest.assert (sc1.closed = [11] ∧ sc2.closed = [])

end LeanSwe.NetRelay
