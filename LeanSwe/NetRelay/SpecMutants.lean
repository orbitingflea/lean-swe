import Core.NondetTest
import LeanSwe.LinuxSyscall.Common.Types
import LeanSwe.LinuxSyscall.Net.Types
import LeanSwe.NetRelay.Types
import LeanSwe.NetRelay.Model
import LeanSwe.NetRelay.SpecTests

namespace LeanSwe.NetRelay

open Core.NondetTest
open LeanSwe.LinuxSyscall
open LeanSwe.NetRelay.Model

private def validRingBufApi : RingBufApi :=
  { len := ringBufLen
  , isEmpty := ringBufIsEmpty
  , writeAvail := ringBufWriteAvail
  , toList := ringBufToList
  , frontSlice := ringBufFrontSlice
  , push := fun rb chunk =>
      let xs := fifoPush rb.cap (ringBufToList rb) chunk.data.toList
      { buf := ByteArray.mk xs.toArray, off := 0, cap := rb.cap }
  , consume := ringBufConsumeModel }

private def mutantDropCapClampPush : RingBufApi :=
  { validRingBufApi with
    push := fun rb chunk =>
      { buf := ByteArray.mk ((ringBufToList rb ++ chunk.data.toList).toArray)
      , off := 0
      , cap := rb.cap } }

example : ¬ Core.AllPass (test_netRelay_ringBuf_pushAndViewLaws mutantDropCapClampPush) := by
  intro h
  have h0 := h { buf := ByteArray.empty, off := 0, cap := 1 } (ByteArray.mk #[1, 2])
  have hBad : (2 : Nat) ≤ 1 := h0.2.2.2.2.2.2.2.1
  omega

private def mutantResetCapOnPush : RingBufApi :=
  { validRingBufApi with
    push := fun rb chunk =>
      let base := validRingBufApi.push rb chunk
      { base with cap := RING_CAP } }

example : ¬ Core.AllPass (test_netRelay_ringBuf_pushAndViewLaws mutantResetCapOnPush) := by
  intro h
  have h0 := h { buf := ByteArray.empty, off := 0, cap := 4 } ByteArray.empty
  have hBad : RING_CAP = 4 := h0.2.2.2.2.2.2.1
  cases hBad

private def mutantResetCapOnConsume : RingBufApi :=
  { validRingBufApi with
    consume := fun rb n =>
      { ringBufConsumeModel rb n with cap := RING_CAP } }

example : ¬ Core.AllPass (test_netRelay_ringBuf_consumePreservesCapAndFifo mutantResetCapOnConsume) := by
  intro h
  have h0 := h { buf := ByteArray.mk #[1, 2], off := 0, cap := 4 } 1 (by decide)
  have hBad : RING_CAP = 4 := h0.1
  cases hBad

private def stubMkApi : RelayApiBuilder :=
  fun _ =>
    { closeOptFd := fun _ => pure ()
    , flushBytesNonblock := fun _ _ _ off => pure (some off)
    , recvIntoRing := fun _ _ rb => pure (some (rb, false))
    , flushRingNonblock := fun _ _ rb => pure (some rb)
    , shutdownWrClean := fun _ _ => pure false
    , drainDeadPeerRx := fun _ _ => pure false }

private def mutantSkipEintrRecv : RelayApiBuilder :=
  fun raw =>
    { stubMkApi raw with
      recvIntoRing := fun fd fuel rb =>
        match fuel with
        | 0 => pure (some (rb, false))
        | _ + 1 => do
          let avail := ringBufWriteAvail rb
          if avail == 0 then pure (some (rb, false))
          else
            match ← raw.net.recvfrom fd (UInt32.ofNat avail) { dontwait := true } with
            | .ok bs => pure (some (validRingBufApi.push rb bs, bs.size == 0))
            | .error _ => pure none }

example : ¬ Core.AllPass (test_netRelay_recvIntoRing_eintrCapAndErrors mutantSkipEintrRecv) := by
  intro h
  exact h.1

private def mutantSkipEintrFlushRing : RelayApiBuilder :=
  fun raw =>
    { stubMkApi raw with
      flushRingNonblock := fun _ _ _ => pure none }

example : ¬ Core.AllPass (test_netRelay_flushRingNonblock_shortWritesAndEintr mutantSkipEintrFlushRing) := by
  intro h
  exact h.1

private def mutantRejectEnoconnShutdown : RelayApiBuilder :=
  fun raw =>
    { stubMkApi raw with
      shutdownWrClean := fun fd _ => do
        match ← raw.net.shutdown fd .wr with
        | .ok () => pure true
        | .error _ => pure false }

example : ¬ Core.AllPass (test_netRelay_flushBytesShutdownDrainAndClose mutantRejectEnoconnShutdown) := by
  intro h
  have hBad : false = true := h.2.2.1.1
  cases hBad

end LeanSwe.NetRelay
