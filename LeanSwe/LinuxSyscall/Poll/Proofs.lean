import LeanSwe.LinuxSyscall.Poll.SpecTests
import LeanSwe.LinuxSyscall.Poll.Impl
import LeanSwe.LinuxSyscall.Poll.Interface

namespace LeanSwe.LinuxSyscall.Poll

open Core (NondetTest AllPass CanReach)
open Core.NondetTest
open LeanSwe.LinuxSyscall

private theorem bool_beq_eq_of_inj {α : Type} [BEq α] [DecidableEq α]
    (hBeq : ∀ x y : α, (x == y) = decide (x = y))
    (enc : α → UInt32) (hInj : ∀ x y : α, enc x = enc y → x = y) :
    ∀ x y : α, (enc x == enc y) = (x == y) := by
  intro x y
  rw [hBeq x y]
  by_cases h : x = y
  · subst h; simp
  · have hne : enc x ≠ enc y := fun heq => h (hInj x y heq)
    simp [h, beq_false_of_ne hne]

private theorem pollEvents_beq_eq_decide (x y : PollEvents) : (x == y) = decide (x = y) := by
  cases x with | mk x1 x2 x3 x4 x5 =>
  cases y with | mk y1 y2 y3 y4 y5 =>
  cases x1 <;> cases x2 <;> cases x3 <;> cases x4 <;> cases x5 <;>
    cases y1 <;> cases y2 <;> cases y3 <;> cases y4 <;> cases y5 <;> rfl

private theorem eventFdFlags_beq_eq_decide (x y : EventFdFlags) : (x == y) = decide (x = y) := by
  cases x with | mk x1 x2 x3 =>
  cases y with | mk y1 y2 y3 =>
  cases x1 <;> cases x2 <;> cases x3 <;> cases y1 <;> cases y2 <;> cases y3 <;> rfl

private theorem pollEvents_ofBits_toBits (ev : PollEvents) : PollEvents.ofBits ev.toBits = ev := by
  rcases ev with ⟨a, b, c, d, e⟩
  cases a <;> cases b <;> cases c <;> cases d <;> cases e <;> rfl

private theorem pollEvents_toBits_lt (ev : PollEvents) : ev.toBits < 32 := by
  rcases ev with ⟨a, b, c, d, e⟩
  cases a <;> cases b <;> cases c <;> cases d <;> cases e <;> decide

private theorem pollEvents_toBits_inj (x y : PollEvents) (h : x.toBits = y.toBits) : x = y := by
  have hm := congrArg PollEvents.ofBits h
  rwa [pollEvents_ofBits_toBits, pollEvents_ofBits_toBits] at hm

private def eventFdFlagsOfBits (bits : UInt32) : EventFdFlags :=
  { nonblock := (bits &&& ((1 : UInt32) <<< 0)) != 0
    cloexec := (bits &&& ((1 : UInt32) <<< 1)) != 0
    semaphore := (bits &&& ((1 : UInt32) <<< 2)) != 0 }

private theorem eventFdFlags_ofBits_toBits (f : EventFdFlags) : eventFdFlagsOfBits f.toBits = f := by
  rcases f with ⟨a, b, c⟩
  cases a <;> cases b <;> cases c <;> rfl

private theorem eventFdFlags_toBits_lt (f : EventFdFlags) : f.toBits < 8 := by
  rcases f with ⟨a, b, c⟩
  cases a <;> cases b <;> cases c <;> decide

private theorem eventFdFlags_toBits_inj (x y : EventFdFlags) (h : x.toBits = y.toBits) : x = y := by
  have hm := congrArg eventFdFlagsOfBits h
  rwa [eventFdFlags_ofBits_toBits, eventFdFlags_ofBits_toBits] at hm

private theorem ui8_ofNat_toUInt32_of_lt {x : UInt32} (h : x < 32) :
    (UInt8.ofNat x.toNat).toUInt32 = x := by
  have hNat : x.toNat < 32 := h
  have hMod : x.toNat % 256 = x.toNat := Nat.mod_eq_of_lt (Nat.lt_trans hNat (by decide))
  apply UInt32.toNat_inj.mp
  change (UInt8.ofNat x.toNat).toNat = x.toNat
  change x.toNat % 256 = x.toNat
  exact hMod

private theorem decode_encode_pair (ev1 ev2 : PollEvents) :
    let pair := encodePollRequests #[(10, ev1), (20, ev2)]
    pair.1 = #[10, 20] ∧ pair.2.size = 2 ∧ decodePollRevents pair.2 = #[ev1, ev2] := by
  have h1 := ui8_ofNat_toUInt32_of_lt (pollEvents_toBits_lt ev1)
  have h2 := ui8_ofNat_toUInt32_of_lt (pollEvents_toBits_lt ev2)
  have hPair : encodePollRequests #[(10, ev1), (20, ev2)] =
      (#[10, 20], ByteArray.mk #[UInt8.ofNat ev1.toBits.toNat, UInt8.ofNat ev2.toBits.toNat]) := by
    simp [encodePollRequests]
  rw [hPair]
  refine ⟨rfl, rfl, ?_⟩
  have hDec : decodePollRevents (ByteArray.mk #[UInt8.ofNat ev1.toBits.toNat, UInt8.ofNat ev2.toBits.toNat]) =
      #[PollEvents.ofBits (UInt8.ofNat ev1.toBits.toNat).toUInt32,
        PollEvents.ofBits (UInt8.ofNat ev2.toBits.toNat).toUInt32] := by
    simp [decodePollRevents, ByteArray.foldl, ByteArray.foldlM, Id.run]
    rfl
  rw [hDec, h1, h2, pollEvents_ofBits_toBits, pollEvents_ofBits_toBits]

private theorem decode_encode_empty_and_triple (ev1 ev2 ev3 : PollEvents) :
    let emptyEnc := encodePollRequests (#[] : Array (Nat × PollEvents))
    let triEnc := encodePollRequests #[(10, ev1), (20, ev2), (30, ev3)]
    emptyEnc.1 = #[] ∧ emptyEnc.2.size = 0 ∧ decodePollRevents emptyEnc.2 = #[] ∧
      triEnc.1 = #[10, 20, 30] ∧ triEnc.2.size = 3 ∧ decodePollRevents triEnc.2 = #[ev1, ev2, ev3] := by
  have h1 := ui8_ofNat_toUInt32_of_lt (pollEvents_toBits_lt ev1)
  have h2 := ui8_ofNat_toUInt32_of_lt (pollEvents_toBits_lt ev2)
  have h3 := ui8_ofNat_toUInt32_of_lt (pollEvents_toBits_lt ev3)
  have hEmpty : encodePollRequests (#[] : Array (Nat × PollEvents)) = (#[], ByteArray.mk #[]) := by
    simp [encodePollRequests]
  have hTri : encodePollRequests #[(10, ev1), (20, ev2), (30, ev3)] =
      (#[10, 20, 30], ByteArray.mk #[UInt8.ofNat ev1.toBits.toNat, UInt8.ofNat ev2.toBits.toNat, UInt8.ofNat ev3.toBits.toNat]) := by
    simp [encodePollRequests]
  rw [hEmpty, hTri]
  refine ⟨rfl, rfl, rfl, rfl, rfl, ?_⟩
  have hDec : decodePollRevents (ByteArray.mk #[UInt8.ofNat ev1.toBits.toNat, UInt8.ofNat ev2.toBits.toNat, UInt8.ofNat ev3.toBits.toNat]) =
      #[PollEvents.ofBits (UInt8.ofNat ev1.toBits.toNat).toUInt32,
        PollEvents.ofBits (UInt8.ofNat ev2.toBits.toNat).toUInt32,
        PollEvents.ofBits (UInt8.ofNat ev3.toBits.toNat).toUInt32] := by
    simp [decodePollRevents, ByteArray.foldl, ByteArray.foldlM, Id.run]
    rfl
  rw [hDec, h1, h2, h3, pollEvents_ofBits_toBits, pollEvents_ofBits_toBits, pollEvents_ofBits_toBits]

/-- `Errno.isTransientOsErrno` and `PollErrorKind.ofErrno` satisfy their complete classification promise. -/
theorem poll_errno_classification_allPass :
    AllPass (test_poll_errno_classification Errno.isTransientOsErrno PollErrorKind.ofErrno) := by
  intro e
  dsimp only [Bind.bind, assert, pure]
  refine ⟨by decide, rfl, ?_⟩
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, trivial⟩

/-- `PollEvents`, `EventFdFlags`, `Timespec.isValid`/`isZero`, and `encodePollRequests`/`decodePollRevents` satisfy all codec and injectivity checks. -/
theorem poll_flags_and_codecs_roundtripAndInjective_allPass :
    AllPass (test_poll_flags_and_codecs_roundtripAndInjective
      PollEvents.toBits PollEvents.ofBits EventFdFlags.toBits
      Timespec.isValid encodePollRequests decodePollRevents
      Timespec.isZero {} {}) := by
  intro ev1 ev2
  refine ⟨bool_beq_eq_of_inj pollEvents_beq_eq_decide PollEvents.toBits pollEvents_toBits_inj ev1 ev2, ?_⟩
  refine ⟨pollEvents_toBits_lt ev1, pollEvents_ofBits_toBits ev1, ?_⟩
  intro f1 f2
  refine ⟨bool_beq_eq_of_inj eventFdFlags_beq_eq_decide EventFdFlags.toBits eventFdFlags_toBits_inj f1 f2, ?_⟩
  refine ⟨eventFdFlags_toBits_lt f1, ?_⟩
  refine ⟨⟨rfl, rfl, rfl, rfl, rfl⟩, ⟨rfl, rfl, rfl⟩, by decide, by decide, by decide, by decide,
    decode_encode_pair ev1 ev2, ⟨rfl, rfl⟩, ⟨by decide, by decide, by decide⟩, ⟨rfl, rfl, rfl⟩, ?_⟩
  intro ev3
  exact ⟨decode_encode_empty_and_triple ev1 ev2 ev3, trivial⟩

private theorem mkPollOpsM_ppoll_badTs {S fd : Type} (raw : Internal.PosixPollOpsM (StateM S) fd)
    (entries : Array (fd × PollEvents)) (badTs : Timespec) (hBad : Timespec.isValid badTs = false)
    (s₀ : S) :
    ((Internal.mkPollOpsM raw).ppoll entries (some badTs)).run s₀ = (.error Errno.EINVAL, s₀) := by
  dsimp only [Internal.mkPollOpsM, StateT.run, Bind.bind, StateT.bind, Pure.pure, StateT.pure]
  have hNot : (!badTs.isValid) = true := by simp [hBad]
  rw [hNot]
  rfl

private theorem mkPollOpsM_ppoll_huge {S fd : Type} (raw : Internal.PosixPollOpsM (StateM S) fd)
    (hugeEntries : Array (fd × PollEvents)) (hHuge : hugeEntries.size > MAX_POLL_NFDS)
    (s₀ : S) :
    ((Internal.mkPollOpsM raw).ppoll hugeEntries (some { sec := 0, nsec := 0 })).run s₀ =
      (.error Errno.EINVAL, s₀) := by
  dsimp only [Internal.mkPollOpsM, StateT.run, Bind.bind, StateT.bind, Pure.pure, StateT.pure]
  have hValid : ({ sec := 0, nsec := 0 } : Timespec).isValid = true := by decide
  have hNot : (!({ sec := 0, nsec := 0 } : Timespec).isValid) = false := by simp [hValid]
  rw [hNot]
  have hGt : (hugeEntries.size > MAX_POLL_NFDS) := hHuge
  simp only [↓reduceIte, hGt]
  rfl

private theorem mkPollOpsM_ppoll_huge_none {S fd : Type} (raw : Internal.PosixPollOpsM (StateM S) fd)
    (hugeEntries : Array (fd × PollEvents)) (hHuge : hugeEntries.size > MAX_POLL_NFDS)
    (s₀ : S) :
    ((Internal.mkPollOpsM raw).ppoll hugeEntries none).run s₀ =
      (.error Errno.EINVAL, s₀) := by
  dsimp only [Internal.mkPollOpsM, StateT.run, Bind.bind, StateT.bind, Pure.pure, StateT.pure]
  have hGt : (hugeEntries.size > MAX_POLL_NFDS) := hHuge
  simp only [↓reduceIte, hGt]
  rfl

/-- `Internal.mkPollOpsM raw` rejects any invalid `Timespec` or `nfds > MAX_POLL_NFDS` with `Errno.EINVAL` before calling raw C hooks. -/
theorem poll_ops_invalidTimespecAndMaxNfdsRejectedWithEinval_mkPollOpsM_allPass
    {S fd : Type} (raw : Internal.PosixPollOpsM (StateM S) fd) :
    AllPass (test_poll_ops_invalidTimespecAndMaxNfdsRejectedWithEinval (Internal.mkPollOpsM raw)) := by
  intro s₀ entries badTs hBad hugeEntries hHuge
  dsimp only [Bind.bind, assert, pure]
  refine ⟨mkPollOpsM_ppoll_badTs raw entries badTs hBad s₀, ?_, ?_, ?_, trivial⟩
  · exact mkPollOpsM_ppoll_badTs raw #[] badTs hBad s₀
  · exact mkPollOpsM_ppoll_huge raw hugeEntries hHuge s₀
  · exact mkPollOpsM_ppoll_huge_none raw hugeEntries hHuge s₀

private def dummyRawPollOps : Internal.PosixPollOpsM (StateM PollState) HandleId :=
  { ppoll := fun _ _ _ _ _ => pure (.error Errno.ENOSYS)
    eventfd2 := fun _ _ => pure (.error Errno.ENOSYS) }

/-- Concrete witness demonstrating reachability of `test_poll_ops_invalidTimespecAndMaxNfdsRejectedWithEinval` on `Internal.mkPollOpsM`. -/
theorem poll_ops_invalidTimespecAndMaxNfdsRejectedWithEinval_mkPollOpsM_canReach :
    CanReach (test_poll_ops_invalidTimespecAndMaxNfdsRejectedWithEinval (Internal.mkPollOpsM dummyRawPollOps)) := by
  have hBad : Timespec.isValid { sec := -1, nsec := 0 } = false := by decide
  have hHuge : (Array.replicate (MAX_POLL_NFDS + 1) ((0 : HandleId), ({} : PollEvents))).size > MAX_POLL_NFDS := by
    rw [Array.size_replicate]
    exact Nat.lt_succ_self MAX_POLL_NFDS
  refine ⟨PollState.initial, #[], { sec := -1, nsec := 0 }, hBad,
    Array.replicate (MAX_POLL_NFDS + 1) ((0 : HandleId), ({} : PollEvents)), hHuge, ?_⟩
  exact poll_ops_invalidTimespecAndMaxNfdsRejectedWithEinval_mkPollOpsM_allPass dummyRawPollOps
    PollState.initial #[] { sec := -1, nsec := 0 } hBad
    (Array.replicate (MAX_POLL_NFDS + 1) ((0 : HandleId), ({} : PollEvents))) hHuge

private theorem modelOps_ppoll_badTs (entries : Array (HandleId × PollEvents))
    (badTs : Timespec) (hBad : Timespec.isValid badTs = false) (s₀ : PollState) :
    (modelOps.ppoll entries (some badTs)).run s₀ = (.error Errno.EINVAL, s₀) := by
  dsimp only [modelOps, stepPollCore, preCheckPoll, StateT.run, Bind.bind, StateT.bind, get, getThe,
    MonadState.get, MonadStateOf.get, StateT.get, Pure.pure, StateT.pure]
  have hNot : (!badTs.isValid) = true := by simp [hBad]
  simp [hNot]
  rfl

private theorem modelOps_ppoll_huge (hugeEntries : Array (HandleId × PollEvents))
    (hHuge : hugeEntries.size > MAX_POLL_NFDS) (s₀ : PollState) :
    (modelOps.ppoll hugeEntries (some { sec := 0, nsec := 0 })).run s₀ = (.error Errno.EINVAL, s₀) := by
  dsimp only [modelOps, stepPollCore, preCheckPoll, StateT.run, Bind.bind, StateT.bind, get, getThe,
    MonadState.get, MonadStateOf.get, StateT.get, Pure.pure, StateT.pure]
  have hValid : ({ sec := 0, nsec := 0 } : Timespec).isValid = true := by decide
  have hNot : (!({ sec := 0, nsec := 0 } : Timespec).isValid) = false := by simp [hValid]
  have hGt : (hugeEntries.size > MAX_POLL_NFDS) := hHuge
  simp [hNot, hGt]
  rfl

private theorem modelOps_ppoll_huge_none (hugeEntries : Array (HandleId × PollEvents))
    (hHuge : hugeEntries.size > MAX_POLL_NFDS) (s₀ : PollState) :
    (modelOps.ppoll hugeEntries none).run s₀ = (.error Errno.EINVAL, s₀) := by
  dsimp only [modelOps, stepPollCore, preCheckPoll, StateT.run, Bind.bind, StateT.bind, get, getThe,
    MonadState.get, MonadStateOf.get, StateT.get, Pure.pure, StateT.pure]
  have hGt : (hugeEntries.size > MAX_POLL_NFDS) := hHuge
  simp [hGt]
  rfl

/-- `modelOps` rejects any invalid `Timespec` or `nfds > MAX_POLL_NFDS` with `Errno.EINVAL` and leaves `PollState` unchanged. -/
theorem poll_ops_invalidTimespecAndMaxNfdsRejectedWithEinval_model_allPass :
    AllPass (test_poll_ops_invalidTimespecAndMaxNfdsRejectedWithEinval modelOps) := by
  intro s₀ entries badTs hBad hugeEntries hHuge
  dsimp only [Bind.bind, assert, pure]
  refine ⟨modelOps_ppoll_badTs entries badTs hBad s₀, ?_, ?_, ?_, trivial⟩
  · exact modelOps_ppoll_badTs #[] badTs hBad s₀
  · exact modelOps_ppoll_huge hugeEntries hHuge s₀
  · exact modelOps_ppoll_huge_none hugeEntries hHuge s₀

/-- Concrete witness demonstrating reachability of `test_poll_ops_invalidTimespecAndMaxNfdsRejectedWithEinval` on `modelOps`. -/
theorem poll_ops_invalidTimespecAndMaxNfdsRejectedWithEinval_model_canReach :
    CanReach (test_poll_ops_invalidTimespecAndMaxNfdsRejectedWithEinval modelOps) := by
  have hBad : Timespec.isValid { sec := -1, nsec := 0 } = false := by decide
  have hHuge : (Array.replicate (MAX_POLL_NFDS + 1) ((0 : HandleId), ({} : PollEvents))).size > MAX_POLL_NFDS := by
    rw [Array.size_replicate]
    exact Nat.lt_succ_self MAX_POLL_NFDS
  refine ⟨PollState.initial, #[], { sec := -1, nsec := 0 }, hBad,
    Array.replicate (MAX_POLL_NFDS + 1) ((0 : HandleId), ({} : PollEvents)), hHuge, ?_⟩
  exact poll_ops_invalidTimespecAndMaxNfdsRejectedWithEinval_model_allPass
    PollState.initial #[] { sec := -1, nsec := 0 } hBad
    (Array.replicate (MAX_POLL_NFDS + 1) ((0 : HandleId), ({} : PollEvents))) hHuge

/-- `modelOps` satisfies `eventfd` readiness, timeout semantics, infinite unready `EINTR`, and duplicate FD checks. -/
theorem poll_ops_eventfdReadinessAndTimeouts_allPass :
    AllPass (test_poll_ops_eventfdReadinessAndTimeouts modelOps PollState.initial) := by
  dsimp only [AllPass, test_poll_ops_eventfdReadinessAndTimeouts, Bind.bind, assert, pure]
  refine ⟨⟨rfl, rfl⟩, ⟨rfl, rfl⟩, ⟨rfl, rfl⟩, ⟨rfl, rfl⟩, rfl, ⟨rfl, rfl⟩, rfl, trivial⟩

/-- `modelOps` and `PollState` satisfy counter saturation, `EFD_SEMAPHORE`, output flags, and `closeHandle` `EBADF` checks. -/
theorem poll_state_counterSemaphoreCloseAndOutputFlags_allPass :
    AllPass (test_poll_state_counterSemaphoreCloseAndOutputFlags modelOps) := by
  dsimp only [AllPass, test_poll_state_counterSemaphoreCloseAndOutputFlags, Bind.bind, assert, pure]
  repeat (first | exact trivial | exact rfl | decide | constructor)

/-- `Model.allowedStep` satisfies all timeout, `EINVAL`, `EBADF`, handle-allocation, and `revents` invariants. -/
theorem poll_model_allowedStep_invariants_allPass :
    AllPass (test_poll_model_allowedStep_invariants allowedStep) := by
  dsimp only [AllPass, test_poll_model_allowedStep_invariants, Bind.bind, assert, pure]
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, trivial⟩

/-- `Model.allowedStep` satisfies `softNofile?` and `ambientSeccomp` invariants. -/
theorem poll_model_softNofileAndAmbientSeccomp_allPass :
    AllPass (test_poll_model_softNofileAndAmbientSeccomp allowedStep) := by
  dsimp only [AllPass, test_poll_model_softNofileAndAmbientSeccomp, Bind.bind, assert, pure]
  repeat (first | exact trivial | exact rfl | decide | constructor)

private theorem evalPollListAux_length (s : PollState) (xs : List (HandleId × PollEvents))
    (acc revList : List PollEvents) (h : evalPollListAux s xs acc = .ok revList) :
    revList.length = acc.length + xs.length := by
  induction xs generalizing acc revList with
  | nil =>
    simp only [evalPollListAux] at h
    injection h with hEq; cases hEq
    simp
  | cons x rest ih =>
    simp only [evalPollListAux] at h
    cases hGet : assocGet s.fds x.1 with
    | none => simp [hGet] at h
    | some desc =>
      simp only [hGet] at h
      have hSub := ih (computeDescRevents desc x.2 :: acc) revList h
      simp only [List.length_cons] at hSub ⊢
      omega

private theorem evalPollList_length (s : PollState) (xs : List (HandleId × PollEvents))
    (revList : List PollEvents) (h : evalPollList s xs = .ok revList) :
    revList.length = xs.length := by
  simpa using evalPollListAux_length s xs [] revList h

private theorem pollEvents_list_beq_self (xs : List PollEvents) : (xs == xs) = true := by
  induction xs with
  | nil => rfl
  | cons x rest ih =>
    have hx : (x == x) = true := by simp [pollEvents_beq_eq_decide]
    change (x == x && rest == rest) = true
    simp [hx, ih]

private theorem stepPollCore_none_sound (s s' : PollState) (req : PollReq) (out : PollOutcome)
    (hFresh : assocGet s.fds s.nextHid = none)
    (h : stepPollCore s req none = some (out, s')) :
    allowedStep s req out = some s' := by
  unfold allowedStep
  cases req with
  | eventfd2 initval flags =>
    simp only [stepPollCore] at h
    injection h with hPair
    cases hPair
    have hNext : max s.nextHid (s.nextHid + 1) = s.nextHid + 1 := Nat.max_eq_right (Nat.le_succ _)
    simp [stepPollCore, hFresh, hNext]
  | ppoll entries timeout =>
    simp only [stepPollCore] at h
    split at h
    · next preErr hPre =>
      injection h with hPair; cases hPair
      simp [stepPollCore, hPre]
    · next hPre =>
      split at h
      · next pinErr hPin =>
        injection h with hPair; cases hPair
        simp [stepPollCore, hPre, hPin]
      · next revList hPin =>
        have hLen : revList.length = entries.size := evalPollList_length s entries.toList revList hPin
        have hSelf : (revList == revList) = true := pollEvents_list_beq_self revList
        have hEintr : Errno.EINTR.isTransientOsErrno = true := by decide
        cases hSoft : s.softNofile? with
        | some lim =>
          by_cases hGt : entries.size > lim
          · simp only [hSoft, hGt, decide_true, ↓reduceIte] at h
            injection h with hPair; cases hPair
            simp [stepPollCore, hPre, hPin, hSoft, hGt]
          · simp only [hSoft, hGt, decide_false, Bool.false_eq_true, ↓reduceIte] at h
            by_cases hAny : revList.any (fun ev => !ev.isEmpty) = true
            · simp only [hAny, Bool.not_true, Bool.false_and, Bool.false_eq_true, ↓reduceIte] at h
              injection h with hPair; cases hPair
              simp [stepPollCore, hPre, hPin, hSoft, hGt, hAny, hLen, hSelf]
            · have hAnyF : revList.any (fun ev => !ev.isEmpty) = false := Bool.eq_false_iff.mpr hAny
              cases hTo : timeout with
              | none =>
                rw [hTo] at hPre
                simp only [hAnyF, Bool.not_false, hTo, Option.isNone_none, Bool.and_self, ↓reduceIte] at h
                injection h with hPair; cases hPair
                simp [stepPollCore, hPre, hPin, hSoft, hGt, hEintr]
              | some ts =>
                rw [hTo] at hPre
                simp only [hAnyF, Bool.not_false, hTo, Option.isNone_some, Bool.and_false,
                  Bool.false_eq_true, ↓reduceIte] at h
                injection h with hPair; cases hPair
                simp [stepPollCore, hPre, hPin, hSoft, hGt, hAnyF, hLen, hSelf]
        | none =>
          simp only [hSoft, Bool.false_eq_true, ↓reduceIte] at h
          by_cases hAny : revList.any (fun ev => !ev.isEmpty) = true
          · simp only [hAny, Bool.not_true, Bool.false_and, Bool.false_eq_true, ↓reduceIte] at h
            injection h with hPair; cases hPair
            simp [stepPollCore, hPre, hPin, hSoft, hAny, hLen, hSelf]
          · have hAnyF : revList.any (fun ev => !ev.isEmpty) = false := Bool.eq_false_iff.mpr hAny
            cases hTo : timeout with
            | none =>
              rw [hTo] at hPre
              simp only [hAnyF, Bool.not_false, hTo, Option.isNone_none, Bool.and_self, ↓reduceIte] at h
              injection h with hPair; cases hPair
              simp [stepPollCore, hPre, hPin, hSoft, hEintr]
            | some ts =>
              rw [hTo] at hPre
              simp only [hAnyF, Bool.not_false, hTo, Option.isNone_some, Bool.and_false,
                Bool.false_eq_true, ↓reduceIte] at h
              injection h with hPair; cases hPair
              simp [stepPollCore, hPre, hPin, hSoft, hAnyF, hLen, hSelf]

/-- Every outcome produced by `stepPollCore s req none` is accepted by `allowedStep`. -/
theorem poll_model_stepCoreSound_allPass :
    AllPass (test_poll_model_stepCoreSound allowedStep) := by
  intro s req out s' hFresh h
  dsimp only [Bind.bind, assert, pure]
  exact ⟨stepPollCore_none_sound s s' req out hFresh h, trivial⟩

/-- Concrete witness demonstrating reachability of `test_poll_model_stepCoreSound`. -/
theorem poll_model_stepCoreSound_canReach :
    CanReach (test_poll_model_stepCoreSound allowedStep) := by
  refine ⟨PollState.initial, .eventfd2 0 {}, .opened 0,
    { PollState.initial with fds := [(0, { kind := .eventfd 0 {} })], nextHid := 1 }, rfl, rfl, ?_⟩
  exact ⟨rfl, trivial⟩

/-- `Internal.mkPollOpsM` satisfies its complete codec, flag, timeout, and `EIO` delegation promise. -/
theorem poll_mkPollOps_encodesAndDelegates_allPass :
    AllPass (test_poll_mkPollOps_encodesAndDelegates (@Internal.mkPollOpsM Id Nat _)) := by
  intro rawPpoll rawEfd entries hLe ts hTs initval flags
  have hNotGt : ¬ (entries.size > MAX_POLL_NFDS) := Nat.not_lt_of_ge hLe
  have hNotBad : (!ts.isValid) = false := by simp [hTs]
  dsimp only [test_poll_mkPollOps_encodesAndDelegates, Internal.mkPollOpsM, Bind.bind, assert, pure, Id.instMonad]
  refine ⟨rfl, ?_, ?_, trivial⟩
  · simp only [hNotGt, ↓reduceIte]
    cases rawPpoll (encodePollRequests entries).1 (encodePollRequests entries).2 0 0 0 <;> rfl
  · simp only [hNotBad, Bool.false_eq_true, ↓reduceIte, hNotGt]
    cases rawPpoll (encodePollRequests entries).1 (encodePollRequests entries).2 1 ts.sec.toUInt64 ts.nsec <;> rfl

/-- Concrete witness demonstrating reachability of `test_poll_mkPollOps_encodesAndDelegates`. -/
theorem poll_mkPollOps_encodesAndDelegates_canReach :
    CanReach (test_poll_mkPollOps_encodesAndDelegates (@Internal.mkPollOpsM Id Nat _)) := by
  have hLe : (#[] : Array (Nat × PollEvents)).size ≤ MAX_POLL_NFDS := Nat.zero_le _
  have hTs : ({ sec := 0, nsec := 0 } : Timespec).isValid = true := by decide
  refine ⟨fun _ _ _ _ _ => .ok (ByteArray.mk #[]), fun _ _ => .ok 0, #[], hLe, { sec := 0, nsec := 0 }, hTs, 0, {}, ?_⟩
  exact poll_mkPollOps_encodesAndDelegates_allPass
    (fun _ _ _ _ _ => .ok (ByteArray.mk #[])) (fun _ _ => .ok 0) #[] hLe { sec := 0, nsec := 0 } hTs 0 {}

/-- `Poll.defaultOps`, `Poll.ppoll`, and `Poll.eventfd2` satisfy their `Interface` wiring and default-argument specification. -/
theorem poll_interface_defaultOpsWiring_allPass :
    AllPass (test_poll_interface_defaultOpsWiring
      Internal.mkPollOps defaultOps
      (fun fds to? => ppoll fds to?) (fun fds => ppoll fds)
      (fun iv fl => eventfd2 iv fl) eventfd2) := by
  intro fds timeout initval flags
  dsimp only [test_poll_interface_defaultOpsWiring, Bind.bind, assert, pure]
  exact ⟨⟨_, rfl⟩, rfl, rfl, rfl, rfl, trivial⟩

/-- Soundness: every `healthyStep` transition refines `allowedStep` with `ambientSeccomp = false`, `isCriticalFault = false`, and exact `eintrBudget` accounting. -/
theorem healthyStep_implies_allowedStep
    {env env' : HealthyEnv} {req : PollReq} {out : PollOutcome}
    (h : healthyStep env req out = some env') :
    allowedStep env.state req out = some env'.state ∧
    env.wf = true ∧
    env.state.ambientSeccomp = false ∧
    isCriticalFault out = false ∧
    env'.eintrBudget ≤ env.eintrBudget ∧
    (isEintrOutcome out = true → env.eintrBudget > 0 ∧ env'.eintrBudget = env.eintrBudget - 1) ∧
    (isEintrOutcome out = false → env'.eintrBudget = env.eintrBudget) := by
  unfold healthyStep at h
  by_cases hBad : (!env.wf || isCriticalFault out) = true
  · simp [hBad] at h
  · have hWf : env.wf = true := by cases hw : env.wf <;> simp_all
    have hSec : env.state.ambientSeccomp = false := by
      unfold HealthyEnv.wf at hWf; cases hs : env.state.ambientSeccomp <;> simp_all
    have hCrit : isCriticalFault out = false := by cases hc : isCriticalFault out <;> simp_all
    simp only [hBad, Bool.false_eq_true, ↓reduceIte] at h
    cases hAl : allowedStep env.state req out with
    | none => simp [hAl] at h
    | some s' =>
      rw [hAl] at h; dsimp only at h
      cases hEi : isEintrOutcome out with
      | false =>
        simp only [hEi, Bool.false_eq_true, ↓reduceIte, Option.some.injEq] at h
        subst h
        exact ⟨rfl, hWf, hSec, hCrit, Nat.le_refl _, (by intro hc; cases hc), fun _ => rfl⟩
      | true =>
        simp only [hEi, ↓reduceIte] at h
        by_cases hPos : env.eintrBudget > 0
        · simp only [hPos, ↓reduceIte, Option.some.injEq] at h
          subst h
          exact ⟨rfl, hWf, hSec, hCrit, Nat.sub_le _ _, fun _ => ⟨hPos, rfl⟩, (by intro hc; cases hc)⟩
        · simp [hPos] at h

/-- Tightness by construction: every non-critical `allowedStep` transition from a healthy `Poll` environment (with positive `eintrBudget` on `EINTR`) is accepted by `healthyStep`. -/
theorem allowedStep_healthy_tight
    {env : HealthyEnv} {req : PollReq} {out : PollOutcome} {s' : PollState}
    (hStep : allowedStep env.state req out = some s')
    (hWf : env.wf = true)
    (hNoCrit : isCriticalFault out = false)
    (hBudget : isEintrOutcome out = true → 0 < env.eintrBudget) :
    healthyStep env req out =
      some { state := s',
             eintrBudget := if isEintrOutcome out then env.eintrBudget - 1 else env.eintrBudget } := by
  unfold healthyStep
  have hGuard : (!env.wf || isCriticalFault out) = false := by simp [hWf, hNoCrit]
  simp only [hGuard, Bool.false_eq_true, ↓reduceIte, hStep]
  cases hEi : isEintrOutcome out
  · simp
  · have hPos : env.eintrBudget > 0 := hBudget hEi
    simp [hPos]

/-- `msToPollTimespec` produces a kernel-valid `Poll.Timespec` (`0 ≤ sec` and `nsec < 1_000_000_000`) for every `ms : Nat`. -/
theorem msToPollTimespec_isValid (ms : Nat) :
    (msToPollTimespec ms).isValid = true := by
  unfold msToPollTimespec Timespec.isValid NANOS_PER_SEC
  dsimp only
  simp only [Bool.and_eq_true, decide_eq_true_eq, Int.ofNat_eq_natCast]
  have hCap : Nat.min (ms / 1000) 9223372036854775807 ≤ 9223372036854775807 :=
    Nat.min_le_right _ _
  refine ⟨?_, ?_⟩
  · rw [Int64.le_iff_toInt_le, Int64.toInt_ofInt, Int.bmod_eq_of_le]
    · have : (0 : Int64).toInt = 0 := rfl; omega
    · change -9223372036854775808 ≤ (↑(Nat.min (ms / 1000) 9223372036854775807) : Int); omega
    · change (↑(Nat.min (ms / 1000) 9223372036854775807) : Int) < 9223372036854775808; omega
  · have hMod : ms % 1000 < 1000 := Nat.mod_lt ms (by decide)
    rw [UInt32.lt_iff_toNat_lt, UInt32.toNat_ofNat',
      Nat.mod_eq_of_lt (by change ms % 1000 * 1000000 < 4294967296; omega)]
    have : (1000000000 : UInt32).toNat = 1000000000 := rfl
    omega

end LeanSwe.LinuxSyscall.Poll
