import LeanSwe.Uuid.Interface
import LeanSwe.Uuid.SpecTests

/-!
# UUIDv4 Entropy-Gathering Loop & `TimeRand` Model Lemmas

Effectful proof layer for `LeanSwe.Uuid.Proofs` (independent of `Codec`):
- `mapRawError` kind and non-empty message invariants.
- `appendBytes` size invariant and bounded `gatherRandomBytes16` unfolding rules.
- Scripted chunked-read / `EINTR` retry loops and `TimeRand.modelOps` single-step reduction.
- Exhaustive `NeverErrorKindIO` reduction for `LeanSwe.Uuid.getUuid`.
-/

namespace LeanSwe.Uuid.Proofs.Entropy

open Core LeanSwe.Uuid
open LeanSwe.LinuxSyscall (Errno)
open LeanSwe.LinuxSyscall.TimeRand (TimeRandOpsM TimeRandOps TimeRandState GrndFlags
  deterministicEntropyList deterministicEntropyBytes modelOps)

private theorem append_ne_empty {a b : String} (hl : 0 < a.length) : a ++ b ≠ "" := by
  intro h; have hs := congrArg String.length h; rw [String.length_append] at hs
  have h0 : ("" : String).length = 0 := rfl; omega
private theorem nonEmptyMsg_ne {fallback msg : String} (hf : fallback ≠ "") : Internal.nonEmptyMsg fallback msg ≠ "" := by
  unfold Internal.nonEmptyMsg; by_cases h : msg.isEmpty; · simp [h, hf]
  simp [h]; rintro rfl; exact h rfl

/-- Every `Internal.mapRawError` result has kind `.entropyFailed`. -/
theorem mapRawError_kind (r : UuidRawError) : (Internal.mapRawError r).kind = .entropyFailed := by cases r <;> rfl

/-- Every `Internal.mapRawError` result carries a non-empty diagnostic message. -/
theorem mapRawError_msg_ne (r : UuidRawError) : (Internal.mapRawError r).message ≠ "" := by
  cases r <;> apply nonEmptyMsg_ne <;> first | exact append_ne_empty (by decide) | decide

/-- `Internal.appendBytes` adds the sizes of its two input byte arrays. -/
theorem appendBytes_size (a b : ByteArray) : (Internal.appendBytes a b).size = a.size + b.size := by
  cases a with | mk arrA => cases b with | mk arrB =>
    unfold Internal.appendBytes; by_cases h0 : (ByteArray.mk arrA).size == 0
    · have ha : arrA.size = 0 := beq_iff_eq.mp h0; simp only [h0, ↓reduceIte]; change arrB.size = arrA.size + arrB.size; omega
    · simp only [h0, Bool.false_eq_true, ↓reduceIte]; change (arrA.toList ++ arrB.toList).toArray.size = arrA.size + arrB.size; simp

/-- One-step unfolding of `gatherRandomBytes16` when `acc.size < 16` and fuel is positive. -/
theorem gatherRandomBytes16_step_succ {m : Type → Type} [Monad m]
    (sys : TimeRandOpsM m) (fuel' : Nat) (acc : ByteArray) (hacc : acc.size < 16) (last? : Option Errno) :
    Internal.gatherRandomBytes16 sys (fuel' + 1) acc last? =
      (sys.getrandom (UInt32.ofNat (16 - acc.size)) {} >>= fun r =>
        match Internal.stepRandomBytes16 (16 - acc.size) acc r with
        | .error err => pure (.error err) | .ok (.inl doneBytes) => pure (.ok doneBytes)
        | .ok (.inr (nextAcc, nextLast)) => Internal.gatherRandomBytes16 sys fuel' nextAcc nextLast) := by
  rw [Internal.gatherRandomBytes16.eq_def]
  simp only [beq_false_of_ne (by omega : acc.size ≠ 16), decide_eq_false (by omega : ¬acc.size > 16),
    Bool.false_eq_true, ↓reduceIte]; rfl

/-- Initial-step unfolding of `gatherRandomBytes16` from `ByteArray.empty` with `MAX_GETRANDOM_ATTEMPTS` fuel. -/
theorem gather_first_step {m : Type → Type} [Monad m] (sys : TimeRandOpsM m) :
    Internal.gatherRandomBytes16 sys Internal.MAX_GETRANDOM_ATTEMPTS ByteArray.empty none =
      (sys.getrandom (UInt32.ofNat 16) {} >>= fun r =>
        match Internal.stepRandomBytes16 16 ByteArray.empty r with
        | .error err => pure (.error err) | .ok (.inl doneBytes) => pure (.ok doneBytes)
        | .ok (.inr (nextAcc, nextLast)) => Internal.gatherRandomBytes16 sys 31 nextAcc nextLast) :=
  gatherRandomBytes16_step_succ sys 31 ByteArray.empty (by decide) none

private theorem gatherRandomBytes16_zero_lt {m : Type → Type} [Monad m]
    (sys : TimeRandOpsM m) (acc : ByteArray) (hacc : acc.size < 16) (last? : Option Errno) :
    Internal.gatherRandomBytes16 sys 0 acc last? =
      match last? with
      | some e => pure (.error (Internal.mapErrnoToUuidError e))
      | none => pure (.error (Internal.mapRawError (.shortRead acc.size s!"getrandom retry budget exhausted after {acc.size} of 16 bytes"))) := by
  rw [Internal.gatherRandomBytes16.eq_def]
  simp only [beq_false_of_ne (by omega : acc.size ≠ 16), decide_eq_false (by omega : ¬acc.size > 16), Bool.false_eq_true, ↓reduceIte]
  cases last? <;> rfl

/-- Single-step pop equation for `scriptedGetrandomOps`. -/
theorem scripted_cons (x : Except Errno ByteArray) (xs : List (Except Errno ByteArray))
    (len : UInt32) (flags : GrndFlags) : scriptedGetrandomOps.getrandom len flags (x :: xs) = (x, xs) := rfl

/-- Single-step counter increment equation for `countingFixedGetrandomOps`. -/
theorem counting_run (fixed : Except Errno ByteArray) (len : UInt32) (flags : GrndFlags) (c : Nat) :
    (countingFixedGetrandomOps fixed).getrandom len flags c = (fixed, c + 1) := rfl

private theorem deterministicEntropyList_length (d : Nat) : ∀ rem pos, (deterministicEntropyList d rem pos).length = rem
  | 0, _ => rfl | rem + 1, pos => by simp [deterministicEntropyList, deterministicEntropyList_length d rem (pos + 1)]

/-- `deterministicEntropyBytes d len` has exact length `len`. -/
theorem deterministicEntropyBytes_size (d len : Nat) : (deterministicEntropyBytes d len).size = len := by
  simp [deterministicEntropyBytes, ByteArray.size, deterministicEntropyList_length]

/-- Byte `0` of `deterministicEntropyBytes d 16` equals `UInt8.ofNat (d % 256)`. -/
theorem deterministicEntropyBytes_16_get0 (d : Nat) : (deterministicEntropyBytes d 16)[0]! = UInt8.ofNat (d % 256) := by
  unfold deterministicEntropyBytes
  rw [getElem!_pos _ 0 (by simp [ByteArray.size, deterministicEntropyList_length])]; simp [deterministicEntropyList]; rfl

/-- Single-call execution of `(Internal.mkApiM modelOps).getUuid` on any `TimeRandState`. -/
theorem mkApiM_modelOps_getUuid_run (s : TimeRandState) :
    (Internal.mkApiM modelOps).getUuid s =
      (Internal.fromRandomBytes (deterministicEntropyBytes s.entropyDraws 16),
        { s with crngReady := true, entropyDraws := s.entropyDraws + 1 }) := by
  cases s with | mk _ _ crng _ _ =>
    cases crng <;>
    · dsimp [Internal.mkApiM, Internal.mkApi, Bind.bind, Pure.pure, StateT.bind, StateT.pure]; rw [gather_first_step]
      dsimp [Internal.stepRandomBytes16, Internal.appendBytes, modelOps, Bind.bind, Pure.pure,
        StateT.bind, StateT.pure, MonadStateOf.get, get, StateT.get, MonadStateOf.set, set, StateT.set]; rfl

/-- Retrying `k` `EINTR` responses before completing with `b2` concatenates `acc` and `b2`. -/
theorem gather_script_eintr_loop (k fuel : Nat) (hk : k + 1 ≤ fuel)
    (acc b2 : ByteArray) (hacc0 : 0 < acc.size) (hb20 : 0 < b2.size) (hsum : acc.size + b2.size = 16) (last? : Option Errno) :
    Internal.gatherRandomBytes16 scriptedGetrandomOps fuel acc last? (List.replicate k (.error Errno.EINTR) ++ [.ok b2]) =
      (.ok (ByteArray.mk (acc.data.toList ++ b2.data.toList).toArray), []) := by
  induction k generalizing fuel last? with
  | zero =>
    obtain ⟨fuel', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : fuel ≠ 0)
    rw [gatherRandomBytes16_step_succ _ _ acc (by omega)]; dsimp only [Bind.bind, StateT.bind, List.replicate_zero, List.nil_append]; rw [scripted_cons]
    have hcond : (b2.size == 0 || decide (b2.size > 16 - acc.size)) = false := by rw [beq_false_of_ne (by omega), decide_eq_false (by omega)]; rfl
    have hnext16 : ((Internal.appendBytes acc b2).size == 16) = true := by rw [appendBytes_size, hsum]; rfl
    have happ : Internal.appendBytes acc b2 = ByteArray.mk (acc.data.toList ++ b2.data.toList).toArray := by
      unfold Internal.appendBytes; rw [beq_false_of_ne (by omega)]; rfl
    dsimp only [Internal.stepRandomBytes16]; rw [hcond]; simp only [Bool.false_eq_true, ↓reduceIte, hnext16]; rw [happ]; rfl
  | succ k' ih =>
    obtain ⟨fuel', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : fuel ≠ 0)
    rw [gatherRandomBytes16_step_succ _ _ acc (by omega)]; dsimp only [Bind.bind, StateT.bind, List.replicate_succ, List.cons_append]; rw [scripted_cons]
    dsimp only [Internal.stepRandomBytes16]; rw [show (Errno.EINTR == Errno.EINTR) = true from rfl]
    exact ih fuel' (by omega) (some Errno.EINTR)

private theorem gather_fixed_eintr_loop (fuel c : Nat) :
    Internal.gatherRandomBytes16 (countingFixedGetrandomOps (.error Errno.EINTR)) fuel ByteArray.empty (some Errno.EINTR) c =
      (.error (Internal.mapErrnoToUuidError Errno.EINTR), c + fuel) := by
  induction fuel generalizing c with
  | zero => rw [gatherRandomBytes16_zero_lt _ _ (by decide)]; rfl
  | succ fuel' ih =>
    rw [gatherRandomBytes16_step_succ _ _ ByteArray.empty (by decide)]; dsimp only [Bind.bind, StateT.bind]; rw [counting_run]
    dsimp only [Internal.stepRandomBytes16]; rw [show (Errno.EINTR == Errno.EINTR) = true from rfl]
    simp only [↓reduceIte]; rw [ih (c + 1)]; congr 1; omega

/-- Outcome equations for persistent `EINTR`, empty chunk, and oversized chunk against `countingFixedGetrandomOps`. -/
theorem gather_fixed_failures {bigChunk : ByteArray} (hbig : bigChunk.size > 16) :
    Internal.gatherRandomBytes16 (countingFixedGetrandomOps (.error Errno.EINTR)) Internal.MAX_GETRANDOM_ATTEMPTS ByteArray.empty none 0 =
      (.error (Internal.mapErrnoToUuidError Errno.EINTR), Internal.MAX_GETRANDOM_ATTEMPTS) ∧
    Internal.gatherRandomBytes16 (countingFixedGetrandomOps (.ok ByteArray.empty)) Internal.MAX_GETRANDOM_ATTEMPTS ByteArray.empty none 0 =
      (.error (Internal.mapRawError (.shortRead 0 "unexpected getrandom chunk length 0 (expected 1..16)")), 1) ∧
    ∃ err, Internal.gatherRandomBytes16 (countingFixedGetrandomOps (.ok bigChunk)) Internal.MAX_GETRANDOM_ATTEMPTS ByteArray.empty none 0 =
      (.error err, 1) ∧ err.kind = .entropyFailed ∧ err.errnoCode = none ∧ err.message ≠ "" := by
  refine ⟨?_, ?_, ?_⟩ <;> (rw [gather_first_step]; dsimp only [Bind.bind, StateT.bind]; rw [counting_run])
  · dsimp only [Internal.stepRandomBytes16]; rw [show (Errno.EINTR == Errno.EINTR) = true from rfl]; simp only [↓reduceIte]; exact gather_fixed_eintr_loop 31 1
  · rfl
  · dsimp only [Internal.stepRandomBytes16]; rw [decide_eq_true hbig, Bool.or_true]; simp only [↓reduceIte]; dsimp only [Pure.pure, StateT.pure]
    exact ⟨_, rfl, rfl, rfl, mapRawError_msg_ne _⟩

private theorem stepRandomBytes16_error_and_size (acc : ByteArray) (hacc : acc.size ≤ 16) (r : Except Errno ByteArray) :
    match Internal.stepRandomBytes16 (16 - acc.size) acc r with
    | .error err => err.kind = .entropyFailed | .ok (.inl bs) => bs.size = 16 | .ok (.inr (nextAcc, _)) => nextAcc.size ≤ 16 := by
  cases r with
  | error e =>
    dsimp [Internal.stepRandomBytes16]; by_cases he : e == Errno.EINTR
    · simp only [he, ↓reduceIte]; exact hacc
    · simp only [he, Bool.false_eq_true, ↓reduceIte]; exact mapRawError_kind _
  | ok chunk =>
    dsimp [Internal.stepRandomBytes16]; by_cases hc : (chunk.size == 0 || decide (chunk.size > 16 - acc.size))
    · simp only [hc, ↓reduceIte]; exact mapRawError_kind _
    · simp only [hc, Bool.false_eq_true, ↓reduceIte]
      have hgt : ¬(chunk.size > 16 - acc.size) := fun h => hc (by simp [decide_eq_true h])
      by_cases h16 : (Internal.appendBytes acc chunk).size == 16
      · simp only [h16, ↓reduceIte]; exact beq_iff_eq.mp h16
      · simp only [h16, Bool.false_eq_true, ↓reduceIte]; rw [appendBytes_size]; omega

private theorem io_bind_eq {α β : Type} (x : IO α) (f : α → IO β) (w : Void IO.RealWorld)
    {a : α} {w' : Void IO.RealWorld} (hx : x w = EST.Out.ok a w') : (x >>= f) w = f a w' := by
  change EST.bind x f w = f a w'; dsimp only [EST.bind]; rw [hx]
private theorem liftM_baseIO_ok {α : Type} (act : BaseIO α) (w : Void IO.RealWorld) :
    ∃ a w', (liftM act : IO α) w = EST.Out.ok a w' := by cases act w; exact ⟨_, _, rfl⟩

private theorem gatherRandomBytes16_ok_or_entropyFailed (sys : TimeRandOps)
    (hsys : ∀ len flags (w : Void IO.RealWorld), ∃ r w', sys.getrandom len flags w = EST.Out.ok r w')
    (fuel : Nat) (acc : ByteArray) (hacc : acc.size ≤ 16) (last? : Option Errno) (w : Void IO.RealWorld) :
    match (Internal.gatherRandomBytes16 sys fuel acc last?) w with
    | EST.Out.ok (.error err) _ => err.kind = .entropyFailed | EST.Out.ok (.ok bs) _ => bs.size = 16 | EST.Out.error _ _ => False := by
  induction fuel generalizing acc last? w with
  | zero =>
    by_cases h16 : acc.size = 16
    · rw [Internal.gatherRandomBytes16.eq_def]; simp only [beq_iff_eq.mpr h16, ↓reduceIte]; exact h16
    · rw [gatherRandomBytes16_zero_lt _ acc (by omega)]; cases last? <;> exact mapRawError_kind _
  | succ fuel' ih =>
    by_cases h16 : acc.size = 16
    · rw [Internal.gatherRandomBytes16.eq_def]; simp only [beq_iff_eq.mpr h16, ↓reduceIte]; exact h16
    · rw [gatherRandomBytes16_step_succ _ _ acc (by omega)]
      obtain ⟨r, w', hr⟩ := hsys (UInt32.ofNat (16 - acc.size)) {} w; rw [io_bind_eq _ _ w hr]
      have hs := stepRandomBytes16_error_and_size acc hacc r
      cases hsRes : Internal.stepRandomBytes16 (16 - acc.size) acc r with
      | error err => rw [hsRes] at hs; exact hs
      | ok x => rw [hsRes] at hs; cases x with | inl bs => exact hs | inr p => exact ih p.1 hs p.2 w'

/-- `LeanSwe.Uuid.getUuid` can never throw an `IO.Error` or return any error kind other than `.entropyFailed`. -/
theorem getUuid_never (k : UuidErrorKind) (hk : UuidErrorKind.entropyFailed ≠ k) (w : Void IO.RealWorld) :
    NeverErrorKindIO UuidError.kind k LeanSwe.Uuid.getUuid w := by
  have hgDef : LeanSwe.Uuid.getUuid =
      (Internal.gatherRandomBytes16 LeanSwe.LinuxSyscall.TimeRand.defaultOps Internal.MAX_GETRANDOM_ATTEMPTS ByteArray.empty none >>=
        fun res => match res with | .error err => pure (.error err) | .ok bs => pure (Internal.fromRandomBytes bs)) := rfl
  have h := gatherRandomBytes16_ok_or_entropyFailed LeanSwe.LinuxSyscall.TimeRand.defaultOps
    (fun _ _ w0 => liftM_baseIO_ok _ w0) Internal.MAX_GETRANDOM_ATTEMPTS ByteArray.empty (by decide) none w
  dsimp [NeverErrorKindIO]; rw [hgDef]
  cases hg : (Internal.gatherRandomBytes16 LeanSwe.LinuxSyscall.TimeRand.defaultOps Internal.MAX_GETRANDOM_ATTEMPTS ByteArray.empty none) w with
  | error _ _ => rw [hg] at h; exact False.elim h
  | ok res w' =>
    rw [hg] at h; rw [io_bind_eq _ _ w hg]
    cases res with
    | error err => change err.kind ≠ k; rw [h]; exact hk
    | ok bs => have hne : (bs.size != 16) = false := by simp [h]
               dsimp only [Internal.fromRandomBytes]; rw [hne]; trivial

end LeanSwe.Uuid.Proofs.Entropy
