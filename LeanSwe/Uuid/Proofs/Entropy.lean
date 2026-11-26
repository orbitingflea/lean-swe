import Core.Assumptions
import LeanSwe.Uuid.Interface

/-!
# UUIDv4 Entropy-Gathering Loop & Error-Impossibility Lemmas

Effectful proof layer for `LeanSwe.Uuid.Proofs`:
- `mapRawError` kind and non-empty message invariants.
- `appendBytes` size invariant and bounded `gatherRandomBytes16` unfolding rules.
- Exhaustive `NeverErrorKindIO` reduction for `LeanSwe.Uuid.getUuid`.
-/

namespace LeanSwe.Uuid.Proofs.Entropy

open Core LeanSwe.Uuid
open LeanSwe.LinuxSyscall (Errno)
open LeanSwe.LinuxSyscall.TimeRand (TimeRandOpsM TimeRandOps)

private theorem append_ne_empty {a b : String} (hl : 0 < a.length) : a ++ b ≠ "" := by
  intro h
  have hs := congrArg String.length h
  rw [String.length_append] at hs
  have h0 : ("" : String).length = 0 := rfl
  omega

private theorem nonEmptyMsg_ne {fallback msg : String} (hf : fallback ≠ "") :
    Internal.nonEmptyMsg fallback msg ≠ "" := by
  unfold Internal.nonEmptyMsg
  by_cases h : msg.isEmpty
  · simp [h, hf]
  · simp [h]
    rintro rfl
    exact h rfl

/-- Every `Internal.mapRawError` result has kind `.entropyFailed`. -/
theorem mapRawError_kind (r : UuidRawError) : (Internal.mapRawError r).kind = .entropyFailed := by
  cases r <;> rfl

/-- Every `Internal.mapRawError` result carries a non-empty diagnostic message. -/
theorem mapRawError_msg_ne (r : UuidRawError) : (Internal.mapRawError r).message ≠ "" := by
  cases r <;> apply nonEmptyMsg_ne <;> first | exact append_ne_empty (by decide) | decide

/-- `Internal.appendBytes` adds the sizes of its two input byte arrays. -/
theorem appendBytes_size (a b : ByteArray) : (Internal.appendBytes a b).size = a.size + b.size := by
  cases a with
  | mk arrA =>
    cases b with
    | mk arrB =>
      unfold Internal.appendBytes
      by_cases h0 : (ByteArray.mk arrA).size == 0
      · have ha : arrA.size = 0 := beq_iff_eq.mp h0
        simp only [h0, ↓reduceIte]
        change arrB.size = arrA.size + arrB.size
        omega
      · simp only [h0, Bool.false_eq_true, ↓reduceIte]
        change (arrA.toList ++ arrB.toList).toArray.size = arrA.size + arrB.size
        simp

/-- One-step unfolding of `gatherRandomBytes16` when `acc.size < 16` and fuel is positive. -/
theorem gatherRandomBytes16_step_succ {m : Type → Type} [Monad m]
    (sys : TimeRandOpsM m) (fuel' : Nat) (acc : ByteArray) (hacc : acc.size < 16)
    (last? : Option Errno) :
    Internal.gatherRandomBytes16 sys (fuel' + 1) acc last? =
      (sys.getrandom (UInt32.ofNat (16 - acc.size)) {} >>= fun r =>
        match Internal.stepRandomBytes16 (16 - acc.size) acc r with
        | .error err => pure (.error err)
        | .ok (.inl doneBytes) => pure (.ok doneBytes)
        | .ok (.inr (nextAcc, nextLast)) => Internal.gatherRandomBytes16 sys fuel' nextAcc nextLast) := by
  rw [Internal.gatherRandomBytes16.eq_def]
  simp only [beq_false_of_ne (by omega : acc.size ≠ 16), decide_eq_false (by omega : ¬acc.size > 16),
    Bool.false_eq_true, ↓reduceIte]
  rfl

/-- Initial-step unfolding of `gatherRandomBytes16` from `ByteArray.empty` with `MAX_GETRANDOM_ATTEMPTS` fuel. -/
theorem gather_first_step {m : Type → Type} [Monad m] (sys : TimeRandOpsM m) :
    Internal.gatherRandomBytes16 sys Internal.MAX_GETRANDOM_ATTEMPTS ByteArray.empty none =
      (sys.getrandom (UInt32.ofNat 16) {} >>= fun r =>
        match Internal.stepRandomBytes16 16 ByteArray.empty r with
        | .error err => pure (.error err)
        | .ok (.inl doneBytes) => pure (.ok doneBytes)
        | .ok (.inr (nextAcc, nextLast)) => Internal.gatherRandomBytes16 sys 31 nextAcc nextLast) :=
  gatherRandomBytes16_step_succ sys 31 ByteArray.empty (by decide) none

private theorem gatherRandomBytes16_zero_lt {m : Type → Type} [Monad m]
    (sys : TimeRandOpsM m) (acc : ByteArray) (hacc : acc.size < 16) (last? : Option Errno) :
    Internal.gatherRandomBytes16 sys 0 acc last? =
      match last? with
      | some e => pure (.error (Internal.mapErrnoToUuidError e))
      | none => pure (.error (Internal.mapRawError (.shortRead acc.size s!"getrandom retry budget exhausted after {acc.size} of 16 bytes"))) := by
  rw [Internal.gatherRandomBytes16.eq_def]
  simp only [beq_false_of_ne (by omega : acc.size ≠ 16), decide_eq_false (by omega : ¬acc.size > 16),
    Bool.false_eq_true, ↓reduceIte]
  cases last? <;> rfl

private theorem stepRandomBytes16_error_and_size (acc : ByteArray) (hacc : acc.size ≤ 16)
    (r : Except Errno ByteArray) :
    match Internal.stepRandomBytes16 (16 - acc.size) acc r with
    | .error err => err.kind = .entropyFailed
    | .ok (.inl bs) => bs.size = 16
    | .ok (.inr (nextAcc, _)) => nextAcc.size ≤ 16 := by
  cases r with
  | error e =>
    dsimp [Internal.stepRandomBytes16]
    by_cases he : e == Errno.EINTR
    · simp only [he, ↓reduceIte]; exact hacc
    · simp only [he, Bool.false_eq_true, ↓reduceIte]; exact mapRawError_kind _
  | ok chunk =>
    dsimp [Internal.stepRandomBytes16]
    by_cases hc : (chunk.size == 0 || decide (chunk.size > 16 - acc.size))
    · simp only [hc, ↓reduceIte]; exact mapRawError_kind _
    · simp only [hc, Bool.false_eq_true, ↓reduceIte]
      have hgt : ¬(chunk.size > 16 - acc.size) := fun h => hc (by simp [decide_eq_true h])
      by_cases h16 : (Internal.appendBytes acc chunk).size == 16
      · simp only [h16, ↓reduceIte]; exact beq_iff_eq.mp h16
      · simp only [h16, Bool.false_eq_true, ↓reduceIte]; rw [appendBytes_size]; omega

private theorem io_bind_eq {α β : Type} (x : IO α) (f : α → IO β) (w : Void IO.RealWorld)
    {a : α} {w' : Void IO.RealWorld} (hx : x w = EST.Out.ok a w') : (x >>= f) w = f a w' := by
  change EST.bind x f w = f a w'
  dsimp only [EST.bind]
  rw [hx]

private theorem liftM_baseIO_ok {α : Type} (act : BaseIO α) (w : Void IO.RealWorld) :
    ∃ a w', (liftM act : IO α) w = EST.Out.ok a w' := by
  cases act w
  exact ⟨_, _, rfl⟩

private theorem gatherRandomBytes16_ok_or_entropyFailed (sys : TimeRandOps)
    (hsys : ∀ len flags (w : Void IO.RealWorld), ∃ r w', sys.getrandom len flags w = EST.Out.ok r w')
    (fuel : Nat) (acc : ByteArray) (hacc : acc.size ≤ 16) (last? : Option Errno)
    (w : Void IO.RealWorld) :
    match (Internal.gatherRandomBytes16 sys fuel acc last?) w with
    | EST.Out.ok (.error err) _ => err.kind = .entropyFailed
    | EST.Out.ok (.ok bs) _ => bs.size = 16
    | EST.Out.error _ _ => False := by
  induction fuel generalizing acc last? w with
  | zero =>
    by_cases h16 : acc.size = 16
    · rw [Internal.gatherRandomBytes16.eq_def]
      simp only [beq_iff_eq.mpr h16, ↓reduceIte]
      exact h16
    · rw [gatherRandomBytes16_zero_lt _ acc (by omega)]
      cases last? <;> exact mapRawError_kind _
  | succ fuel' ih =>
    by_cases h16 : acc.size = 16
    · rw [Internal.gatherRandomBytes16.eq_def]
      simp only [beq_iff_eq.mpr h16, ↓reduceIte]
      exact h16
    · rw [gatherRandomBytes16_step_succ _ _ acc (by omega)]
      obtain ⟨r, w', hr⟩ := hsys (UInt32.ofNat (16 - acc.size)) {} w
      rw [io_bind_eq _ _ w hr]
      have hs := stepRandomBytes16_error_and_size acc hacc r
      cases hsRes : Internal.stepRandomBytes16 (16 - acc.size) acc r with
      | error err => rw [hsRes] at hs; exact hs
      | ok x =>
        rw [hsRes] at hs
        cases x with
        | inl bs => exact hs
        | inr p => exact ih p.1 hs p.2 w'

/-- `LeanSwe.Uuid.getUuid` can never throw an `IO.Error` or return any error kind other than `.entropyFailed`. -/
theorem getUuid_never (k : UuidErrorKind) (hk : UuidErrorKind.entropyFailed ≠ k)
    (w : Void IO.RealWorld) :
    NeverErrorKindIO UuidError.kind k LeanSwe.Uuid.getUuid w := by
  have hgDef : LeanSwe.Uuid.getUuid =
      (Internal.gatherRandomBytes16 LeanSwe.LinuxSyscall.TimeRand.defaultOps Internal.MAX_GETRANDOM_ATTEMPTS ByteArray.empty none >>=
        fun res => match res with | .error err => pure (.error err) | .ok bs => pure (Internal.fromRandomBytes bs)) := rfl
  have h := gatherRandomBytes16_ok_or_entropyFailed LeanSwe.LinuxSyscall.TimeRand.defaultOps
    (fun _ _ w0 => liftM_baseIO_ok _ w0) Internal.MAX_GETRANDOM_ATTEMPTS ByteArray.empty (by decide) none w
  dsimp [NeverErrorKindIO]
  rw [hgDef]
  cases hg : (Internal.gatherRandomBytes16 LeanSwe.LinuxSyscall.TimeRand.defaultOps Internal.MAX_GETRANDOM_ATTEMPTS ByteArray.empty none) w with
  | error _ _ => rw [hg] at h; exact False.elim h
  | ok res w' =>
    rw [hg] at h
    rw [io_bind_eq _ _ w hg]
    cases res with
    | error err => change err.kind ≠ k; rw [h]; exact hk
    | ok bs =>
      have hne : (bs.size != 16) = false := by simp [h]
      dsimp only [Internal.fromRandomBytes]
      rw [hne]
      trivial

end LeanSwe.Uuid.Proofs.Entropy
