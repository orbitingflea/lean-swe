import Core.Assumptions
import LeanSwe.Compress.Types
import LeanSwe.Compress.Impl
import LeanSwe.Compress.Interface
import LeanSweProofs.Process.Proofs
import LeanSweProofs.Compress.SpecTests
import LeanSweProofs.Compress.Proofs.SharedHelpers

/-!
Error-impossibility (`NeverErrorKindIO`) proofs for `LeanSwe.Compress.compress` and `compressWith`.
-/

namespace LeanSwe.Compress.Proofs

open LeanSwe.Process
open LeanSwe.Compress

private theorem io_pure_eq {α : Type} (a : α) (w : Void IO.RealWorld) :
    (pure a : IO α) w = EST.Out.ok a w := rfl

private theorem io_bind_eq {α β : Type} (x : IO α) (f : α → IO β) (w : Void IO.RealWorld) :
    (x >>= f) w =
      match x w with
      | EST.Out.ok a w' => f a w'
      | EST.Out.error e w' => EST.Out.error e w' := by
  change EST.bind x f w = _
  unfold EST.bind
  cases x w <;> rfl

private theorem validateCompressOptions_error_ne_corruptData (codec : Codec)
    (opts : CompressOptions) (input : ByteArray) {e : CompressError}
    (h : Internal.validateCompressOptions codec opts input = .error e) :
    e.kind ≠ .corruptData := by
  by_cases hv : isValidCompressInput codec opts input = true
  · have := (validateCompressOptions_true_implies_ok codec opts input hv).1
    rw [this] at h
    cases h
  · have hfalse : isValidCompressInput codec opts input = false := by
      cases hc : isValidCompressInput codec opts input <;> simp_all
    rcases validateCompressOptions_false_implies_error codec opts input hfalse with
      ⟨_, hVal, hk, _⟩
    rw [hVal] at h
    injection h with heq
    rw [← heq, hk]
    decide

/-- Formal impossibility proof for `LeanSwe.Compress.compressWith` never returning `.corruptData`. -/
theorem compress_compressWith_never_corruptData (codec : Codec) (opts : CompressOptions)
    (input : ByteArray) (w : Void IO.RealWorld) :
    Core.NeverErrorKindIO CompressError.kind .corruptData
      (Compress.compressWith codec opts input) w := by
  unfold Core.NeverErrorKindIO Compress.compressWith Compress.defaultApi Internal.mkApiM
    Internal.compressWith
  dsimp only
  cases hVal : Internal.validateCompressOptions codec opts input with
  | error e =>
    dsimp only
    rw [io_pure_eq]
    exact validateCompressOptions_error_ne_corruptData codec opts input hVal
  | ok _ =>
    dsimp only
    rw [io_bind_eq]
    rcases LeanSwe.Process.Proofs.defaultApi_run_never_throws (Internal.mkCompressRequest codec opts input) w with
      ⟨r, _, hRun⟩
    rw [hRun]
    cases r with
    | error pe =>
      dsimp only
      rw [io_pure_eq]
      dsimp only
      unfold Internal.classifyProcessError
      cases pe.kind with
      | invalidInput =>
        by_cases hRes : Internal.isResourceExhaustedProcessError pe <;> simp [hRes]
      | notFound | permissionDenied | timedOut | outputLimitExceeded | terminatedBySignal | nonZeroExit | ioError => simp
    | ok res =>
      dsimp only
      rw [io_pure_eq]
      dsimp only [Internal.classifyExitResult]
      by_cases hNz : (res.exitCode != 0) = true
      · simp [hNz]
      · simp only [hNz, Bool.false_eq_true, ↓reduceIte]
        by_cases hLim : res.stdout.size > opts.maxOutputBytes
        · simp [hLim]
        · simp [hLim]

/-- Formal impossibility proof for `LeanSwe.Compress.compress` never returning `.corruptData`. -/
theorem compress_compress_never_corruptData (codec : Codec) (input : ByteArray)
    (w : Void IO.RealWorld) :
    Core.NeverErrorKindIO CompressError.kind .corruptData
      (Compress.compress codec input) w :=
  compress_compressWith_never_corruptData codec {} input w

end LeanSwe.Compress.Proofs
