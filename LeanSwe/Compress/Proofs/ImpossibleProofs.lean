import LeanSwe.Compress.Types
import LeanSwe.Compress.Impl
import LeanSwe.Compress.Interface
import LeanSwe.Compress.SpecTests
import LeanSwe.Compress.Proofs.SharedHelpers

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

private theorem catchProc_never_throws {α : Type} (prog? : Option String)
    (act : IO (Except ProcessError α)) (w : Void IO.RealWorld) :
    ∃ r w', LeanSwe.Process.SysBridge.catchProc prog? act w = EST.Out.ok r w' := by
  have heq : LeanSwe.Process.SysBridge.catchProc prog? act w =
      EST.tryCatch act
        (fun err => EST.pure (.error (LeanSwe.Process.SysBridge.mapIoError prog? err))) w := rfl
  rw [heq]
  cases h : act w with
  | ok a w' => exact ⟨a, w', by simp [EST.tryCatch, h]⟩
  | error err w' =>
    exact ⟨.error (LeanSwe.Process.SysBridge.mapIoError prog? err), w',
      by simp [EST.tryCatch, EST.pure, h]⟩

private theorem defaultOps_spawn_never_throws (req : ExecRequest) (w : Void IO.RealWorld) :
    ∃ r w', LeanSwe.Process.SysBridge.defaultOps.spawn req w = EST.Out.ok r w' :=
  catchProc_never_throws (some req.program) _ w

private theorem defaultOps_awaitOutput_never_throws (h : LeanSwe.Process.ProcessHandle)
    (stdin : ByteArray) (timeoutMs maxOut : Option Nat) (w : Void IO.RealWorld) :
    ∃ r w', LeanSwe.Process.SysBridge.defaultOps.awaitOutput h stdin timeoutMs maxOut w = EST.Out.ok r w' :=
  catchProc_never_throws none _ w

private theorem defaultOps_killProcessGroup_never_throws (h : LeanSwe.Process.ProcessHandle)
    (w : Void IO.RealWorld) :
    ∃ r w', LeanSwe.Process.SysBridge.defaultOps.killProcessGroup h w = EST.Out.ok r w' :=
  catchProc_never_throws none _ w

private theorem defaultOps_reap_never_throws (h : LeanSwe.Process.ProcessHandle)
    (w : Void IO.RealWorld) :
    ∃ r w', LeanSwe.Process.SysBridge.defaultOps.reap h w = EST.Out.ok r w' :=
  catchProc_never_throws none _ w

private theorem processRun_defaultOps_never_throws (req : ExecRequest) (w : Void IO.RealWorld) :
    ∃ r w', LeanSwe.Process.Internal.run LeanSwe.Process.SysBridge.defaultOps req w = EST.Out.ok r w' := by
  unfold LeanSwe.Process.Internal.run
  cases hVal : LeanSwe.Process.Internal.validateRequest req with
  | error e =>
    dsimp only
    rw [io_pure_eq]
    exact ⟨Except.error e, w, rfl⟩
  | ok vreq =>
    dsimp only
    rw [io_bind_eq]
    rcases defaultOps_spawn_never_throws vreq w with ⟨rSpawn, w1, hSpawn⟩
    rw [hSpawn]
    cases rSpawn with
    | error err =>
      dsimp only
      rw [io_pure_eq]
      exact ⟨_, _, rfl⟩
    | ok h =>
      dsimp only
      rw [io_bind_eq]
      rcases defaultOps_awaitOutput_never_throws h vreq.stdin vreq.timeoutMs vreq.maxOutputBytes w1 with
        ⟨rAwait, w2, hAwait⟩
      rw [hAwait]
      rcases rAwait with err | outcome
      · dsimp only
        rw [io_bind_eq]
        rcases defaultOps_killProcessGroup_never_throws h w2 with ⟨_, w3, hKill⟩
        rw [hKill]; dsimp only; rw [io_bind_eq]
        rcases defaultOps_reap_never_throws h w3 with ⟨_, w4, hReap⟩
        rw [hReap]; dsimp only; rw [io_pure_eq]
        exact ⟨_, _, rfl⟩
      · cases outcome with
        | exited res =>
          dsimp only
          rw [io_bind_eq]
          rcases defaultOps_reap_never_throws h w2 with ⟨rReap, w3, hReap⟩
          rw [hReap]
          cases rReap <;> (dsimp only; rw [io_pure_eq]; exact ⟨_, _, rfl⟩)
        | signaled _ _ _ | timedOut _ _ | outputLimitExceeded _ _ =>
          dsimp only
          rw [io_bind_eq]
          rcases defaultOps_killProcessGroup_never_throws h w2 with ⟨_, w3, hKill⟩
          rw [hKill]; dsimp only; rw [io_bind_eq]
          rcases defaultOps_reap_never_throws h w3 with ⟨_, w4, hReap⟩
          rw [hReap]; dsimp only; rw [io_pure_eq]
          exact ⟨_, _, rfl⟩

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
    Internal.compressWith LeanSwe.Process.defaultApi LeanSwe.Process.Internal.mkApiM
  dsimp only
  cases hVal : Internal.validateCompressOptions codec opts input with
  | error e =>
    dsimp only
    rw [io_pure_eq]
    exact validateCompressOptions_error_ne_corruptData codec opts input hVal
  | ok _ =>
    dsimp only
    rw [io_bind_eq]
    rcases processRun_defaultOps_never_throws (Internal.mkCompressRequest codec opts input) w with
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
