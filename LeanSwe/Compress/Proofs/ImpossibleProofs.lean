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

private theorem io_bind_ok {α β : Type} (act : IO α) (k : α → IO β) (w : Void IO.RealWorld)
    {a : α} {w' : Void IO.RealWorld} (h : act w = EST.Out.ok a w') :
    (act >>= k) w = k a w' := by
  change EST.bind act k w = k a w'
  simp [EST.bind, h]

private theorem ioConc_tryCatch_ok {α : Type} (act : IO α) (w : Void IO.RealWorld) :
    ∃ r w', Core.ioConcOps.tryCatchMsg act w = EST.Out.ok r w' := by
  have heq : Core.ioConcOps.tryCatchMsg act w =
      EST.tryCatch (EST.bind act (fun a => EST.pure (.ok a)))
        (fun err => EST.pure (.error (toString err))) w := rfl
  rw [heq]; unfold EST.tryCatch EST.bind EST.pure
  cases act w <;> exact ⟨_, _, rfl⟩

private theorem ioCell_get_ok {S : Type} (r : IO.Ref S) (w : Void IO.RealWorld) :
    ∃ s w', (Core.ioStateCell r).get w = EST.Out.ok s w' := by
  change ∃ s w', (r.get : BaseIO S).toEIO w = EST.Out.ok s w'
  unfold BaseIO.toEIO
  cases (r.get : BaseIO S) w with | mk a s => exact ⟨a, s, rfl⟩

private theorem ioCell_mod_ok {S α : Type} (r : IO.Ref S) (f : S → α × S) (w : Void IO.RealWorld) :
    ∃ a w', (Core.ioStateCell r).modifyGet f w = EST.Out.ok a w' := by
  change ∃ a w', (r.modifyGet f : BaseIO α).toEIO w = EST.Out.ok a w'
  unfold BaseIO.toEIO
  cases (r.modifyGet f : BaseIO α) w with | mk a s => exact ⟨a, s, rfl⟩

private theorem mkFullRaw_spawn_ok (sys : LeanSwe.Process.Internal.ProcessSysCapsM IO)
    (r : IO.Ref (LeanSwe.Process.Internal.ProcTableState LeanSwe.LinuxSyscall.RawFd))
    (ef : Nat) (req : ExecRequest) (w : Void IO.RealWorld) :
    ∃ res w', LeanSwe.Process.SysBridge.spawnConc sys Core.ioConcOps (Core.ioStateCell r) ef req w = EST.Out.ok res w' := by
  unfold LeanSwe.Process.SysBridge.spawnConc
  rcases ioConc_tryCatch_ok _ w with ⟨tr, w1, h1⟩; rw [io_bind_ok _ _ _ h1]
  cases tr with
  | error _ => exact ⟨_, w1, rfl⟩
  | ok os => cases os with
    | error _ => exact ⟨_, w1, rfl⟩
    | ok slot =>
      dsimp only; rcases ioCell_mod_ok r _ w1 with ⟨_, w2, h2⟩; rw [io_bind_ok _ _ _ h2]; exact ⟨_, w2, rfl⟩

private theorem mkFullRaw_await_ok (sys : LeanSwe.Process.Internal.ProcessSysCapsM IO)
    (r : IO.Ref (LeanSwe.Process.Internal.ProcTableState LeanSwe.LinuxSyscall.RawFd))
    (ef iof : Nat) (h : LeanSwe.Process.ProcessHandle) (stdin : ByteArray) (to? max? : Option Nat)
    (w : Void IO.RealWorld) :
    ∃ res w', LeanSwe.Process.SysBridge.awaitOutputConc sys Core.ioConcOps (Core.ioStateCell r) ef iof h stdin to? max? w = EST.Out.ok res w' := by
  unfold LeanSwe.Process.SysBridge.awaitOutputConc
  rcases ioCell_mod_ok r _ w with ⟨tk, w1, h1⟩; rw [io_bind_ok _ _ _ h1]
  cases tk with
  | none => exact ⟨_, w1, rfl⟩
  | some tup =>
    rcases tup with ⟨_, _, _, _⟩; dsimp only
    rcases ioConc_tryCatch_ok _ w1 with ⟨tr, w2, h2⟩; rw [io_bind_ok _ _ _ h2]
    cases tr with
    | error _ => exact ⟨_, w2, rfl⟩
    | ok os => cases os with
      | error _ => exact ⟨_, w2, rfl⟩
      | ok p =>
        rcases p with ⟨_, _⟩; dsimp only
        rcases ioCell_mod_ok r _ w2 with ⟨okF, w3, h3⟩; rw [io_bind_ok _ _ _ h3]
        cases okF <;> exact ⟨_, w3, rfl⟩

private theorem mkFullRaw_kill_ok (sys : LeanSwe.Process.Internal.ProcessSysCapsM IO)
    (r : IO.Ref (LeanSwe.Process.Internal.ProcTableState LeanSwe.LinuxSyscall.RawFd))
    (ef : Nat) (h : LeanSwe.Process.ProcessHandle) (w : Void IO.RealWorld) :
    ∃ res w', LeanSwe.Process.SysBridge.killProcessGroupConc sys Core.ioConcOps (Core.ioStateCell r) ef h w = EST.Out.ok res w' := by
  unfold LeanSwe.Process.SysBridge.killProcessGroupConc
  rcases ioCell_get_ok r w with ⟨st, w1, h1⟩; rw [io_bind_ok _ _ _ h1]
  cases (LeanSwe.Process.SysBridge.findSlotPure h.handleId st.slots).map (·.pgid) with
  | none => exact ⟨_, w1, rfl⟩
  | some _ => dsimp only; rcases ioConc_tryCatch_ok _ w1 with ⟨tr, w2, h2⟩; rw [io_bind_ok _ _ _ h2]; cases tr <;> exact ⟨_, w2, rfl⟩

private theorem mkFullRaw_reap_ok (sys : LeanSwe.Process.Internal.ProcessSysCapsM IO)
    (r : IO.Ref (LeanSwe.Process.Internal.ProcTableState LeanSwe.LinuxSyscall.RawFd))
    (ef : Nat) (h : LeanSwe.Process.ProcessHandle) (w : Void IO.RealWorld) :
    ∃ res w', LeanSwe.Process.SysBridge.reapConc sys Core.ioConcOps (Core.ioStateCell r) ef h w = EST.Out.ok res w' := by
  unfold LeanSwe.Process.SysBridge.reapConc
  rcases ioCell_mod_ok r _ w with ⟨det, w1, h1⟩; rw [io_bind_ok _ _ _ h1]
  cases det with
  | none => exact ⟨_, w1, rfl⟩
  | some _ => dsimp only; rcases ioConc_tryCatch_ok _ w1 with ⟨tr, w2, h2⟩; rw [io_bind_ok _ _ _ h2]; cases tr <;> exact ⟨_, w2, rfl⟩

private theorem mkFullRaw_run_never_throws (sys : LeanSwe.Process.Internal.ProcessSysCapsM IO)
    (r : IO.Ref (LeanSwe.Process.Internal.ProcTableState LeanSwe.LinuxSyscall.RawFd))
    (req : ExecRequest) (w : Void IO.RealWorld) :
    ∃ res w', LeanSwe.Process.Internal.run (LeanSwe.Process.SysBridge.mkFullRawOpsM sys Core.ioConcOps (Core.ioStateCell r)) req w = EST.Out.ok res w' := by
  unfold LeanSwe.Process.Internal.run LeanSwe.Process.SysBridge.mkFullRawOpsM
  cases LeanSwe.Process.Internal.validateRequest req with
  | error e => exact ⟨Except.error e, w, rfl⟩
  | ok vreq =>
    dsimp only
    rcases mkFullRaw_spawn_ok sys r _ vreq w with ⟨rSpawn, w1, hSpawn⟩; rw [io_bind_ok _ _ _ hSpawn]
    cases rSpawn with
    | error _ => exact ⟨_, w1, rfl⟩
    | ok h =>
      dsimp only
      rcases mkFullRaw_await_ok sys r _ _ h vreq.stdin vreq.timeoutMs vreq.maxOutputBytes w1 with ⟨rAwait, w2, hAwait⟩
      rw [io_bind_ok _ _ _ hAwait]
      rcases rAwait with _ | outcome
      · dsimp only
        rcases mkFullRaw_kill_ok sys r _ h w2 with ⟨_, w3, hKill⟩; rw [io_bind_ok _ _ _ hKill]
        rcases mkFullRaw_reap_ok sys r _ h w3 with ⟨_, w4, hReap⟩; rw [io_bind_ok _ _ _ hReap]
        exact ⟨_, w4, rfl⟩
      · cases outcome with
        | exited _ =>
          dsimp only
          rcases mkFullRaw_reap_ok sys r _ h w2 with ⟨rReap, w3, hReap⟩; rw [io_bind_ok _ _ _ hReap]
          cases rReap <;> exact ⟨_, w3, rfl⟩
        | signaled _ _ _ | timedOut _ _ | outputLimitExceeded _ _ =>
          dsimp only
          rcases mkFullRaw_kill_ok sys r _ h w2 with ⟨_, w3, hKill⟩; rw [io_bind_ok _ _ _ hKill]
          rcases mkFullRaw_reap_ok sys r _ h w3 with ⟨_, w4, hReap⟩; rw [io_bind_ok _ _ _ hReap]
          exact ⟨_, w4, rfl⟩

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
    Internal.compressWith LeanSwe.Process.defaultApi LeanSwe.Process.Internal.mkFullApiM
  dsimp only
  cases hVal : Internal.validateCompressOptions codec opts input with
  | error e =>
    dsimp only
    rw [io_pure_eq]
    exact validateCompressOptions_error_ne_corruptData codec opts input hVal
  | ok _ =>
    dsimp only
    rw [io_bind_eq]
    rcases mkFullRaw_run_never_throws _ _ (Internal.mkCompressRequest codec opts input) w with
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
