import LeanSwe.Process.Proofs.ImpossibleHelpers
import LeanSwe.Process.Proofs.ImpossibleRunProofs

/-!
`NeverErrorKindIO` proofs for `spawn`, `awaitOutput`, `killProcessGroup`, and `reap` in
`LeanSwe.Process`, plus re-exports of `ImpossibleRunProofs`.
-/

namespace LeanSwe.Process.Proofs

open Core
open LeanSwe.Process
open LeanSwe.Process.SysBridge

private theorem defaultApi_spawn_inv (req : SpawnRequest) (w : Void IO.RealWorld) :
    ∃ r w', LeanSwe.Process.spawn req w = .ok r w' ∧ basicErrOrOk r := by
  unfold LeanSwe.Process.spawn defaultApi Internal.mkFullApiM Internal.spawn mkFullRawOpsM
  dsimp only
  cases hVal : Internal.validateSpawnRequest req with
  | error err =>
    exact ⟨.error err, w, rfl, basic_invalid (validateSpawnRequest_err_is_invalidInput req err hVal)⟩
  | ok norm =>
    dsimp only
    rcases spawnConc_sat _ _ _ { toSpawnRequest := norm } w with ⟨rSpawn, w1, hSpawn, hSpawnInv⟩
    rw [imp_io_bind_ok _ _ _ hSpawn]
    cases rSpawn with
    | error _ => exact ⟨_, w1, rfl, ensureNonEmptyMsg_basic "process spawn failed" hSpawnInv⟩
    | ok h => exact ⟨.ok h, w1, rfl, trivial⟩

private theorem defaultApi_awaitOutput_inv (h : ProcessHandle) (stdin : ByteArray)
    (timeoutMs maxOutputBytes : Option Nat) (w : Void IO.RealWorld) :
    ∃ r w', LeanSwe.Process.awaitOutput h stdin timeoutMs maxOutputBytes w = .ok r w' ∧ basicErrOrOk r := by
  unfold LeanSwe.Process.awaitOutput defaultApi Internal.mkFullApiM Internal.awaitOutput mkFullRawOpsM
  dsimp only
  split
  · exact ⟨_, w, rfl, basic_invalid rfl⟩
  · rcases awaitOutputConc_sat _ _ _ _ h stdin timeoutMs maxOutputBytes w with ⟨rAw, w1, hAw, hAwInv⟩
    rw [imp_io_bind_ok _ _ _ hAw]
    cases rAw with
    | error _ => exact ⟨_, w1, rfl, ensureNonEmptyMsg_basic "process I/O failed" hAwInv⟩
    | ok out => exact ⟨.ok out, w1, rfl, trivial⟩

private theorem defaultApi_killProcessGroup_inv (h : ProcessHandle) (w : Void IO.RealWorld) :
    ∃ r w', LeanSwe.Process.killProcessGroup h w = .ok r w' ∧ basicErrOrOk r := by
  unfold LeanSwe.Process.killProcessGroup defaultApi Internal.mkFullApiM Internal.killProcessGroup mkFullRawOpsM
  dsimp only
  rcases killProcessGroupConc_sat _ _ _ h w with ⟨rKg, w1, hKg, hKgInv⟩
  rw [imp_io_bind_ok _ _ _ hKg]
  cases rKg with
  | error _ => exact ⟨_, w1, rfl, ensureNonEmptyMsg_basic "process group termination failed" hKgInv⟩
  | ok u => exact ⟨.ok u, w1, rfl, trivial⟩

private theorem defaultApi_reap_inv (h : ProcessHandle) (w : Void IO.RealWorld) :
    ∃ r w', LeanSwe.Process.reap h w = .ok r w' ∧ basicErrOrOk r := by
  unfold LeanSwe.Process.reap defaultApi Internal.mkFullApiM Internal.reap mkFullRawOpsM
  dsimp only
  rcases reapConc_sat _ _ _ h w with ⟨rRp, w1, hRp, hRpInv⟩
  rw [imp_io_bind_ok _ _ _ hRp]
  cases rRp with
  | error _ => exact ⟨_, w1, rfl, ensureNonEmptyMsg_basic "process reap failed" hRpInv⟩
  | ok u => exact ⟨.ok u, w1, rfl, trivial⟩

/-- `Process.spawn` never fails with `.timedOut`. -/
theorem process_spawn_never_timedOut (req : SpawnRequest) (w : Void IO.RealWorld) :
    Core.NeverErrorKindIO ProcessError.kind .timedOut (LeanSwe.Process.spawn req) w := by
  unfold Core.NeverErrorKindIO
  rcases defaultApi_spawn_inv req w with ⟨r, _, hr, hinv⟩
  rw [hr]; cases r with | ok _ => exact trivial | error _ => exact hinv.1

/-- `Process.spawn` never fails with `.outputLimitExceeded`. -/
theorem process_spawn_never_outputLimitExceeded (req : SpawnRequest) (w : Void IO.RealWorld) :
    Core.NeverErrorKindIO ProcessError.kind .outputLimitExceeded (LeanSwe.Process.spawn req) w := by
  unfold Core.NeverErrorKindIO
  rcases defaultApi_spawn_inv req w with ⟨r, _, hr, hinv⟩
  rw [hr]; cases r with | ok _ => exact trivial | error _ => exact hinv.2.1

/-- `Process.spawn` never fails with `.terminatedBySignal`. -/
theorem process_spawn_never_terminatedBySignal (req : SpawnRequest) (w : Void IO.RealWorld) :
    Core.NeverErrorKindIO ProcessError.kind .terminatedBySignal (LeanSwe.Process.spawn req) w := by
  unfold Core.NeverErrorKindIO
  rcases defaultApi_spawn_inv req w with ⟨r, _, hr, hinv⟩
  rw [hr]; cases r with | ok _ => exact trivial | error _ => exact hinv.2.2.1

/-- `Process.spawn` never fails with `.nonZeroExit`. -/
theorem process_spawn_never_nonZeroExit (req : SpawnRequest) (w : Void IO.RealWorld) :
    Core.NeverErrorKindIO ProcessError.kind .nonZeroExit (LeanSwe.Process.spawn req) w := by
  unfold Core.NeverErrorKindIO
  rcases defaultApi_spawn_inv req w with ⟨r, _, hr, hinv⟩
  rw [hr]; cases r with | ok _ => exact trivial | error _ => exact hinv.2.2.2

/-- `Process.awaitOutput` reports timeouts as `.ok (.timedOut ..)`, so it never fails with `.timedOut`. -/
theorem process_awaitOutput_never_timedOut (h : ProcessHandle) (stdin : ByteArray)
    (timeoutMs maxOutputBytes : Option Nat) (w : Void IO.RealWorld) :
    Core.NeverErrorKindIO ProcessError.kind .timedOut
      (LeanSwe.Process.awaitOutput h stdin timeoutMs maxOutputBytes) w := by
  unfold Core.NeverErrorKindIO
  rcases defaultApi_awaitOutput_inv h stdin timeoutMs maxOutputBytes w with ⟨r, _, hr, hinv⟩
  rw [hr]; cases r with | ok _ => exact trivial | error _ => exact hinv.1

/-- `Process.awaitOutput` reports output caps as `.ok (.outputLimitExceeded ..)`, so it never fails with `.outputLimitExceeded`. -/
theorem process_awaitOutput_never_outputLimitExceeded (h : ProcessHandle) (stdin : ByteArray)
    (timeoutMs maxOutputBytes : Option Nat) (w : Void IO.RealWorld) :
    Core.NeverErrorKindIO ProcessError.kind .outputLimitExceeded
      (LeanSwe.Process.awaitOutput h stdin timeoutMs maxOutputBytes) w := by
  unfold Core.NeverErrorKindIO
  rcases defaultApi_awaitOutput_inv h stdin timeoutMs maxOutputBytes w with ⟨r, _, hr, hinv⟩
  rw [hr]; cases r with | ok _ => exact trivial | error _ => exact hinv.2.1

/-- `Process.awaitOutput` reports signals as `.ok (.signaled ..)`, so it never fails with `.terminatedBySignal`. -/
theorem process_awaitOutput_never_terminatedBySignal (h : ProcessHandle) (stdin : ByteArray)
    (timeoutMs maxOutputBytes : Option Nat) (w : Void IO.RealWorld) :
    Core.NeverErrorKindIO ProcessError.kind .terminatedBySignal
      (LeanSwe.Process.awaitOutput h stdin timeoutMs maxOutputBytes) w := by
  unfold Core.NeverErrorKindIO
  rcases defaultApi_awaitOutput_inv h stdin timeoutMs maxOutputBytes w with ⟨r, _, hr, hinv⟩
  rw [hr]; cases r with | ok _ => exact trivial | error _ => exact hinv.2.2.1

/-- `Process.awaitOutput` reports non-zero exit codes inside `.ok (.exited ..)`, so it never fails with `.nonZeroExit`. -/
theorem process_awaitOutput_never_nonZeroExit (h : ProcessHandle) (stdin : ByteArray)
    (timeoutMs maxOutputBytes : Option Nat) (w : Void IO.RealWorld) :
    Core.NeverErrorKindIO ProcessError.kind .nonZeroExit
      (LeanSwe.Process.awaitOutput h stdin timeoutMs maxOutputBytes) w := by
  unfold Core.NeverErrorKindIO
  rcases defaultApi_awaitOutput_inv h stdin timeoutMs maxOutputBytes w with ⟨r, _, hr, hinv⟩
  rw [hr]; cases r with | ok _ => exact trivial | error _ => exact hinv.2.2.2

/-- `Process.killProcessGroup` never fails with `.timedOut`. -/
theorem process_killProcessGroup_never_timedOut (h : ProcessHandle) (w : Void IO.RealWorld) :
    Core.NeverErrorKindIO ProcessError.kind .timedOut (LeanSwe.Process.killProcessGroup h) w := by
  unfold Core.NeverErrorKindIO
  rcases defaultApi_killProcessGroup_inv h w with ⟨r, _, hr, hinv⟩
  rw [hr]; cases r with | ok _ => exact trivial | error _ => exact hinv.1

/-- `Process.killProcessGroup` never fails with `.outputLimitExceeded`. -/
theorem process_killProcessGroup_never_outputLimitExceeded (h : ProcessHandle) (w : Void IO.RealWorld) :
    Core.NeverErrorKindIO ProcessError.kind .outputLimitExceeded (LeanSwe.Process.killProcessGroup h) w := by
  unfold Core.NeverErrorKindIO
  rcases defaultApi_killProcessGroup_inv h w with ⟨r, _, hr, hinv⟩
  rw [hr]; cases r with | ok _ => exact trivial | error _ => exact hinv.2.1

/-- `Process.killProcessGroup` never fails with `.terminatedBySignal`. -/
theorem process_killProcessGroup_never_terminatedBySignal (h : ProcessHandle) (w : Void IO.RealWorld) :
    Core.NeverErrorKindIO ProcessError.kind .terminatedBySignal (LeanSwe.Process.killProcessGroup h) w := by
  unfold Core.NeverErrorKindIO
  rcases defaultApi_killProcessGroup_inv h w with ⟨r, _, hr, hinv⟩
  rw [hr]; cases r with | ok _ => exact trivial | error _ => exact hinv.2.2.1

/-- `Process.killProcessGroup` never fails with `.nonZeroExit`. -/
theorem process_killProcessGroup_never_nonZeroExit (h : ProcessHandle) (w : Void IO.RealWorld) :
    Core.NeverErrorKindIO ProcessError.kind .nonZeroExit (LeanSwe.Process.killProcessGroup h) w := by
  unfold Core.NeverErrorKindIO
  rcases defaultApi_killProcessGroup_inv h w with ⟨r, _, hr, hinv⟩
  rw [hr]; cases r with | ok _ => exact trivial | error _ => exact hinv.2.2.2

/-- `Process.reap` never fails with `.timedOut`. -/
theorem process_reap_never_timedOut (h : ProcessHandle) (w : Void IO.RealWorld) :
    Core.NeverErrorKindIO ProcessError.kind .timedOut (LeanSwe.Process.reap h) w := by
  unfold Core.NeverErrorKindIO
  rcases defaultApi_reap_inv h w with ⟨r, _, hr, hinv⟩
  rw [hr]; cases r with | ok _ => exact trivial | error _ => exact hinv.1

/-- `Process.reap` never fails with `.outputLimitExceeded`. -/
theorem process_reap_never_outputLimitExceeded (h : ProcessHandle) (w : Void IO.RealWorld) :
    Core.NeverErrorKindIO ProcessError.kind .outputLimitExceeded (LeanSwe.Process.reap h) w := by
  unfold Core.NeverErrorKindIO
  rcases defaultApi_reap_inv h w with ⟨r, _, hr, hinv⟩
  rw [hr]; cases r with | ok _ => exact trivial | error _ => exact hinv.2.1

/-- `Process.reap` never fails with `.terminatedBySignal`. -/
theorem process_reap_never_terminatedBySignal (h : ProcessHandle) (w : Void IO.RealWorld) :
    Core.NeverErrorKindIO ProcessError.kind .terminatedBySignal (LeanSwe.Process.reap h) w := by
  unfold Core.NeverErrorKindIO
  rcases defaultApi_reap_inv h w with ⟨r, _, hr, hinv⟩
  rw [hr]; cases r with | ok _ => exact trivial | error _ => exact hinv.2.2.1

/-- `Process.reap` never fails with `.nonZeroExit`. -/
theorem process_reap_never_nonZeroExit (h : ProcessHandle) (w : Void IO.RealWorld) :
    Core.NeverErrorKindIO ProcessError.kind .nonZeroExit (LeanSwe.Process.reap h) w := by
  unfold Core.NeverErrorKindIO
  rcases defaultApi_reap_inv h w with ⟨r, _, hr, hinv⟩
  rw [hr]; cases r with | ok _ => exact trivial | error _ => exact hinv.2.2.2

end LeanSwe.Process.Proofs
