import LeanSwe.ProcessSandbox.Raw.Types
import LeanSwe.ProcessSandbox.Raw.Model
import LeanSwe.ProcessSandbox.Raw.Interface
import LeanSwe.ProcessSandbox.Raw.Impl
import LeanSwe.ProcessSandbox.Raw.SpecTests
import LeanSwe.ProcessSandbox.Raw.Proofs.EncodePlan
import LeanSwe.ProcessSandbox.Raw.Proofs.HostCgroupPresetProofs
import LeanSwe.ProcessSandbox.Raw.Proofs.HostBwrapProofs
import LeanSwe.ProcessSandbox.Raw.Proofs.HostForwarderStreamProofs
import LeanSwe.ProcessSandbox.Raw.Proofs.HostBridgeProofs

namespace LeanSwe.ProcessSandbox.Raw.Proofs

open Core
open Core.NondetTest
open LeanSwe.ProcessSandbox.Raw.Model.Internal (MockRawState mockRawOps freshU32 hasHandle)

private theorem ifEmpty_ne_empty (fallback msg : String) (hf : fallback ≠ "") :
    (if msg.isEmpty then fallback else msg) ≠ "" := by
  split
  · exact hf
  · next h =>
    intro hem
    subst hem
    simp [String.isEmpty] at h

private theorem append_head_ne_empty (pre rest : String) (hp : pre ≠ "") :
    pre ++ rest ≠ "" := by
  simp [String.append_eq_empty_iff, hp]

private theorem u32_size_lt_u64_size : UInt32.size < UInt64.size := by
  decide

private theorem isValidSandboxHandleId_of_lt_u32
    (id : Nat) (hpos : 0 < id) (hlt : id < UInt32.size) :
    isValidSandboxHandleId id = true :=
  decide_eq_true ⟨hpos, Nat.lt_trans hlt u32_size_lt_u64_size⟩

private theorem freshU32_pos (xs : List UInt32) : 0 < freshU32 xs := by
  unfold freshU32
  omega

private theorem foldl_max_ge (xs : List UInt32) (init : Nat) :
    init ≤ xs.foldl (fun m x => max m x.toNat) init ∧
    ∀ x ∈ xs, x.toNat ≤ xs.foldl (fun m x => max m x.toNat) init := by
  induction xs generalizing init with
  | nil => exact ⟨Nat.le_refl _, fun _ h => by contradiction⟩
  | cons y rest ih =>
    obtain ⟨h1, h2⟩ := ih (max init y.toNat)
    refine ⟨Nat.le_trans (Nat.le_max_left _ _) h1, fun x hx => ?_⟩
    rcases List.mem_cons.mp hx with rfl | hx'
    · exact Nat.le_trans (Nat.le_max_right _ _) h1
    · exact h2 x hx'

private theorem freshU32_gt_all (xs : List UInt32) :
    ∀ x ∈ xs, x.toNat < freshU32 xs := by
  intro x hx
  have h := (foldl_max_ge xs 0).2 x hx
  unfold freshU32
  omega

private theorem any_freshU32_false (xs : List UInt32) :
    xs.any (fun x => x.toNat == freshU32 xs) = false := by
  rw [List.any_eq_false]
  intro x hx hbeq
  have hlt := freshU32_gt_all xs x hx
  have heq := beq_iff_eq.mp hbeq
  omega

private theorem any_cons_u32_ofNat_self (id : Nat) (hlt : id < UInt32.size) (xs : List UInt32) :
    (UInt32.ofNat id :: xs).any (fun x => x.toNat == id) = true := by
  simp [List.any_cons, Nat.mod_eq_of_lt hlt]

private theorem u32_erase_cons_head (x : UInt32) (xs : List UInt32) :
    (x :: xs).erase x = xs := by
  simp [List.erase_cons_head]

private theorem hasHandle_zero (xs : List UInt32) : hasHandle xs 0 = false := by
  simp [hasHandle, isValidSandboxHandleId]

private theorem hasHandle_u64_size (xs : List UInt32) : hasHandle xs UInt64.size = false := by
  simp [hasHandle, isValidSandboxHandleId, UInt64.size]

private theorem hasHandle_fresh_self (xs : List UInt32) :
    hasHandle xs (freshU32 xs) = false := by
  simp [hasHandle, any_freshU32_false]

private theorem hasHandle_cons_fresh (xs : List UInt32) (hlt : freshU32 xs < UInt32.size) :
    hasHandle (UInt32.ofNat (freshU32 xs) :: xs) (freshU32 xs) = true := by
  simp [hasHandle, isValidSandboxHandleId_of_lt_u32 (freshU32 xs) (freshU32_pos xs) hlt,
    any_cons_u32_ofNat_self (freshU32 xs) hlt xs]

/-- Proof of `test_psandboxRaw_isValidSandboxHandleId_bounds` for `isValidSandboxHandleId`. -/
theorem proof_psandboxRaw_isValidSandboxHandleId_bounds :
    AllPass test_psandboxRaw_isValidSandboxHandleId_bounds := by
  intro n
  refine ⟨by decide, by decide, ?_, fun h => ⟨decide_eq_true h, trivial⟩⟩
  exact decide_eq_false (fun h => Nat.lt_irrefl _ (Nat.lt_of_le_of_lt (Nat.le_add_right UInt64.size n) h.2))

/-- Non-vacuity `CanReach` witness for `test_psandboxRaw_isValidSandboxHandleId_bounds`. -/
theorem reach_psandboxRaw_isValidSandboxHandleId_bounds :
    CanReach test_psandboxRaw_isValidSandboxHandleId_bounds := by
  refine ⟨1, by decide, by decide, by decide, by decide, by decide, trivial⟩

/-- Proof of `test_psandboxRaw_mapRawError_returnsNonEmptyMessage` for `defaultOps`. -/
theorem proof_psandboxRaw_mapRawError_returnsNonEmptyMessage :
    AllPass (test_psandboxRaw_mapRawError_returnsNonEmptyMessage defaultOps) := by
  intro raw
  simp only [defaultOps, Internal.mapRawError, Model.Internal.mapRawError, assert]
  refine ⟨?_, trivial⟩
  cases raw with
  | unavailable _ _ => exact ifEmpty_ne_empty _ _ (by decide)
  | notFound p _ _ =>
    exact ifEmpty_ne_empty _ _ (append_head_ne_empty "not found: " p (by decide))
  | permissionDenied _ _ _ => exact ifEmpty_ne_empty _ _ (by decide)
  | invalidArgument _ _ _ => exact ifEmpty_ne_empty _ _ (by decide)
  | ioError _ errno _ =>
    exact ifEmpty_ne_empty _ _ (by simp [String.append_eq_empty_iff, toString])
  | userError _ => exact ifEmpty_ne_empty _ _ (by decide)

/-- Non-vacuity `CanReach` witness for `test_psandboxRaw_mapRawError_returnsNonEmptyMessage`. -/
theorem reach_psandboxRaw_mapRawError_returnsNonEmptyMessage :
    CanReach (test_psandboxRaw_mapRawError_returnsNonEmptyMessage defaultOps) :=
  ⟨.userError "", proof_psandboxRaw_mapRawError_returnsNonEmptyMessage (.userError "")⟩

/-- Proof of `test_psandboxRaw_mapRawError_preservesKindAndFields` for `defaultOps`. -/
theorem proof_psandboxRaw_mapRawError_preservesKindAndFields :
    AllPass (test_psandboxRaw_mapRawError_preservesKindAndFields defaultOps) := by
  intro raw
  cases raw <;> simp [defaultOps, Internal.mapRawError, Model.Internal.mapRawError, assert]

/-- Non-vacuity `CanReach` witness for `test_psandboxRaw_mapRawError_preservesKindAndFields`. -/
theorem reach_psandboxRaw_mapRawError_preservesKindAndFields :
    CanReach (test_psandboxRaw_mapRawError_preservesKindAndFields defaultOps) :=
  ⟨.userError "err", by simp [defaultOps, Internal.mapRawError, Model.Internal.mapRawError, assert]⟩

/-- Proof of `test_psandboxRaw_decodeHostAuditArch_exactConstantsAndFailClosed` for `defaultOps`. -/
theorem proof_psandboxRaw_decodeHostAuditArch_exactConstantsAndFailClosed :
    AllPass (test_psandboxRaw_decodeHostAuditArch_exactConstantsAndFailClosed defaultOps) := by
  refine ⟨?_, ?_, ?_⟩
  · rfl
  · rfl
  · intro raw hne
    have h0 : raw ≠ 0xc000003e := hne.1
    have h1 : raw ≠ 0xc00000b7 := hne.2
    simp only [defaultOps, Internal.decodeHostAuditArch,
      LeanSwe.ProcessSandbox.Model.seccompArchOfAudit?,
      LeanSwe.ProcessSandbox.Model.AUDIT_ARCH_X86_64,
      LeanSwe.ProcessSandbox.Model.AUDIT_ARCH_AARCH64]
    have hb0 : (raw == 0xc000003e) = false := beq_false_of_ne h0
    have hb1 : (raw == 0xc00000b7) = false := beq_false_of_ne h1
    simp [hb0, hb1, Internal.mapRawError, Model.Internal.mapRawError, assert]

/-- Non-vacuity `CanReach` witness for `test_psandboxRaw_decodeHostAuditArch_exactConstantsAndFailClosed`. -/
theorem reach_psandboxRaw_decodeHostAuditArch_exactConstantsAndFailClosed :
    CanReach (test_psandboxRaw_decodeHostAuditArch_exactConstantsAndFailClosed defaultOps) := by
  refine ⟨rfl, rfl, 0, ⟨by decide, by decide⟩, ?_⟩
  simp [defaultOps, Internal.decodeHostAuditArch,
    LeanSwe.ProcessSandbox.Model.seccompArchOfAudit?,
    LeanSwe.ProcessSandbox.Model.AUDIT_ARCH_X86_64,
    LeanSwe.ProcessSandbox.Model.AUDIT_ARCH_AARCH64,
    Internal.mapRawError, Model.Internal.mapRawError, assert]

/-- Proof of `test_psandboxRaw_hostSeccompArch_failClosedUnavailable` for `mockRawOps`. -/
theorem proof_psandboxRaw_hostSeccompArch_failClosedUnavailable :
    AllPass (test_psandboxRaw_hostSeccompArch_failClosedUnavailable mockRawOps) := by
  intro s₀
  cases hok : s₀.preflightOk
  · simp [mockRawOps, Model.Internal.mapRawError, hok, StateT.run, assert]
  · simp [mockRawOps, hok, StateT.run, assert]

/-- Non-vacuity `CanReach` witness for `test_psandboxRaw_hostSeccompArch_failClosedUnavailable`. -/
theorem reach_psandboxRaw_hostSeccompArch_failClosedUnavailable :
    CanReach (test_psandboxRaw_hostSeccompArch_failClosedUnavailable mockRawOps) := by
  refine ⟨{ preflightOk := false }, ?_⟩
  simp [mockRawOps, Model.Internal.mapRawError, StateT.run, assert]

/-- Proof of `test_psandboxRaw_preflight_failClosedUnavailable` for `mockRawOps`. -/
theorem proof_psandboxRaw_preflight_failClosedUnavailable :
    AllPass (test_psandboxRaw_preflight_failClosedUnavailable mockRawOps) := by
  intro s₀ _
  cases hok : s₀.preflightOk
  · simp [mockRawOps, Model.Internal.mapRawError, hok, StateT.run, assert]
  · simp [mockRawOps, hok, StateT.run, assert]

/-- Non-vacuity `CanReach` witness for `test_psandboxRaw_preflight_failClosedUnavailable`. -/
theorem reach_psandboxRaw_preflight_failClosedUnavailable :
    CanReach (test_psandboxRaw_preflight_failClosedUnavailable mockRawOps) := by
  refine ⟨{ preflightOk := false }, {}, ?_⟩
  simp [mockRawOps, Model.Internal.mapRawError, StateT.run, assert]

/-- Proof of `test_psandboxRaw_planLifecycle_conservesOpenPlansAndRejectsClosed` for `mockRawOps`. -/
theorem proof_psandboxRaw_planLifecycle_conservesOpenPlansAndRejectsClosed :
    AllPass (test_psandboxRaw_planLifecycle_conservesOpenPlansAndRejectsClosed mockRawOps) := by
  intro s₀ _ _
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [mockRawOps, hasHandle_zero, Model.Internal.mapRawError, StateT.run]
  · simp [mockRawOps, hasHandle_u64_size, Model.Internal.mapRawError, StateT.run]
  · simp [mockRawOps, hasHandle_zero, Model.Internal.mapRawError, StateT.run]
  · dsimp only [mockRawOps, StateT.run]
    by_cases hlt : freshU32 s₀.plans < UInt32.size
    · have hval : isValidSandboxHandleId (freshU32 s₀.plans) = true :=
        isValidSandboxHandleId_of_lt_u32 (freshU32 s₀.plans) (freshU32_pos s₀.plans) hlt
      have hhas : hasHandle (UInt32.ofNat (freshU32 s₀.plans) :: s₀.plans) (freshU32 s₀.plans) = true :=
        hasHandle_cons_fresh s₀.plans hlt
      have herase : (UInt32.ofNat (freshU32 s₀.plans) :: s₀.plans).erase (UInt32.ofNat (freshU32 s₀.plans)) = s₀.plans :=
        u32_erase_cons_head _ _
      have hnone : hasHandle s₀.plans (freshU32 s₀.plans) = false :=
        hasHandle_fresh_self s₀.plans
      simp only [hlt, ↓reduceIte, hval, hhas, herase, hnone, Bool.false_eq_true,
        List.length_cons, Model.Internal.mapRawError, assert]
      repeat first | exact trivial | exact rfl | exact ⟨_, rfl, rfl⟩ | refine ⟨?_, ?_⟩
    · simp only [hlt, ↓reduceIte, Model.Internal.mapRawError, assert]
      exact ⟨⟨by decide, trivial⟩, trivial⟩

/-- Non-vacuity `CanReach` witness for `test_psandboxRaw_planLifecycle_conservesOpenPlansAndRejectsClosed`. -/
theorem reach_psandboxRaw_planLifecycle_conservesOpenPlansAndRejectsClosed :
    CanReach (test_psandboxRaw_planLifecycle_conservesOpenPlansAndRejectsClosed mockRawOps) := by
  refine ⟨{}, { program := "/bin/true" }, ByteArray.empty, ?_⟩
  simp [mockRawOps, hasHandle, isValidSandboxHandleId, UInt64.size, UInt32.size,
    freshU32, Model.Internal.mapRawError, assert, Bind.bind, StateT.run]

/-- Proof of `test_psandboxRaw_boxAndForwarderLifecycle_conservesResources` for `mockRawOps`. -/
theorem proof_psandboxRaw_boxAndForwarderLifecycle_conservesResources :
    AllPass (test_psandboxRaw_boxAndForwarderLifecycle_conservesResources mockRawOps) := by
  intro s₀ _ _ _ _ _
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp [mockRawOps, hasHandle_zero, Model.Internal.mapRawError, StateT.run]
  · simp [mockRawOps, hasHandle_zero, Model.Internal.mapRawError, StateT.run]
  · simp [mockRawOps, hasHandle_zero, Model.Internal.mapRawError, StateT.run]
  · simp [mockRawOps, hasHandle_zero, Model.Internal.mapRawError, StateT.run]
  · dsimp only [mockRawOps, StateT.run]
    by_cases hp : freshU32 s₀.plans < UInt32.size
    · have hhasP : hasHandle (UInt32.ofNat (freshU32 s₀.plans) :: s₀.plans) (freshU32 s₀.plans) = true :=
        hasHandle_cons_fresh s₀.plans hp
      have heraseP : (UInt32.ofNat (freshU32 s₀.plans) :: s₀.plans).erase (UInt32.ofNat (freshU32 s₀.plans)) = s₀.plans :=
        u32_erase_cons_head _ _
      simp only [hp, ↓reduceIte, hhasP]
      by_cases hb : freshU32 s₀.boxes < UInt32.size
      · have hvalB : isValidSandboxHandleId (freshU32 s₀.boxes) = true :=
          isValidSandboxHandleId_of_lt_u32 (freshU32 s₀.boxes) (freshU32_pos s₀.boxes) hb
        have hhasB : hasHandle (UInt32.ofNat (freshU32 s₀.boxes) :: s₀.boxes) (freshU32 s₀.boxes) = true :=
          hasHandle_cons_fresh s₀.boxes hb
        have heraseB : (UInt32.ofNat (freshU32 s₀.boxes) :: s₀.boxes).erase (UInt32.ofNat (freshU32 s₀.boxes)) = s₀.boxes :=
          u32_erase_cons_head _ _
        have hnoneB : hasHandle s₀.boxes (freshU32 s₀.boxes) = false :=
          hasHandle_fresh_self s₀.boxes
        simp only [hb, ↓reduceIte, assert]
        refine ⟨⟨hvalB, by omega, by omega, by omega, rfl⟩, ?_⟩
        simp only [hhasB, ↓reduceIte]
        by_cases hf : freshU32 s₀.fwds < UInt32.size
        · have hvalF : isValidSandboxHandleId (freshU32 s₀.fwds) = true :=
            isValidSandboxHandleId_of_lt_u32 (freshU32 s₀.fwds) (freshU32_pos s₀.fwds) hf
          have hhasF : hasHandle (UInt32.ofNat (freshU32 s₀.fwds) :: s₀.fwds) (freshU32 s₀.fwds) = true :=
            hasHandle_cons_fresh s₀.fwds hf
          have heraseF : (UInt32.ofNat (freshU32 s₀.fwds) :: s₀.fwds).erase (UInt32.ofNat (freshU32 s₀.fwds)) = s₀.fwds :=
            u32_erase_cons_head _ _
          have hnoneF : hasHandle s₀.fwds (freshU32 s₀.fwds) = false :=
            hasHandle_fresh_self s₀.fwds
          simp only [hf, ↓reduceIte, hvalF, hhasF, heraseF, hhasB, heraseB, hhasP, heraseP,
            hnoneB, hnoneF, Bool.false_eq_true, List.length_cons, Model.Internal.mapRawError]
          repeat first | exact trivial | exact rfl | exact ⟨_, rfl, rfl⟩ | refine ⟨?_, ?_⟩
        · simp [hf, assume]
      · simp [hb, assume]
    · simp [hp, assume]

/-- Non-vacuity `CanReach` witness for `test_psandboxRaw_boxAndForwarderLifecycle_conservesResources`. -/
theorem reach_psandboxRaw_boxAndForwarderLifecycle_conservesResources :
    CanReach (test_psandboxRaw_boxAndForwarderLifecycle_conservesResources mockRawOps) := by
  refine ⟨{}, { program := "/bin/true" }, ByteArray.empty, #[{ boxPort := 8080, hostPort := 8080 }], by decide, by decide, ?_⟩
  simp [mockRawOps, hasHandle, isValidSandboxHandleId, UInt64.size, UInt32.size,
    freshU32, Model.Internal.mapRawError, assert, Bind.bind, StateT.run]

end LeanSwe.ProcessSandbox.Raw.Proofs
