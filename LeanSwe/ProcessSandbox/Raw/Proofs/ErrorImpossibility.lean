import Core.Assumptions
import LeanSwe.ProcessSandbox.Raw.Interface
import LeanSwe.ProcessSandbox.Raw.Proofs.EncodePlan

namespace LeanSwe.ProcessSandbox.Raw.Proofs

open Core
open LeanSwe.ProcessSandbox.Raw

private theorem decodeHostAuditArch_err_kind (raw : UInt32) (e : SandboxError)
    (h : Internal.decodeHostAuditArch raw = .error e) : e.kind = .unavailable := by
  unfold Internal.decodeHostAuditArch at h
  cases hm : LeanSwe.ProcessSandbox.Model.seccompArchOfAudit? raw with
  | some _ => rw [hm] at h; cases h
  | none => rw [hm] at h; cases h; rfl

/-- `decodeHostAuditArch` never fails with `.invalidInput`. -/
theorem raw_decodeHostAuditArch_never_invalidInput (raw : UInt32) :
    Core.NeverErrorKindPure SandboxError.kind .invalidInput (LeanSwe.ProcessSandbox.Raw.decodeHostAuditArch raw) := by
  cases h : LeanSwe.ProcessSandbox.Raw.decodeHostAuditArch raw with
  | ok _ => trivial
  | error e =>
    dsimp only [Core.NeverErrorKindPure]
    have hk := decodeHostAuditArch_err_kind raw e h
    rw [hk]; decide

/-- `decodeHostAuditArch` never fails with `.notFound`. -/
theorem raw_decodeHostAuditArch_never_notFound (raw : UInt32) :
    Core.NeverErrorKindPure SandboxError.kind .notFound (LeanSwe.ProcessSandbox.Raw.decodeHostAuditArch raw) := by
  cases h : LeanSwe.ProcessSandbox.Raw.decodeHostAuditArch raw with
  | ok _ => trivial
  | error e =>
    dsimp only [Core.NeverErrorKindPure]
    have hk := decodeHostAuditArch_err_kind raw e h
    rw [hk]; decide

/-- `decodeHostAuditArch` never fails with `.permissionDenied`. -/
theorem raw_decodeHostAuditArch_never_permissionDenied (raw : UInt32) :
    Core.NeverErrorKindPure SandboxError.kind .permissionDenied (LeanSwe.ProcessSandbox.Raw.decodeHostAuditArch raw) := by
  cases h : LeanSwe.ProcessSandbox.Raw.decodeHostAuditArch raw with
  | ok _ => trivial
  | error e =>
    dsimp only [Core.NeverErrorKindPure]
    have hk := decodeHostAuditArch_err_kind raw e h
    rw [hk]; decide

/-- `decodeHostAuditArch` never fails with `.ioError`. -/
theorem raw_decodeHostAuditArch_never_ioError (raw : UInt32) :
    Core.NeverErrorKindPure SandboxError.kind .ioError (LeanSwe.ProcessSandbox.Raw.decodeHostAuditArch raw) := by
  cases h : LeanSwe.ProcessSandbox.Raw.decodeHostAuditArch raw with
  | ok _ => trivial
  | error e =>
    dsimp only [Core.NeverErrorKindPure]
    have hk := decodeHostAuditArch_err_kind raw e h
    rw [hk]; decide

private theorem encodePlan_err_kind (plan : CompiledSandboxPlan) (seccompBytes : ByteArray) (e : SandboxError)
    (h : LeanSwe.ProcessSandbox.Raw.encodePlan plan seccompBytes = .error e) :
    e.kind = .invalidInput := by
  have hinv := encodePlan_inv plan seccompBytes
  have h' : Internal.encodePlan plan seccompBytes = .error e := h
  rw [h'] at hinv
  exact hinv.1

/-- `encodePlan` never fails with `.unavailable`. -/
theorem raw_encodePlan_never_unavailable (plan : CompiledSandboxPlan) (seccompBytes : ByteArray) :
    Core.NeverErrorKindPure SandboxError.kind .unavailable (LeanSwe.ProcessSandbox.Raw.encodePlan plan seccompBytes) := by
  cases h : LeanSwe.ProcessSandbox.Raw.encodePlan plan seccompBytes with
  | ok _ => trivial
  | error e =>
    dsimp only [Core.NeverErrorKindPure]
    rw [encodePlan_err_kind plan seccompBytes e h]; decide

/-- `encodePlan` never fails with `.notFound`. -/
theorem raw_encodePlan_never_notFound (plan : CompiledSandboxPlan) (seccompBytes : ByteArray) :
    Core.NeverErrorKindPure SandboxError.kind .notFound (LeanSwe.ProcessSandbox.Raw.encodePlan plan seccompBytes) := by
  cases h : LeanSwe.ProcessSandbox.Raw.encodePlan plan seccompBytes with
  | ok _ => trivial
  | error e =>
    dsimp only [Core.NeverErrorKindPure]
    rw [encodePlan_err_kind plan seccompBytes e h]; decide

/-- `encodePlan` never fails with `.permissionDenied`. -/
theorem raw_encodePlan_never_permissionDenied (plan : CompiledSandboxPlan) (seccompBytes : ByteArray) :
    Core.NeverErrorKindPure SandboxError.kind .permissionDenied (LeanSwe.ProcessSandbox.Raw.encodePlan plan seccompBytes) := by
  cases h : LeanSwe.ProcessSandbox.Raw.encodePlan plan seccompBytes with
  | ok _ => trivial
  | error e =>
    dsimp only [Core.NeverErrorKindPure]
    rw [encodePlan_err_kind plan seccompBytes e h]; decide

/-- `encodePlan` never fails with `.ioError`. -/
theorem raw_encodePlan_never_ioError (plan : CompiledSandboxPlan) (seccompBytes : ByteArray) :
    Core.NeverErrorKindPure SandboxError.kind .ioError (LeanSwe.ProcessSandbox.Raw.encodePlan plan seccompBytes) := by
  cases h : LeanSwe.ProcessSandbox.Raw.encodePlan plan seccompBytes with
  | ok _ => trivial
  | error e =>
    dsimp only [Core.NeverErrorKindPure]
    rw [encodePlan_err_kind plan seccompBytes e h]; decide

private theorem hostSeccompArch_never_kind (forbidden : SandboxErrorKind)
    (hne : SandboxErrorKind.unavailable ≠ forbidden) (w : Void IO.RealWorld) :
    Core.NeverErrorKindIO SandboxError.kind forbidden LeanSwe.ProcessSandbox.Raw.hostSeccompArch w := by
  have hRun : LeanSwe.ProcessSandbox.Raw.hostSeccompArch w =
      .ok (Internal.decodeHostAuditArch (SysBridge.Bwrap.detectHostAuditArch
        Model.hostPlatformIsLinux Model.hostPlatformTarget)) w := rfl
  unfold Core.NeverErrorKindIO
  rw [hRun]
  cases h : Internal.decodeHostAuditArch (SysBridge.Bwrap.detectHostAuditArch
      Model.hostPlatformIsLinux Model.hostPlatformTarget) with
  | ok _ => trivial
  | error e =>
    dsimp only
    have hk := decodeHostAuditArch_err_kind _ e h
    rw [hk]; exact hne

/-- `hostSeccompArch` never fails with `.invalidInput`. -/
theorem raw_hostSeccompArch_never_invalidInput (w : Void IO.RealWorld) :
    Core.NeverErrorKindIO SandboxError.kind .invalidInput LeanSwe.ProcessSandbox.Raw.hostSeccompArch w :=
  hostSeccompArch_never_kind .invalidInput (by decide) w

/-- `hostSeccompArch` never fails with `.notFound`. -/
theorem raw_hostSeccompArch_never_notFound (w : Void IO.RealWorld) :
    Core.NeverErrorKindIO SandboxError.kind .notFound LeanSwe.ProcessSandbox.Raw.hostSeccompArch w :=
  hostSeccompArch_never_kind .notFound (by decide) w

/-- `hostSeccompArch` never fails with `.permissionDenied`. -/
theorem raw_hostSeccompArch_never_permissionDenied (w : Void IO.RealWorld) :
    Core.NeverErrorKindIO SandboxError.kind .permissionDenied LeanSwe.ProcessSandbox.Raw.hostSeccompArch w :=
  hostSeccompArch_never_kind .permissionDenied (by decide) w

/-- `hostSeccompArch` never fails with `.ioError`. -/
theorem raw_hostSeccompArch_never_ioError (w : Void IO.RealWorld) :
    Core.NeverErrorKindIO SandboxError.kind .ioError LeanSwe.ProcessSandbox.Raw.hostSeccompArch w :=
  hostSeccompArch_never_kind .ioError (by decide) w

end LeanSwe.ProcessSandbox.Raw.Proofs
