import Core.Assumptions
import LeanSwe.ProcessSandbox.Interface
import LeanSwe.ProcessSandbox.Proofs.ApiHelpers

namespace LeanSwe.ProcessSandbox.Proofs

open Core
open LeanSwe.ProcessSandbox
open LeanSwe.ProcessSandbox.Raw

private theorem validateSpec_never_kind (forbidden : SandboxErrorKind)
    (hne : SandboxErrorKind.invalidInput ≠ forbidden) (spec : BoxSpec) :
    Core.NeverErrorKindPure SandboxError.kind forbidden
      (LeanSwe.ProcessSandbox.validateSpec spec) := by
  cases h : LeanSwe.ProcessSandbox.validateSpec spec with
  | ok _ => trivial
  | error e =>
    dsimp only [Core.NeverErrorKindPure]
    have hPure : Model.validateSpecPure spec = .error e := h
    rw [validateSpecPure_error_kind hPure]
    exact hne

/-- `ProcessSandbox.validateSpec` never fails with `.unavailable`. -/
theorem psandbox_validateSpec_never_unavailable (spec : BoxSpec) :
    Core.NeverErrorKindPure SandboxError.kind .unavailable
      (LeanSwe.ProcessSandbox.validateSpec spec) :=
  validateSpec_never_kind .unavailable (by decide) spec

/-- `ProcessSandbox.validateSpec` never fails with `.notFound`. -/
theorem psandbox_validateSpec_never_notFound (spec : BoxSpec) :
    Core.NeverErrorKindPure SandboxError.kind .notFound
      (LeanSwe.ProcessSandbox.validateSpec spec) :=
  validateSpec_never_kind .notFound (by decide) spec

/-- `ProcessSandbox.validateSpec` never fails with `.permissionDenied`. -/
theorem psandbox_validateSpec_never_permissionDenied (spec : BoxSpec) :
    Core.NeverErrorKindPure SandboxError.kind .permissionDenied
      (LeanSwe.ProcessSandbox.validateSpec spec) :=
  validateSpec_never_kind .permissionDenied (by decide) spec

/-- `ProcessSandbox.validateSpec` never fails with `.ioError`. -/
theorem psandbox_validateSpec_never_ioError (spec : BoxSpec) :
    Core.NeverErrorKindPure SandboxError.kind .ioError
      (LeanSwe.ProcessSandbox.validateSpec spec) :=
  validateSpec_never_kind .ioError (by decide) spec

end LeanSwe.ProcessSandbox.Proofs
