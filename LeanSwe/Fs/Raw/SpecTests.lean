import Core.NondetTest
import LeanSwe.Fs.Raw.Types

namespace LeanSwe.Fs.Raw

open Core (NondetTest)
open Core.NondetTest

/-- Every error returned by `ops.mapRawError` carries a non-empty diagnostic message. -/
def test_fsraw_mapRawError_returnsNonEmptyMessage
    {runner} [NondetTest runner] (ops : RawFsOps) : runner Unit := do
  let raw ← nondet FsRawError
  let err := ops.mapRawError raw
  assert (err.message ≠ "")

/-- Mapping a `.wouldBlock` raw error preserves `.wouldBlock` kind, path, errno, and non-empty message. -/
def test_fsraw_mapRawError_wouldBlock
    {runner} [NondetTest runner] (ops : RawFsOps) : runner Unit := do
  let path? ← nondet (Option String)
  let errno ← nondet UInt32
  let detail ← nondet String
  let err := ops.mapRawError (.wouldBlock path? errno detail)
  assert (err.kind = .wouldBlock ∧ err.path = path? ∧ err.errnoCode = some errno ∧ err.message ≠ "")

private def buggyEmptyErrRaw (base : RawFsOps) : RawFsOps :=
  { base with mapRawError := fun _ => { kind := .ioError, message := "" } }

private def buggyWouldBlockToInvalidRaw (base : RawFsOps) : RawFsOps :=
  { base with
    mapRawError := fun
      | .wouldBlock path? errno _ =>
        { kind := .invalidInput, path := path?, errnoCode := some errno, message := "invalid" }
      | other => base.mapRawError other }

private def stubRawOps : RawFsOps :=
  { mapRawError := fun _ => { kind := .ioError, message := "stub" }
    stat := fun _ _ => pure (.error { kind := .notFound, message := "stub" })
    readDir := fun _ => pure (.ok #[])
    createDir := fun _ => pure (.ok ())
    removeDir := fun _ => pure (.ok ())
    unlinkFile := fun _ => pure (.ok ())
    readBytes := fun _ => pure (.ok ByteArray.empty)
    writeBytes := fun _ _ => pure (.ok ())
    appendText := fun _ _ => pure (.ok ())
    rename := fun _ _ => pure (.ok ())
    chmod := fun _ _ => pure (.ok ())
    symlink := fun _ _ => pure (.ok ())
    readLink := fun _ => pure (.error { kind := .notFound, message := "stub" })
    realPath := fun _ => pure (.error { kind := .notFound, message := "stub" })
    cwd := pure (.ok "/")
    monotonicNonce := pure 0
    acquireLock := fun path mode _ _ => pure (.ok { handleId := 1, path := path, mode := mode })
    releaseLock := fun _ => pure (.ok ()) }

example : ¬ Core.AllPass (test_fsraw_mapRawError_returnsNonEmptyMessage (buggyEmptyErrRaw stubRawOps)) := by
  intro h
  have h0 := h (.userError "boom")
  simp [buggyEmptyErrRaw, assert] at h0

example : ¬ Core.AllPass (test_fsraw_mapRawError_wouldBlock (buggyWouldBlockToInvalidRaw stubRawOps)) := by
  intro h
  have h0 := h (some "/tmp/a.lock") 11 "Resource temporarily unavailable"
  simp [buggyWouldBlockToInvalidRaw, assert] at h0

end LeanSwe.Fs.Raw
