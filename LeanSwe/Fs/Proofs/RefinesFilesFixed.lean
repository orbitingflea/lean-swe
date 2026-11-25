import LeanSwe.Fs.Proofs.HealthyFilesBase

namespace LeanSwe.Fs.Proofs

open LeanSwe.LinuxSyscall
open LeanSwe.LinuxSyscall.Files
open LeanSwe.Fs
open LeanSwe.Fs.Model

/-- Convert `Except Errno fd` into `FilesOutcome` via descriptor projection `hidOf`. -/
def outcomeOfOpenedFd {fd : Type} (hidOf : fd → HandleId) : Except Errno fd → FilesOutcome
  | .ok h => .opened (hidOf h)
  | .error e => .err e

/-- Parametric step-refinement invariant for `FilesOpsM (StateM W) fd` paired with a nonce source `nextNonce`. -/
structure RefinesFsFilesFixed {W fd : Type}
    (proj : W → FsWorld) (hidOf : fd → HandleId)
    (files : FilesOpsM (StateM W) fd) (nextNonce : StateM W Nat) : Prop where
  /-- Every `RawFilesReq fd` transitions `FsWorld.env` via `healthyStep` and preserves `tempSeq`. -/
  file_step : ∀ {s : W} (req : RawFilesReq fd), fsWorldWf (proj s) = true →
    let p := (execRawFilesReq files req).run s
    fsWorldWf (proj p.2) = true ∧
    healthyStep (proj s).env (req.toFilesReq hidOf) (p.1.toFilesOutcome hidOf) = some (proj p.2).env ∧
    (proj p.2).tempSeq = (proj s).tempSeq
  /-- Every `nextNonce` step preserves `FsWorld.env` and is monotonic in `tempSeq`. -/
  nonce_step : ∀ {s : W}, fsWorldWf (proj s) = true →
    let p := nextNonce.run s
    fsWorldWf (proj p.2) = true ∧
    (proj p.2).env = (proj s).env ∧
    (proj s).tempSeq ≤ (proj p.2).tempSeq

/-- Generic helper unpacking one `FilesOpsM` method call from `RefinesFsFilesFixed`. -/
theorem cap_method_step {W fd α : Type} {proj : W → FsWorld} {hidOf : fd → HandleId}
    {files : FilesOpsM (StateM W) fd} {nextNonce : StateM W Nat}
    (hCap : RefinesFsFilesFixed proj hidOf files nextNonce)
    (req : RawFilesReq fd) (act : StateM W (Except Errno α))
    (rawOut : Except Errno α → RawFilesOut fd) (toOut : Except Errno α → FilesOutcome)
    (hExec : execRawFilesReq files req = rawOut <$> act)
    (hOut : ∀ r, (rawOut r).toFilesOutcome hidOf = toOut r)
    {s : W} (hWf : fsWorldWf (proj s) = true) :
    let p := act.run s
    fsWorldWf (proj p.2) = true ∧
    healthyStep (proj s).env (req.toFilesReq hidOf) (toOut p.1) = some (proj p.2).env ∧
    (proj p.2).tempSeq = (proj s).tempSeq := by
  have h := hCap.file_step req hWf
  have hRun : (execRawFilesReq files req).run s = (rawOut (act.run s).1, (act.run s).2) := by
    rw [hExec]
    change (match act.run s with | (x, s') => (rawOut x, s')) = (rawOut (act.run s).1, (act.run s).2)
    cases act.run s
    rfl
  dsimp only at h ⊢
  rw [hRun, hOut] at h
  exact h

/-- Unpack a `Unit`-returning `FilesOpsM` method call from `RefinesFsFilesFixed`. -/
theorem cap_unit_step {W fd : Type} {proj : W → FsWorld} {hidOf : fd → HandleId}
    {files : FilesOpsM (StateM W) fd} {nextNonce : StateM W Nat}
    (hCap : RefinesFsFilesFixed proj hidOf files nextNonce)
    (req : RawFilesReq fd) (act : StateM W (Except Errno Unit))
    (hExec : execRawFilesReq files req = rawOutcomeOfUnit <$> act)
    {s : W} (hWf : fsWorldWf (proj s) = true) :
    let p := act.run s
    fsWorldWf (proj p.2) = true ∧
    healthyStep (proj s).env (req.toFilesReq hidOf) (outcomeOfUnit p.1) = some (proj p.2).env ∧
    (proj p.2).tempSeq = (proj s).tempSeq :=
  cap_method_step hCap req act rawOutcomeOfUnit outcomeOfUnit hExec
    (fun r => by cases r with | ok u => cases u; rfl | error _ => rfl) hWf

/-- Unpack an `fd`-opening `FilesOpsM` method call from `RefinesFsFilesFixed`. -/
theorem cap_opened_step {W fd : Type} {proj : W → FsWorld} {hidOf : fd → HandleId}
    {files : FilesOpsM (StateM W) fd} {nextNonce : StateM W Nat}
    (hCap : RefinesFsFilesFixed proj hidOf files nextNonce)
    (req : RawFilesReq fd) (act : StateM W (Except Errno fd))
    (hExec : execRawFilesReq files req = rawOutcomeOfOpened <$> act)
    {s : W} (hWf : fsWorldWf (proj s) = true) :
    let p := act.run s
    fsWorldWf (proj p.2) = true ∧
    healthyStep (proj s).env (req.toFilesReq hidOf) (outcomeOfOpenedFd hidOf p.1) = some (proj p.2).env ∧
    (proj p.2).tempSeq = (proj s).tempSeq :=
  cap_method_step hCap req act rawOutcomeOfOpened (outcomeOfOpenedFd hidOf) hExec
    (fun r => by cases r <;> rfl) hWf

/-- Unpack a `ByteArray`-returning `FilesOpsM` method call from `RefinesFsFilesFixed`. -/
theorem cap_bytes_step {W fd : Type} {proj : W → FsWorld} {hidOf : fd → HandleId}
    {files : FilesOpsM (StateM W) fd} {nextNonce : StateM W Nat}
    (hCap : RefinesFsFilesFixed proj hidOf files nextNonce)
    (req : RawFilesReq fd) (act : StateM W (Except Errno ByteArray))
    (hExec : execRawFilesReq files req = rawOutcomeOfBytes <$> act)
    {s : W} (hWf : fsWorldWf (proj s) = true) :
    let p := act.run s
    fsWorldWf (proj p.2) = true ∧
    healthyStep (proj s).env (req.toFilesReq hidOf) (outcomeOfBytes p.1) = some (proj p.2).env ∧
    (proj p.2).tempSeq = (proj s).tempSeq :=
  cap_method_step hCap req act rawOutcomeOfBytes outcomeOfBytes hExec
    (fun r => by cases r <;> rfl) hWf

/-- Unpack a `UInt32`-returning `FilesOpsM` method call from `RefinesFsFilesFixed`. -/
theorem cap_u32_step {W fd : Type} {proj : W → FsWorld} {hidOf : fd → HandleId}
    {files : FilesOpsM (StateM W) fd} {nextNonce : StateM W Nat}
    (hCap : RefinesFsFilesFixed proj hidOf files nextNonce)
    (req : RawFilesReq fd) (act : StateM W (Except Errno UInt32))
    (hExec : execRawFilesReq files req = rawOutcomeOfU32 <$> act)
    {s : W} (hWf : fsWorldWf (proj s) = true) :
    let p := act.run s
    fsWorldWf (proj p.2) = true ∧
    healthyStep (proj s).env (req.toFilesReq hidOf) (outcomeOfU32 p.1) = some (proj p.2).env ∧
    (proj p.2).tempSeq = (proj s).tempSeq :=
  cap_method_step hCap req act rawOutcomeOfU32 outcomeOfU32 hExec
    (fun r => by cases r <;> rfl) hWf

/-- Unpack a `UInt64`-returning `FilesOpsM` method call from `RefinesFsFilesFixed`. -/
theorem cap_u64_step {W fd : Type} {proj : W → FsWorld} {hidOf : fd → HandleId}
    {files : FilesOpsM (StateM W) fd} {nextNonce : StateM W Nat}
    (hCap : RefinesFsFilesFixed proj hidOf files nextNonce)
    (req : RawFilesReq fd) (act : StateM W (Except Errno UInt64))
    (hExec : execRawFilesReq files req = rawOutcomeOfU64 <$> act)
    {s : W} (hWf : fsWorldWf (proj s) = true) :
    let p := act.run s
    fsWorldWf (proj p.2) = true ∧
    healthyStep (proj s).env (req.toFilesReq hidOf) (outcomeOfU64 p.1) = some (proj p.2).env ∧
    (proj p.2).tempSeq = (proj s).tempSeq :=
  cap_method_step hCap req act rawOutcomeOfU64 outcomeOfU64 hExec
    (fun r => by cases r <;> rfl) hWf

/-- Unpack a `StatInfo`-returning `FilesOpsM` method call from `RefinesFsFilesFixed`. -/
theorem cap_statted_step {W fd : Type} {proj : W → FsWorld} {hidOf : fd → HandleId}
    {files : FilesOpsM (StateM W) fd} {nextNonce : StateM W Nat}
    (hCap : RefinesFsFilesFixed proj hidOf files nextNonce)
    (req : RawFilesReq fd) (act : StateM W (Except Errno StatInfo))
    (hExec : execRawFilesReq files req = rawOutcomeOfStatted <$> act)
    {s : W} (hWf : fsWorldWf (proj s) = true) :
    let p := act.run s
    fsWorldWf (proj p.2) = true ∧
    healthyStep (proj s).env (req.toFilesReq hidOf) (outcomeOfStatted p.1) = some (proj p.2).env ∧
    (proj p.2).tempSeq = (proj s).tempSeq :=
  cap_method_step hCap req act rawOutcomeOfStatted outcomeOfStatted hExec
    (fun r => by cases r <;> rfl) hWf

end LeanSwe.Fs.Proofs
