import LeanSwe.ProcessSandbox.Raw.Types

namespace LeanSwe.ProcessSandbox.Raw.Model.Internal

open LeanSwe.ProcessSandbox.Raw

/-- Convert a `SandboxRawError` into a `SandboxError` with a non-empty diagnostic message. -/
def mapRawError : SandboxRawError → SandboxError
  | .unavailable errno? detail =>
    { kind := .unavailable, path := none, errnoCode := errno?,
      message := if detail.isEmpty then "sandbox unavailable" else detail }
  | .notFound p errno detail =>
    { kind := .notFound, path := some p, errnoCode := some errno,
      message := if detail.isEmpty then s!"not found: {p}" else detail }
  | .permissionDenied p? errno detail =>
    { kind := .permissionDenied, path := p?, errnoCode := some errno,
      message := if detail.isEmpty then "permission denied" else detail }
  | .invalidArgument p? errno? detail =>
    { kind := .invalidInput, path := p?, errnoCode := errno?,
      message := if detail.isEmpty then "invalid sandbox argument" else detail }
  | .ioError p? errno detail =>
    { kind := .ioError, path := p?, errnoCode := some errno,
      message := if detail.isEmpty then s!"sandbox I/O error {errno}" else detail }
  | .userError detail =>
    { kind := .ioError, path := none, errnoCode := none,
      message := if detail.isEmpty then "sandbox error" else detail }

/-- Compute a strictly greater positive handle ID above every `UInt32` currently in `xs`. -/
def freshU32 (xs : List UInt32) : Nat :=
  (xs.foldl (fun m x => max m x.toNat) 0) + 1

/-- Return `true` iff `id` is a valid sandbox handle ID present in `xs`. -/
def hasHandle (xs : List UInt32) (id : Nat) : Bool :=
  isValidSandboxHandleId id && xs.any (fun x => x.toNat == id)

/-- Pure `StateM` model state for verifying `RawProcessSandboxOpsM` lifecycle contracts. -/
structure MockRawState where
  /-- Whether `preflight` succeeds (`true`) or fails closed (`false`). -/
  preflightOk : Bool := true
  /-- Currently open sealed plan handle IDs (`< UInt32.size`). -/
  plans : List UInt32 := []
  /-- Currently active spawned box handle IDs (`< UInt32.size`). -/
  boxes : List UInt32 := []
  /-- Currently active port-forwarder handle IDs (`< UInt32.size`). -/
  fwds : List UInt32 := []
  deriving Repr, BEq, DecidableEq, Inhabited

/-- Pure `StateM MockRawState` implementation of `RawProcessSandboxOpsM` with fresh bounded handle allocation. -/
def mockRawOps : RawProcessSandboxOpsM (StateM MockRawState) :=
  { mapRawError := mapRawError
    decodeHostAuditArch := fun raw =>
      match LeanSwe.ProcessSandbox.Model.seccompArchOfAudit? raw with
      | some arch => .ok arch
      | none => .error (mapRawError (.unavailable none "unsupported host architecture for seccomp"))
    encodePlan := fun _ seccompBytes =>
      if seccompBytes.size == 0 || seccompBytes.size % 8 != 0 ||
          seccompBytes.size > 8 * SECCOMP_MAX_INSNS then
        .error (mapRawError (.invalidArgument none none "compiled seccomp filter must contain 1..160 8-byte instructions"))
      else
        let n := seccompBytes.size / 8
        let hdr := "LSWP0002".toUTF8 ++ ByteArray.mk #[
          UInt8.ofNat (n % 256),
          UInt8.ofNat ((n / 256) % 256),
          UInt8.ofNat ((n / 65536) % 256),
          UInt8.ofNat ((n / 16777216) % 256)]
        .ok (hdr ++ seccompBytes)
    hostSeccompArch := fun s =>
      if s.preflightOk then (.ok .x86_64, s)
      else (.error (mapRawError (.unavailable none "sandbox unavailable")), s)
    preflight := fun _ s =>
      if s.preflightOk then (.ok (), s)
      else (.error (mapRawError (.unavailable none "sandbox unavailable")), s)
    discoverHostPreset := fun s => (.ok {}, s)
    sealPlan := fun _ _ s =>
      let fresh := freshU32 s.plans
      if fresh < UInt32.size then
        (.ok { handleId := fresh }, { s with plans := UInt32.ofNat fresh :: s.plans })
      else
        (.error (mapRawError (.ioError none 12 "plan handle table exhausted")), s)
    closePlan := fun ph s =>
      if hasHandle s.plans ph.handleId then
        (.ok (), { s with plans := s.plans.erase (UInt32.ofNat ph.handleId) })
      else
        (.error (mapRawError (.invalidArgument none none "invalid plan handle")), s)
    spawnBox := fun ph s =>
      if hasHandle s.plans ph.handleId then
        let fresh := freshU32 s.boxes
        if fresh < UInt32.size then
          (.ok { handleId := fresh, pid := 100, pgid := 100, pidfd := 4 },
            { s with boxes := UInt32.ofNat fresh :: s.boxes })
        else
          (.error (mapRawError (.ioError none 12 "box handle table exhausted")), s)
      else
        (.error (mapRawError (.invalidArgument none none "invalid plan handle")), s)
    startPortForwarders := fun bh _ s =>
      if hasHandle s.boxes bh.handleId then
        let fresh := freshU32 s.fwds
        if fresh < UInt32.size then
          (.ok { handleId := fresh, boxHandleId := bh.handleId },
            { s with fwds := UInt32.ofNat fresh :: s.fwds })
        else
          (.error (mapRawError (.ioError none 12 "forwarder handle table exhausted")), s)
      else
        (.error (mapRawError (.invalidArgument none none "invalid box handle")), s)
    stopPortForwarders := fun fh s =>
      if hasHandle s.fwds fh.handleId then
        (.ok (), { s with fwds := s.fwds.erase (UInt32.ofNat fh.handleId) })
      else
        (.error (mapRawError (.invalidArgument none none "invalid forwarder handle")), s)
    readBoxOutput := fun bh _ _ _ s =>
      if hasHandle s.boxes bh.handleId then
        (.ok { outcome := .exited 0, stdout := ByteArray.empty, stderr := ByteArray.empty }, s)
      else
        (.error (mapRawError (.invalidArgument none none "invalid box handle")), s)
    killProcessGroup := fun bh s =>
      if hasHandle s.boxes bh.handleId then (.ok (), s)
      else (.error (mapRawError (.invalidArgument none none "invalid box handle")), s)
    pidfdKill := fun bh s =>
      if hasHandle s.boxes bh.handleId then (.ok (), s)
      else (.error (mapRawError (.invalidArgument none none "invalid box handle")), s)
    reapBox := fun bh s =>
      if hasHandle s.boxes bh.handleId then
        (.ok (), { s with boxes := s.boxes.erase (UInt32.ofNat bh.handleId) })
      else
        (.error (mapRawError (.invalidArgument none none "invalid box handle")), s)
    activeResourceCounts := fun s =>
      ({ openPlans := s.plans.length, activeBoxes := s.boxes.length, activeForwarders := s.fwds.length }, s) }

end LeanSwe.ProcessSandbox.Raw.Model.Internal
