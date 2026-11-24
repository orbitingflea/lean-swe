import LeanSwe.ProcessSandbox.Raw.Types
import LeanSwe.ProcessSandbox.Raw.Model

namespace LeanSwe.ProcessSandbox.Raw.Internal

open LeanSwe.ProcessSandbox.Raw
  (SeccompArch SockFilter SECCOMP_MAX_INSNS
   SandboxErrorKind SandboxError SandboxRawError SandboxMount PortForward
   SandboxLimits PreflightReq PresetSystemEntry HostRuntimePreset
   CompiledSandboxPlan isValidSandboxHandleId PlanHandle BoxHandle
   PortForwarderHandle SandboxResourceCounts SandboxOutcome SandboxResult
   RawProcessSandboxOps)

/-- FFI hooks injected by `LeanSwe.ProcessSandbox.Raw.Interface`. -/
structure PosixRawOps where
  /-- Return the host's native `AUDIT_ARCH_*` constant (`0` on unsupported platforms). -/
  hostArch : IO UInt32
  /-- Probe Linux, `bwrap`, Landlock ABI >= 4, `seccomp`, namespaces, and direct `cgroup v2`. -/
  preflight : Bool → Bool → IO (UInt8 × UInt32 × String × String)
  /-- Discover system runtime preset entries, `/etc` paths, and nested `$HOME` directories. -/
  discoverPreset : IO (UInt8 × UInt32 × String × Array (UInt8 × String × String) × Array String × Array String)
  /-- Create and seal `memfd` descriptors from serialized `LSWP0002` bytes. -/
  sealPlan : ByteArray → IO (UInt8 × UInt32 × String × String × UInt64)
  /-- Close and release a sealed plan handle. -/
  closePlan : UInt64 → IO (UInt8 × UInt32 × String × String)
  /-- Spawn a sandbox box instance from a sealed plan handle. -/
  spawnBox : UInt64 → IO (UInt8 × UInt32 × String × String × UInt64 × UInt32 × UInt32 × UInt32)
  /-- Start the host non-blocking TCP forwarder thread for handed-off listener FDs. -/
  startForwarders : UInt64 → Array UInt16 → Array UInt16 → IO (UInt8 × UInt32 × String × String × UInt64)
  /-- Stop and free a running TCP forwarder handle. -/
  stopForwarders : UInt64 → IO (UInt8 × UInt32 × String × String)
  /-- Release the pre-`execvp` gate, stream `stdin`, and collect bounded `stdout`/`stderr`. -/
  readOutput : UInt64 → ByteArray → UInt64 → Bool → UInt64 → IO (UInt8 × UInt32 × String × String × UInt8 × UInt32 × ByteArray × ByteArray)
  /-- Send `SIGKILL` to the sandbox process group (`-pgid`). -/
  killPg : UInt64 → IO (UInt8 × UInt32 × String × String)
  /-- Send `SIGKILL` via Linux `pidfd_send_signal`. -/
  pidfdKill : UInt64 → IO (UInt8 × UInt32 × String × String)
  /-- Kill the cgroup, reap the sandbox process, remove the cgroup directory, and free `BoxHandle`. -/
  reapBox : UInt64 → IO (UInt8 × UInt32 × String × String)
  /-- Return active `(openPlans, activeBoxes, activeForwarders)` resource counts. -/
  activeCounts : IO (Nat × Nat × Nat)

/-- Clamp a `Nat` to `UInt64` without modulo wraparound. -/
def natToUInt64Sat (n : Nat) : UInt64 :=
  UInt64.ofNat (Nat.min n (UInt64.size - 1))

/-- Reuse canonical `Raw.Model.Internal.mapRawError` to normalize a pure `SandboxRawError` into a `SandboxError` with a non-empty message. -/
abbrev mapRawError : SandboxRawError → SandboxError :=
  LeanSwe.ProcessSandbox.Raw.Model.Internal.mapRawError

/-- Decode a structured FFI error tag and fields into a normalized `SandboxError`. -/
def decodeTupleError (tag : UInt8) (errnum : UInt32) (path detail : String) : SandboxError :=
  let optPath := if path.isEmpty then none else some path
  let optErrno := if errnum == 0 then none else some errnum
  match tag.toNat with
  | 1 => mapRawError (.unavailable optErrno detail)
  | 2 => mapRawError (.notFound path errnum detail)
  | 3 => mapRawError (.permissionDenied optPath errnum detail)
  | 4 => mapRawError (.invalidArgument optPath optErrno detail)
  | _ => mapRawError (.ioError optPath errnum detail)

/-- Convert an uncaught Lean `IO.Error` into `SandboxRawError`. -/
def ioErrorToRaw : IO.Error → SandboxRawError
  | .noFileOrDirectory p code detail => .notFound p code detail
  | .permissionDenied p? code detail => .permissionDenied p? code detail
  | .invalidArgument p? code detail => .invalidArgument p? (some code) detail
  | .otherError code detail => .ioError none code detail
  | .userError detail => .userError detail
  | .interrupted p code detail => .ioError (if p.isEmpty then none else some p) code detail
  | .timeExpired code detail => .ioError none code detail
  | .resourceExhausted p? code detail => .ioError p? code detail
  | .noSuchThing p? code detail => .notFound (p?.getD "") code detail
  | .alreadyExists p? code detail => .ioError p? code detail
  | .inappropriateType p? code detail => .ioError p? code detail
  | .unsupportedOperation code detail => .unavailable (some code) detail
  | .unsatisfiedConstraints code detail => .unavailable (some code) detail
  | .illegalOperation code detail => .ioError none code detail
  | .resourceBusy code detail => .ioError none code detail
  | .resourceVanished code detail => .ioError none code detail
  | .hardwareFault code detail => .ioError none code detail
  | .protocolError code detail => .ioError none code detail
  | .unexpectedEof => .userError "unexpected end of file"

/-- Execute an `IO` action and capture any thrown `IO.Error` into `Except SandboxError`. -/
def catchSandbox {α : Type} (act : IO (Except SandboxError α)) : IO (Except SandboxError α) := do
  try
    return (← act)
  catch err =>
    return .error (mapRawError (ioErrorToRaw err))

/-- Decode a raw Linux `AUDIT_ARCH_*` word into `SeccompArch`, failing closed with `.unavailable` on unsupported hosts. -/
def decodeHostAuditArch (raw : UInt32) : Except SandboxError SeccompArch :=
  match LeanSwe.ProcessSandbox.Model.seccompArchOfAudit? raw with
  | some arch => .ok arch
  | none => .error (mapRawError (.unavailable none "unsupported host architecture for seccomp"))

/-- Append a single byte to a `ByteArray`. -/
def pushU8 (ba : ByteArray) (v : UInt8) : ByteArray :=
  ba.push v

/-- Append a little-endian `UInt16` to a `ByteArray`. -/
def pushU16LE (ba : ByteArray) (v : UInt16) : ByteArray :=
  let n := v.toNat
  ba.push (UInt8.ofNat (n % 256))
    |>.push (UInt8.ofNat ((n / 256) % 256))

/-- Append a little-endian `UInt32` to a `ByteArray`. -/
def pushU32LE (ba : ByteArray) (v : UInt32) : ByteArray :=
  let n := v.toNat
  ba.push (UInt8.ofNat (n % 256))
    |>.push (UInt8.ofNat ((n / 256) % 256))
    |>.push (UInt8.ofNat ((n / 65536) % 256))
    |>.push (UInt8.ofNat ((n / 16777216) % 256))

/-- Append a little-endian `UInt64` to a `ByteArray`. -/
def pushU64LE (ba : ByteArray) (v : UInt64) : ByteArray :=
  let rec go (idx : Nat) (cur : UInt64) (acc : ByteArray) : ByteArray :=
    match idx with
    | 0 => acc
    | k + 1 =>
      let b := UInt8.ofNat (cur.toNat % 256)
      go k (cur >>> 8) (acc.push b)
  go 8 v ba

/-- Return `true` iff the UTF-8 encoding of `s` contains a NUL byte. -/
def hasNulByte (s : String) : Bool :=
  s.toUTF8.data.toList.contains 0

/-- Append a length-prefixed NUL-free UTF-8 string to a `ByteArray`. -/
def pushStr (ba : ByteArray) (s : String) : Except SandboxError ByteArray := do
  if hasNulByte s then
    .error (mapRawError (.invalidArgument none none "string contains NUL byte"))
  let utf := s.toUTF8
  if utf.size >= UInt32.size then
    .error (mapRawError (.invalidArgument none none "string exceeds 32-bit length"))
  let ba := pushU32LE ba (UInt32.ofNat utf.size)
  return ba ++ utf

/-- Encode a `Bool` as `1` or `0` (`UInt8`). -/
def boolU8 (b : Bool) : UInt8 :=
  if b then 1 else 0

/-- Serialize the body of a `CompiledSandboxPlan` before appending the `seccomp` filter trailer. -/
def encodePlanPrefix (plan : CompiledSandboxPlan) : Except SandboxError ByteArray :=
  let ba := "LSWP0002".toUTF8
  let ba := pushU8 ba (boolU8 plan.emptyRoot)
  let ba := pushU8 ba (boolU8 plan.unshareAllNamespaces)
  let ba := pushU8 ba (boolU8 plan.mountFreshProc)
  let ba := pushU8 ba (boolU8 plan.mountSafeDev)
  let ba := pushU8 ba (boolU8 plan.directCgroupV2Fs)
  let ba := pushU32LE ba (UInt32.ofNat (Nat.min plan.landlockMinAbi (UInt32.size - 1)))
  let ba := pushU8 ba (boolU8 plan.allowBoxLocalhost)
  let ba := pushU8 ba (boolU8 plan.blockUnixSocketAndSmc)
  let ba := pushU8 ba (boolU8 plan.allowAnonUnixSocketpair)
  let ba := pushU8 ba (boolU8 plan.clone3EnosysFallback)
  let ba := pushU8 ba (boolU8 plan.seccompStrictDenylist)
  let ba := pushU8 ba (boolU8 plan.noNewPrivs)
  let ba := pushU8 ba (boolU8 plan.rlimitCoreZero)
  let ba := pushU8 ba (boolU8 plan.subreaperAndPdeathsig)
  let ba := pushU8 ba (boolU8 plan.cleanEnv)
  let ba := pushU64LE ba (natToUInt64Sat plan.limits.timeoutMs)
  let ba := pushU8 ba (boolU8 plan.limits.memoryMaxBytes.isSome)
  let ba := pushU64LE ba (natToUInt64Sat (plan.limits.memoryMaxBytes.getD 0))
  let ba := pushU8 ba (boolU8 plan.limits.pidsMax.isSome)
  let ba := pushU64LE ba (natToUInt64Sat (plan.limits.pidsMax.getD 0))
  let ba := pushU8 ba (boolU8 plan.limits.fileSizeMaxBytes.isSome)
  let ba := pushU64LE ba (natToUInt64Sat (plan.limits.fileSizeMaxBytes.getD 0))
  let ba := pushU8 ba (boolU8 plan.limits.maxOutputBytes.isSome)
  let ba := pushU64LE ba (natToUInt64Sat (plan.limits.maxOutputBytes.getD 0))
  do
    let ba ← pushStr ba plan.program
    let ba ← pushStr ba plan.cwd
    let ba := pushU32LE ba (UInt32.ofNat plan.args.size)
    let ba ← forIn plan.args ba fun a ba => do
      let ba ← pushStr ba a
      pure (ForInStep.yield ba)
    let ba := pushU32LE ba (UInt32.ofNat plan.env.size)
    let ba ← forIn plan.env ba fun (k, v) ba => do
      let ba ← pushStr ba k
      let ba ← pushStr ba v
      pure (ForInStep.yield ba)
    let ba := pushU32LE ba (UInt32.ofNat plan.presetSystemEntries.size)
    let ba ← forIn plan.presetSystemEntries ba fun e ba => do
      match e with
      | .readOnlyDir p =>
        let ba := pushU8 ba 0
        let ba ← pushStr ba p
        pure (ForInStep.yield ba)
      | .topSymlink lp tgt =>
        let ba := pushU8 ba 1
        let ba ← pushStr ba lp
        let ba ← pushStr ba tgt
        pure (ForInStep.yield ba)
    let ba := pushU32LE ba (UInt32.ofNat plan.presetEtcPaths.size)
    let ba ← forIn plan.presetEtcPaths ba fun p ba => do
      let ba ← pushStr ba p
      pure (ForInStep.yield ba)
    let ba := pushU32LE ba (UInt32.ofNat plan.maskedPresetPaths.size)
    let ba ← forIn plan.maskedPresetPaths ba fun m ba => do
      let ba ← pushStr ba m
      pure (ForInStep.yield ba)
    let ba := pushU32LE ba (UInt32.ofNat plan.userMounts.size)
    let ba ← forIn plan.userMounts ba fun m ba => do
      match m with
      | .readOnly hp bp =>
        let ba := pushU8 ba 0
        let ba ← pushStr ba hp
        let ba ← pushStr ba bp
        pure (ForInStep.yield ba)
      | .readWrite hp bp =>
        let ba := pushU8 ba 1
        let ba ← pushStr ba hp
        let ba ← pushStr ba bp
        pure (ForInStep.yield ba)
      | .scratch bp =>
        let ba := pushU8 ba 2
        let ba ← pushStr ba bp
        pure (ForInStep.yield ba)
    let ba := pushU32LE ba (UInt32.ofNat plan.portForwards.size)
    forIn plan.portForwards ba fun pf ba =>
      pure (ForInStep.yield (pushU16LE (pushU16LE ba pf.boxPort) pf.hostPort))

/-- Serialize a `CompiledSandboxPlan` and `8 * n`-byte (`1 ≤ n ≤ 160`) `seccomp` filter into `LSWP0002` binary bytes after verifying mandatory sandbox invariants. -/
def encodePlan (plan : CompiledSandboxPlan) (seccompBytes : ByteArray) : Except SandboxError ByteArray :=
  if !plan.emptyRoot || !plan.unshareAllNamespaces || !plan.mountFreshProc || !plan.mountSafeDev ||
      !plan.directCgroupV2Fs || plan.landlockMinAbi < 4 || !plan.blockUnixSocketAndSmc ||
      !plan.allowAnonUnixSocketpair || !plan.clone3EnosysFallback || !plan.seccompStrictDenylist ||
      !plan.noNewPrivs || !plan.rlimitCoreZero || !plan.subreaperAndPdeathsig || !plan.cleanEnv then
    .error (mapRawError (.invalidArgument none none "compiled plan violates mandatory sandbox invariants"))
  else if plan.program.isEmpty || plan.cwd.isEmpty then
    .error (mapRawError (.invalidArgument none none "compiled plan requires non-empty program and cwd"))
  else if plan.limits.timeoutMs == 0 || plan.limits.memoryMaxBytes == some 0 || plan.limits.pidsMax == some 0 then
    .error (mapRawError (.invalidArgument none none "compiled plan has invalid zero limit"))
  else if plan.portForwards.any (fun pf => pf.boxPort == 0 || pf.hostPort == 0) then
    .error (mapRawError (.invalidArgument none none "compiled plan has zero port"))
  else if seccompBytes.size == 0 || seccompBytes.size % 8 != 0 || seccompBytes.size > 8 * SECCOMP_MAX_INSNS then
    .error (mapRawError (.invalidArgument none none "compiled seccomp filter must contain 1..160 8-byte instructions"))
  else do
    let ba ← encodePlanPrefix plan
    let ba := pushU32LE ba (UInt32.ofNat (seccompBytes.size / 8))
    return ba ++ seccompBytes

/-- Construct a concrete `RawProcessSandboxOps` bundle backed by injected POSIX FFI hooks. -/
def mkRawOps (posix : PosixRawOps) : RawProcessSandboxOps :=
  { mapRawError := mapRawError
    decodeHostAuditArch := decodeHostAuditArch
    encodePlan := encodePlan
    hostSeccompArch := catchSandbox do
      let raw ← posix.hostArch
      return decodeHostAuditArch raw
    preflight := fun req => catchSandbox do
      let (tag, errnum, _path, msg) ← posix.preflight req.needMemoryCgroup req.needPidsCgroup
      if tag == 0 then
        return .ok ()
      else
        return .error (mapRawError (.unavailable (if errnum == 0 then none else some errnum) msg))
    discoverHostPreset := catchSandbox do
      let (tag, errnum, msg, rawSys, etcPaths, homePaths) ← posix.discoverPreset
      if tag != 0 then
        return .error (decodeTupleError tag errnum "" msg)
      let sysEntries := rawSys.map fun (stag, p, tgt) =>
        if stag == 1 then PresetSystemEntry.topSymlink p tgt else PresetSystemEntry.readOnlyDir p
      return .ok
        { systemEntries := sysEntries
          etcPaths := etcPaths
          excludedHomePaths := homePaths }
    sealPlan := fun plan seccompBytes => catchSandbox do
      match encodePlan plan seccompBytes with
      | .error e => return .error e
      | .ok bytes =>
        let (tag, errnum, path, msg, hid) ← posix.sealPlan bytes
        if tag != 0 then
          return .error (decodeTupleError tag errnum path msg)
        let hidNat := hid.toNat
        if !isValidSandboxHandleId hidNat then
          return .error (mapRawError (.ioError none 22 "shim returned invalid plan handle id"))
        return .ok { handleId := hidNat }
    closePlan := fun ph => catchSandbox do
      if !isValidSandboxHandleId ph.handleId then
        return .error (mapRawError (.invalidArgument none none "invalid plan handle"))
      let (tag, errnum, path, msg) ← posix.closePlan (UInt64.ofNat ph.handleId)
      if tag != 0 then
        return .error (decodeTupleError tag errnum path msg)
      return .ok ()
    spawnBox := fun ph => catchSandbox do
      if !isValidSandboxHandleId ph.handleId then
        return .error (mapRawError (.invalidArgument none none "invalid plan handle"))
      let (tag, errnum, path, msg, hid, pid, pgid, pidfd) ← posix.spawnBox (UInt64.ofNat ph.handleId)
      if tag != 0 then
        return .error (decodeTupleError tag errnum path msg)
      let hidNat := hid.toNat
      if !isValidSandboxHandleId hidNat || pid == 0 || pgid == 0 then
        return .error (mapRawError (.unavailable none "shim returned invalid box handle"))
      return .ok
        { handleId := hidNat
          pid := Int.ofNat pid.toNat
          pgid := Int.ofNat pgid.toNat
          pidfd := Int.ofNat pidfd.toNat }
    startPortForwarders := fun bh fwds => catchSandbox do
      if !isValidSandboxHandleId bh.handleId then
        return .error (mapRawError (.invalidArgument none none "invalid box handle"))
      let bps := fwds.map (·.boxPort)
      let hps := fwds.map (·.hostPort)
      let (tag, errnum, path, msg, fhid) ← posix.startForwarders (UInt64.ofNat bh.handleId) bps hps
      if tag != 0 then
        return .error (decodeTupleError tag errnum path msg)
      let fhidNat := fhid.toNat
      if !isValidSandboxHandleId fhidNat then
        return .error (mapRawError (.ioError none 22 "shim returned invalid forwarder handle id"))
      return .ok { handleId := fhidNat, boxHandleId := bh.handleId }
    stopPortForwarders := fun fh => catchSandbox do
      if !isValidSandboxHandleId fh.handleId then
        return .error (mapRawError (.invalidArgument none none "invalid forwarder handle"))
      let (tag, errnum, path, msg) ← posix.stopForwarders (UInt64.ofNat fh.handleId)
      if tag != 0 then
        return .error (decodeTupleError tag errnum path msg)
      return .ok ()
    readBoxOutput := fun bh stdin timeoutMs maxOut? => catchSandbox do
      if !isValidSandboxHandleId bh.handleId then
        return .error (mapRawError (.invalidArgument none none "invalid box handle"))
      let toU64 := natToUInt64Sat (Nat.max 1 timeoutMs)
      let hasLimit := maxOut?.isSome
      let limU64 := natToUInt64Sat (maxOut?.getD 0)
      let (tag, errnum, path, msg, outTag, exitOrSig, outBytes, errBytes) ←
        posix.readOutput (UInt64.ofNat bh.handleId) stdin toU64 hasLimit limU64
      if tag != 0 then
        return .error (decodeTupleError tag errnum path msg)
      let outcome :=
        match outTag.toNat with
        | 0 => SandboxOutcome.exited (Int.ofNat exitOrSig.toNat)
        | 1 => SandboxOutcome.signaled (Int.ofNat exitOrSig.toNat)
        | 2 => SandboxOutcome.timedOut
        | _ => SandboxOutcome.outputLimitExceeded
      return .ok { outcome := outcome, stdout := outBytes, stderr := errBytes }
    killProcessGroup := fun bh => catchSandbox do
      if !isValidSandboxHandleId bh.handleId then
        return .error (mapRawError (.invalidArgument none none "invalid box handle"))
      let (tag, errnum, path, msg) ← posix.killPg (UInt64.ofNat bh.handleId)
      if tag != 0 then
        return .error (decodeTupleError tag errnum path msg)
      return .ok ()
    pidfdKill := fun bh => catchSandbox do
      if !isValidSandboxHandleId bh.handleId then
        return .error (mapRawError (.invalidArgument none none "invalid box handle"))
      let (tag, errnum, path, msg) ← posix.pidfdKill (UInt64.ofNat bh.handleId)
      if tag != 0 then
        return .error (decodeTupleError tag errnum path msg)
      return .ok ()
    reapBox := fun bh => catchSandbox do
      if !isValidSandboxHandleId bh.handleId then
        return .error (mapRawError (.invalidArgument none none "invalid box handle"))
      let (tag, errnum, path, msg) ← posix.reapBox (UInt64.ofNat bh.handleId)
      if tag != 0 then
        return .error (decodeTupleError tag errnum path msg)
      return .ok ()
    activeResourceCounts := do
      let (np, nb, nf) ← posix.activeCounts
      return { openPlans := np, activeBoxes := nb, activeForwarders := nf } }

end LeanSwe.ProcessSandbox.Raw.Internal
