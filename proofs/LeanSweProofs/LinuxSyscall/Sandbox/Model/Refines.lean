import LeanSwe.LinuxSyscall.Sandbox.Types
import LeanSweProofs.LinuxSyscall.Sandbox.Model

/-!
Pure capability-refinement specification for `LeanSwe.LinuxSyscall.Sandbox` (`Core.ObeysStepFrom`),
relating thin `PosixSandboxOpsM` syscall hooks over `HealthyEnv` to `SandboxOpsM`.
-/

namespace LeanSwe.LinuxSyscall.Sandbox.Model

open LeanSwe.LinuxSyscall

/-- Monadic raw capability bundle specialized to `HandleId` for `Core.ObeysStepFrom`. -/
abbrev RawSandboxOpsM (m : Type → Type) := PosixSandboxOpsM m HandleId

/-- Monadic public `Sandbox` capability bundle specialized to `HandleId` for `Core.ObeysStepFrom`. -/
abbrev PkgSandboxOpsM (m : Type → Type) := SandboxOpsM m HandleId

/-- Single-step raw FFI request covering all 10 fields of `PosixSandboxOpsM`. -/
inductive RawStepReq where
  /-- `raw.landlockQuery flags`. -/
  | landlockQuery (flags : UInt32)
  /-- `raw.landlockCreate fs net`. -/
  | landlockCreate (handledAccessFs : UInt64) (handledAccessNet : UInt64)
  /-- `raw.landlockAddPathBeneath ruleset parentFd allowedAccess`. -/
  | landlockAddPathBeneath (ruleset : HandleId) (parentFd : HandleId) (allowedAccess : UInt64)
  /-- `raw.landlockAddNetPort ruleset port allowedAccess`. -/
  | landlockAddNetPort (ruleset : HandleId) (port : UInt64) (allowedAccess : UInt64)
  /-- `raw.landlockRestrictSelf ruleset`. -/
  | landlockRestrictSelf (ruleset : HandleId)
  /-- `raw.seccompGetActionAvail action`. -/
  | seccompGetActionAvail (action : UInt32)
  /-- `raw.seccompSetFilter flagsBits filterBytes`. -/
  | seccompSetFilter (flagsBits : UInt32) (filterBytes : ByteArray)
  /-- `raw.prctl cmdTag arg`. -/
  | prctl (cmdTag : UInt32) (arg : UInt32)
  /-- `raw.setrlimit resTag cur max`. -/
  | setrlimit (resTag : UInt32) (cur : UInt64) (max : UInt64)
  /-- `raw.memfdCreate name flagsBits`. -/
  | memfdCreate (name : ByteArray) (flagsBits : UInt32)
  deriving DecidableEq, BEq, Inhabited

/-- Decode raw `SeccompFlags.toBits` bitmasks (`0x37` mask), returning `none` on unknown bits. -/
def decodeSeccompFlags? (bits : UInt32) : Option SeccompFlags :=
  if (bits &&& ~~~(0x37 : UInt32)) != 0 then
    none
  else
    some
      { tsync := (bits &&& 1) != 0
        log := (bits &&& 2) != 0
        specAllow := (bits &&& 4) != 0
        tsyncEsrch := (bits &&& 16) != 0
        waitKillableRecv := (bits &&& 32) != 0 }

/-- Decode raw `(cmdTag, arg)` pairs accepted by `sandbox_shim.c` (`PrctlOp.toRaw`). -/
def decodePrctlOp? (cmdTag arg : UInt32) : Option PrctlOp :=
  if cmdTag == 0 then
    if arg == 1 then some .setNoNewPrivs else none
  else if cmdTag == 1 then
    if arg == 0 then some .getNoNewPrivs else none
  else if cmdTag == 2 then
    if arg == 1 then some (.setChildSubreaper true)
    else if arg == 0 then some (.setChildSubreaper false)
    else none
  else if cmdTag == 3 then
    some (.setPdeathsig arg)
  else
    none

/-- Decode raw `RlimitResource.toTag` selector tags (`0..2`) accepted by `sandbox_shim.c`. -/
def decodeRlimitResource? (resTag : UInt32) : Option RlimitResource :=
  if resTag == 0 then some .core
  else if resTag == 1 then some .fsize
  else if resTag == 2 then some .nofile
  else none

/-- Decode raw `MemfdFlags.toBits` bitmasks (`0x1B` mask), returning `none` on unknown bits. -/
def decodeMemfdFlags? (bits : UInt32) : Option MemfdFlags :=
  if (bits &&& ~~~(0x1B : UInt32)) != 0 then
    none
  else
    some
      { cloexec := (bits &&& 1) != 0
        allowSealing := (bits &&& 2) != 0
        noexecSeal := (bits &&& 8) != 0
        exec := (bits &&& 16) != 0 }

/-- Decode a `RawStepReq` into its logical `SandboxReq`, or `none` on out-of-range raw tags/bits. -/
def decodeRawStepReq? : RawStepReq → Option SandboxReq
  | .landlockQuery flags =>
    some (.landlockCreateRuleset none flags)
  | .landlockCreate fs net =>
    some (.landlockCreateRuleset (some { handledAccessFs := fs, handledAccessNet := net }) 0)
  | .landlockAddPathBeneath rs parentFd access =>
    some (.landlockAddRule rs (.pathBeneath parentFd access))
  | .landlockAddNetPort rs port access =>
    some (.landlockAddRule rs (.netPort port access))
  | .landlockRestrictSelf rs =>
    some (.landlockRestrictSelf rs)
  | .seccompGetActionAvail action =>
    some (.seccomp (.getActionAvail action) {} ByteArray.empty)
  | .seccompSetFilter flagsBits filterBytes =>
    match decodeSeccompFlags? flagsBits with
    | some flags => some (.seccomp .setModeFilter flags filterBytes)
    | none => none
  | .prctl cmdTag arg =>
    (decodePrctlOp? cmdTag arg).map .prctl
  | .setrlimit resTag cur max =>
    (decodeRlimitResource? resTag).map (fun res => .setrlimit res cur max)
  | .memfdCreate name flagsBits =>
    (decodeMemfdFlags? flagsBits).map (fun flags => .memfdCreate name flags)

/-- Well-formedness guard on `HealthyEnv` for `Core.ObeysStepFrom`. -/
def rawStepWf (env : HealthyEnv) : Bool :=
  env.wf

/-- Execute one `RawStepReq` against `raw : RawSandboxOpsM (StateM W)` and normalize to `SandboxOutcome`. -/
def execRawStep {W : Type} (raw : RawSandboxOpsM (StateM W)) :
    RawStepReq → StateM W SandboxOutcome
  | .landlockQuery flags => do
    match ← raw.landlockQuery flags with
    | .ok v => return .landlockVersion v
    | .error e => return .err e
  | .landlockCreate fs net => do
    match ← raw.landlockCreate fs net with
    | .ok hid => return .opened hid
    | .error e => return .err e
  | .landlockAddPathBeneath rs parentFd access => do
    match ← raw.landlockAddPathBeneath rs parentFd access with
    | .ok () => return .unit
    | .error e => return .err e
  | .landlockAddNetPort rs port access => do
    match ← raw.landlockAddNetPort rs port access with
    | .ok () => return .unit
    | .error e => return .err e
  | .landlockRestrictSelf rs => do
    match ← raw.landlockRestrictSelf rs with
    | .ok () => return .unit
    | .error e => return .err e
  | .seccompGetActionAvail action => do
    match ← raw.seccompGetActionAvail action with
    | .ok v => return .u32 v
    | .error e => return .err e
  | .seccompSetFilter flagsBits filterBytes => do
    match ← raw.seccompSetFilter flagsBits filterBytes with
    | .ok v => return .u32 v
    | .error e => return .err e
  | .prctl cmdTag arg => do
    match ← raw.prctl cmdTag arg with
    | .ok v => return .u32 v
    | .error e => return .err e
  | .setrlimit resTag cur max => do
    match ← raw.setrlimit resTag cur max with
    | .ok () => return .unit
    | .error e => return .err e
  | .memfdCreate name flagsBits => do
    match ← raw.memfdCreate name flagsBits with
    | .ok hid => return .opened hid
    | .error e => return .err e

/-- Allowed healthy-host transition for a single raw `PosixSandboxOpsM` call:
    out-of-range raw tags or flag bits reject with `Errno.EINVAL`, and valid raw requests
    transition according to `healthyStep`. -/
def allowedRawStep (env : HealthyEnv) (req : RawStepReq) (out : SandboxOutcome)
    (env' : HealthyEnv) : Prop :=
  match decodeRawStepReq? req with
  | none => env.wf = true ∧ env' = env ∧ out = .err Errno.EINVAL
  | some pkgReq => healthyStep env pkgReq out = some env'

/-- Execute one `SandboxReq` against `ops : PkgSandboxOpsM (StateM W)`. -/
def execPkgStep {W : Type} (ops : PkgSandboxOpsM (StateM W))
    (req : SandboxReq) : StateM W SandboxOutcome :=
  execSandboxReq ops req

/-- Allowed healthy-host transition for a public `SandboxOpsM` operation. -/
def allowedPkgStep (env : HealthyEnv) (req : SandboxReq) (out : SandboxOutcome)
    (env' : HealthyEnv) : Prop :=
  healthyStep env req out = some env'

/-- Executable reference `RawSandboxOpsM (StateM HealthyEnv)` lifting `healthyModelOps`. -/
def modelRawOps : RawSandboxOpsM (StateM HealthyEnv) :=
  { landlockQuery := fun flags => do
      match ← healthyModelOps.landlockCreateRuleset none flags with
      | .ok (.version v) => return .ok v
      | .ok (.ruleset _) => return .error Errno.EINVAL
      | .error e => return .error e
    landlockCreate := fun fs net => do
      match ← healthyModelOps.landlockCreateRuleset
          (some { handledAccessFs := fs, handledAccessNet := net }) 0 with
      | .ok (.ruleset hid) => return .ok hid
      | .ok (.version _) => return .error Errno.EINVAL
      | .error e => return .error e
    landlockAddPathBeneath := fun rs parentFd access =>
      healthyModelOps.landlockAddRule rs (.pathBeneath parentFd access)
    landlockAddNetPort := fun rs port access =>
      healthyModelOps.landlockAddRule rs (.netPort port access)
    landlockRestrictSelf := healthyModelOps.landlockRestrictSelf
    seccompGetActionAvail := fun action =>
      healthyModelOps.seccomp (.getActionAvail action) {} ByteArray.empty
    seccompSetFilter := fun flagsBits filterBytes => do
      match decodeSeccompFlags? flagsBits with
      | none => return .error Errno.EINVAL
      | some flags => healthyModelOps.seccomp .setModeFilter flags filterBytes
    prctl := fun cmdTag arg => do
      match decodePrctlOp? cmdTag arg with
      | none => return .error Errno.EINVAL
      | some op => healthyModelOps.prctl op
    setrlimit := fun resTag cur max => do
      match decodeRlimitResource? resTag with
      | none => return .error Errno.EINVAL
      | some res => healthyModelOps.setrlimit res cur max
    memfdCreate := fun name flagsBits => do
      match decodeMemfdFlags? flagsBits with
      | none => return .error Errno.EINVAL
      | some flags => healthyModelOps.memfdCreate name flags }

end LeanSwe.LinuxSyscall.Sandbox.Model
