import Core.NondetTest
import LeanSwe.ProcessSandbox.Raw.Types

namespace LeanSwe.ProcessSandbox.Raw

open Core (NondetTest)
open Core.NondetTest

/-- `isValidSandboxHandleId` rejects `0` and values `≥ UInt64.size` while accepting positive 64-bit IDs. -/
def test_psandboxRaw_isValidSandboxHandleId_bounds
    {runner} [NondetTest runner]
    (checkId : Nat → Bool := isValidSandboxHandleId) : runner Unit := do
  let n ← nondet Nat
  NondetTest.assert (checkId 0 = false)
  NondetTest.assert (checkId UInt64.size = false)
  NondetTest.assert (checkId (UInt64.size + n) = false)
  assume (0 < n ∧ n < UInt64.size)
  NondetTest.assert (checkId n = true)

/-- Every error returned by `ops.mapRawError` carries a non-empty diagnostic message. -/
def test_psandboxRaw_mapRawError_returnsNonEmptyMessage
    {runner} [NondetTest runner] (ops : RawProcessSandboxOps) : runner Unit := do
  let raw ← nondet SandboxRawError
  let err := ops.mapRawError raw
  NondetTest.assert (err.message ≠ "")

/-- `ops.mapRawError` preserves the exact `SandboxErrorKind`, `path`, and `errnoCode` for every `SandboxRawError` variant. -/
def test_psandboxRaw_mapRawError_preservesKindAndFields
    {runner} [NondetTest runner] (ops : RawProcessSandboxOps) : runner Unit := do
  let raw ← nondet SandboxRawError
  let err := ops.mapRawError raw
  match raw with
  | .unavailable errno? _ =>
    NondetTest.assert (err.kind = .unavailable ∧ err.path = none ∧ err.errnoCode = errno?)
  | .notFound p errno _ =>
    NondetTest.assert (err.kind = .notFound ∧ err.path = some p ∧ err.errnoCode = some errno)
  | .permissionDenied p? errno _ =>
    NondetTest.assert (err.kind = .permissionDenied ∧ err.path = p? ∧ err.errnoCode = some errno)
  | .invalidArgument p? errno? _ =>
    NondetTest.assert (err.kind = .invalidInput ∧ err.path = p? ∧ err.errnoCode = errno?)
  | .ioError p? errno _ =>
    NondetTest.assert (err.kind = .ioError ∧ err.path = p? ∧ err.errnoCode = some errno)
  | .userError _ =>
    NondetTest.assert (err.kind = .ioError ∧ err.path = none ∧ err.errnoCode = none)

/-- `ops.decodeHostAuditArch` maps `0xc000003e` to `.ok .x86_64`, `0xc00000b7` to `.ok .aarch64`, and rejects every other `UInt32` fail-closed with `.unavailable` and a non-empty message. -/
def test_psandboxRaw_decodeHostAuditArch_exactConstantsAndFailClosed
    {runner} [NondetTest runner] (ops : RawProcessSandboxOps) : runner Unit := do
  NondetTest.assert (ops.decodeHostAuditArch 0xc000003e = .ok .x86_64)
  NondetTest.assert (ops.decodeHostAuditArch 0xc00000b7 = .ok .aarch64)
  let raw ← nondet UInt32
  assume (raw ≠ 0xc000003e ∧ raw ≠ 0xc00000b7)
  match ops.decodeHostAuditArch raw with
  | .ok _ => NondetTest.assert False
  | .error err => NondetTest.assert (err.kind = .unavailable ∧ err.message ≠ "")

/-- `ops.encodePlan` rejects empty, non-8-byte-aligned, or `> 160`-instruction `seccompBytes` with `.invalidInput`, succeeds on valid plans with `1..160` 8-byte instructions, and frames `.ok` outputs with `"LSWP0002"` header and trailing `u32LE (seccompBytes.size / 8) ++ seccompBytes`. -/
def test_psandboxRaw_encodePlan_validatesSeccompFilterAndFramesLswp0002
    {runner} [NondetTest runner] (ops : RawProcessSandboxOps) : runner Unit := do
  let planBad ← nondet CompiledSandboxPlan
  let badSeccomp ← nondet ByteArray
  assume (badSeccomp.size = 0 ∨ badSeccomp.size % 8 ≠ 0 ∨ badSeccomp.size > 8 * SECCOMP_MAX_INSNS)
  match ops.encodePlan planBad badSeccomp with
  | .ok _ => NondetTest.assert False
  | .error err => NondetTest.assert (err.kind = .invalidInput ∧ err.message ≠ "")
  let goodSeccomp ← nondet ByteArray
  assume (0 < goodSeccomp.size ∧ goodSeccomp.size % 8 = 0 ∧ goodSeccomp.size ≤ 8 * SECCOMP_MAX_INSNS)
  match ops.encodePlan { program := "/bin/true" } goodSeccomp with
  | .error _ => NondetTest.assert False
  | .ok _ => pure ()
  let planAny ← nondet CompiledSandboxPlan
  let seccompAny ← nondet ByteArray
  match ops.encodePlan planAny seccompAny with
  | .error err =>
    NondetTest.assert (err.kind = .invalidInput ∧ err.message ≠ "")
  | .ok wire =>
    let nInsns := seccompAny.size / 8
    let countOff := wire.size - (4 + seccompAny.size)
    NondetTest.assert (0 < seccompAny.size ∧
      seccompAny.size % 8 = 0 ∧
      seccompAny.size ≤ 8 * SECCOMP_MAX_INSNS ∧
      wire.size ≥ 12 + seccompAny.size ∧
      wire.extract 0 8 = "LSWP0002".toUTF8 ∧
      wire[countOff]! = UInt8.ofNat (nInsns % 256) ∧
      wire[countOff + 1]! = UInt8.ofNat ((nInsns / 256) % 256) ∧
      wire[countOff + 2]! = UInt8.ofNat ((nInsns / 65536) % 256) ∧
      wire[countOff + 3]! = UInt8.ofNat ((nInsns / 16777216) % 256) ∧
      wire.extract (wire.size - seccompAny.size) wire.size = seccompAny)

/-- When `ops.hostSeccompArch` fails, it fails closed with `.unavailable`, a non-empty message, and unchanged resource counts; when it succeeds, resource counts are unchanged. -/
def test_psandboxRaw_hostSeccompArch_failClosedUnavailable
    {S : Type} {runner} [NondetTest runner] (ops : RawProcessSandboxOpsM (StateM S)) : runner Unit := do
  let s₀ ← nondet S
  let c₀ := (ops.activeResourceCounts.run s₀).1
  let (res, s₁) := ops.hostSeccompArch.run s₀
  let c₁ := (ops.activeResourceCounts.run s₁).1
  match res with
  | .ok arch =>
    NondetTest.assert ((arch = .x86_64 ∨ arch = .aarch64) ∧ c₁ = c₀)
  | .error err =>
    NondetTest.assert (err.kind = .unavailable ∧ err.message ≠ "" ∧ c₁ = c₀)

/-- When `ops.preflight req` fails, it fails closed with `.unavailable`, a non-empty message, and unchanged resource counts. -/
def test_psandboxRaw_preflight_failClosedUnavailable
    {S : Type} {runner} [NondetTest runner] (ops : RawProcessSandboxOpsM (StateM S)) : runner Unit := do
  let s₀ ← nondet S
  let req ← nondet PreflightReq
  let c₀ := (ops.activeResourceCounts.run s₀).1
  let (res, s₁) := (ops.preflight req).run s₀
  match res with
  | .ok () =>
    let c₁ := (ops.activeResourceCounts.run s₁).1
    NondetTest.assert (c₁ = c₀)
  | .error err =>
    let c₁ := (ops.activeResourceCounts.run s₁).1
    NondetTest.assert (err.kind = .unavailable ∧ err.message ≠ "" ∧ c₁ = c₀)

/-- `sealPlan` allocates a valid `PlanHandle` incrementing `openPlans`, `closePlan` restores `openPlans`, and forged/closed handles fail with `.invalidInput`. -/
def test_psandboxRaw_planLifecycle_conservesOpenPlansAndRejectsClosed
    {S : Type} {runner} [NondetTest runner] (ops : RawProcessSandboxOpsM (StateM S)) : runner Unit := do
  let s₀ ← nondet S
  let plan ← nondet CompiledSandboxPlan
  let seccompBytes ← nondet ByteArray
  let forgedZero : PlanHandle := { handleId := 0 }
  let forgedOverflow : PlanHandle := { handleId := UInt64.size }
  NondetTest.assert (∃ e, (ops.closePlan forgedZero |>.run s₀).1 = .error e ∧ e.kind = .invalidInput)
  NondetTest.assert (∃ e, (ops.closePlan forgedOverflow |>.run s₀).1 = .error e ∧ e.kind = .invalidInput)
  NondetTest.assert (∃ e, (ops.spawnBox forgedZero |>.run s₀).1 = .error e ∧ e.kind = .invalidInput)
  let c₀ := (ops.activeResourceCounts.run s₀).1
  let (sealRes, s₁) := (ops.sealPlan plan seccompBytes).run s₀
  match sealRes with
  | .error err =>
    let c₁ := (ops.activeResourceCounts.run s₁).1
    NondetTest.assert (err.message ≠ "" ∧ c₁ = c₀)
  | .ok ph =>
    let c₁ := (ops.activeResourceCounts.run s₁).1
    NondetTest.assert (isValidSandboxHandleId ph.handleId = true ∧
      c₁.openPlans = c₀.openPlans + 1 ∧
      c₁.activeBoxes = c₀.activeBoxes ∧
      c₁.activeForwarders = c₀.activeForwarders)
    let (closeRes, s₂) := (ops.closePlan ph).run s₁
    let c₂ := (ops.activeResourceCounts.run s₂).1
    NondetTest.assert (closeRes = .ok () ∧ c₂ = c₀)
    NondetTest.assert (∃ e, (ops.closePlan ph |>.run s₂).1 = .error e ∧ e.kind = .invalidInput)

/-- `spawnBox`, `startPortForwarders`, `stopPortForwarders`, `killProcessGroup`, `pidfdKill`, and `reapBox` conserve resource counts and reject forged/reaped handles. -/
def test_psandboxRaw_boxAndForwarderLifecycle_conservesResources
    {S : Type} {runner} [NondetTest runner] (ops : RawProcessSandboxOpsM (StateM S)) : runner Unit := do
  let s₀ ← nondet S
  let plan ← nondet CompiledSandboxPlan
  let seccompBytes ← nondet ByteArray
  let fwds ← nondet (Array PortForward)
  assume (!fwds.isEmpty)
  assume (fwds.toList.all (fun pf => pf.boxPort != 0 && pf.hostPort != 0) = true)
  let forgedBox : BoxHandle := { handleId := 0, pid := 1, pgid := 1, pidfd := 3 }
  let forgedFwd : PortForwarderHandle := { handleId := 0, boxHandleId := 0 }
  NondetTest.assert (∃ e, (ops.killProcessGroup forgedBox |>.run s₀).1 = .error e ∧ e.kind = .invalidInput)
  NondetTest.assert (∃ e, (ops.pidfdKill forgedBox |>.run s₀).1 = .error e ∧ e.kind = .invalidInput)
  NondetTest.assert (∃ e, (ops.reapBox forgedBox |>.run s₀).1 = .error e ∧ e.kind = .invalidInput)
  NondetTest.assert (∃ e, (ops.stopPortForwarders forgedFwd |>.run s₀).1 = .error e ∧ e.kind = .invalidInput)
  let c₀ := (ops.activeResourceCounts.run s₀).1
  let (sealRes, s₁) := (ops.sealPlan plan seccompBytes).run s₀
  match sealRes with
  | .error _ => assume False
  | .ok ph =>
    let (spawnRes, s₂) := (ops.spawnBox ph).run s₁
    match spawnRes with
    | .error _ => assume False
    | .ok bh =>
      let c₂ := (ops.activeResourceCounts.run s₂).1
      NondetTest.assert (isValidSandboxHandleId bh.handleId = true ∧
        bh.pid > 0 ∧ bh.pgid > 0 ∧ bh.pidfd ≥ 0 ∧
        c₂.activeBoxes = c₀.activeBoxes + 1)
      let (fwdRes, s₃) := (ops.startPortForwarders bh fwds).run s₂
      match fwdRes with
      | .error _ => assume False
      | .ok fh =>
        let c₃ := (ops.activeResourceCounts.run s₃).1
        NondetTest.assert (isValidSandboxHandleId fh.handleId = true ∧
          fh.boxHandleId = bh.handleId ∧
          c₃.activeForwarders = c₀.activeForwarders + 1)
        let (stopRes, s₄) := (ops.stopPortForwarders fh).run s₃
        let (killPgRes, s₅) := (ops.killProcessGroup bh).run s₄
        let (pidfdRes, s₆) := (ops.pidfdKill bh).run s₅
        let (reapRes, s₇) := (ops.reapBox bh).run s₆
        let (closeRes, s₈) := (ops.closePlan ph).run s₇
        let c₈ := (ops.activeResourceCounts.run s₈).1
        NondetTest.assert (stopRes = .ok () ∧
          killPgRes = .ok () ∧
          pidfdRes = .ok () ∧
          reapRes = .ok () ∧
          closeRes = .ok () ∧
          c₈ = c₀)
        NondetTest.assert (∃ e, (ops.reapBox bh |>.run s₈).1 = .error e ∧ e.kind = .invalidInput)
        NondetTest.assert (∃ e, (ops.stopPortForwarders fh |>.run s₈).1 = .error e ∧ e.kind = .invalidInput)

end LeanSwe.ProcessSandbox.Raw
