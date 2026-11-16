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
  let forgedZero : PlanHandle := { handleId := 0 }
  let forgedOverflow : PlanHandle := { handleId := UInt64.size }
  NondetTest.assert (∃ e, (ops.closePlan forgedZero |>.run s₀).1 = .error e ∧ e.kind = .invalidInput)
  NondetTest.assert (∃ e, (ops.closePlan forgedOverflow |>.run s₀).1 = .error e ∧ e.kind = .invalidInput)
  NondetTest.assert (∃ e, (ops.spawnBox forgedZero |>.run s₀).1 = .error e ∧ e.kind = .invalidInput)
  let c₀ := (ops.activeResourceCounts.run s₀).1
  let (sealRes, s₁) := (ops.sealPlan plan).run s₀
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
  let (sealRes, s₁) := (ops.sealPlan plan).run s₀
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

/-- External trust boundary assumptions for `LeanSwe.ProcessSandbox.Raw` (`psandbox_shim.c` and `psandbox_init.c`) grounded in `RuntimeTests.lean`. -/
structure EmpiricalAssumptions where
  /-- `preflight` verifies Linux host, `bwrap` availability, unprivileged `user`/`pid`/`net`/`mount`/`ipc`/`uts` namespace creation, Landlock `landlock_create_ruleset` ABI >= 4, `seccomp` BPF support, and direct `/sys/fs/cgroup` sibling cgroup creation plus `memory` (`memory.max`, ignoring `ENOENT` on `memory.swap.max` on swapless kernels) and `pids` (`pids.max`) controller delegation when requested, failing closed with `.unavailable`. -/
  preflightProbesNamespacesLandlockV4AndDirectCgroupV2 : Prop
  /-- `discoverHostPreset` inspects `/usr`, `/bin`, `/sbin`, `/lib`, `/lib64` via `lstat` (preserving top-level symlinks such as `/bin -> usr/bin`), checks the 9 allowlisted `/etc` paths, reads `getenv("HOME")` plus `getpwuid_r(getuid())` without touching unmounted `/home` autofs mounts, and includes nested home paths (including through symlinked system roots) in `excludedHomePaths` iff `stat` confirms the host directory exists. -/
  discoverHostPresetPreservesTopSymlinksAndAvoidsAutofs : Prop
  /-- `sealPlan` writes the serialized `CompiledSandboxPlan`, embedded `leanswe-psandbox-init` (`--perms 0555 --ro-bind-data <fd> /etc/.leanswe-psandbox-init`), and synthetic `/etc/hosts` (`127.0.0.1 localhost\n::1 localhost\n`) into `memfd_create(..., MFD_CLOEXEC | MFD_ALLOW_SEALING)` descriptors sealed with `F_SEAL_SEAL | F_SEAL_SHRINK | F_SEAL_GROW | F_SEAL_WRITE`, and `spawnBox` opens fresh per-spawn `open("/proc/self/fd/<memfd>", O_RDONLY)` descriptors to avoid shared-offset `lseek` races across concurrent `run` calls. -/
  memfdPlanAndInitSealedImmutable : Prop
  /-- `spawnBox` never uses `systemd-run --user --scope` (which closes inherited FDs `>= 3` with `EBADF`); instead `psandbox_shim.c` always creates a per-box sibling directory in `/sys/fs/cgroup` under `/proc/self/cgroup`'s delegated parent, writes `memory.max`, `memory.swap.max = "0"` (ignoring `ENOENT`), and `pids.max = pidsMax + 2` (for the 2 `--as-pid-1` wrapper tasks), spawns `bwrap --unshare-all --as-pid-1 --die-with-parent` from a dedicated `pthread_once` process-lifetime spawner thread (avoiding Linux `PR_SET_PDEATHSIG` misfires on short-lived Lean `Task` worker pthreads), places child PID into `cgroup.procs` before `execvp`, prechecks user mount `hostPath`s (`.notFound`/`.permissionDenied`) while mapping pre-`execvp` nested mountpoint `EROFS` to `.unavailable`, opens a race-free `pidfd`, and `reapBox` writes `cgroup.kill = "1"`, reaps `bwrap`, and polls `cgroup.events` (`populated 0`) with bounded `EBUSY`-retrying `rmdir`. -/
  directCgroupV2FsScopeAndCgroupKillRmdir : Prop
  /-- `psandbox_init.c` runs under `bwrap` with `--perms 0000 --tmpfs <mask> --remount-ro <mask>` on `maskedPresetPaths` and trailing `--remount-ro /`, sets `PR_SET_PDEATHSIG(SIGKILL)` and `PR_SET_CHILD_SUBREAPER`, sets `RLIMIT_CORE = 0` and `RLIMIT_FSIZE`, binds `127.0.0.1:boxPort` listeners inside the box `net` namespace and hands them over `SCM_RIGHTS` before closing the control socket while keeping `O_CLOEXEC` `status_pipe` and `exec_err_pipe` reporting `{ EXEC_ERR(errno, isCwd), EXITED(code), SIGNALED(sig) }` (`ENOENT -> .notFound`, `EACCES | EPERM -> .permissionDenied`, other `errno -> .ioError`), installs `PR_SET_NO_NEW_PRIVS = 1`, Landlock ABI v4 rules (`handled_access_fs` masked strictly to ABI v4 bits without `IOCTL_DEV`, strictly `READ_DIR` on `"/"`, opening targets without `O_NOFOLLOW`, stripping directory-only bits when `!S_ISDIR`, granting `EXECUTE` on presets/mounts/`/tmp`, and setting `handled_access_net = 0` when `allowBoxLocalhost = true` vs `BIND_TCP | CONNECT_TCP` when `false`), and `seccomp` BPF returning `SECCOMP_RET_ERRNO | ENOSYS` on `clone3`, `EPERM` on `clone` iff `(flags & 0x7e020000) != 0` (excluding `0x80` `CSIGNAL`), blocking `socket(AF_UNIX, ...)`, `AF_SMC`, `MSG_FASTOPEN`, and admin/escape syscalls while allowing `socketpair(AF_UNIX, type, 0, sv)` when `(type & ~(SOCK_CLOEXEC | SOCK_NONBLOCK)) ∈ {SOCK_STREAM, SOCK_SEQPACKET}`, clears inherited env (`clearenv`), and reaps all descendants via `kill(-1, SIGKILL)` + blocking `waitpid(-1, &s, 0)` until `ECHILD`. -/
  psandboxInitLandlockSeccompClone3EnosysAndUnixSocketpair : Prop
  /-- `startPortForwarders` runs a non-blocking `poll()` TCP relay (`SOCK_NONBLOCK | SOCK_CLOEXEC`, `send(..., MSG_NOSIGNAL)`) capping concurrent active relay slots at `MAX_RELAY_SLOTS = 128` (clearing `listenerFd` `POLLIN` at capacity to prevent host `EMFILE`), gating `POLLIN`/`POLLOUT` on `16 KiB` per-direction ring buffers, propagating independent directional EOF via buffer drain + `shutdown(dstFd, SHUT_WR)` so TCP half-close works cleanly, and isolating per-slot socket/`ECONNREFUSED` errors, while `readBoxOutput` feeds `stdin` and bounds captured `stdout.size + stderr.size` to `maxOutputBytes` under monotonic `timeoutMs`. -/
  nonBlockingTcpForwarderAndBoundedOutputCapture : Prop
  /-- C-shim handle tables for `PlanHandle`, `BoxHandle`, and `PortForwarderHandle` allocate `0 < handleId < UInt64.size`, protect close/reap transitions under mutexes without FD-reuse races, and reject invalid/closed handles with `.invalidInput`. -/
  handleTables64BitSafeAndRaceFree : Prop

private def mapRawErrStub : SandboxRawError → SandboxError
  | .unavailable errno? detail =>
    { kind := .unavailable, path := none, errnoCode := errno?,
      message := if detail.isEmpty then "sandbox unavailable" else detail }
  | .notFound p errno detail =>
    { kind := .notFound, path := some p, errnoCode := some errno,
      message := if detail.isEmpty then "not found" else detail }
  | .permissionDenied p? errno detail =>
    { kind := .permissionDenied, path := p?, errnoCode := some errno,
      message := if detail.isEmpty then "permission denied" else detail }
  | .invalidArgument p? errno? detail =>
    { kind := .invalidInput, path := p?, errnoCode := errno?,
      message := if detail.isEmpty then "invalid argument" else detail }
  | .ioError p? errno detail =>
    { kind := .ioError, path := p?, errnoCode := some errno,
      message := if detail.isEmpty then "io error" else detail }
  | .userError detail =>
    { kind := .ioError, path := none, errnoCode := none,
      message := if detail.isEmpty then "sandbox error" else detail }

private def stubRawOps : RawProcessSandboxOps :=
  { mapRawError := mapRawErrStub
    preflight := fun _ => pure (.error { kind := .unavailable, message := "stub" })
    discoverHostPreset := pure (.ok {})
    sealPlan := fun _ => pure (.error { kind := .unavailable, message := "stub" })
    closePlan := fun _ => pure (.error { kind := .invalidInput, message := "closed" })
    spawnBox := fun _ => pure (.error { kind := .invalidInput, message := "closed" })
    startPortForwarders := fun _ _ => pure (.error { kind := .invalidInput, message := "closed" })
    stopPortForwarders := fun _ => pure (.error { kind := .invalidInput, message := "closed" })
    readBoxOutput := fun _ _ _ _ => pure (.error { kind := .invalidInput, message := "closed" })
    killProcessGroup := fun _ => pure (.error { kind := .invalidInput, message := "closed" })
    pidfdKill := fun _ => pure (.error { kind := .invalidInput, message := "closed" })
    reapBox := fun _ => pure (.error { kind := .invalidInput, message := "closed" })
    activeResourceCounts := pure {} }

private structure RawMockState where
  nextId : Nat := 1
  plans : List Nat := []
  boxes : List Nat := []
  fwds : List (Nat × Nat) := []
  preflightOk : Bool := true
  deriving Repr, BEq, DecidableEq, Inhabited

private def stubStatefulRawOps : RawProcessSandboxOpsM (StateM RawMockState) :=
  { mapRawError := mapRawErrStub
    preflight := fun _ s =>
      if s.preflightOk then (.ok (), s)
      else (.error { kind := .unavailable, message := "unavailable" }, s)
    discoverHostPreset := fun s => (.ok {}, s)
    sealPlan := fun _ s =>
      let id := if isValidSandboxHandleId s.nextId then s.nextId else 1
      (.ok { handleId := id }, { s with nextId := id + 1, plans := id :: s.plans })
    closePlan := fun ph s =>
      if !isValidSandboxHandleId ph.handleId || !s.plans.contains ph.handleId then
        (.error { kind := .invalidInput, message := "invalid plan handle" }, s)
      else
        (.ok (), { s with plans := s.plans.erase ph.handleId })
    spawnBox := fun ph s =>
      if !isValidSandboxHandleId ph.handleId || !s.plans.contains ph.handleId then
        (.error { kind := .invalidInput, message := "invalid plan handle" }, s)
      else
        let id := if isValidSandboxHandleId s.nextId then s.nextId else 1
        let bh : BoxHandle := { handleId := id, pid := 100, pgid := 100, pidfd := 4 }
        (.ok bh, { s with nextId := id + 1, boxes := id :: s.boxes })
    startPortForwarders := fun bh _ s =>
      if !isValidSandboxHandleId bh.handleId || !s.boxes.contains bh.handleId then
        (.error { kind := .invalidInput, message := "invalid box handle" }, s)
      else
        let id := if isValidSandboxHandleId s.nextId then s.nextId else 1
        (.ok { handleId := id, boxHandleId := bh.handleId },
          { s with nextId := id + 1, fwds := (id, bh.handleId) :: s.fwds })
    stopPortForwarders := fun fh s =>
      if !isValidSandboxHandleId fh.handleId || !s.fwds.any (fun p => p.1 == fh.handleId) then
        (.error { kind := .invalidInput, message := "invalid forwarder handle" }, s)
      else
        (.ok (), { s with fwds := s.fwds.filter (fun p => p.1 != fh.handleId) })
    readBoxOutput := fun bh _ _ _ s =>
      if !isValidSandboxHandleId bh.handleId || !s.boxes.contains bh.handleId then
        (.error { kind := .invalidInput, message := "invalid box handle" }, s)
      else
        (.ok { outcome := .exited 0, stdout := ByteArray.empty, stderr := ByteArray.empty }, s)
    killProcessGroup := fun bh s =>
      if !isValidSandboxHandleId bh.handleId || !s.boxes.contains bh.handleId then
        (.error { kind := .invalidInput, message := "invalid box handle" }, s)
      else
        (.ok (), s)
    pidfdKill := fun bh s =>
      if !isValidSandboxHandleId bh.handleId || !s.boxes.contains bh.handleId then
        (.error { kind := .invalidInput, message := "invalid box handle" }, s)
      else
        (.ok (), s)
    reapBox := fun bh s =>
      if !isValidSandboxHandleId bh.handleId || !s.boxes.contains bh.handleId then
        (.error { kind := .invalidInput, message := "invalid box handle" }, s)
      else
        (.ok (), { s with boxes := s.boxes.erase bh.handleId })
    activeResourceCounts := fun s =>
      ({ openPlans := s.plans.length, activeBoxes := s.boxes.length, activeForwarders := s.fwds.length }, s) }

example : ¬ Core.AllPass (test_psandboxRaw_isValidSandboxHandleId_bounds (fun _ => true)) := by
  intro h
  have h0 := h 1
  simp [Bind.bind, assert] at h0

example : ¬ Core.AllPass (test_psandboxRaw_isValidSandboxHandleId_bounds (fun id => decide (0 < id))) := by
  intro h
  have h0 := h 1
  simp [Bind.bind, assert, UInt64.size] at h0

example : ¬ Core.AllPass (test_psandboxRaw_mapRawError_returnsNonEmptyMessage
    { stubRawOps with mapRawError := fun _ => { kind := .ioError, message := "" } }) := by
  intro h
  have h0 := h (.userError "")
  simp [assert] at h0

example : ¬ Core.AllPass (test_psandboxRaw_mapRawError_preservesKindAndFields
    { stubRawOps with
      mapRawError := fun
        | .unavailable errno? _ => { kind := .ioError, errnoCode := errno?, message := "wrong kind" }
        | other => mapRawErrStub other }) := by
  intro h
  have h0 := h (.unavailable none "missing landlock")
  simp [assert] at h0

example : ¬ Core.AllPass (test_psandboxRaw_preflight_failClosedUnavailable
    { stubStatefulRawOps with
      preflight := fun _ s => (.error { kind := .ioError, message := "not fail-closed kind" }, s) }) := by
  intro h
  have h0 := h {} {}
  simp [StateT.run, assert] at h0

example : ¬ Core.AllPass (test_psandboxRaw_planLifecycle_conservesOpenPlansAndRejectsClosed
    { stubStatefulRawOps with
      closePlan := fun _ s => (.ok (), s) }) := by
  intro h
  have h0 := h {} { program := "/bin/true" }
  simp [Bind.bind, StateT.run, assert] at h0

example : ¬ Core.AllPass (test_psandboxRaw_boxAndForwarderLifecycle_conservesResources
    { stubStatefulRawOps with
      reapBox := fun bh s =>
        if !isValidSandboxHandleId bh.handleId || !s.boxes.contains bh.handleId then
          (.error { kind := .invalidInput, message := "invalid" }, s)
        else
          (.ok (), s) }) := by
  intro h
  have h0 := h {} { program := "/bin/true" } #[{ boxPort := 8080, hostPort := 8080 }]
    (by decide) (by decide)
  simp [Bind.bind, stubStatefulRawOps, isValidSandboxHandleId, UInt64.size, StateT.run, assert] at h0

end LeanSwe.ProcessSandbox.Raw
