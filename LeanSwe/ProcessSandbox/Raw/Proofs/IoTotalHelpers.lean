import Core.Assumptions
import LeanSwe.ProcessSandbox.Raw.Interface

namespace LeanSwe.ProcessSandbox.Raw.Proofs

open Core
open LeanSwe.LinuxSyscall
open LeanSwe.ProcessSandbox.Raw
open LeanSwe.ProcessSandbox.Raw.SysBridge
open LeanSwe.ProcessSandbox.Raw.SysBridge.Driver
open LeanSwe.ProcessSandbox.Raw.SysBridge.Cgroup
open LeanSwe.ProcessSandbox.Raw.SysBridge.Preset
open LeanSwe.ProcessSandbox.Raw.SysBridge.Bwrap

/-- Totality predicate stating that `act : IO α` never throws an uncaught `IO.Error`. -/
def IoTotal {α : Type} (act : IO α) : Prop :=
  ∀ w : Void IO.RealWorld, ∃ a w', act w = .ok a w'

/-- Safety predicate stating that `act` never throws `IO.Error` and every `Except.error e` satisfies `P e.kind`. -/
def IoSafeErr {α : Type} (P : SandboxErrorKind → Prop)
    (act : IO (Except SandboxError α)) : Prop :=
  ∀ w : Void IO.RealWorld, ∃ res w', act w = .ok res w' ∧
    match res with
    | .ok _ => True
    | .error e => P e.kind

/-- Any `BaseIO` action lifted to `IO` is total. -/
theorem baseIo_total {α : Type} (b : BaseIO α) : IoTotal (b : IO α) := by
  intro w
  change ∃ a w', b.toEIO w = .ok a w'
  unfold BaseIO.toEIO
  cases b w with
  | mk a w' => exact ⟨a, w', rfl⟩

/-- `pure a` is total in `IO`. -/
theorem ioTotal_pure {α : Type} (a : α) : IoTotal (pure a : IO α) :=
  fun w => ⟨a, w, rfl⟩

/-- `>>=` preserves `IoTotal`. -/
theorem ioTotal_bind {α β : Type} {ma : IO α} {k : α → IO β}
    (ha : IoTotal ma) (hk : ∀ a, IoTotal (k a)) : IoTotal (ma >>= k) := by
  intro w
  obtain ⟨a, w1, h1⟩ := ha w
  obtain ⟨b, w2, h2⟩ := hk a w1
  refine ⟨b, w2, ?_⟩
  change EST.bind ma k w = .ok b w2
  unfold EST.bind
  rw [h1]
  exact h2

/-- `if` preserves `IoTotal`. -/
theorem ioTotal_ite {α : Type} {c : Prop} [Decidable c] {t e : IO α}
    (ht : IoTotal t) (he : IoTotal e) : IoTotal (if c then t else e) := by
  by_cases hc : c <;> simp [hc, ht, he]

private theorem ioTotal_est_tryCatch {β : Type} (m1 : IO β) (h : IO.Error → IO β)
    (hh : ∀ err, IoTotal (h err)) : IoTotal (EST.tryCatch m1 h) := by
  intro w; unfold EST.tryCatch
  cases m1 w with
  | ok b w' => exact ⟨b, w', rfl⟩
  | error err w' => exact hh err w'

/-- `Core.ioConcOps.tryCatchMsg` is total in `IO` for every underlying `act : IO α`. -/
theorem ioTotal_ioConcOps_tryCatchMsg {α : Type} (act : IO α) :
    IoTotal (Core.ioConcOps.tryCatchMsg act) :=
  ioTotal_est_tryCatch _ _ (fun _ w => ⟨_, w, rfl⟩)

/-- `catchSysErrno Core.ioConcOps` is total in `IO`. -/
theorem ioTotal_catchSysErrno {α : Type} (act : IO (Except Errno α)) :
    IoTotal (catchSysErrno Core.ioConcOps act) := by
  unfold catchSysErrno
  refine ioTotal_bind (ioTotal_ioConcOps_tryCatchMsg act) fun r => ?_
  cases r <;> exact ioTotal_pure _

/-- `catchSysPf Core.ioConcOps` is total in `IO`. -/
theorem ioTotal_catchSysPf {α : Type} (act : IO (Except PostFork.PostForkError α)) :
    IoTotal (catchSysPf Core.ioConcOps act) := by
  unfold catchSysPf
  refine ioTotal_bind (ioTotal_ioConcOps_tryCatchMsg act) fun r => ?_
  cases r <;> exact ioTotal_pure _

/-- `catchSysOpt Core.ioConcOps` is total in `IO`. -/
theorem ioTotal_catchSysOpt {α : Type} (act : IO (Option α)) :
    IoTotal (catchSysOpt Core.ioConcOps act) := by
  unfold catchSysOpt
  refine ioTotal_bind (ioTotal_ioConcOps_tryCatchMsg act) fun r => ?_
  cases r <;> exact ioTotal_pure _

/-- `List.forIn` preserves `IoTotal`. -/
theorem ioTotal_forIn_list {α β : Type} (step : α → β → IO (ForInStep β))
    (hstep : ∀ x b, IoTotal (step x b)) :
    ∀ (xs : List α) (b : β), IoTotal (forIn xs b step)
  | [], b => ioTotal_pure b
  | x :: xs, b => by
    simp only [List.forIn_cons]
    refine ioTotal_bind (hstep x b) fun r => ?_
    cases r with
    | done b' => exact ioTotal_pure b'
    | yield b' => exact ioTotal_forIn_list step hstep xs b'

/-- `Array.forIn` preserves `IoTotal`. -/
theorem ioTotal_forIn_array {α β : Type} (step : α → β → IO (ForInStep β))
    (hstep : ∀ x b, IoTotal (step x b)) (arr : Array α) (b : β) :
    IoTotal (forIn arr b step) := by
  rw [← Array.forIn_toList]
  exact ioTotal_forIn_list step hstep arr.toList b

/-- `pure (.ok v)` satisfies `IoSafeErr P`. -/
theorem ioSafeErr_ok {α : Type} {P : SandboxErrorKind → Prop} (v : α) :
    IoSafeErr P (pure (.ok v)) :=
  fun w => ⟨.ok v, w, rfl, trivial⟩

/-- `pure (.error e)` satisfies `IoSafeErr P` when `P e.kind`. -/
theorem ioSafeErr_err {α : Type} {P : SandboxErrorKind → Prop}
    {e : SandboxError} (he : P e.kind) :
    IoSafeErr P (pure (.error e : Except SandboxError α)) :=
  fun w => ⟨.error e, w, rfl, he⟩

/-- Binding a total action before an `IoSafeErr P` continuation satisfies `IoSafeErr P`. -/
theorem ioSafeErr_bind {α β : Type} {P : SandboxErrorKind → Prop}
    {ma : IO α} {k : α → IO (Except SandboxError β)}
    (ha : IoTotal ma) (hk : ∀ a, IoSafeErr P (k a)) :
    IoSafeErr P (ma >>= k) := by
  intro w
  obtain ⟨a, w1, h1⟩ := ha w
  obtain ⟨res, w2, h2, hP⟩ := hk a w1
  refine ⟨res, w2, ?_, hP⟩
  change EST.bind ma k w = .ok res w2
  unfold EST.bind
  rw [h1]
  exact h2

/-- `if` preserves `IoSafeErr P`. -/
theorem ioSafeErr_ite {α : Type} {P : SandboxErrorKind → Prop} {c : Prop} [Decidable c]
    {t e : IO (Except SandboxError α)} (ht : IoSafeErr P t) (he : IoSafeErr P e) :
    IoSafeErr P (if c then t else e) := by
  by_cases hc : c <;> simp [hc, ht, he]

/-- Convert `IoSafeErr P act` into `Core.NeverErrorKindIO` for any `forbidden` excluded by `P`. -/
theorem ioSafeErr_never {α : Type} {P : SandboxErrorKind → Prop}
    {act : IO (Except SandboxError α)} (hSafe : IoSafeErr P act)
    {forbidden : SandboxErrorKind} (hForb : ∀ k, P k → k ≠ forbidden)
    (w : Void IO.RealWorld) :
    Core.NeverErrorKindIO SandboxError.kind forbidden act w := by
  obtain ⟨res, w', hRun, hP⟩ := hSafe w
  unfold Core.NeverErrorKindIO
  rw [hRun]
  cases res with
  | ok _ => trivial
  | error e => exact hForb e.kind hP

/-- Bundle of `IoTotal` witnesses for all `HostSysDepsM IO fd fwdTask` methods used by `SysBridge`. -/
structure SysDepsTotal {fd fwdTask : Type} (deps : HostSysDepsM IO fd fwdTask) : Prop where
  /-- `files.openat` is total. -/
  openat : ∀ d p fl m, IoTotal (deps.files.openat d p fl m)
  /-- `files.close` is total. -/
  close : ∀ fd, IoTotal (deps.files.close fd)
  /-- `files.read` is total. -/
  read : ∀ fd n, IoTotal (deps.files.read fd n)
  /-- `files.write` is total. -/
  write : ∀ fd bs, IoTotal (deps.files.write fd bs)
  /-- `files.fstatat` is total. -/
  fstatat : ∀ d p fl, IoTotal (deps.files.fstatat d p fl)
  /-- `files.faccessat` is total. -/
  faccessat : ∀ d p mk fl, IoTotal (deps.files.faccessat d p mk fl)
  /-- `files.mkdirat` is total. -/
  mkdirat : ∀ d p m, IoTotal (deps.files.mkdirat d p m)
  /-- `files.unlinkat` is total. -/
  unlinkat : ∀ d p rm, IoTotal (deps.files.unlinkat d p rm)
  /-- `files.readlinkat` is total. -/
  readlinkat : ∀ d p c, IoTotal (deps.files.readlinkat d p c)
  /-- `files.fcntl` is total. -/
  fcntl : ∀ fd cmd, IoTotal (deps.files.fcntl fd cmd)
  /-- `files.reopenReadOnly` is total. -/
  reopenReadOnly : ∀ fd, IoTotal (deps.files.reopenReadOnly fd)
  /-- `proc.waitpid` is total. -/
  waitpid : ∀ pid fl, IoTotal (deps.proc.waitpid pid fl)
  /-- `proc.kill` is total. -/
  kill : ∀ pid sig, IoTotal (deps.proc.kill pid sig)
  /-- `proc.pidfd_send_signal` is total. -/
  pidfdSendSignal : ∀ fd sig fl, IoTotal (deps.proc.pidfd_send_signal fd sig fl)
  /-- `proc.getpid` is total. -/
  getpid : IoTotal deps.proc.getpid
  /-- `proc.getuid` is total. -/
  getuid : IoTotal deps.proc.getuid
  /-- `sandbox.landlockCreateRuleset` is total. -/
  landlockCreateRuleset : ∀ a fl, IoTotal (deps.sandbox.landlockCreateRuleset a fl)
  /-- `sandbox.seccomp` is total. -/
  seccomp : ∀ op fl bs, IoTotal (deps.sandbox.seccomp op fl bs)
  /-- `sandbox.memfdCreate` is total. -/
  memfdCreate : ∀ n fl, IoTotal (deps.sandbox.memfdCreate n fl)
  /-- `timeRand.clock_nanosleep` is total. -/
  clockNanosleep : ∀ clk a ts, IoTotal (deps.timeRand.clock_nanosleep clk a ts)
  /-- `passwd.getpwuid` is total. -/
  getpwuid : ∀ uid, IoTotal (deps.passwd.getpwuid uid)
  /-- `postFork.spawn` is total. -/
  pfSpawn : ∀ sp, IoTotal (deps.postFork.spawn sp)
  /-- `getEnvPath` is total. -/
  getEnvPath : IoTotal deps.getEnvPath
  /-- `getEnvHome` is total. -/
  getEnvHome : IoTotal deps.getEnvHome
  /-- `startFwdTask` is total. -/
  startFwdTask : ∀ fds ps, IoTotal (deps.startFwdTask fds ps)
  /-- `stopFwdTask` is total. -/
  stopFwdTask : ∀ tid, IoTotal (deps.stopFwdTask tid)

/-- Bundle of `IoTotal` witnesses for all `HostTableOpsM IO fd fwdTask` methods. -/
structure TableOpsTotal {fd fwdTask : Type} (tbl : HostTableOpsM IO fd fwdTask) : Prop where
  /-- `insertPlan` is total. -/
  insertPlan : ∀ s, IoTotal (tbl.insertPlan s)
  /-- `findPlan` is total. -/
  findPlan : ∀ hid, IoTotal (tbl.findPlan hid)
  /-- `detachPlan` is total. -/
  detachPlan : ∀ hid, IoTotal (tbl.detachPlan hid)
  /-- `insertBox` is total. -/
  insertBox : ∀ s, IoTotal (tbl.insertBox s)
  /-- `findBoxKillInfo` is total. -/
  findBoxKillInfo : ∀ hid, IoTotal (tbl.findBoxKillInfo hid)
  /-- `takeBoxListeners` is total. -/
  takeBoxListeners : ∀ hid exp, IoTotal (tbl.takeBoxListeners hid exp)
  /-- `takeBoxIo` is total. -/
  takeBoxIo : ∀ hid, IoTotal (tbl.takeBoxIo hid)
  /-- `detachBox` is total. -/
  detachBox : ∀ hid, IoTotal (tbl.detachBox hid)
  /-- `insertFwd` is total. -/
  insertFwd : ∀ s, IoTotal (tbl.insertFwd s)
  /-- `detachFwd` is total. -/
  detachFwd : ∀ hid, IoTotal (tbl.detachFwd hid)
  /-- `nextCgSeq` is total. -/
  nextCgSeq : IoTotal tbl.nextCgSeq
  /-- `counts` is total. -/
  counts : IoTotal tbl.counts

/-- `mkSafeSysDepsM sys Core.ioConcOps` satisfies `SysDepsTotal` for every `sys`, `isLinux`, and `target`. -/
theorem mkSafeSysDepsM_total (sys : Model.FullSysOpsM IO) (isLinux : Bool) (target : String) :
    SysDepsTotal (mkSafeSysDepsM sys Core.ioConcOps isLinux target) := by
  dsimp only [mkSafeSysDepsM, mkSafeFilesOps, mkSafeNetOps, mkSafePollOps, mkSafeProcOps,
    mkSafeSandboxOps, mkSafeTimeRandOps, mkSafePasswdOps, mkSafePostForkOps]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro d p fl m; exact ioTotal_catchSysErrno _
  · intro fd; exact ioTotal_catchSysErrno _
  · intro fd n; exact ioTotal_catchSysErrno _
  · intro fd bs; exact ioTotal_catchSysErrno _
  · intro d p fl; exact ioTotal_catchSysErrno _
  · intro d p mk fl; exact ioTotal_catchSysErrno _
  · intro d p m; exact ioTotal_catchSysErrno _
  · intro d p rm; exact ioTotal_catchSysErrno _
  · intro d p c; exact ioTotal_catchSysErrno _
  · intro fd cmd; exact ioTotal_catchSysErrno _
  · intro fd; exact ioTotal_catchSysErrno _
  · intro pid fl; exact ioTotal_catchSysErrno _
  · intro pid sig; exact ioTotal_catchSysErrno _
  · intro fd sig fl; exact ioTotal_catchSysErrno _
  · exact ioTotal_catchSysErrno _
  · exact ioTotal_catchSysErrno _
  · intro a fl; exact ioTotal_catchSysErrno _
  · intro op fl bs; exact ioTotal_catchSysErrno _
  · intro n fl; exact ioTotal_catchSysErrno _
  · intro clk a ts; exact ioTotal_catchSysErrno _
  · intro uid; exact ioTotal_catchSysErrno _
  · intro sp; exact ioTotal_catchSysPf _
  · exact ioTotal_catchSysOpt _
  · exact ioTotal_catchSysOpt _
  · intro fds ps; exact ioTotal_catchSysErrno _
  · intro tid
    exact ioTotal_bind (ioTotal_ioConcOps_tryCatchMsg _) (fun _ => ioTotal_pure ())

/-- `mkCellTableOps (Core.ioStateCell ref)` satisfies `TableOpsTotal` for every `ref`. -/
theorem mkCellTableOps_ioStateCell_total {fd fwdTask : Type}
    (ref : IO.Ref (HostTableState fd fwdTask)) :
    TableOpsTotal (mkCellTableOps (Core.ioStateCell ref)) := by
  dsimp only [mkCellTableOps, Core.ioStateCell]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro _; exact baseIo_total _
  · intro _; exact ioTotal_bind (baseIo_total _) (fun _ => ioTotal_pure _)
  · intro _; exact baseIo_total _
  · intro _; exact baseIo_total _
  · intro _; exact ioTotal_bind (baseIo_total _) (fun _ => ioTotal_pure _)
  · intro _ _; exact baseIo_total _
  · intro _; exact baseIo_total _
  · intro _; exact baseIo_total _
  · intro _; exact baseIo_total _
  · intro _; exact baseIo_total _
  · exact baseIo_total _
  · exact ioTotal_bind (baseIo_total _) (fun _ => ioTotal_pure _)

/-- `retryEintr` preserves `IoTotal`. -/
theorem ioTotal_retryEintr {α : Type} {act : IO (Except Errno α)} (hact : IoTotal act) :
    ∀ fuel, IoTotal (retryEintr act fuel)
  | 0 => hact
  | fuel + 1 => by
    unfold retryEintr
    refine ioTotal_bind hact fun r => ?_
    cases r with
    | ok _ => exact ioTotal_pure _
    | error _ => exact ioTotal_ite (ioTotal_retryEintr hact fuel) (ioTotal_pure _)

/-- `Files.closeOpt` is total under `SysDepsTotal`. -/
theorem ioTotal_closeOpt {fd fwdTask : Type} {deps : HostSysDepsM IO fd fwdTask}
    (hc : SysDepsTotal deps) : ∀ opt : Option fd, IoTotal (Files.closeOpt deps.files opt)
  | none => ioTotal_pure ()
  | some h => ioTotal_bind (hc.close h) (fun _ => ioTotal_pure ())

/-- `closeFdArray` is total under `SysDepsTotal`. -/
theorem ioTotal_closeFdArray {fd fwdTask : Type} {deps : HostSysDepsM IO fd fwdTask}
    (hc : SysDepsTotal deps) (fds : Array fd) : IoTotal (closeFdArray deps.files fds) := by
  unfold closeFdArray
  refine ioTotal_bind (ioTotal_forIn_array _ ?_ fds PUnit.unit) (fun _ => ioTotal_pure ())
  intro h _
  exact ioTotal_bind (ioTotal_closeOpt hc (some h)) (fun _ => ioTotal_pure (ForInStep.yield PUnit.unit))

/-- `TimeRand.sleepMonoMs` is total under `SysDepsTotal`. -/
theorem ioTotal_sleepMonoMs {fd fwdTask : Type} {deps : HostSysDepsM IO fd fwdTask}
    (hc : SysDepsTotal deps) (ms : Nat) : IoTotal (TimeRand.sleepMonoMs deps.timeRand ms) := by
  unfold TimeRand.sleepMonoMs
  exact ioTotal_bind (hc.clockNanosleep _ _ _) (fun _ => ioTotal_pure ())

/-- `writeAllFd` is total under `SysDepsTotal`. -/
theorem ioTotal_writeAllFd {fd fwdTask : Type} {deps : HostSysDepsM IO fd fwdTask}
    (hc : SysDepsTotal deps) (h : fd) (data : ByteArray) :
    ∀ off fuel, IoTotal (writeAllFd deps.files h data off fuel)
  | _, 0 => ioTotal_ite (ioTotal_pure _) (ioTotal_pure _)
  | off, fuel + 1 => by
    unfold writeAllFd
    refine ioTotal_ite (ioTotal_pure _) ?_
    refine ioTotal_bind (hc.write h _) fun r => ?_
    cases r with
    | ok _ => exact ioTotal_ite (ioTotal_pure _) (ioTotal_writeAllFd hc h data _ fuel)
    | error _ => exact ioTotal_ite (ioTotal_writeAllFd hc h data off fuel) (ioTotal_pure _)

/-- `writeTextFile` is total under `SysDepsTotal`. -/
theorem ioTotal_writeTextFile {fd fwdTask : Type} {deps : HostSysDepsM IO fd fwdTask}
    (hc : SysDepsTotal deps) (path text : String) (fuel : Nat) :
    IoTotal (writeTextFile deps.files path text fuel) := by
  unfold writeTextFile
  refine ioTotal_bind (ioTotal_retryEintr (hc.openat _ _ _ _) fuel) fun r => ?_
  cases r with
  | error _ => exact ioTotal_pure _
  | ok h =>
    refine ioTotal_bind (ioTotal_writeAllFd hc h text.toUTF8 0 fuel) fun res => ?_
    exact ioTotal_bind (ioTotal_closeOpt hc (some h)) (fun _ => ioTotal_pure res)

/-- `readBoundedLoop` is total under `SysDepsTotal`. -/
theorem ioTotal_readBoundedLoop {fd fwdTask : Type} {deps : HostSysDepsM IO fd fwdTask}
    (hc : SysDepsTotal deps) (h : fd) (maxB : Nat) :
    ∀ chunks tot fuel, IoTotal (readBoundedLoop deps.files h maxB chunks tot fuel)
  | _, _, 0 => ioTotal_pure _
  | chunks, tot, fuel + 1 => by
    unfold readBoundedLoop
    refine ioTotal_ite (ioTotal_pure _) ?_
    refine ioTotal_bind (hc.read h _) fun r => ?_
    cases r with
    | ok _ => exact ioTotal_ite (ioTotal_pure _) (ioTotal_readBoundedLoop hc h maxB _ _ fuel)
    | error _ => exact ioTotal_ite (ioTotal_readBoundedLoop hc h maxB chunks tot fuel) (ioTotal_pure _)

/-- `readSmallFile` is total under `SysDepsTotal`. -/
theorem ioTotal_readSmallFile {fd fwdTask : Type} {deps : HostSysDepsM IO fd fwdTask}
    (hc : SysDepsTotal deps) (path : String) (maxB fuel : Nat) :
    IoTotal (readSmallFile deps.files path maxB fuel) := by
  unfold readSmallFile
  refine ioTotal_bind (ioTotal_retryEintr (hc.openat _ _ _ _) fuel) fun r => ?_
  cases r with
  | error _ => exact ioTotal_pure _
  | ok h =>
    refine ioTotal_bind (ioTotal_readBoundedLoop hc h maxB #[] 0 fuel) fun res => ?_
    exact ioTotal_bind (ioTotal_closeOpt hc (some h)) (fun _ => ioTotal_pure res)

/-- `createSiblingCgroup` is total under `SysDepsTotal`. -/
theorem ioTotal_createSiblingCgroup {fd fwdTask : Type} {deps : HostSysDepsM IO fd fwdTask}
    (hc : SysDepsTotal deps) (pid : UInt32) (seq fuel : Nat) :
    IoTotal (createSiblingCgroup deps.files pid seq fuel) := by
  unfold createSiblingCgroup findDelegatedCgroupParent
  refine ioTotal_bind (ioTotal_bind (ioTotal_readSmallFile hc _ _ fuel) fun r => ?_) fun rPar => ?_
  · cases r with
    | error _ => exact ioTotal_pure _
    | ok raw =>
      dsimp only
      cases String.fromUTF8? raw with
      | none => exact ioTotal_pure _
      | some txt =>
        dsimp only
        cases parseDelegatedCgroupParent txt <;> exact ioTotal_pure _
  · cases rPar with
    | error _ => exact ioTotal_pure _
    | ok _ =>
      refine ioTotal_bind (ioTotal_retryEintr (hc.mkdirat _ _ _) fuel) fun rMk => ?_
      cases rMk <;> exact ioTotal_pure _

/-- `configureCgroupMemory` is total under `SysDepsTotal`. -/
theorem ioTotal_configureCgroupMemory {fd fwdTask : Type} {deps : HostSysDepsM IO fd fwdTask}
    (hc : SysDepsTotal deps) (cgDir lim : String) (fuel : Nat) :
    IoTotal (configureCgroupMemory deps.files cgDir lim fuel) := by
  unfold configureCgroupMemory
  refine ioTotal_bind (ioTotal_writeTextFile hc _ lim fuel) fun r1 => ?_
  cases r1 with
  | error _ => exact ioTotal_pure _
  | ok _ =>
    have hRest : IoTotal (do
        match ← writeTextFile deps.files (cgroupSubfile cgDir "memory.oom.group") "1" fuel with
        | .error e =>
          if e != Errno.ENOENT then pure (Except.error ("memory.oom.group", e))
          else pure (Except.ok ())
        | .ok _ => pure (Except.ok ())) := by
      refine ioTotal_bind (ioTotal_writeTextFile hc _ "1" fuel) fun r3 => ?_
      cases r3 with
      | ok _ => exact ioTotal_pure _
      | error _ => exact ioTotal_ite (ioTotal_pure _) (ioTotal_pure _)
    refine ioTotal_bind (ioTotal_writeTextFile hc _ "0" fuel) fun r2 => ?_
    cases r2 with
    | ok _ => exact hRest
    | error _ => exact ioTotal_ite (ioTotal_pure _) hRest

/-- `pollCgroupUnpopulated` is total under `SysDepsTotal`. -/
theorem ioTotal_pollCgroupUnpopulated {fd fwdTask : Type} {deps : HostSysDepsM IO fd fwdTask}
    (hc : SysDepsTotal deps) (evPath : String) (fuel : Nat) :
    ∀ steps, IoTotal (pollCgroupUnpopulated deps.files deps.timeRand evPath fuel steps)
  | 0 => ioTotal_pure ()
  | steps + 1 => by
    unfold pollCgroupUnpopulated
    refine ioTotal_bind (ioTotal_readSmallFile hc evPath 256 fuel) fun r => ?_
    cases r with
    | error _ => exact ioTotal_pure ()
    | ok raw =>
      dsimp only
      cases String.fromUTF8? raw with
      | none =>
        exact ioTotal_bind (ioTotal_sleepMonoMs hc _) (fun _ => ioTotal_pollCgroupUnpopulated hc evPath fuel steps)
      | some _ =>
        exact ioTotal_ite (ioTotal_pure ())
          (ioTotal_bind (ioTotal_sleepMonoMs hc _) (fun _ => ioTotal_pollCgroupUnpopulated hc evPath fuel steps))

/-- `retryRmdirCgroup` is total under `SysDepsTotal`. -/
theorem ioTotal_retryRmdirCgroup {fd fwdTask : Type} {deps : HostSysDepsM IO fd fwdTask}
    (hc : SysDepsTotal deps) (bs : ByteArray) :
    ∀ steps, IoTotal (retryRmdirCgroup deps.files deps.timeRand bs steps)
  | 0 => by
    unfold retryRmdirCgroup
    refine ioTotal_bind (hc.unlinkat none bs true) fun r => ?_
    cases r with
    | ok _ => exact ioTotal_pure _
    | error _ => exact ioTotal_ite (ioTotal_pure _) (ioTotal_pure _)
  | steps + 1 => by
    unfold retryRmdirCgroup
    refine ioTotal_bind (hc.unlinkat none bs true) fun r => ?_
    cases r with
    | ok _ => exact ioTotal_pure _
    | error _ =>
      exact ioTotal_ite (ioTotal_pure _)
        (ioTotal_ite
          (ioTotal_bind (ioTotal_sleepMonoMs hc _) (fun _ => ioTotal_retryRmdirCgroup hc bs steps))
          (ioTotal_pure _))

/-- `cleanupCgroupDir` is total under `SysDepsTotal`. -/
theorem ioTotal_cleanupCgroupDir {fd fwdTask : Type} {deps : HostSysDepsM IO fd fwdTask}
    (hc : SysDepsTotal deps) (cgDir : String) (ps rs fuel : Nat) :
    IoTotal (cleanupCgroupDir deps.files deps.timeRand cgDir ps rs fuel) := by
  unfold cleanupCgroupDir
  refine ioTotal_ite (ioTotal_pure _) ?_
  refine ioTotal_bind (ioTotal_writeTextFile hc _ "1" fuel) fun _ => ?_
  refine ioTotal_bind (ioTotal_pollCgroupUnpopulated hc _ fuel ps) fun _ => ?_
  exact ioTotal_retryRmdirCgroup hc _ rs

/-- `discoverSystemEntries` is total under `SysDepsTotal`. -/
theorem ioTotal_discoverSystemEntries {fd fwdTask : Type} {deps : HostSysDepsM IO fd fwdTask}
    (hc : SysDepsTotal deps) (fuel : Nat) : IoTotal (discoverSystemEntries deps.files fuel) := by
  unfold discoverSystemEntries
  refine ioTotal_bind (ioTotal_forIn_array _ ?_ presetSystemRoots #[]) (fun es => ioTotal_pure es)
  intro root _
  refine ioTotal_bind (ioTotal_retryEintr (hc.fstatat none root.toUTF8 _) fuel) fun r => ?_
  cases r with
  | error _ => exact ioTotal_pure _
  | ok _ =>
    refine ioTotal_ite ?_ (ioTotal_ite (ioTotal_pure _) (ioTotal_pure _))
    refine ioTotal_bind (ioTotal_retryEintr (hc.readlinkat none root.toUTF8 4096) fuel) fun r2 => ?_
    cases r2 with
    | error _ => exact ioTotal_pure _
    | ok _ =>
      refine ioTotal_ite ?_ (ioTotal_pure _)
      cases String.fromUTF8? _ <;> exact ioTotal_pure _

/-- `discoverHostPresetM` is total under `SysDepsTotal`. -/
theorem ioTotal_discoverHostPresetM {fd fwdTask : Type} {deps : HostSysDepsM IO fd fwdTask}
    (hc : SysDepsTotal deps) (fuel : Nat) :
    IoTotal (discoverHostPresetM deps.files deps.proc deps.passwd deps.getEnvHome fuel) := by
  unfold discoverHostPresetM
  refine ioTotal_bind (ioTotal_discoverSystemEntries hc fuel) fun sysEs => ?_
  have hEtc : IoTotal (discoverEtcPaths deps.files fuel) := by
    unfold discoverEtcPaths
    refine ioTotal_bind (ioTotal_forIn_array _ ?_ presetEtcAllowlist #[]) (fun ps => ioTotal_pure ps)
    intro p _
    refine ioTotal_bind (ioTotal_retryEintr (hc.fstatat none p.toUTF8 {}) fuel) fun r => ?_
    cases r <;> exact ioTotal_pure _
  refine ioTotal_bind hEtc fun etcPs => ?_
  unfold discoverExcludedHomes
  refine ioTotal_bind (ioTotal_bind hc.getEnvHome fun home? => ?_) fun exHs =>
    ioTotal_pure ({ systemEntries := sysEs, etcPaths := etcPs, excludedHomePaths := exHs } : HostRuntimePreset)
  have hFilt (pwDir? : Option String) : IoTotal (filterExistingNestedHomes deps.files [home?, pwDir?] fuel) := by
    unfold filterExistingNestedHomes
    refine ioTotal_bind (ioTotal_forIn_list _ ?_ _ []) (fun ks => ioTotal_pure (dedupStrings ks))
    intro c? _
    dsimp only
    cases c? with
    | none => exact ioTotal_pure _
    | some raw =>
      dsimp only
      cases normalizeAbsLexical raw with
      | none => exact ioTotal_pure _
      | some norm =>
        dsimp only
        refine ioTotal_ite ?_ (ioTotal_pure _)
        refine ioTotal_bind (ioTotal_retryEintr (hc.fstatat none norm.toUTF8 {}) fuel) fun r => ?_
        cases r with
        | error _ => exact ioTotal_pure _
        | ok _ => exact ioTotal_ite (ioTotal_pure _) (ioTotal_pure _)
  refine ioTotal_bind hc.getuid fun rU => ?_
  cases rU with
  | error _ => exact ioTotal_bind (ioTotal_pure none) hFilt
  | ok uid =>
    refine ioTotal_bind (hc.getpwuid uid) fun rP => ?_
    cases rP with
    | error _ => exact ioTotal_bind (ioTotal_pure none) hFilt
    | ok opt =>
      cases opt with
      | none => exact ioTotal_bind (ioTotal_pure none) hFilt
      | some entry => exact ioTotal_bind (ioTotal_pure entry.homeDirUtf8?) hFilt

/-- `createSealedMemfd` is total under `SysDepsTotal`. -/
theorem ioTotal_createSealedMemfd {fd fwdTask : Type} {deps : HostSysDepsM IO fd fwdTask}
    (hc : SysDepsTotal deps) (nm : String) (bs : ByteArray) (fuel : Nat) :
    IoTotal (createSealedMemfd deps.sandbox deps.files nm bs fuel) := by
  unfold createSealedMemfd
  refine ioTotal_bind (hc.memfdCreate _ _) fun r => ?_
  cases r with
  | error _ => exact ioTotal_pure _
  | ok h =>
    dsimp only
    have hAfterWr (rW : Except Errno Unit) : IoTotal (do
        match rW with
        | .error e =>
          Files.closeOpt deps.files (some h)
          pure (Except.error e)
        | .ok () =>
          match ← retryEintr (deps.files.fcntl h (.addSeals F_SEAL_ALL)) fuel with
          | .error e =>
            Files.closeOpt deps.files (some h)
            pure (Except.error e)
          | .ok _ => pure (Except.ok h)) := by
      cases rW with
      | error _ => exact ioTotal_bind (ioTotal_closeOpt hc (some h)) (fun _ => ioTotal_pure _)
      | ok _ =>
        refine ioTotal_bind (ioTotal_retryEintr (hc.fcntl h _) fuel) fun rF => ?_
        cases rF with
        | error _ => exact ioTotal_bind (ioTotal_closeOpt hc (some h)) (fun _ => ioTotal_pure _)
        | ok _ => exact ioTotal_pure _
    by_cases hb : bs.size > 0
    · simp only [hb, ↓reduceIte]
      exact ioTotal_bind (ioTotal_writeAllFd hc h bs 0 fuel) hAfterWr
    · simp only [hb, ↓reduceIte]
      exact ioTotal_bind (ioTotal_pure (Except.ok ())) hAfterWr

private theorem ioTotal_searchBwrapDirs {fd fwdTask : Type} {deps : HostSysDepsM IO fd fwdTask}
    (hc : SysDepsTotal deps) (fuel : Nat) : ∀ ds : List String, IoTotal (searchBwrapDirs deps.files fuel ds)
  | [] => by
    unfold searchBwrapDirs isExecutableRegFile
    refine ioTotal_bind (ioTotal_bind (ioTotal_retryEintr (hc.fstatat none _ {}) fuel) fun r => ?_) fun _ =>
      ioTotal_ite (ioTotal_pure _) (ioTotal_pure _)
    cases r with
    | error _ => exact ioTotal_pure false
    | ok _ =>
      refine ioTotal_ite (ioTotal_pure false) ?_
      refine ioTotal_bind (ioTotal_retryEintr (hc.faccessat none _ _ {}) fuel) fun r2 => ?_
      cases r2 <;> exact ioTotal_pure _
  | _ :: rest => by
    unfold searchBwrapDirs isExecutableRegFile
    refine ioTotal_bind (ioTotal_bind (ioTotal_retryEintr (hc.fstatat none _ {}) fuel) fun r => ?_) fun _ =>
      ioTotal_ite (ioTotal_pure _) (ioTotal_searchBwrapDirs hc fuel rest)
    cases r with
    | error _ => exact ioTotal_pure false
    | ok _ =>
      refine ioTotal_ite (ioTotal_pure false) ?_
      refine ioTotal_bind (ioTotal_retryEintr (hc.faccessat none _ _ {}) fuel) fun r2 => ?_
      cases r2 <;> exact ioTotal_pure _

/-- `resolveBwrapPath` is total under `SysDepsTotal`. -/
theorem ioTotal_resolveBwrapPath {fd fwdTask : Type} {deps : HostSysDepsM IO fd fwdTask}
    (hc : SysDepsTotal deps) (fuel : Nat) : IoTotal (resolveBwrapPath deps.files deps.getEnvPath fuel) := by
  unfold resolveBwrapPath
  refine ioTotal_bind hc.getEnvPath fun r => ?_
  cases r <;> exact ioTotal_searchBwrapDirs hc fuel _

end LeanSwe.ProcessSandbox.Raw.Proofs
