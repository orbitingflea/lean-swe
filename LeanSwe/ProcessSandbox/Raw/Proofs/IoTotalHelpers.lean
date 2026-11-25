import Core.Assumptions
import LeanSwe.ProcessSandbox.Raw.Interface

namespace LeanSwe.ProcessSandbox.Raw.Proofs

open Core
open LeanSwe.LinuxSyscall
open LeanSwe.ProcessSandbox.Raw
open LeanSwe.ProcessSandbox.Raw.SysBridge
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

/-- `catchIoTotal` produces a total `IO` action for any underlying `act` and `fb`. -/
theorem catchIoTotal_total {α : Type} (act : IO α) (fb : IO.Error → α) :
    IoTotal (catchIoTotal act fb) :=
  baseIo_total _

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

/-- Bundle of `IoTotal` witnesses for all host syscall and table methods used by `SysBridge`. -/
structure CapTotal (cap : Model.RawHostCapM IO) : Prop where
  /-- `files.openat` is total. -/
  openat : ∀ d p fl m, IoTotal (cap.files.openat d p fl m)
  /-- `files.close` is total. -/
  close : ∀ fd, IoTotal (cap.files.close fd)
  /-- `files.read` is total. -/
  read : ∀ fd n, IoTotal (cap.files.read fd n)
  /-- `files.write` is total. -/
  write : ∀ fd bs, IoTotal (cap.files.write fd bs)
  /-- `files.fstatat` is total. -/
  fstatat : ∀ d p fl, IoTotal (cap.files.fstatat d p fl)
  /-- `files.faccessat` is total. -/
  faccessat : ∀ d p mk fl, IoTotal (cap.files.faccessat d p mk fl)
  /-- `files.mkdirat` is total. -/
  mkdirat : ∀ d p m, IoTotal (cap.files.mkdirat d p m)
  /-- `files.unlinkat` is total. -/
  unlinkat : ∀ d p rm, IoTotal (cap.files.unlinkat d p rm)
  /-- `files.readlinkat` is total. -/
  readlinkat : ∀ d p c, IoTotal (cap.files.readlinkat d p c)
  /-- `files.fcntl` is total. -/
  fcntl : ∀ fd cmd, IoTotal (cap.files.fcntl fd cmd)
  /-- `files.reopenReadOnly` is total. -/
  reopenReadOnly : ∀ fd, IoTotal (cap.files.reopenReadOnly fd)
  /-- `proc.waitpid` is total. -/
  waitpid : ∀ pid fl, IoTotal (cap.proc.waitpid pid fl)
  /-- `proc.kill` is total. -/
  kill : ∀ pid sig, IoTotal (cap.proc.kill pid sig)
  /-- `proc.pidfd_send_signal` is total. -/
  pidfdSendSignal : ∀ fd sig fl, IoTotal (cap.proc.pidfd_send_signal fd sig fl)
  /-- `proc.getpid` is total. -/
  getpid : IoTotal cap.proc.getpid
  /-- `proc.getuid` is total. -/
  getuid : IoTotal cap.proc.getuid
  /-- `sandbox.landlockCreateRuleset` is total. -/
  landlockCreateRuleset : ∀ a fl, IoTotal (cap.sandbox.landlockCreateRuleset a fl)
  /-- `sandbox.seccomp` is total. -/
  seccomp : ∀ op fl bs, IoTotal (cap.sandbox.seccomp op fl bs)
  /-- `sandbox.memfdCreate` is total. -/
  memfdCreate : ∀ n fl, IoTotal (cap.sandbox.memfdCreate n fl)
  /-- `timeRand.clock_nanosleep` is total. -/
  clockNanosleep : ∀ clk a ts, IoTotal (cap.timeRand.clock_nanosleep clk a ts)
  /-- `passwd.getpwuid` is total. -/
  getpwuid : ∀ uid, IoTotal (cap.passwd.getpwuid uid)
  /-- `postFork.spawn` is total. -/
  pfSpawn : ∀ sp, IoTotal (cap.postFork.spawn sp)
  /-- `getEnvPath` is total. -/
  getEnvPath : IoTotal cap.getEnvPath
  /-- `getEnvHome` is total. -/
  getEnvHome : IoTotal cap.getEnvHome
  /-- `startFwdTask` is total. -/
  startFwdTask : ∀ fds ps, IoTotal (cap.startFwdTask fds ps)
  /-- `stopFwdTask` is total. -/
  stopFwdTask : ∀ tid, IoTotal (cap.stopFwdTask tid)
  /-- `getTable` is total. -/
  getTable : IoTotal cap.getTable
  /-- `modifyTable` is total. -/
  modifyTable : ∀ f, IoTotal (cap.modifyTable f)

/-- `mkIoHostCap ref` satisfies `CapTotal` for every `ref`. -/
theorem mkIoHostCap_total (ref : IO.Ref IoHostState) : CapTotal (mkIoHostCap ref) := by
  dsimp only [mkIoHostCap, mkIoFilesOps, mkIoProcOps, mkIoSandboxOps,
    mkIoTimeRandOps, mkIoPasswdOps, mkIoPostForkOps, catchErrno, catchPf]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    intros <;> exact catchIoTotal_total _ _

/-- `SysBridge.defaultOps` satisfies `CapTotal`. -/
theorem sysBridge_defaultOps_total : CapTotal SysBridge.defaultOps :=
  mkIoHostCap_total _

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

/-- `Files.closeOpt` is total under `CapTotal`. -/
theorem ioTotal_closeOpt {cap : Model.RawHostCapM IO} (hc : CapTotal cap) :
    ∀ opt : Option Nat, IoTotal (Files.closeOpt cap.files opt)
  | none => ioTotal_pure ()
  | some h => ioTotal_bind (hc.close h) (fun _ => ioTotal_pure ())

/-- `closeFdArray` is total under `CapTotal`. -/
theorem ioTotal_closeFdArray {cap : Model.RawHostCapM IO} (hc : CapTotal cap)
    (fds : Array Nat) : IoTotal (closeFdArray cap.files fds) := by
  unfold closeFdArray
  refine ioTotal_bind (ioTotal_forIn_array _ ?_ fds PUnit.unit) (fun _ => ioTotal_pure ())
  intro h _
  exact ioTotal_bind (ioTotal_closeOpt hc (some h)) (fun _ => ioTotal_pure (ForInStep.yield PUnit.unit))

/-- `TimeRand.sleepMonoMs` is total under `CapTotal`. -/
theorem ioTotal_sleepMonoMs {cap : Model.RawHostCapM IO} (hc : CapTotal cap) (ms : Nat) :
    IoTotal (TimeRand.sleepMonoMs cap.timeRand ms) := by
  unfold TimeRand.sleepMonoMs
  exact ioTotal_bind (hc.clockNanosleep _ _ _) (fun _ => ioTotal_pure ())

/-- `writeAllFd` is total under `CapTotal`. -/
theorem ioTotal_writeAllFd {cap : Model.RawHostCapM IO} (hc : CapTotal cap)
    (h : Nat) (data : ByteArray) : ∀ off fuel, IoTotal (writeAllFd cap.files h data off fuel)
  | _, 0 => ioTotal_ite (ioTotal_pure _) (ioTotal_pure _)
  | off, fuel + 1 => by
    unfold writeAllFd
    refine ioTotal_ite (ioTotal_pure _) ?_
    refine ioTotal_bind (hc.write h _) fun r => ?_
    cases r with
    | ok _ => exact ioTotal_ite (ioTotal_pure _) (ioTotal_writeAllFd hc h data _ fuel)
    | error _ => exact ioTotal_ite (ioTotal_writeAllFd hc h data off fuel) (ioTotal_pure _)

/-- `writeTextFile` is total under `CapTotal`. -/
theorem ioTotal_writeTextFile {cap : Model.RawHostCapM IO} (hc : CapTotal cap)
    (path text : String) (fuel : Nat) : IoTotal (writeTextFile cap.files path text fuel) := by
  unfold writeTextFile
  refine ioTotal_bind (ioTotal_retryEintr (hc.openat _ _ _ _) fuel) fun r => ?_
  cases r with
  | error _ => exact ioTotal_pure _
  | ok h =>
    refine ioTotal_bind (ioTotal_writeAllFd hc h text.toUTF8 0 fuel) fun res => ?_
    exact ioTotal_bind (ioTotal_closeOpt hc (some h)) (fun _ => ioTotal_pure res)

/-- `readBoundedLoop` is total under `CapTotal`. -/
theorem ioTotal_readBoundedLoop {cap : Model.RawHostCapM IO} (hc : CapTotal cap)
    (h maxB : Nat) : ∀ chunks tot fuel, IoTotal (readBoundedLoop cap.files h maxB chunks tot fuel)
  | _, _, 0 => ioTotal_pure _
  | chunks, tot, fuel + 1 => by
    unfold readBoundedLoop
    refine ioTotal_ite (ioTotal_pure _) ?_
    refine ioTotal_bind (hc.read h _) fun r => ?_
    cases r with
    | ok _ => exact ioTotal_ite (ioTotal_pure _) (ioTotal_readBoundedLoop hc h maxB _ _ fuel)
    | error _ => exact ioTotal_ite (ioTotal_readBoundedLoop hc h maxB chunks tot fuel) (ioTotal_pure _)

/-- `readSmallFile` is total under `CapTotal`. -/
theorem ioTotal_readSmallFile {cap : Model.RawHostCapM IO} (hc : CapTotal cap)
    (path : String) (maxB fuel : Nat) : IoTotal (readSmallFile cap.files path maxB fuel) := by
  unfold readSmallFile
  refine ioTotal_bind (ioTotal_retryEintr (hc.openat _ _ _ _) fuel) fun r => ?_
  cases r with
  | error _ => exact ioTotal_pure _
  | ok h =>
    refine ioTotal_bind (ioTotal_readBoundedLoop hc h maxB #[] 0 fuel) fun res => ?_
    exact ioTotal_bind (ioTotal_closeOpt hc (some h)) (fun _ => ioTotal_pure res)

/-- `createSiblingCgroup` is total under `CapTotal`. -/
theorem ioTotal_createSiblingCgroup {cap : Model.RawHostCapM IO} (hc : CapTotal cap)
    (pid : UInt32) (seq fuel : Nat) : IoTotal (createSiblingCgroup cap.files pid seq fuel) := by
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

/-- `configureCgroupMemory` is total under `CapTotal`. -/
theorem ioTotal_configureCgroupMemory {cap : Model.RawHostCapM IO} (hc : CapTotal cap)
    (cgDir lim : String) (fuel : Nat) : IoTotal (configureCgroupMemory cap.files cgDir lim fuel) := by
  unfold configureCgroupMemory
  refine ioTotal_bind (ioTotal_writeTextFile hc _ lim fuel) fun r1 => ?_
  cases r1 with
  | error _ => exact ioTotal_pure _
  | ok _ =>
    have hRest : IoTotal (do
        match ← writeTextFile cap.files (cgroupSubfile cgDir "memory.oom.group") "1" fuel with
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

/-- `pollCgroupUnpopulated` is total under `CapTotal`. -/
theorem ioTotal_pollCgroupUnpopulated {cap : Model.RawHostCapM IO} (hc : CapTotal cap)
    (evPath : String) (fuel : Nat) : ∀ steps, IoTotal (pollCgroupUnpopulated cap.files cap.timeRand evPath fuel steps)
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

/-- `retryRmdirCgroup` is total under `CapTotal`. -/
theorem ioTotal_retryRmdirCgroup {cap : Model.RawHostCapM IO} (hc : CapTotal cap)
    (bs : ByteArray) : ∀ steps, IoTotal (retryRmdirCgroup cap.files cap.timeRand bs steps)
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

/-- `cleanupCgroupDir` is total under `CapTotal`. -/
theorem ioTotal_cleanupCgroupDir {cap : Model.RawHostCapM IO} (hc : CapTotal cap)
    (cgDir : String) (ps rs fuel : Nat) :
    IoTotal (cleanupCgroupDir cap.files cap.timeRand cgDir ps rs fuel) := by
  unfold cleanupCgroupDir
  refine ioTotal_ite (ioTotal_pure _) ?_
  refine ioTotal_bind (ioTotal_writeTextFile hc _ "1" fuel) fun _ => ?_
  refine ioTotal_bind (ioTotal_pollCgroupUnpopulated hc _ fuel ps) fun _ => ?_
  exact ioTotal_retryRmdirCgroup hc _ rs

/-- `discoverSystemEntries` is total under `CapTotal`. -/
theorem ioTotal_discoverSystemEntries {cap : Model.RawHostCapM IO} (hc : CapTotal cap)
    (fuel : Nat) : IoTotal (discoverSystemEntries cap.files fuel) := by
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

/-- `discoverHostPresetM` is total under `CapTotal`. -/
theorem ioTotal_discoverHostPresetM {cap : Model.RawHostCapM IO} (hc : CapTotal cap)
    (fuel : Nat) : IoTotal (discoverHostPresetM cap.files cap.proc cap.passwd cap.getEnvHome fuel) := by
  unfold discoverHostPresetM
  refine ioTotal_bind (ioTotal_discoverSystemEntries hc fuel) fun sysEs => ?_
  have hEtc : IoTotal (discoverEtcPaths cap.files fuel) := by
    unfold discoverEtcPaths
    refine ioTotal_bind (ioTotal_forIn_array _ ?_ presetEtcAllowlist #[]) (fun ps => ioTotal_pure ps)
    intro p _
    refine ioTotal_bind (ioTotal_retryEintr (hc.fstatat none p.toUTF8 {}) fuel) fun r => ?_
    cases r <;> exact ioTotal_pure _
  refine ioTotal_bind hEtc fun etcPs => ?_
  unfold discoverExcludedHomes
  refine ioTotal_bind (ioTotal_bind hc.getEnvHome fun home? => ?_) fun exHs =>
    ioTotal_pure ({ systemEntries := sysEs, etcPaths := etcPs, excludedHomePaths := exHs } : HostRuntimePreset)
  have hFilt (pwDir? : Option String) : IoTotal (filterExistingNestedHomes cap.files [home?, pwDir?] fuel) := by
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

/-- `createSealedMemfd` is total under `CapTotal`. -/
theorem ioTotal_createSealedMemfd {cap : Model.RawHostCapM IO} (hc : CapTotal cap)
    (nm : String) (bs : ByteArray) (fuel : Nat) :
    IoTotal (createSealedMemfd cap.sandbox cap.files nm bs fuel) := by
  unfold createSealedMemfd
  refine ioTotal_bind (hc.memfdCreate _ _) fun r => ?_
  cases r with
  | error _ => exact ioTotal_pure _
  | ok h =>
    dsimp only
    have hAfterWr (rW : Except Errno Unit) : IoTotal (do
        match rW with
        | .error e =>
          Files.closeOpt cap.files (some h)
          pure (Except.error e)
        | .ok () =>
          match ← retryEintr (cap.files.fcntl h (.addSeals F_SEAL_ALL)) fuel with
          | .error e =>
            Files.closeOpt cap.files (some h)
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

private theorem ioTotal_searchBwrapDirs {cap : Model.RawHostCapM IO} (hc : CapTotal cap)
    (fuel : Nat) : ∀ ds : List String, IoTotal (searchBwrapDirs cap.files fuel ds)
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

/-- `resolveBwrapPath` is total under `CapTotal`. -/
theorem ioTotal_resolveBwrapPath {cap : Model.RawHostCapM IO} (hc : CapTotal cap)
    (fuel : Nat) : IoTotal (resolveBwrapPath cap.files cap.getEnvPath fuel) := by
  unfold resolveBwrapPath
  refine ioTotal_bind hc.getEnvPath fun r => ?_
  cases r <;> exact ioTotal_searchBwrapDirs hc fuel _

private theorem ioTotal_waitProbeExitZero {cap : Model.RawHostCapM IO} (hc : CapTotal cap)
    (pid : Int32) : ∀ fuel, IoTotal (waitProbeExitZero cap.proc pid fuel)
  | 0 => ioTotal_pure _
  | fuel + 1 => by
    unfold waitProbeExitZero
    refine ioTotal_bind (hc.waitpid pid {}) fun r => ?_
    cases r with
    | ok wr =>
      cases wr with
      | exited _ c => exact if h : c = 0 then by simp [h]; exact ioTotal_pure _ else by simp [h]; exact ioTotal_pure _
      | _ => exact ioTotal_pure _
    | error _ => exact ioTotal_ite (ioTotal_waitProbeExitZero hc pid fuel) (ioTotal_pure _)

/-- `probeBwrapNamespaces` is total under `CapTotal`. -/
theorem ioTotal_probeBwrapNamespaces {cap : Model.RawHostCapM IO} (hc : CapTotal cap)
    (bw : String) (ib : ByteArray) (fuel : Nat) :
    IoTotal (probeBwrapNamespaces cap.files cap.sandbox cap.proc cap.postFork bw ib fuel) := by
  have hOpen3 : IoTotal (openThreeDevNull cap.files fuel) := by
    unfold openThreeDevNull
    have h1 := ioTotal_retryEintr (hc.openat none "/dev/null".toUTF8 { access := .rdwr, cloexec := true } 0) fuel
    refine ioTotal_bind h1 fun r0 => ?_
    cases r0 with
    | error _ => exact ioTotal_pure _
    | ok d0 =>
      refine ioTotal_bind h1 fun r1 => ?_
      cases r1 with
      | error _ => exact ioTotal_bind (ioTotal_closeOpt hc (some d0)) (fun _ => ioTotal_pure _)
      | ok d1 =>
        refine ioTotal_bind h1 fun r2 => ?_
        cases r2 with
        | error _ =>
          exact ioTotal_bind (ioTotal_closeOpt hc (some d0)) fun _ =>
            ioTotal_bind (ioTotal_closeOpt hc (some d1)) (fun _ => ioTotal_pure _)
        | ok _ => exact ioTotal_pure _
  unfold probeBwrapNamespaces
  refine ioTotal_bind hOpen3 fun r3 => ?_
  cases r3 with
  | error _ => exact ioTotal_pure _
  | ok ds =>
    rcases ds with ⟨d0, d1, d2⟩
    refine ioTotal_bind (ioTotal_createSealedMemfd hc _ ib fuel) fun rM => ?_
    cases rM with
    | error _ =>
      exact ioTotal_bind (ioTotal_closeOpt hc (some d0)) fun _ =>
        ioTotal_bind (ioTotal_closeOpt hc (some d1)) fun _ =>
          ioTotal_bind (ioTotal_closeOpt hc (some d2)) (fun _ => ioTotal_pure _)
    | ok mfd =>
      refine ioTotal_bind (ioTotal_retryEintr (hc.reopenReadOnly mfd) fuel) fun rRo => ?_
      refine ioTotal_bind (ioTotal_closeOpt hc (some mfd)) fun _ => ?_
      cases rRo with
      | error _ =>
        exact ioTotal_bind (ioTotal_closeOpt hc (some d0)) fun _ =>
          ioTotal_bind (ioTotal_closeOpt hc (some d1)) fun _ =>
            ioTotal_bind (ioTotal_closeOpt hc (some d2)) (fun _ => ioTotal_pure _)
      | ok ifd =>
        refine ioTotal_bind (ioTotal_discoverSystemEntries hc fuel) fun sysEs => ?_
        have hAfterLd (hasLd : Bool) : IoTotal (do
            let childSpec : PostFork.ChildSpecM Nat := {
              path := bw
              argv := buildProbeBwrapArgv bw sysEs hasLd ifd
              stdio := .redirect (.handle d0) (.handle d1) (.handle d2) false
              fdPolicy := .closeAllAbove2Except #[.handle ifd]
              processGroup := .newGroup
              sigpipe := .resetDefault
              forkMode := .immortalThread
            }
            let spawnRes ← cap.postFork.spawn childSpec
            Files.closeOpt cap.files (some d0)
            Files.closeOpt cap.files (some d1)
            Files.closeOpt cap.files (some d2)
            Files.closeOpt cap.files (some ifd)
            match spawnRes with
            | .error pfErr => return .error (pfErr.errno.getD Errno.EPERM)
            | .ok child => waitProbeExitZero cap.proc child.pid.toInt32 fuel) := by
          refine ioTotal_bind (hc.pfSpawn _) fun rSp => ?_
          refine ioTotal_bind (ioTotal_closeOpt hc (some d0)) fun _ => ?_
          refine ioTotal_bind (ioTotal_closeOpt hc (some d1)) fun _ => ?_
          refine ioTotal_bind (ioTotal_closeOpt hc (some d2)) fun _ => ?_
          refine ioTotal_bind (ioTotal_closeOpt hc (some ifd)) fun _ => ?_
          cases rSp with
          | error _ => exact ioTotal_pure _
          | ok child => exact ioTotal_waitProbeExitZero hc child.pid.toInt32 fuel
        refine ioTotal_bind (ioTotal_retryEintr (hc.fstatat none "/etc/ld.so.cache".toUTF8 {}) fuel) fun rLd => ?_
        cases rLd with
        | ok _ => exact ioTotal_bind (ioTotal_pure true) hAfterLd
        | error _ => exact ioTotal_bind (ioTotal_pure false) hAfterLd

end LeanSwe.ProcessSandbox.Raw.Proofs
