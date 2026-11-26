import Core.Obeys
import LeanSwe.ProcessSandbox.Raw.Model.Refines
import LeanSwe.ProcessSandbox.Raw.SysBridge
import LeanSwe.ProcessSandbox.Raw.SysBridge.HostCap
import LeanSwe.ProcessSandbox.Raw.Proofs.HostCgroupPresetProofs
import LeanSwe.ProcessSandbox.Raw.Proofs.HostBwrapProofs
import LeanSwe.ProcessSandbox.Raw.Proofs.HostForwarderStreamProofs

namespace LeanSwe.ProcessSandbox.Raw.Proofs

open LeanSwe.LinuxSyscall
open LeanSwe.ProcessSandbox.Raw
open LeanSwe.ProcessSandbox.Raw.Model
open LeanSwe.ProcessSandbox.Raw.SysBridge
open LeanSwe.ProcessSandbox.Raw.SysBridge.Cgroup
open LeanSwe.ProcessSandbox.Raw.SysBridge.Preset
open LeanSwe.ProcessSandbox.Raw.SysBridge.Bwrap
open LeanSwe.ProcessSandbox.Raw.SysBridge.PipeIo
open LeanSwe.ProcessSandbox.Raw.SysBridge.StreamIo

/-- Predicate stating that `act` preserves `proj w` from any well-formed state `w`. -/
def PreservesProj {W α : Type} (proj : W → RawHostWorld) (act : StateM W α) : Prop :=
  ∀ w, rawHostWorldWf (proj w) = true → proj (act.run w).2 = proj w

/-- Run-level reduction for `StateM` bind. -/
theorem stateM_bind_run {W α β : Type} (ma : StateM W α) (k : α → StateM W β) (w : W) :
    (ma >>= k).run w = (k (ma.run w).1).run (ma.run w).2 := by
  change (match ma.run w with | (a, s) => (k a).run s) = _
  cases ma.run w; rfl

/-- Run-level reduction for `StateM` map. -/
theorem stateM_map_run {W α β : Type} (f : α → β) (ma : StateM W α) (w : W) :
    (f <$> ma).run w = (f (ma.run w).1, (ma.run w).2) := by
  change (match ma.run w with | (a, s) => (f a, s)) = _
  cases ma.run w; rfl

/-- Run-level reduction for `StateM` seqRight. -/
theorem stateM_seqRight_run {W α β : Type} (ma : StateM W α) (mb : StateM W β) (w : W) :
    (ma *> mb).run w = mb.run (ma.run w).2 := by
  change (match ma.run w with | (_, s) => mb.run s) = _
  cases ma.run w; rfl

/-- Run-level reduction for `StateM` pure. -/
theorem stateM_pure_run {W α : Type} (a : α) (w : W) :
    (pure a : StateM W α).run w = (a, w) := rfl

/-- Pure actions preserve `proj`. -/
theorem preservesProj_pure {W α : Type} {proj : W → RawHostWorld} (a : α) :
    PreservesProj proj (pure a : StateM W α) :=
  fun _ _ => rfl

/-- Conditional of `proj`-preserving actions preserves `proj`. -/
theorem preservesProj_ite {W α : Type} {proj : W → RawHostWorld} {c : Prop} [Decidable c]
    {t e : StateM W α} (ht : PreservesProj proj t) (he : PreservesProj proj e) :
    PreservesProj proj (if c then t else e) := by
  by_cases hc : c
  · simp [hc, ht]
  · simp [hc, he]

/-- Bind of `proj`-preserving actions preserves `proj`. -/
theorem preservesProj_bind {W α β : Type} {proj : W → RawHostWorld}
    {ma : StateM W α} {k : α → StateM W β}
    (ha : PreservesProj proj ma) (hk : ∀ a, PreservesProj proj (k a)) :
    PreservesProj proj (ma >>= k) := by
  intro w hWf
  have h1 := ha w hWf
  have hWf1 : rawHostWorldWf (proj (ma.run w).2) = true := by rw [h1]; exact hWf
  have h2 := hk (ma.run w).1 (ma.run w).2 hWf1
  change proj (match ma.run w with | (a, s) => (k a).run s).2 = proj w
  rcases hR : ma.run w with ⟨a, s⟩
  rw [hR] at h1 h2
  exact h2.trans h1

/-- Extract `PreservesProj` from a `StateM` action sequenced with `pure RawCapStepOut.unit`. -/
theorem preservesProj_of_seqUnit {W α : Type} {proj : W → RawHostWorld}
    (act : StateM W α)
    (h : ∀ w, rawHostWorldWf (proj w) = true →
      proj ((act *> pure RawCapStepOut.unit).run w).2 = proj w) :
    PreservesProj proj act := by
  intro w hWf
  have hw := h w hWf
  change proj (match act.run w with | (_, s) => (RawCapStepOut.unit, s)).2 = proj w at hw
  rcases hR : act.run w with ⟨a, s⟩
  rw [hR] at hw
  exact hw

/-- Capability-preservation bundle stating that every `HostSysDepsM (StateM W) fd fwdTask` operation
    consumed by `SysBridge` preserves `proj w` from any `rawHostWorldWf`-valid state and matches `(isLinux, target)`. -/
structure DepsPreservesProj {W fd fwdTask : Type} (proj : W → RawHostWorld)
    (deps : HostSysDepsM (StateM W) fd fwdTask) : Prop where
  /-- Platform identity `(isLinux, target)` matches `proj w` at well-formed states. -/
  metaInfo : ∀ w, rawHostWorldWf (proj w) = true →
    deps.isLinux = (proj w).isLinux ∧ deps.target = (proj w).target
  /-- `files.openat` preserves `proj`. -/
  filesOpenat : ∀ d p fl m, PreservesProj proj (deps.files.openat d p fl m)
  /-- `files.close` preserves `proj`. -/
  filesClose : ∀ h, PreservesProj proj (deps.files.close h)
  /-- `files.read` preserves `proj`. -/
  filesRead : ∀ h n, PreservesProj proj (deps.files.read h n)
  /-- `files.write` preserves `proj`. -/
  filesWrite : ∀ h bs, PreservesProj proj (deps.files.write h bs)
  /-- `files.fstatat` preserves `proj`. -/
  filesFstatat : ∀ d p fl, PreservesProj proj (deps.files.fstatat d p fl)
  /-- `files.faccessat` preserves `proj`. -/
  filesFaccessat : ∀ d p mk fl, PreservesProj proj (deps.files.faccessat d p mk fl)
  /-- `files.mkdirat` preserves `proj`. -/
  filesMkdirat : ∀ d p m, PreservesProj proj (deps.files.mkdirat d p m)
  /-- `files.unlinkat` preserves `proj`. -/
  filesUnlinkat : ∀ d p rm, PreservesProj proj (deps.files.unlinkat d p rm)
  /-- `files.readlinkat` preserves `proj`. -/
  filesReadlinkat : ∀ d p c, PreservesProj proj (deps.files.readlinkat d p c)
  /-- `files.fcntl` preserves `proj`. -/
  filesFcntl : ∀ h cmd, PreservesProj proj (deps.files.fcntl h cmd)
  /-- `files.reopenReadOnly` preserves `proj`. -/
  filesReopenReadOnly : ∀ h, PreservesProj proj (deps.files.reopenReadOnly h)
  /-- `net.socketpair` preserves `proj`. -/
  netSocketpair : ∀ dom st fl, PreservesProj proj (deps.net.socketpair dom st fl)
  /-- `net.recvmsg` preserves `proj`. -/
  netRecvmsg : ∀ h mf, PreservesProj proj (deps.net.recvmsg h mf)
  /-- `poll.ppoll` preserves `proj`. -/
  pollPpoll : ∀ es ts, PreservesProj proj (deps.poll.ppoll es ts)
  /-- `proc.pipe2` preserves `proj`. -/
  procPipe2 : ∀ fl, PreservesProj proj (deps.proc.pipe2 fl)
  /-- `proc.waitpid` preserves `proj`. -/
  procWaitpid : ∀ pid fl, PreservesProj proj (deps.proc.waitpid pid fl)
  /-- `proc.kill` preserves `proj`. -/
  procKill : ∀ pid sig, PreservesProj proj (deps.proc.kill pid sig)
  /-- `proc.pidfd_open` preserves `proj`. -/
  procPidfdOpen : ∀ pid fl, PreservesProj proj (deps.proc.pidfd_open pid fl)
  /-- `proc.pidfd_send_signal` preserves `proj`. -/
  procPidfdSendSignal : ∀ h sig fl, PreservesProj proj (deps.proc.pidfd_send_signal h sig fl)
  /-- `proc.getpid` preserves `proj`. -/
  procGetpid : PreservesProj proj deps.proc.getpid
  /-- `proc.getuid` preserves `proj`. -/
  procGetuid : PreservesProj proj deps.proc.getuid
  /-- `sandbox.landlockCreateRuleset` preserves `proj`. -/
  sandboxLandlockCreateRuleset : ∀ a fl, PreservesProj proj (deps.sandbox.landlockCreateRuleset a fl)
  /-- `sandbox.seccomp` preserves `proj`. -/
  sandboxSeccomp : ∀ op fl bs, PreservesProj proj (deps.sandbox.seccomp op fl bs)
  /-- `sandbox.memfdCreate` preserves `proj`. -/
  sandboxMemfdCreate : ∀ nm fl, PreservesProj proj (deps.sandbox.memfdCreate nm fl)
  /-- `timeRand.clock_gettime` preserves `proj`. -/
  timeRandClockGettime : ∀ clk, PreservesProj proj (deps.timeRand.clock_gettime clk)
  /-- `timeRand.clock_nanosleep` preserves `proj`. -/
  timeRandClockNanosleep : ∀ clk a ts, PreservesProj proj (deps.timeRand.clock_nanosleep clk a ts)
  /-- `passwd.getpwuid` preserves `proj`. -/
  passwdGetpwuid : ∀ uid, PreservesProj proj (deps.passwd.getpwuid uid)
  /-- `postFork.spawn` preserves `proj`. -/
  postForkSpawn : ∀ sp, PreservesProj proj (deps.postFork.spawn sp)
  /-- `postFork.spawnWithBarrier` preserves `proj`. -/
  postForkSpawnWithBarrier : ∀ sp, PreservesProj proj (deps.postFork.spawnWithBarrier sp)
  /-- `postFork.releaseBarrier` preserves `proj`. -/
  postForkReleaseBarrier : ∀ p, PreservesProj proj (deps.postFork.releaseBarrier p)
  /-- `postFork.abortBarrier` preserves `proj`. -/
  postForkAbortBarrier : ∀ p, PreservesProj proj (deps.postFork.abortBarrier p)
  /-- `getEnvPath` preserves `proj`. -/
  getEnvPath : PreservesProj proj deps.getEnvPath
  /-- `getEnvHome` preserves `proj`. -/
  getEnvHome : PreservesProj proj deps.getEnvHome
  /-- `startFwdTask` preserves `proj`. -/
  startFwdTask : ∀ fds ps, PreservesProj proj (deps.startFwdTask fds ps)
  /-- `stopFwdTask` preserves `proj`. -/
  stopFwdTask : ∀ th, PreservesProj proj (deps.stopFwdTask th)

/-- Bridge `ObeysStep` on `RawHostCapM` to `DepsPreservesProj` on `toHostSysDeps cap`. -/
theorem depsPreservesProj_toHostSysDeps {W : Type} {proj : W → RawHostWorld}
    {cap : RawHostCapM (StateM W)}
    (hCap : Core.ObeysStep proj rawHostWorldWf (execRawCapStep cap) allowedRawCapStep) :
    DepsPreservesProj proj (toHostSysDeps cap) where
  metaInfo w hWf := by
    have h := (hCap w .metaInfo hWf).1
    simpa only [execRawCapStep, stateM_pure_run, RawCapStepOut.metaInfo.injEq, toHostSysDeps] using h
  filesOpenat d p fl m := preservesProj_of_seqUnit _ fun w hWf => (hCap w (.filesOpenat d p fl m) hWf).2
  filesClose h := preservesProj_of_seqUnit _ fun w hWf => (hCap w (.filesClose h) hWf).2
  filesRead h n := preservesProj_of_seqUnit _ fun w hWf => (hCap w (.filesRead h n) hWf).2
  filesWrite h bs := preservesProj_of_seqUnit _ fun w hWf => (hCap w (.filesWrite h bs) hWf).2
  filesFstatat d p fl := preservesProj_of_seqUnit _ fun w hWf => (hCap w (.filesFstatat d p fl) hWf).2
  filesFaccessat d p mk fl := preservesProj_of_seqUnit _ fun w hWf => (hCap w (.filesFaccessat d p mk fl) hWf).2
  filesMkdirat d p m := preservesProj_of_seqUnit _ fun w hWf => (hCap w (.filesMkdirat d p m) hWf).2
  filesUnlinkat d p rm := preservesProj_of_seqUnit _ fun w hWf => (hCap w (.filesUnlinkat d p rm) hWf).2
  filesReadlinkat d p c := preservesProj_of_seqUnit _ fun w hWf => (hCap w (.filesReadlinkat d p c) hWf).2
  filesFcntl h cmd := preservesProj_of_seqUnit _ fun w hWf => (hCap w (.filesFcntl h cmd) hWf).2
  filesReopenReadOnly h := preservesProj_of_seqUnit _ fun w hWf => (hCap w (.filesReopenReadOnly h) hWf).2
  netSocketpair dom st fl := preservesProj_of_seqUnit _ fun w hWf => (hCap w (.netSocketpair dom st fl) hWf).2
  netRecvmsg h mf := preservesProj_of_seqUnit _ fun w hWf => (hCap w (.netRecvmsg h mf) hWf).2
  pollPpoll es ts := preservesProj_of_seqUnit _ fun w hWf => (hCap w (.pollPpoll es ts) hWf).2
  procPipe2 fl := preservesProj_of_seqUnit _ fun w hWf => (hCap w (.procPipe2 fl) hWf).2
  procWaitpid pid fl := preservesProj_of_seqUnit _ fun w hWf => (hCap w (.procWaitpid pid fl) hWf).2
  procKill pid sig := preservesProj_of_seqUnit _ fun w hWf => (hCap w (.procKill pid sig) hWf).2
  procPidfdOpen pid fl := preservesProj_of_seqUnit _ fun w hWf => (hCap w (.procPidfdOpen pid fl) hWf).2
  procPidfdSendSignal h sig fl := preservesProj_of_seqUnit _ fun w hWf => (hCap w (.procPidfdSendSignal h sig fl) hWf).2
  procGetpid := preservesProj_of_seqUnit _ fun w hWf => (hCap w .procGetpid hWf).2
  procGetuid := preservesProj_of_seqUnit _ fun w hWf => (hCap w .procGetuid hWf).2
  sandboxLandlockCreateRuleset a fl := preservesProj_of_seqUnit _ fun w hWf => (hCap w (.sandboxLandlockCreateRuleset a fl) hWf).2
  sandboxSeccomp op fl bs := preservesProj_of_seqUnit _ fun w hWf => (hCap w (.sandboxSeccomp op fl bs) hWf).2
  sandboxMemfdCreate nm fl := preservesProj_of_seqUnit _ fun w hWf => (hCap w (.sandboxMemfdCreate nm fl) hWf).2
  timeRandClockGettime clk := preservesProj_of_seqUnit _ fun w hWf => (hCap w (.timeRandClockGettime clk) hWf).2
  timeRandClockNanosleep clk a ts := preservesProj_of_seqUnit _ fun w hWf => (hCap w (.timeRandClockNanosleep clk a ts) hWf).2
  passwdGetpwuid uid := preservesProj_of_seqUnit _ fun w hWf => (hCap w (.passwdGetpwuid uid) hWf).2
  postForkSpawn sp := preservesProj_of_seqUnit _ fun w hWf => (hCap w (.postForkSpawn sp) hWf).2
  postForkSpawnWithBarrier sp := preservesProj_of_seqUnit _ fun w hWf => (hCap w (.postForkSpawnWithBarrier sp) hWf).2
  postForkReleaseBarrier p := preservesProj_of_seqUnit _ fun w hWf => (hCap w (.postForkReleaseBarrier p) hWf).2
  postForkAbortBarrier p := preservesProj_of_seqUnit _ fun w hWf => (hCap w (.postForkAbortBarrier p) hWf).2
  getEnvPath := preservesProj_of_seqUnit _ fun w hWf => (hCap w .getEnvPath hWf).2
  getEnvHome := preservesProj_of_seqUnit _ fun w hWf => (hCap w .getEnvHome hWf).2
  startFwdTask fds ps := preservesProj_of_seqUnit _ fun w hWf => (hCap w (.startFwdTask fds ps) hWf).2
  stopFwdTask th := preservesProj_of_seqUnit _ fun w hWf => (hCap w (.stopFwdTask th) hWf).2

/-- `retryEintr` preserves `proj` whenever the underlying syscall action preserves `proj`. -/
theorem preservesProj_retryEintr {W α : Type} {proj : W → RawHostWorld}
    (act : StateM W (Except Errno α)) (hact : PreservesProj proj act) :
    ∀ fuel, PreservesProj proj (retryEintr act fuel)
  | 0 => hact
  | fuel + 1 => by
    unfold retryEintr
    refine preservesProj_bind hact fun res => ?_
    cases res with
    | ok _ => exact preservesProj_pure _
    | error _ =>
      exact preservesProj_ite (preservesProj_retryEintr act hact fuel) (preservesProj_pure _)

/-- `List.forIn` preserves `proj` and propagates invariant `Inv` across list elements. -/
theorem forIn_list_preservesProj_inv {W α β : Type} {proj : W → RawHostWorld}
    (Inv : β → Prop) (body : α → β → StateM W (ForInStep β))
    (hStep : ∀ x acc, Inv acc →
      PreservesProj proj (body x acc) ∧
      ∀ w, rawHostWorldWf (proj w) = true →
        match ((body x acc).run w).1 with
        | .done b => Inv b
        | .yield b => Inv b) :
    ∀ (xs : List α) (acc : β), Inv acc →
      PreservesProj proj (forIn xs acc body) ∧
      ∀ w, rawHostWorldWf (proj w) = true → Inv ((forIn xs acc body).run w).1
  | [], acc, hInv => ⟨preservesProj_pure acc, fun _ _ => hInv⟩
  | x :: rest, acc, hInv => by
    have ⟨hP1, hI1⟩ := hStep x acc hInv
    constructor
    · intro w hWf
      rw [List.forIn_cons]
      have h1 := hP1 w hWf
      have hWf1 : rawHostWorldWf (proj ((body x acc).run w).2) = true := by rw [h1]; exact hWf
      have hInv1 := hI1 w hWf
      change proj (match (body x acc).run w with
        | (a, s) => (match a with | .done b => pure b | .yield b => forIn rest b body).run s).2 = proj w
      rcases hR : (body x acc).run w with ⟨st, s⟩
      rw [hR] at h1 hWf1 hInv1
      cases st with
      | done b => exact h1
      | yield b =>
        have hP2 := (forIn_list_preservesProj_inv Inv body hStep rest b hInv1).1 s hWf1
        exact hP2.trans h1
    · intro w hWf
      rw [List.forIn_cons]
      have h1 := hP1 w hWf
      have hWf1 : rawHostWorldWf (proj ((body x acc).run w).2) = true := by rw [h1]; exact hWf
      have hInv1 := hI1 w hWf
      change Inv (match (body x acc).run w with
        | (a, s) => (match a with | .done b => pure b | .yield b => forIn rest b body).run s).1
      rcases hR : (body x acc).run w with ⟨st, s⟩
      rw [hR] at hWf1 hInv1
      cases st with
      | done b => exact hInv1
      | yield b =>
        exact (forIn_list_preservesProj_inv Inv body hStep rest b hInv1).2 s hWf1

/-- `Array.forIn` preserves `proj` and propagates invariant `Inv` across array elements. -/
theorem forIn_array_preservesProj_inv {W α β : Type} {proj : W → RawHostWorld}
    (Inv : β → Prop) (body : α → β → StateM W (ForInStep β))
    (arr : Array α) (acc : β) (hInv : Inv acc)
    (hStep : ∀ x ∈ arr.toList, ∀ b, Inv b →
      PreservesProj proj (body x b) ∧
      ∀ w, rawHostWorldWf (proj w) = true →
        match ((body x b).run w).1 with
        | .done b' => Inv b'
        | .yield b' => Inv b') :
    PreservesProj proj (forIn arr acc body) ∧
    ∀ w, rawHostWorldWf (proj w) = true → Inv ((forIn arr acc body).run w).1 := by
  rw [← Array.forIn_toList]
  suffices ∀ (xs : List α), (∀ x ∈ xs, x ∈ arr.toList) → ∀ b, Inv b →
      PreservesProj proj (forIn xs b body) ∧
      ∀ w, rawHostWorldWf (proj w) = true → Inv ((forIn xs b body).run w).1 from
    this arr.toList (fun _ h => h) acc hInv
  intro xs hSub
  induction xs with
  | nil => intro b hb; exact ⟨preservesProj_pure b, fun _ _ => hb⟩
  | cons x rest ih =>
    intro b hb
    have hx : x ∈ arr.toList := hSub x (List.mem_cons_self ..)
    have hRestSub : ∀ y ∈ rest, y ∈ arr.toList := fun y hy => hSub y (List.mem_cons_of_mem x hy)
    have ⟨hP1, hI1⟩ := hStep x hx b hb
    constructor
    · intro w hWf
      rw [List.forIn_cons]
      have h1 := hP1 w hWf
      have hWf1 : rawHostWorldWf (proj ((body x b).run w).2) = true := by rw [h1]; exact hWf
      have hInv1 := hI1 w hWf
      change proj (match (body x b).run w with
        | (a, s) => (match a with | .done b' => pure b' | .yield b' => forIn rest b' body).run s).2 = proj w
      rcases hR : (body x b).run w with ⟨st, s⟩
      rw [hR] at h1 hWf1 hInv1
      cases st with
      | done b' => exact h1
      | yield b' =>
        have hP2 := (ih hRestSub b' hInv1).1 s hWf1
        exact hP2.trans h1
    · intro w hWf
      rw [List.forIn_cons]
      have h1 := hP1 w hWf
      have hWf1 : rawHostWorldWf (proj ((body x b).run w).2) = true := by rw [h1]; exact hWf
      have hInv1 := hI1 w hWf
      change Inv (match (body x b).run w with
        | (a, s) => (match a with | .done b' => pure b' | .yield b' => forIn rest b' body).run s).1
      rcases hR : (body x b).run w with ⟨st, s⟩
      rw [hR] at hWf1 hInv1
      cases st with
      | done b' => exact hInv1
      | yield b' =>
        exact (ih hRestSub b' hInv1).2 s hWf1

/-- `Files.closeOpt` preserves `proj`. -/
theorem preservesProj_closeOpt {W fd fwdTask : Type} {proj : W → RawHostWorld}
    {deps : HostSysDepsM (StateM W) fd fwdTask}
    (hDeps : DepsPreservesProj proj deps) (fd? : Option fd) :
    PreservesProj proj (Files.closeOpt deps.files fd?) := by
  cases fd? with
  | none => exact preservesProj_pure ()
  | some h =>
    unfold Files.closeOpt
    exact preservesProj_bind (hDeps.filesClose h) (fun _ => preservesProj_pure ())

/-- `Files.setNonblockingOpt` preserves `proj`. -/
theorem preservesProj_setNonblockingOpt {W fd fwdTask : Type} {proj : W → RawHostWorld}
    {deps : HostSysDepsM (StateM W) fd fwdTask}
    (hDeps : DepsPreservesProj proj deps) (fd? : Option fd) :
    PreservesProj proj (Files.setNonblockingOpt deps.files fd?) := by
  cases fd? with
  | none => exact preservesProj_pure ()
  | some h =>
    unfold Files.setNonblockingOpt
    exact preservesProj_bind (hDeps.filesFcntl h (.setFl true false)) (fun _ => preservesProj_pure ())

/-- `closeFdArray` preserves `proj`. -/
theorem preservesProj_closeFdArray {W fd fwdTask : Type} {proj : W → RawHostWorld}
    {deps : HostSysDepsM (StateM W) fd fwdTask}
    (hDeps : DepsPreservesProj proj deps) (fds : Array fd) :
    PreservesProj proj (closeFdArray deps.files fds) := by
  unfold closeFdArray
  exact (forIn_array_preservesProj_inv (fun _ => True) _ fds () trivial fun h _ _ _ =>
    ⟨preservesProj_bind (preservesProj_closeOpt hDeps (some h)) (fun _ => preservesProj_pure _),
     fun _ _ => trivial⟩).1

/-- `writeAllFd` preserves `proj`. -/
theorem preservesProj_writeAllFd {W fd fwdTask : Type} {proj : W → RawHostWorld}
    {deps : HostSysDepsM (StateM W) fd fwdTask}
    (hDeps : DepsPreservesProj proj deps) (h : fd) (data : ByteArray) :
    ∀ off fuel, PreservesProj proj (writeAllFd deps.files h data off fuel)
  | _, 0 => by unfold writeAllFd; exact preservesProj_ite (preservesProj_pure _) (preservesProj_pure _)
  | off, fuel + 1 => by
    unfold writeAllFd
    refine preservesProj_ite (preservesProj_pure _) ?_
    refine preservesProj_bind (hDeps.filesWrite h _) fun res => ?_
    cases res with
    | ok _ =>
      exact preservesProj_ite (preservesProj_pure _) (preservesProj_writeAllFd hDeps h data _ fuel)
    | error _ =>
      exact preservesProj_ite (preservesProj_writeAllFd hDeps h data off fuel) (preservesProj_pure _)

/-- `writeTextFile` preserves `proj`. -/
theorem preservesProj_writeTextFile {W fd fwdTask : Type} {proj : W → RawHostWorld}
    {deps : HostSysDepsM (StateM W) fd fwdTask}
    (hDeps : DepsPreservesProj proj deps) (path text : String) (fuel : Nat) :
    PreservesProj proj (writeTextFile deps.files path text fuel) := by
  unfold writeTextFile
  refine preservesProj_bind
    (preservesProj_retryEintr _ (hDeps.filesOpenat none path.toUTF8 _ 0) fuel) fun r => ?_
  cases r with
  | error _ => exact preservesProj_pure _
  | ok h =>
    refine preservesProj_bind (preservesProj_writeAllFd hDeps h text.toUTF8 0 fuel) fun res => ?_
    exact preservesProj_bind (preservesProj_closeOpt hDeps (some h)) (fun _ => preservesProj_pure res)

/-- `readBoundedLoop` preserves `proj`. -/
theorem preservesProj_readBoundedLoop {W fd fwdTask : Type} {proj : W → RawHostWorld}
    {deps : HostSysDepsM (StateM W) fd fwdTask}
    (hDeps : DepsPreservesProj proj deps) (h : fd) (maxBytes : Nat) :
    ∀ chunks total fuel, PreservesProj proj (readBoundedLoop deps.files h maxBytes chunks total fuel)
  | _, _, 0 => preservesProj_pure _
  | chunks, total, fuel + 1 => by
    unfold readBoundedLoop
    refine preservesProj_ite (preservesProj_pure _) ?_
    refine preservesProj_bind (hDeps.filesRead h _) fun r => ?_
    cases r with
    | ok _ =>
      exact preservesProj_ite (preservesProj_pure _) (preservesProj_readBoundedLoop hDeps h maxBytes _ _ fuel)
    | error _ =>
      exact preservesProj_ite (preservesProj_readBoundedLoop hDeps h maxBytes chunks total fuel) (preservesProj_pure _)

/-- `readSmallFile` preserves `proj`. -/
theorem preservesProj_readSmallFile {W fd fwdTask : Type} {proj : W → RawHostWorld}
    {deps : HostSysDepsM (StateM W) fd fwdTask}
    (hDeps : DepsPreservesProj proj deps) (path : String) (maxBytes fuel : Nat) :
    PreservesProj proj (readSmallFile deps.files path maxBytes fuel) := by
  unfold readSmallFile
  refine preservesProj_bind
    (preservesProj_retryEintr _ (hDeps.filesOpenat none path.toUTF8 _ 0) fuel) fun r => ?_
  cases r with
  | error _ => exact preservesProj_pure _
  | ok h =>
    refine preservesProj_bind (preservesProj_readBoundedLoop hDeps h maxBytes #[] 0 fuel) fun res => ?_
    exact preservesProj_bind (preservesProj_closeOpt hDeps (some h)) (fun _ => preservesProj_pure res)

/-- `findDelegatedCgroupParent` preserves `proj`. -/
theorem preservesProj_findDelegatedCgroupParent {W fd fwdTask : Type} {proj : W → RawHostWorld}
    {deps : HostSysDepsM (StateM W) fd fwdTask}
    (hDeps : DepsPreservesProj proj deps) (fuel : Nat) :
    PreservesProj proj (findDelegatedCgroupParent deps.files fuel) := by
  unfold findDelegatedCgroupParent
  refine preservesProj_bind (preservesProj_readSmallFile hDeps "/proc/self/cgroup" CGROUP_READ_CAP fuel) fun r => ?_
  cases r with
  | error _ => exact preservesProj_pure _
  | ok raw =>
    dsimp only
    cases String.fromUTF8? raw with
    | none => exact preservesProj_pure _
    | some text =>
      dsimp only
      cases parseDelegatedCgroupParent text <;> exact preservesProj_pure _

/-- `createSiblingCgroup` preserves `proj`. -/
theorem preservesProj_createSiblingCgroup {W fd fwdTask : Type} {proj : W → RawHostWorld}
    {deps : HostSysDepsM (StateM W) fd fwdTask}
    (hDeps : DepsPreservesProj proj deps) (pid : UInt32) (seq fuel : Nat) :
    PreservesProj proj (createSiblingCgroup deps.files pid seq fuel) := by
  unfold createSiblingCgroup
  refine preservesProj_bind (preservesProj_findDelegatedCgroupParent hDeps fuel) fun r => ?_
  cases r with
  | error _ => exact preservesProj_pure _
  | ok _ =>
    refine preservesProj_bind
      (preservesProj_retryEintr _ (hDeps.filesMkdirat none _ 0o755) fuel) fun mr => ?_
    cases mr <;> exact preservesProj_pure _

/-- `configureCgroupMemory` preserves `proj`. -/
theorem preservesProj_configureCgroupMemory {W fd fwdTask : Type} {proj : W → RawHostWorld}
    {deps : HostSysDepsM (StateM W) fd fwdTask}
    (hDeps : DepsPreservesProj proj deps) (cgDir memLimit : String) (fuel : Nat) :
    PreservesProj proj (configureCgroupMemory deps.files cgDir memLimit fuel) := by
  have hOom : PreservesProj proj ((do
      match ← writeTextFile deps.files (cgroupSubfile cgDir "memory.oom.group") "1" fuel with
      | .error e =>
        if e != Errno.ENOENT then
          return .error ("memory.oom.group", e)
      | .ok () => pure ()
      return .ok ()) : StateM W (Except (String × Errno) Unit)) := by
    refine preservesProj_bind (preservesProj_writeTextFile hDeps _ "1" fuel) fun r3 => ?_
    cases r3 with
    | ok _ => exact preservesProj_pure _
    | error _ => exact preservesProj_ite (preservesProj_pure _) (preservesProj_pure _)
  unfold configureCgroupMemory
  refine preservesProj_bind (preservesProj_writeTextFile hDeps _ memLimit fuel) fun r1 => ?_
  cases r1 with
  | error _ => exact preservesProj_pure _
  | ok _ =>
    refine preservesProj_bind (preservesProj_writeTextFile hDeps _ "0" fuel) fun r2 => ?_
    cases r2 with
    | error _ => exact preservesProj_ite (preservesProj_pure _) hOom
    | ok _ => exact hOom

/-- `TimeRand.sleepMonoMs` preserves `proj`. -/
theorem preservesProj_sleepMonoMs {W fd fwdTask : Type} {proj : W → RawHostWorld}
    {deps : HostSysDepsM (StateM W) fd fwdTask}
    (hDeps : DepsPreservesProj proj deps) (ms : Nat) :
    PreservesProj proj (TimeRand.sleepMonoMs deps.timeRand ms) := by
  unfold TimeRand.sleepMonoMs
  exact preservesProj_bind (hDeps.timeRandClockNanosleep .monotonic false _)
    (fun _ => preservesProj_pure ())

/-- `pollCgroupUnpopulated` preserves `proj`. -/
theorem preservesProj_pollCgroupUnpopulated {W fd fwdTask : Type} {proj : W → RawHostWorld}
    {deps : HostSysDepsM (StateM W) fd fwdTask}
    (hDeps : DepsPreservesProj proj deps) (eventsPath : String) (fuel : Nat) :
    ∀ steps, PreservesProj proj (pollCgroupUnpopulated deps.files deps.timeRand eventsPath fuel steps)
  | 0 => preservesProj_pure ()
  | steps + 1 => by
    unfold pollCgroupUnpopulated
    refine preservesProj_bind (preservesProj_readSmallFile hDeps eventsPath 256 fuel) fun r => ?_
    cases r with
    | error _ => exact preservesProj_pure ()
    | ok raw =>
      dsimp only
      have hSleepNext : PreservesProj proj (do
          TimeRand.sleepMonoMs deps.timeRand CGROUP_RETRY_SLEEP_MS
          pollCgroupUnpopulated deps.files deps.timeRand eventsPath fuel steps) :=
        preservesProj_bind (preservesProj_sleepMonoMs hDeps CGROUP_RETRY_SLEEP_MS)
          (fun _ => preservesProj_pollCgroupUnpopulated hDeps eventsPath fuel steps)
      cases String.fromUTF8? raw with
      | none => exact hSleepNext
      | some _ => exact preservesProj_ite (preservesProj_pure ()) hSleepNext

/-- `retryRmdirCgroup` preserves `proj`. -/
theorem preservesProj_retryRmdirCgroup {W fd fwdTask : Type} {proj : W → RawHostWorld}
    {deps : HostSysDepsM (StateM W) fd fwdTask}
    (hDeps : DepsPreservesProj proj deps) (cgBytes : ByteArray) :
    ∀ steps, PreservesProj proj (retryRmdirCgroup deps.files deps.timeRand cgBytes steps)
  | 0 => by
    unfold retryRmdirCgroup
    refine preservesProj_bind (hDeps.filesUnlinkat none cgBytes true) fun r => ?_
    cases r with
    | ok _ => exact preservesProj_pure _
    | error _ => exact preservesProj_ite (preservesProj_pure _) (preservesProj_pure _)
  | steps + 1 => by
    unfold retryRmdirCgroup
    refine preservesProj_bind (hDeps.filesUnlinkat none cgBytes true) fun r => ?_
    cases r with
    | ok _ => exact preservesProj_pure _
    | error _ =>
      refine preservesProj_ite (preservesProj_pure _) ?_
      refine preservesProj_ite ?_ (preservesProj_pure _)
      exact preservesProj_bind (preservesProj_sleepMonoMs hDeps CGROUP_RETRY_SLEEP_MS)
        (fun _ => preservesProj_retryRmdirCgroup hDeps cgBytes steps)

/-- `cleanupCgroupDir` preserves `proj`. -/
theorem preservesProj_cleanupCgroupDir {W fd fwdTask : Type} {proj : W → RawHostWorld}
    {deps : HostSysDepsM (StateM W) fd fwdTask}
    (hDeps : DepsPreservesProj proj deps) (cgDir : String) (pSteps rSteps fuel : Nat) :
    PreservesProj proj (cleanupCgroupDir deps.files deps.timeRand cgDir pSteps rSteps fuel) := by
  unfold cleanupCgroupDir
  refine preservesProj_ite (preservesProj_pure _) ?_
  refine preservesProj_bind (preservesProj_writeTextFile hDeps _ "1" fuel) fun _ => ?_
  refine preservesProj_bind (preservesProj_pollCgroupUnpopulated hDeps _ fuel pSteps) fun _ => ?_
  exact preservesProj_retryRmdirCgroup hDeps cgDir.toUTF8 rSteps

end LeanSwe.ProcessSandbox.Raw.Proofs
