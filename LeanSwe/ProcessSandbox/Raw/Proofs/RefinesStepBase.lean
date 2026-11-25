import Core.Refines
import LeanSwe.ProcessSandbox.Raw.Model.Refines
import LeanSwe.ProcessSandbox.Raw.SysBridge
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

/-- Cap-step preservation extractor for `files.close`. -/
theorem cap_files_close_preserves {W : Type} {proj : W → RawHostWorld} {cap : RawHostCapM (StateM W)}
    (hCap : Core.RefinesStep proj rawHostWorldWf (execRawCapStep cap) allowedRawCapStep) (fd : Nat) :
    PreservesProj proj (cap.files.close fd) :=
  preservesProj_of_seqUnit _ fun w hWf => (hCap w (.filesClose fd) hWf).2

/-- `Files.closeOpt` preserves `proj`. -/
theorem preservesProj_closeOpt {W : Type} {proj : W → RawHostWorld} {cap : RawHostCapM (StateM W)}
    (hCap : Core.RefinesStep proj rawHostWorldWf (execRawCapStep cap) allowedRawCapStep) (fd? : Option Nat) :
    PreservesProj proj (Files.closeOpt cap.files fd?) := by
  cases fd? with
  | none => exact preservesProj_pure ()
  | some fd =>
    unfold Files.closeOpt
    exact preservesProj_bind (cap_files_close_preserves hCap fd) (fun _ => preservesProj_pure ())

/-- `Files.setNonblockingOpt` preserves `proj`. -/
theorem preservesProj_setNonblockingOpt {W : Type} {proj : W → RawHostWorld} {cap : RawHostCapM (StateM W)}
    (hCap : Core.RefinesStep proj rawHostWorldWf (execRawCapStep cap) allowedRawCapStep) (fd? : Option Nat) :
    PreservesProj proj (Files.setNonblockingOpt cap.files fd?) := by
  cases fd? with
  | none => exact preservesProj_pure ()
  | some fd =>
    unfold Files.setNonblockingOpt
    exact preservesProj_bind
      (preservesProj_of_seqUnit _ fun w hWf => (hCap w (.filesFcntl fd (.setFl true false)) hWf).2)
      (fun _ => preservesProj_pure ())

/-- `closeFdArray` preserves `proj`. -/
theorem preservesProj_closeFdArray {W : Type} {proj : W → RawHostWorld} {cap : RawHostCapM (StateM W)}
    (hCap : Core.RefinesStep proj rawHostWorldWf (execRawCapStep cap) allowedRawCapStep) (fds : Array Nat) :
    PreservesProj proj (closeFdArray cap.files fds) := by
  unfold closeFdArray
  exact (forIn_array_preservesProj_inv (fun _ => True) _ fds () trivial fun fd _ _ _ =>
    ⟨preservesProj_bind (preservesProj_closeOpt hCap (some fd)) (fun _ => preservesProj_pure _),
     fun _ _ => trivial⟩).1

/-- `writeAllFd` preserves `proj`. -/
theorem preservesProj_writeAllFd {W : Type} {proj : W → RawHostWorld} {cap : RawHostCapM (StateM W)}
    (hCap : Core.RefinesStep proj rawHostWorldWf (execRawCapStep cap) allowedRawCapStep)
    (h : Nat) (data : ByteArray) :
    ∀ off fuel, PreservesProj proj (writeAllFd cap.files h data off fuel)
  | off, 0 => by unfold writeAllFd; exact preservesProj_ite (preservesProj_pure _) (preservesProj_pure _)
  | off, fuel + 1 => by
    unfold writeAllFd
    refine preservesProj_ite (preservesProj_pure _) ?_
    refine preservesProj_bind
      (preservesProj_of_seqUnit _ fun w hWf => (hCap w (.filesWrite h _) hWf).2) fun res => ?_
    cases res with
    | ok _ =>
      exact preservesProj_ite (preservesProj_pure _) (preservesProj_writeAllFd hCap h data _ fuel)
    | error _ =>
      exact preservesProj_ite (preservesProj_writeAllFd hCap h data off fuel) (preservesProj_pure _)

/-- `writeTextFile` preserves `proj`. -/
theorem preservesProj_writeTextFile {W : Type} {proj : W → RawHostWorld} {cap : RawHostCapM (StateM W)}
    (hCap : Core.RefinesStep proj rawHostWorldWf (execRawCapStep cap) allowedRawCapStep)
    (path text : String) (fuel : Nat) :
    PreservesProj proj (writeTextFile cap.files path text fuel) := by
  unfold writeTextFile
  refine preservesProj_bind
    (preservesProj_retryEintr _ (preservesProj_of_seqUnit _ fun w hWf => (hCap w (.filesOpenat none path.toUTF8 _ 0) hWf).2) fuel) fun r => ?_
  cases r with
  | error _ => exact preservesProj_pure _
  | ok h =>
    refine preservesProj_bind (preservesProj_writeAllFd hCap h text.toUTF8 0 fuel) fun res => ?_
    exact preservesProj_bind (preservesProj_closeOpt hCap (some h)) (fun _ => preservesProj_pure res)

/-- `readBoundedLoop` preserves `proj`. -/
theorem preservesProj_readBoundedLoop {W : Type} {proj : W → RawHostWorld} {cap : RawHostCapM (StateM W)}
    (hCap : Core.RefinesStep proj rawHostWorldWf (execRawCapStep cap) allowedRawCapStep)
    (h : Nat) (maxBytes : Nat) :
    ∀ chunks total fuel, PreservesProj proj (readBoundedLoop cap.files h maxBytes chunks total fuel)
  | _, _, 0 => preservesProj_pure _
  | chunks, total, fuel + 1 => by
    unfold readBoundedLoop
    refine preservesProj_ite (preservesProj_pure _) ?_
    refine preservesProj_bind
      (preservesProj_of_seqUnit _ fun w hWf => (hCap w (.filesRead h _) hWf).2) fun r => ?_
    cases r with
    | ok _ =>
      exact preservesProj_ite (preservesProj_pure _) (preservesProj_readBoundedLoop hCap h maxBytes _ _ fuel)
    | error _ =>
      exact preservesProj_ite (preservesProj_readBoundedLoop hCap h maxBytes chunks total fuel) (preservesProj_pure _)

/-- `readSmallFile` preserves `proj`. -/
theorem preservesProj_readSmallFile {W : Type} {proj : W → RawHostWorld} {cap : RawHostCapM (StateM W)}
    (hCap : Core.RefinesStep proj rawHostWorldWf (execRawCapStep cap) allowedRawCapStep)
    (path : String) (maxBytes fuel : Nat) :
    PreservesProj proj (readSmallFile cap.files path maxBytes fuel) := by
  unfold readSmallFile
  refine preservesProj_bind
    (preservesProj_retryEintr _ (preservesProj_of_seqUnit _ fun w hWf => (hCap w (.filesOpenat none path.toUTF8 _ 0) hWf).2) fuel) fun r => ?_
  cases r with
  | error _ => exact preservesProj_pure _
  | ok h =>
    refine preservesProj_bind (preservesProj_readBoundedLoop hCap h maxBytes #[] 0 fuel) fun res => ?_
    exact preservesProj_bind (preservesProj_closeOpt hCap (some h)) (fun _ => preservesProj_pure res)

/-- `findDelegatedCgroupParent` preserves `proj`. -/
theorem preservesProj_findDelegatedCgroupParent {W : Type} {proj : W → RawHostWorld} {cap : RawHostCapM (StateM W)}
    (hCap : Core.RefinesStep proj rawHostWorldWf (execRawCapStep cap) allowedRawCapStep)
    (fuel : Nat) :
    PreservesProj proj (findDelegatedCgroupParent cap.files fuel) := by
  unfold findDelegatedCgroupParent
  refine preservesProj_bind (preservesProj_readSmallFile hCap "/proc/self/cgroup" CGROUP_READ_CAP fuel) fun r => ?_
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
theorem preservesProj_createSiblingCgroup {W : Type} {proj : W → RawHostWorld} {cap : RawHostCapM (StateM W)}
    (hCap : Core.RefinesStep proj rawHostWorldWf (execRawCapStep cap) allowedRawCapStep)
    (pid : UInt32) (seq fuel : Nat) :
    PreservesProj proj (createSiblingCgroup cap.files pid seq fuel) := by
  unfold createSiblingCgroup
  refine preservesProj_bind (preservesProj_findDelegatedCgroupParent hCap fuel) fun r => ?_
  cases r with
  | error _ => exact preservesProj_pure _
  | ok _ =>
    refine preservesProj_bind
      (preservesProj_retryEintr _ (preservesProj_of_seqUnit _ fun w hWf => (hCap w (.filesMkdirat none _ 0o755) hWf).2) fuel) fun mr => ?_
    cases mr <;> exact preservesProj_pure _

/-- `configureCgroupMemory` preserves `proj`. -/
theorem preservesProj_configureCgroupMemory {W : Type} {proj : W → RawHostWorld} {cap : RawHostCapM (StateM W)}
    (hCap : Core.RefinesStep proj rawHostWorldWf (execRawCapStep cap) allowedRawCapStep)
    (cgDir memLimit : String) (fuel : Nat) :
    PreservesProj proj (configureCgroupMemory cap.files cgDir memLimit fuel) := by
  have hOom : PreservesProj proj ((do
      match ← writeTextFile cap.files (cgroupSubfile cgDir "memory.oom.group") "1" fuel with
      | .error e =>
        if e != Errno.ENOENT then
          return .error ("memory.oom.group", e)
      | .ok () => pure ()
      return .ok ()) : StateM W (Except (String × Errno) Unit)) := by
    refine preservesProj_bind (preservesProj_writeTextFile hCap _ "1" fuel) fun r3 => ?_
    cases r3 with
    | ok _ => exact preservesProj_pure _
    | error _ => exact preservesProj_ite (preservesProj_pure _) (preservesProj_pure _)
  unfold configureCgroupMemory
  refine preservesProj_bind (preservesProj_writeTextFile hCap _ memLimit fuel) fun r1 => ?_
  cases r1 with
  | error _ => exact preservesProj_pure _
  | ok _ =>
    refine preservesProj_bind (preservesProj_writeTextFile hCap _ "0" fuel) fun r2 => ?_
    cases r2 with
    | error _ => exact preservesProj_ite (preservesProj_pure _) hOom
    | ok _ => exact hOom

/-- `TimeRand.sleepMonoMs` preserves `proj`. -/
theorem preservesProj_sleepMonoMs {W : Type} {proj : W → RawHostWorld} {cap : RawHostCapM (StateM W)}
    (hCap : Core.RefinesStep proj rawHostWorldWf (execRawCapStep cap) allowedRawCapStep) (ms : Nat) :
    PreservesProj proj (TimeRand.sleepMonoMs cap.timeRand ms) := by
  unfold TimeRand.sleepMonoMs
  exact preservesProj_bind
    (preservesProj_of_seqUnit _ fun w hWf => (hCap w (.timeRandClockNanosleep .monotonic false _) hWf).2)
    (fun _ => preservesProj_pure ())

/-- `pollCgroupUnpopulated` preserves `proj`. -/
theorem preservesProj_pollCgroupUnpopulated {W : Type} {proj : W → RawHostWorld} {cap : RawHostCapM (StateM W)}
    (hCap : Core.RefinesStep proj rawHostWorldWf (execRawCapStep cap) allowedRawCapStep)
    (eventsPath : String) (fuel : Nat) :
    ∀ steps, PreservesProj proj (pollCgroupUnpopulated cap.files cap.timeRand eventsPath fuel steps)
  | 0 => preservesProj_pure ()
  | steps + 1 => by
    unfold pollCgroupUnpopulated
    refine preservesProj_bind (preservesProj_readSmallFile hCap eventsPath 256 fuel) fun r => ?_
    cases r with
    | error _ => exact preservesProj_pure ()
    | ok raw =>
      dsimp only
      have hSleepNext : PreservesProj proj (do
          TimeRand.sleepMonoMs cap.timeRand CGROUP_RETRY_SLEEP_MS
          pollCgroupUnpopulated cap.files cap.timeRand eventsPath fuel steps) :=
        preservesProj_bind (preservesProj_sleepMonoMs hCap CGROUP_RETRY_SLEEP_MS)
          (fun _ => preservesProj_pollCgroupUnpopulated hCap eventsPath fuel steps)
      cases String.fromUTF8? raw with
      | none => exact hSleepNext
      | some _ => exact preservesProj_ite (preservesProj_pure ()) hSleepNext

/-- `retryRmdirCgroup` preserves `proj`. -/
theorem preservesProj_retryRmdirCgroup {W : Type} {proj : W → RawHostWorld} {cap : RawHostCapM (StateM W)}
    (hCap : Core.RefinesStep proj rawHostWorldWf (execRawCapStep cap) allowedRawCapStep)
    (cgBytes : ByteArray) :
    ∀ steps, PreservesProj proj (retryRmdirCgroup cap.files cap.timeRand cgBytes steps)
  | 0 => by
    unfold retryRmdirCgroup
    refine preservesProj_bind (preservesProj_of_seqUnit _ fun w hWf => (hCap w (.filesUnlinkat none cgBytes true) hWf).2) fun r => ?_
    cases r with
    | ok _ => exact preservesProj_pure _
    | error _ => exact preservesProj_ite (preservesProj_pure _) (preservesProj_pure _)
  | steps + 1 => by
    unfold retryRmdirCgroup
    refine preservesProj_bind (preservesProj_of_seqUnit _ fun w hWf => (hCap w (.filesUnlinkat none cgBytes true) hWf).2) fun r => ?_
    cases r with
    | ok _ => exact preservesProj_pure _
    | error _ =>
      refine preservesProj_ite (preservesProj_pure _) ?_
      refine preservesProj_ite ?_ (preservesProj_pure _)
      exact preservesProj_bind (preservesProj_sleepMonoMs hCap CGROUP_RETRY_SLEEP_MS)
        (fun _ => preservesProj_retryRmdirCgroup hCap cgBytes steps)

/-- `cleanupCgroupDir` preserves `proj`. -/
theorem preservesProj_cleanupCgroupDir {W : Type} {proj : W → RawHostWorld} {cap : RawHostCapM (StateM W)}
    (hCap : Core.RefinesStep proj rawHostWorldWf (execRawCapStep cap) allowedRawCapStep)
    (cgDir : String) (pSteps rSteps fuel : Nat) :
    PreservesProj proj (cleanupCgroupDir cap.files cap.timeRand cgDir pSteps rSteps fuel) := by
  unfold cleanupCgroupDir
  refine preservesProj_ite (preservesProj_pure _) ?_
  refine preservesProj_bind (preservesProj_writeTextFile hCap _ "1" fuel) fun _ => ?_
  refine preservesProj_bind (preservesProj_pollCgroupUnpopulated hCap _ fuel pSteps) fun _ => ?_
  exact preservesProj_retryRmdirCgroup hCap cgDir.toUTF8 rSteps

end LeanSwe.ProcessSandbox.Raw.Proofs
