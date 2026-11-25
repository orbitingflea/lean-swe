import LeanSwe.ProcessSandbox.Raw.Proofs.RefinesStepBase

namespace LeanSwe.ProcessSandbox.Raw.Proofs

open LeanSwe.LinuxSyscall
open LeanSwe.ProcessSandbox.Raw
open LeanSwe.ProcessSandbox.Raw.Model
open LeanSwe.ProcessSandbox.Raw.SysBridge
open LeanSwe.ProcessSandbox.Raw.SysBridge.Cgroup
open LeanSwe.ProcessSandbox.Raw.SysBridge.Preset
open LeanSwe.ProcessSandbox.Raw.SysBridge.Bwrap

/-- `discoverSystemEntries` preserves `proj` and only emits entries targeting `Model.presetSystemRoots`. -/
theorem discoverSystemEntries_spec {W : Type} {proj : W → RawHostWorld} {cap : RawHostCapM (StateM W)}
    (hCap : Core.ObeysStep proj rawHostWorldWf (execRawCapStep cap) allowedRawCapStep) (fuel : Nat) :
    PreservesProj proj (discoverSystemEntries cap.files fuel) ∧
    ∀ w, rawHostWorldWf (proj w) = true →
      ∀ e ∈ ((discoverSystemEntries cap.files fuel).run w).1.toList,
        presetEntryBoxPath e ∈ Model.presetSystemRoots.toList := by
  have hLoop := forIn_array_preservesProj_inv (proj := proj)
    (fun (es : Array PresetSystemEntry) => ∀ e ∈ es.toList, presetEntryBoxPath e ∈ Model.presetSystemRoots.toList)
    (fun (root : String) (r : Array PresetSystemEntry) => do
      let mut entries := r
      match ← retryEintr (cap.files.fstatat none root.toUTF8 { symlinkNofollow := true }) fuel with
      | .error _ => pure ()
      | .ok st =>
        if st.kind == .symlink then
          match ← retryEintr (cap.files.readlinkat none root.toUTF8 4096) fuel with
          | .ok tgtBytes =>
            if tgtBytes.size > 0 then
              if let some tgt := String.fromUTF8? tgtBytes then
                entries := entries.push (.topSymlink root tgt)
          | .error _ => pure ()
        else if st.kind == .dir then
          entries := entries.push (.readOnlyDir root)
      pure (ForInStep.yield entries))
    Preset.presetSystemRoots #[] (fun _ h => by cases h)
    (fun root hRoot es hInv => by
      have hRootM : root ∈ Model.presetSystemRoots.toList := hRoot
      have hSt : PreservesProj proj (retryEintr (cap.files.fstatat none root.toUTF8 { symlinkNofollow := true }) fuel) :=
        preservesProj_retryEintr _ (preservesProj_of_seqUnit _ fun w hWf => (hCap w (.filesFstatat none root.toUTF8 _) hWf).2) fuel
      have hRl : PreservesProj proj (retryEintr (cap.files.readlinkat none root.toUTF8 4096) fuel) :=
        preservesProj_retryEintr _ (preservesProj_of_seqUnit _ fun w hWf => (hCap w (.filesReadlinkat none root.toUTF8 4096) hWf).2) fuel
      constructor
      · refine preservesProj_bind hSt fun r => ?_
        cases r with
        | error _ => exact preservesProj_pure _
        | ok st =>
          refine preservesProj_ite ?_ (preservesProj_ite (preservesProj_pure _) (preservesProj_pure _))
          refine preservesProj_bind hRl fun r2 => ?_
          cases r2 with
          | error _ => exact preservesProj_pure _
          | ok bs =>
            refine preservesProj_ite ?_ (preservesProj_pure _)
            cases String.fromUTF8? bs <;> exact preservesProj_pure _
      · intro w _
        simp only [stateM_bind_run]
        cases ((retryEintr (cap.files.fstatat none root.toUTF8 { symlinkNofollow := true }) fuel).run w).1 with
        | error _ => exact hInv
        | ok st =>
          dsimp only
          cases hSym : (st.kind == .symlink) with
          | true =>
            simp only [↓reduceIte, stateM_bind_run]
            cases ((retryEintr (cap.files.readlinkat none root.toUTF8 4096) fuel).run _).1 with
            | error _ => exact hInv
            | ok bs =>
              dsimp only
              by_cases hPos : bs.size > 0
              · simp only [hPos, ↓reduceIte]
                cases String.fromUTF8? bs with
                | none => exact hInv
                | some tgt =>
                  intro e he
                  rw [Array.toList_push, List.mem_append, List.mem_singleton] at he
                  rcases he with h1 | rfl
                  · exact hInv e h1
                  · exact hRootM
              · simp only [hPos, ↓reduceIte]; exact hInv
          | false =>
            simp only [Bool.false_eq_true, ↓reduceIte]
            cases hDir : (st.kind == .dir) with
            | true =>
              simp only [↓reduceIte, stateM_pure_run]
              intro e he
              rw [Array.toList_push, List.mem_append, List.mem_singleton] at he
              rcases he with h1 | rfl
              · exact hInv e h1
              · exact hRootM
            | false => simp only [Bool.false_eq_true, ↓reduceIte, stateM_pure_run]; exact hInv)
  unfold discoverSystemEntries
  constructor
  · exact preservesProj_bind hLoop.1 (fun _ => preservesProj_pure _)
  · intro w hWf
    simp only [stateM_bind_run, stateM_pure_run]
    exact hLoop.2 w hWf

/-- `discoverEtcPaths` preserves `proj` and only emits paths in `Model.presetEtcAllowlist`. -/
theorem discoverEtcPaths_spec {W : Type} {proj : W → RawHostWorld} {cap : RawHostCapM (StateM W)}
    (hCap : Core.ObeysStep proj rawHostWorldWf (execRawCapStep cap) allowedRawCapStep) (fuel : Nat) :
    PreservesProj proj (discoverEtcPaths cap.files fuel) ∧
    ∀ w, rawHostWorldWf (proj w) = true →
      ∀ p ∈ ((discoverEtcPaths cap.files fuel).run w).1.toList,
        p ∈ Model.presetEtcAllowlist.toList := by
  have hLoop := forIn_array_preservesProj_inv (proj := proj)
    (fun (ps : Array String) => ∀ p ∈ ps.toList, p ∈ Model.presetEtcAllowlist.toList)
    (fun (etcP : String) (r : Array String) => do
      let mut paths := r
      match ← retryEintr (cap.files.fstatat none etcP.toUTF8 {}) fuel with
      | .ok _ => paths := paths.push etcP
      | .error _ => pure ()
      pure (ForInStep.yield paths))
    Preset.presetEtcAllowlist #[] (fun _ h => by cases h)
    (fun etcP hEtc ps hInv => by
      have hEtcM : etcP ∈ Model.presetEtcAllowlist.toList := hEtc
      have hSt : PreservesProj proj (retryEintr (cap.files.fstatat none etcP.toUTF8 {}) fuel) :=
        preservesProj_retryEintr _ (preservesProj_of_seqUnit _ fun w hWf => (hCap w (.filesFstatat none etcP.toUTF8 {}) hWf).2) fuel
      constructor
      · refine preservesProj_bind hSt fun r => ?_
        cases r <;> exact preservesProj_pure _
      · intro w _
        simp only [stateM_bind_run]
        cases ((retryEintr (cap.files.fstatat none etcP.toUTF8 {}) fuel).run w).1 with
        | error _ => exact hInv
        | ok _ =>
          intro p hp
          rw [Array.toList_push, List.mem_append, List.mem_singleton] at hp
          rcases hp with h1 | rfl
          · exact hInv p h1
          · exact hEtcM)
  unfold discoverEtcPaths
  constructor
  · exact preservesProj_bind hLoop.1 (fun _ => preservesProj_pure _)
  · intro w hWf
    simp only [stateM_bind_run, stateM_pure_run]
    exact hLoop.2 w hWf

/-- `discoverExcludedHomes` preserves `proj` and only emits paths satisfying `Model.isUnderSystemRoot`. -/
theorem discoverExcludedHomes_spec {W : Type} {proj : W → RawHostWorld} {cap : RawHostCapM (StateM W)}
    (hCap : Core.ObeysStep proj rawHostWorldWf (execRawCapStep cap) allowedRawCapStep) (fuel : Nat) :
    PreservesProj proj (discoverExcludedHomes cap.files cap.proc cap.passwd cap.getEnvHome fuel) ∧
    ∀ w, rawHostWorldWf (proj w) = true →
      ∀ h ∈ ((discoverExcludedHomes cap.files cap.proc cap.passwd cap.getEnvHome fuel).run w).1.toList,
        Model.isUnderSystemRoot h = true := by
  have hFilt : ∀ (cands : List (Option String)),
      PreservesProj proj (filterExistingNestedHomes cap.files cands fuel) ∧
      ∀ w, rawHostWorldWf (proj w) = true →
        ∀ h ∈ ((filterExistingNestedHomes cap.files cands fuel).run w).1.toList,
          Model.isUnderSystemRoot h = true := by
    intro cands
    let stepFn : Option String → List String → StateM W (ForInStep (List String)) :=
      fun cand? kept => do
        let mut k := kept
        if let some raw := cand? then
          if let some norm := normalizeAbsLexical raw then
            if isUnderSystemRootLexical norm then
              match ← retryEintr (cap.files.fstatat none norm.toUTF8 {}) fuel with
              | .ok st =>
                if st.kind == .dir then
                  k := k ++ [norm]
              | .error _ => pure ()
        pure (ForInStep.yield k)
    have hLoop := forIn_list_preservesProj_inv (proj := proj)
      (fun (kept : List String) => ∀ h ∈ kept, Model.isUnderSystemRoot h = true) stepFn
      (fun cand? kept hInv => by
        dsimp only [stepFn]
        cases cand? with
        | none => exact ⟨preservesProj_pure _, fun _ _ => hInv⟩
        | some raw =>
          dsimp only
          cases hNorm : normalizeAbsLexical raw with
          | none => exact ⟨preservesProj_pure _, fun _ _ => hInv⟩
          | some norm =>
            dsimp only
            cases hUnder : isUnderSystemRootLexical norm with
            | true =>
              have hSt : PreservesProj proj (retryEintr (cap.files.fstatat none norm.toUTF8 {}) fuel) :=
                preservesProj_retryEintr _ (preservesProj_of_seqUnit _ fun w hWf => (hCap w (.filesFstatat none norm.toUTF8 {}) hWf).2) fuel
              constructor
              · simp only [↓reduceIte]
                refine preservesProj_bind hSt fun r => ?_
                cases r with
                | error _ => exact preservesProj_pure _
                | ok _ => exact preservesProj_ite (preservesProj_pure _) (preservesProj_pure _)
              · intro w _
                simp only [↓reduceIte, stateM_bind_run]
                cases ((retryEintr (cap.files.fstatat none norm.toUTF8 {}) fuel).run w).1 with
                | error _ => exact hInv
                | ok st =>
                  cases hDir : (st.kind == .dir) with
                  | true =>
                    simp only [hDir, ↓reduceIte, stateM_pure_run]
                    intro h hh
                    rw [List.mem_append, List.mem_singleton] at hh
                    rcases hh with h1 | rfl
                    · exact hInv h h1
                    · exact hUnder
                  | false => simp only [hDir, Bool.false_eq_true, ↓reduceIte, stateM_pure_run]; exact hInv
            | false =>
              simp only [Bool.false_eq_true, ↓reduceIte]
              exact ⟨preservesProj_pure _, fun _ _ => hInv⟩)
      cands [] (fun _ h => by cases h)
    unfold filterExistingNestedHomes
    constructor
    · exact preservesProj_bind hLoop.1 (fun _ => preservesProj_pure _)
    · intro w hWf h hh
      simp only [stateM_bind_run, stateM_pure_run] at hh
      have hMemArr : h ∈ dedupStrings ((forIn cands [] stepFn).run w).1 := Array.mem_def.mpr hh
      have hMemList : h ∈ ((forIn cands [] stepFn).run w).1 := (HostCgroupPreset.dedupStrings_mem_iff _ h).mp hMemArr
      exact hLoop.2 w hWf h hMemList
  unfold discoverExcludedHomes
  have hEnv : PreservesProj proj cap.getEnvHome :=
    preservesProj_of_seqUnit _ fun w hWf => (hCap w .getEnvHome hWf).2
  have hUid : PreservesProj proj cap.proc.getuid :=
    preservesProj_of_seqUnit _ fun w hWf => (hCap w .procGetuid hWf).2
  have hPw : ∀ uid, PreservesProj proj (cap.passwd.getpwuid uid) := fun uid =>
    preservesProj_of_seqUnit _ fun w hWf => (hCap w (.passwdGetpwuid uid) hWf).2
  have hAfterEnv : ∀ homeEnv?,
      PreservesProj proj (do
        let pwDir? ← match ← cap.proc.getuid with
          | .error _ => pure none
          | .ok uid =>
            match ← cap.passwd.getpwuid uid with
            | .ok (some entry) => pure entry.homeDirUtf8?
            | _ => pure none
        filterExistingNestedHomes cap.files [homeEnv?, pwDir?] fuel) ∧
      ∀ w, rawHostWorldWf (proj w) = true →
        ∀ h ∈ ((do
          let pwDir? ← match ← cap.proc.getuid with
            | .error _ => pure none
            | .ok uid =>
              match ← cap.passwd.getpwuid uid with
              | .ok (some entry) => pure entry.homeDirUtf8?
              | _ => pure none
          filterExistingNestedHomes cap.files [homeEnv?, pwDir?] fuel).run w).1.toList,
          Model.isUnderSystemRoot h = true := by
    intro homeEnv?
    constructor
    · refine preservesProj_bind hUid fun r1 => ?_
      cases r1 with
      | error _ => exact (hFilt [homeEnv?, none]).1
      | ok uid =>
        refine preservesProj_bind (hPw uid) fun r2 => ?_
        cases r2 with
        | error _ => exact (hFilt [homeEnv?, none]).1
        | ok optE =>
          cases optE with
          | none => exact (hFilt [homeEnv?, none]).1
          | some entry => exact (hFilt [homeEnv?, entry.homeDirUtf8?]).1
    · intro w hWf
      simp only [stateM_bind_run]
      have h1 := hUid w hWf
      have hWf1 : rawHostWorldWf (proj (cap.proc.getuid.run w).2) = true := by rw [h1]; exact hWf
      cases (cap.proc.getuid.run w).1 with
      | error _ => exact (hFilt [homeEnv?, none]).2 _ hWf1
      | ok uid =>
        dsimp only
        simp only [stateM_bind_run]
        let w1 := (cap.proc.getuid.run w).2
        have h2 := hPw uid w1 hWf1
        have hWf2 : rawHostWorldWf (proj ((cap.passwd.getpwuid uid).run w1).2) = true := by rw [h2]; exact hWf1
        cases ((cap.passwd.getpwuid uid).run w1).1 with
        | error _ => exact (hFilt [homeEnv?, none]).2 _ hWf2
        | ok optE =>
          cases optE with
          | none => exact (hFilt [homeEnv?, none]).2 _ hWf2
          | some entry => exact (hFilt [homeEnv?, entry.homeDirUtf8?]).2 _ hWf2
  constructor
  · exact preservesProj_bind hEnv fun homeEnv? => (hAfterEnv homeEnv?).1
  · intro w hWf
    simp only [stateM_bind_run]
    have h1 := hEnv w hWf
    have hWf1 : rawHostWorldWf (proj (cap.getEnvHome.run w).2) = true := by rw [h1]; exact hWf
    exact (hAfterEnv (cap.getEnvHome.run w).1).2 (cap.getEnvHome.run w).2 hWf1

/-- `discoverHostPresetM` preserves `proj` and enforces root/allowlist/home-mask invariants. -/
theorem discoverHostPresetM_spec {W : Type} {proj : W → RawHostWorld} {cap : RawHostCapM (StateM W)}
    (hCap : Core.ObeysStep proj rawHostWorldWf (execRawCapStep cap) allowedRawCapStep) (fuel : Nat) :
    PreservesProj proj (discoverHostPresetM cap.files cap.proc cap.passwd cap.getEnvHome fuel) ∧
    ∀ w, rawHostWorldWf (proj w) = true →
      let preset := ((discoverHostPresetM cap.files cap.proc cap.passwd cap.getEnvHome fuel).run w).1
      (∀ e ∈ preset.systemEntries.toList, presetEntryBoxPath e ∈ Model.presetSystemRoots.toList) ∧
      (∀ p ∈ preset.etcPaths.toList, p ∈ Model.presetEtcAllowlist.toList) ∧
      (∀ h ∈ preset.excludedHomePaths.toList, Model.isUnderSystemRoot h = true) := by
  have ⟨hP1, hI1⟩ := discoverSystemEntries_spec hCap fuel
  have ⟨hP2, hI2⟩ := discoverEtcPaths_spec hCap fuel
  have ⟨hP3, hI3⟩ := discoverExcludedHomes_spec hCap fuel
  unfold discoverHostPresetM
  constructor
  · exact preservesProj_bind hP1 fun _ =>
      preservesProj_bind hP2 fun _ =>
        preservesProj_bind hP3 fun _ => preservesProj_pure _
  · intro w hWf
    simp only [stateM_bind_run, stateM_pure_run]
    have h1 := hP1 w hWf
    have hWf1 : rawHostWorldWf (proj ((discoverSystemEntries cap.files fuel).run w).2) = true := by rw [h1]; exact hWf
    have h2 := hP2 ((discoverSystemEntries cap.files fuel).run w).2 hWf1
    have hWf2 : rawHostWorldWf (proj ((discoverEtcPaths cap.files fuel).run ((discoverSystemEntries cap.files fuel).run w).2).2) = true := by
      rw [h2]; exact hWf1
    exact ⟨hI1 w hWf, hI2 _ hWf1, hI3 _ hWf2⟩

/-- `resolveBwrapPath` preserves `proj`. -/
theorem preservesProj_resolveBwrapPath {W : Type} {proj : W → RawHostWorld} {cap : RawHostCapM (StateM W)}
    (hCap : Core.ObeysStep proj rawHostWorldWf (execRawCapStep cap) allowedRawCapStep) (fuel : Nat) :
    PreservesProj proj (resolveBwrapPath cap.files cap.getEnvPath fuel) := by
  have hExec : ∀ p, PreservesProj proj (isExecutableRegFile cap.files p fuel) := fun p => by
    unfold isExecutableRegFile
    refine preservesProj_bind
      (preservesProj_retryEintr _ (preservesProj_of_seqUnit _ fun w hWf => (hCap w (.filesFstatat none p.toUTF8 {}) hWf).2) fuel) fun r => ?_
    cases r with
    | error _ => exact preservesProj_pure _
    | ok _ =>
      refine preservesProj_ite (preservesProj_pure _) ?_
      refine preservesProj_bind
        (preservesProj_retryEintr _ (preservesProj_of_seqUnit _ fun w hWf => (hCap w (.filesFaccessat none p.toUTF8 { exec := true } {}) hWf).2) fuel) fun r2 => ?_
      cases r2 <;> exact preservesProj_pure _
  have hSearch : ∀ dirs, PreservesProj proj (searchBwrapDirs cap.files fuel dirs) := by
    intro dirs
    induction dirs with
    | nil =>
      unfold searchBwrapDirs
      exact preservesProj_bind (hExec "/usr/bin/bwrap") fun b => by cases b <;> exact preservesProj_pure _
    | cons d rest ih =>
      unfold searchBwrapDirs
      exact preservesProj_bind (hExec (bwrapCandidatePath d)) fun b => by
        cases b
        · exact ih
        · exact preservesProj_pure _
  unfold resolveBwrapPath
  refine preservesProj_bind (preservesProj_of_seqUnit _ fun w hWf => (hCap w .getEnvPath hWf).2) fun _ => ?_
  exact hSearch _

/-- `createSealedMemfd` preserves `proj`. -/
theorem preservesProj_createSealedMemfd {W : Type} {proj : W → RawHostWorld} {cap : RawHostCapM (StateM W)}
    (hCap : Core.ObeysStep proj rawHostWorldWf (execRawCapStep cap) allowedRawCapStep)
    (name : String) (data : ByteArray) (fuel : Nat) :
    PreservesProj proj (createSealedMemfd cap.sandbox cap.files name data fuel) := by
  unfold createSealedMemfd
  refine preservesProj_bind
    (preservesProj_of_seqUnit _ fun w hWf => (hCap w (.sandboxMemfdCreate name.toUTF8 _) hWf).2) fun r => ?_
  cases r with
  | error _ => exact preservesProj_pure _
  | ok h =>
    have hAfterWr : ∀ wr : Except Errno Unit, PreservesProj proj ((match wr with
        | .error e => do Files.closeOpt cap.files (some h); pure (.error e)
        | .ok () => do
          match ← retryEintr (cap.files.fcntl h (.addSeals F_SEAL_ALL)) fuel with
          | .error e => Files.closeOpt cap.files (some h); pure (.error e)
          | .ok _ => pure (.ok h)) : StateM W (Except Errno Nat)) := by
      intro wr
      cases wr with
      | error _ => exact preservesProj_bind (preservesProj_closeOpt hCap (some h)) (fun _ => preservesProj_pure _)
      | ok _ =>
        refine preservesProj_bind
          (preservesProj_retryEintr _ (preservesProj_of_seqUnit _ fun w hWf => (hCap w (.filesFcntl h (.addSeals F_SEAL_ALL)) hWf).2) fuel) fun sr => ?_
        cases sr with
        | error _ => exact preservesProj_bind (preservesProj_closeOpt hCap (some h)) (fun _ => preservesProj_pure _)
        | ok _ => exact preservesProj_pure _
    refine preservesProj_ite
      (preservesProj_bind (preservesProj_writeAllFd hCap h data 0 fuel) hAfterWr)
      (hAfterWr (.ok ()))

/-- `probeBwrapNamespaces` preserves `proj`. -/
theorem preservesProj_probeBwrapNamespaces {W : Type} {proj : W → RawHostWorld} {cap : RawHostCapM (StateM W)}
    (hCap : Core.ObeysStep proj rawHostWorldWf (execRawCapStep cap) allowedRawCapStep)
    (bwrapPath : String) (initBytes : ByteArray) (fuel : Nat) :
    PreservesProj proj (probeBwrapNamespaces cap.files cap.sandbox cap.proc cap.postFork bwrapPath initBytes fuel) := by
  have hOpen1 : PreservesProj proj (retryEintr (cap.files.openat none "/dev/null".toUTF8 { access := .rdwr, cloexec := true } 0) fuel) :=
    preservesProj_retryEintr _ (preservesProj_of_seqUnit _ fun w hWf => (hCap w (.filesOpenat none "/dev/null".toUTF8 _ 0) hWf).2) fuel
  have hOpen3 : PreservesProj proj (openThreeDevNull cap.files fuel) := by
    unfold openThreeDevNull
    refine preservesProj_bind hOpen1 fun r0 => ?_
    cases r0 with
    | error _ => exact preservesProj_pure _
    | ok d0 =>
      refine preservesProj_bind hOpen1 fun r1 => ?_
      cases r1 with
      | error _ => exact preservesProj_bind (preservesProj_closeOpt hCap (some d0)) (fun _ => preservesProj_pure _)
      | ok d1 =>
        refine preservesProj_bind hOpen1 fun r2 => ?_
        cases r2 with
        | error _ =>
          exact preservesProj_bind (preservesProj_closeOpt hCap (some d0)) fun _ =>
            preservesProj_bind (preservesProj_closeOpt hCap (some d1)) (fun _ => preservesProj_pure _)
        | ok _ => exact preservesProj_pure _
  have hWait : ∀ pid f, PreservesProj proj (waitProbeExitZero cap.proc pid f) := by
    intro pid f
    induction f with
    | zero => exact preservesProj_pure _
    | succ f ih =>
      unfold waitProbeExitZero
      refine preservesProj_bind (preservesProj_of_seqUnit _ fun w hWf => (hCap w (.procWaitpid pid {}) hWf).2) fun r => ?_
      split
      · exact preservesProj_pure _
      · exact preservesProj_pure _
      · exact preservesProj_ite ih (preservesProj_pure _)
  unfold probeBwrapNamespaces
  refine preservesProj_bind hOpen3 fun r3 => ?_
  cases r3 with
  | error _ => exact preservesProj_pure _
  | ok ds =>
    rcases ds with ⟨d0, d1, d2⟩
    refine preservesProj_bind (preservesProj_createSealedMemfd hCap "leanswe-psandbox-probe" initBytes fuel) fun rm => ?_
    cases rm with
    | error _ =>
      exact preservesProj_bind (preservesProj_closeOpt hCap (some d0)) fun _ =>
        preservesProj_bind (preservesProj_closeOpt hCap (some d1)) fun _ =>
          preservesProj_bind (preservesProj_closeOpt hCap (some d2)) (fun _ => preservesProj_pure _)
    | ok initMemfd =>
      refine preservesProj_bind
        (preservesProj_retryEintr _ (preservesProj_of_seqUnit _ fun w hWf => (hCap w (.filesReopenReadOnly initMemfd) hWf).2) fuel) fun ro => ?_
      refine preservesProj_bind (preservesProj_closeOpt hCap (some initMemfd)) fun _ => ?_
      cases ro with
      | error _ =>
        exact preservesProj_bind (preservesProj_closeOpt hCap (some d0)) fun _ =>
          preservesProj_bind (preservesProj_closeOpt hCap (some d1)) fun _ =>
            preservesProj_bind (preservesProj_closeOpt hCap (some d2)) (fun _ => preservesProj_pure _)
      | ok initFd =>
        refine preservesProj_bind (discoverSystemEntries_spec hCap fuel).1 fun sysEntries => ?_
        have hAfterLd : ∀ hasLdCache : Bool, PreservesProj proj (do
            let childSpec : PostFork.ChildSpecM Nat := {
              path := bwrapPath
              argv := buildProbeBwrapArgv bwrapPath sysEntries hasLdCache initFd
              stdio := .redirect (.handle d0) (.handle d1) (.handle d2) false
              fdPolicy := .closeAllAbove2Except #[.handle initFd]
              processGroup := .newGroup
              sigpipe := .resetDefault
              forkMode := .immortalThread
            }
            let spawnRes ← cap.postFork.spawn childSpec
            Files.closeOpt cap.files (some d0)
            Files.closeOpt cap.files (some d1)
            Files.closeOpt cap.files (some d2)
            Files.closeOpt cap.files (some initFd)
            match spawnRes with
            | .error pfErr => pure (.error (pfErr.errno.getD Errno.EPERM))
            | .ok child => waitProbeExitZero cap.proc child.pid.toInt32 fuel) := fun hasLdCache => by
          refine preservesProj_bind (preservesProj_of_seqUnit _ fun w hWf => (hCap w (.postForkSpawn _) hWf).2) fun sp => ?_
          refine preservesProj_bind (preservesProj_closeOpt hCap (some d0)) fun _ =>
            preservesProj_bind (preservesProj_closeOpt hCap (some d1)) fun _ =>
              preservesProj_bind (preservesProj_closeOpt hCap (some d2)) fun _ =>
                preservesProj_bind (preservesProj_closeOpt hCap (some initFd)) fun _ => ?_
          cases sp with
          | error _ => exact preservesProj_pure _
          | ok child => exact hWait child.pid.toInt32 fuel
        refine preservesProj_bind
          (preservesProj_retryEintr _ (preservesProj_of_seqUnit _ fun w hWf => (hCap w (.filesFstatat none "/etc/ld.so.cache".toUTF8 {}) hWf).2) fuel) fun r => ?_
        cases r with
        | ok _ => exact hAfterLd true
        | error _ => exact hAfterLd false

end LeanSwe.ProcessSandbox.Raw.Proofs
