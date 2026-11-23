import LeanSwe.Fs.Proofs.SysBridgeDirOps

namespace LeanSwe.Fs.Proofs

open LeanSwe.LinuxSyscall
open LeanSwe.LinuxSyscall.Files
open LeanSwe.Fs
open LeanSwe.Fs.Model

/-- Confined trace specification for `SysBridge.createFileAtPure`. -/
theorem createFileAtPure_trace {W : Type} {proj : W → FsWorld} {cap : HealthyFilesCapM (StateM W)}
    (hCap : Core.RefinesStep proj Model.fsWorldWf (Model.execFilesCapStep cap) Model.allowedFilesCapStep)
    (dirFd : HandleId) (name : EntryName) (bytes : ByteArray) (held : List HandleId) (eintrFuel : Nat)
    {s : W} (hWf : fsWorldWf (proj s) = true) :
    let p := (SysBridge.createFileAtPure cap.files dirFd name bytes eintrFuel).run s
    fsWorldWf (proj p.2) = true ∧
    (proj p.2).tempSeq = (proj s).tempSeq ∧
    ∃ tr,
      HealthyFilesSteps (proj s).env tr (proj p.2).env ∧
      TraceFds held tr held ∧
      (∀ step ∈ tr, SubtreeConfinedReq step.1) ∧
      match p.1 with
      | .ok () => WriteFileTrace (some dirFd) name.val.toUTF8 createNewOpenFlags 0o644 bytes tr
      | .error e => nonLockErrOk e := by
  unfold SysBridge.createFileAtPure
  have hOp := retryEintr_single_req (cap.files.openat (some dirFd) name.val.toUTF8 createNewOpenFlags 0o644)
    (.openat (some dirFd) name.val.toUTF8 createNewOpenFlags 0o644) outcomeOfOpened
    (fun s' hW => cap_method_step hCap (.openat (some dirFd) name.val.toUTF8 createNewOpenFlags 0o644)
      (cap.files.openat (some dirFd) name.val.toUTF8 createNewOpenFlags 0o644) outcomeOfOpened rfl hW)
    (fun _ => rfl) eintrFuel hWf
  cases hR : (retryEintr (cap.files.openat (some dirFd) name.val.toUTF8 createNewOpenFlags 0o644) eintrFuel s) with
  | mk oRes s1 =>
    rw [StateT.run] at hOp; rw [hR] at hOp; dsimp only at hOp
    obtain ⟨hWf1, hTmp1, trR, hStO, hAllO⟩ := hOp
    dsimp only [createNewOpenFlags] at hR
    simp only [Bind.bind, StateT.bind, StateT.run, hR]
    have hFdR : TraceFds held trR held := traceFds_eintr_retries (fun _ hc => by cases hc) hAllO
    have hConfStep : SubtreeConfinedReq (.openat (some dirFd) name.val.toUTF8 createNewOpenFlags 0o644) := ⟨rfl, ⟨name, rfl⟩⟩
    have hConfO : ∀ step ∈ trR ++ [(.openat (some dirFd) name.val.toUTF8 createNewOpenFlags 0o644, outcomeOfOpened oRes)],
        SubtreeConfinedReq step.1 :=
      confined_append (fun step hm => by rw [hAllO step hm]; exact hConfStep) (confined_single hConfStep)
    cases oRes with
    | error e =>
      simp only [Pure.pure, StateT.pure]
      exact ⟨hWf1, hTmp1, _, hStO, traceFds_append hFdR (traceFds_nonFd_step rfl rfl),
        hConfO, nonLockErrOk_mapErrno _ _ _⟩
    | ok h =>
      have hFdO : TraceFds held (trR ++ [(.openat (some dirFd) name.val.toUTF8 createNewOpenFlags 0o644, .opened h)]) (h :: held) :=
        traceFds_append hFdR (traceFds_open_step rfl rfl)
      have hWr := writeAllAndClose_trace hCap h name.val bytes held eintrFuel hWf1
      cases hRw : (SysBridge.writeAllAndClose cap.files h name.val bytes eintrFuel s1) with
      | mk wRes s2 =>
        rw [StateT.run] at hWr; rw [hRw] at hWr; dsimp only at hWr
        obtain ⟨hWf2, hTmp2, trW, trC, hStW, hFdW, hFdC, hConfW, ⟨co, hCeq⟩, hOutW⟩ := hWr
        subst hCeq
        simp only [Bind.bind, StateT.bind, hRw]
        cases wRes with
        | ok u =>
          cases u
          simp only [Pure.pure, StateT.pure]
          exact ⟨hWf2, hTmp2.trans hTmp1, _, healthyFilesSteps_append hStO hStW,
            traceFds_append hFdO (traceFds_append hFdW hFdC), confined_append hConfO hConfW,
            h, trR ++ [(.openat (some dirFd) name.val.toUTF8 createNewOpenFlags 0o644, .opened h)],
            trW, [(.close h, co)], by simp [List.append_assoc, outcomeOfOpened], by simp, hOutW, co, by simp⟩
        | error err =>
          have hUn := cap_method_step hCap (.unlinkat (some dirFd) name.val.toUTF8 false)
            (cap.files.unlinkat (some dirFd) name.val.toUTF8 false) outcomeOfUnit rfl hWf2
          cases hRu : cap.files.unlinkat (some dirFd) name.val.toUTF8 false s2 with
          | mk uRes s3 =>
            have hUn' : fsWorldWf (proj s3) = true ∧
                healthyStep (proj s2).env (.unlinkat (some dirFd) name.val.toUTF8 false) (outcomeOfUnit uRes) = some (proj s3).env ∧
                (proj s3).tempSeq = (proj s2).tempSeq := by
              rw [StateT.run] at hUn; rw [hRu] at hUn; exact hUn
            simp only [Bind.bind, StateT.bind, Pure.pure, StateT.pure, hRu]
            have hFdUn : TraceFds held [(.unlinkat (some dirFd) name.val.toUTF8 false, outcomeOfUnit uRes)] held :=
              traceFds_nonFd_step (by cases uRes <;> rfl) rfl
            exact ⟨hUn'.1, hUn'.2.2.trans (hTmp2.trans hTmp1), _,
              healthyFilesSteps_append (healthyFilesSteps_append hStO hStW) (healthyFilesSteps_single hUn'.2.1),
              traceFds_append (traceFds_append hFdO (traceFds_append hFdW hFdC)) hFdUn,
              confined_append (confined_append hConfO hConfW) (confined_single ⟨name, rfl⟩), hOutW⟩

/-- Confined trace specification for `SysBridge.acquireLockAtPure`. -/
theorem acquireLockAtPure_trace {W : Type} {proj : W → FsWorld} {cap : HealthyFilesCapM (StateM W)}
    (hCap : Core.RefinesStep proj Model.fsWorldWf (Model.execFilesCapStep cap) Model.allowedFilesCapStep)
    (dirFd : HandleId) (name : EntryName) (mode : LockMode) (createIfMissing nonBlocking : Bool)
    (held : List HandleId) (eintrFuel : Nat) {s : W} (hWf : fsWorldWf (proj s) = true) :
    let p := (SysBridge.acquireLockAtPure cap.files dirFd name mode createIfMissing nonBlocking eintrFuel).run s
    fsWorldWf (proj p.2) = true ∧
    (proj p.2).tempSeq = (proj s).tempSeq ∧
    match p.1 with
    | .ok h =>
      ∃ rawSt fl modeArg trOpen trLock,
        HealthyFilesSteps (proj s).env (trOpen ++ trLock) (proj p.2).env ∧
        TraceFds held trOpen (h :: held) ∧
        TraceFds (h :: held) trLock (h :: held) ∧
        (∀ step ∈ trOpen ++ trLock, SubtreeConfinedReq step.1) ∧
        fl.access = .rdonly ∧ fl.nofollow = true ∧ fl.cloexec = true ∧ fl.nonblock = true ∧
        (.openat (some dirFd) name.val.toUTF8 fl modeArg, .opened h) ∈ trOpen ∧
        (.fstat h, .statted rawSt) ∈ trLock ∧
        rawSt.kind = .reg ∧
        (.flock h (lockModeToFlockOp mode nonBlocking), .unit) ∈ trLock
    | .error e =>
      ∃ tr,
        HealthyFilesSteps (proj s).env tr (proj p.2).env ∧
        TraceFds held tr held ∧
        (∀ step ∈ tr, SubtreeConfinedReq step.1) ∧
        (nonLockErrOk e ∨
         (e.kind = .wouldBlock ∧ nonBlocking = true ∧
          TryLockContendedTrace (some dirFd) name.val.toUTF8 mode tr)) := by
  unfold SysBridge.acquireLockAtPure
  let baseFlags : OpenFlags := { access := .rdonly, nofollow := true, cloexec := true, nonblock := true }
  have hOp0 := retryEintr_single_req (cap.files.openat (some dirFd) name.val.toUTF8 baseFlags 0)
    (.openat (some dirFd) name.val.toUTF8 baseFlags 0) outcomeOfOpened
    (fun s' hW => cap_method_step hCap (.openat (some dirFd) name.val.toUTF8 baseFlags 0)
      (cap.files.openat (some dirFd) name.val.toUTF8 baseFlags 0) outcomeOfOpened rfl hW)
    (fun _ => rfl) eintrFuel hWf
  cases hR0 : (retryEintr (cap.files.openat (some dirFd) name.val.toUTF8 baseFlags 0) eintrFuel s) with
  | mk r0 s1 =>
    rw [StateT.run] at hOp0; rw [hR0] at hOp0; dsimp only at hOp0
    obtain ⟨hWf1, hTmp1, tr0, hSt0, hAll0⟩ := hOp0
    have hR0' : retryEintr (cap.files.openat (some dirFd) name.val.toUTF8
        { access := .rdonly, nofollow := true, cloexec := true, nonblock := true } 0) eintrFuel s =
        (r0, s1) := hR0
    simp only [Bind.bind, StateT.bind, StateT.run, hR0']
    have hFd0R : TraceFds held tr0 held := traceFds_eintr_retries (fun _ hc => by cases hc) hAll0
    have hConf0 : ∀ step ∈ tr0 ++ [(.openat (some dirFd) name.val.toUTF8 baseFlags 0, outcomeOfOpened r0)],
        SubtreeConfinedReq step.1 :=
      confined_append (fun step hm => by rw [hAll0 step hm]; exact ⟨rfl, ⟨name, rfl⟩⟩)
        (confined_single ⟨rfl, ⟨name, rfl⟩⟩)
    have hFinish : ∀ {sX : W} {h : HandleId} (fl : OpenFlags) (modeArg : Mode) {trO : List KernelStep},
        fsWorldWf (proj sX) = true →
        (proj sX).tempSeq = (proj s).tempSeq →
        HealthyFilesSteps (proj s).env trO (proj sX).env →
        TraceFds held trO (h :: held) →
        (∀ step ∈ trO, SubtreeConfinedReq step.1) →
        fl.access = .rdonly → fl.nofollow = true → fl.cloexec = true → fl.nonblock = true →
        (.openat (some dirFd) name.val.toUTF8 fl modeArg, .opened h) ∈ trO →
        let q := (SysBridge.finishLockFd cap.files h name.val mode nonBlocking eintrFuel).run sX
        fsWorldWf (proj q.2) = true ∧ (proj q.2).tempSeq = (proj s).tempSeq ∧
        match q.1 with
        | .ok h' =>
          ∃ rawSt fl' mA trOpen trLock,
            HealthyFilesSteps (proj s).env (trOpen ++ trLock) (proj q.2).env ∧
            TraceFds held trOpen (h' :: held) ∧ TraceFds (h' :: held) trLock (h' :: held) ∧
            (∀ step ∈ trOpen ++ trLock, SubtreeConfinedReq step.1) ∧
            fl'.access = .rdonly ∧ fl'.nofollow = true ∧ fl'.cloexec = true ∧ fl'.nonblock = true ∧
            (.openat (some dirFd) name.val.toUTF8 fl' mA, .opened h') ∈ trOpen ∧
            (.fstat h', .statted rawSt) ∈ trLock ∧ rawSt.kind = .reg ∧
            (.flock h' (lockModeToFlockOp mode nonBlocking), .unit) ∈ trLock
        | .error e =>
          ∃ tr, HealthyFilesSteps (proj s).env tr (proj q.2).env ∧ TraceFds held tr held ∧
            (∀ step ∈ tr, SubtreeConfinedReq step.1) ∧
            (nonLockErrOk e ∨ (e.kind = .wouldBlock ∧ nonBlocking = true ∧
              TryLockContendedTrace (some dirFd) name.val.toUTF8 mode tr)) := by
      intro sX h fl modeArg trO hWfX hTmpX hStO hFdO hConfO hAcc hNf hCl hNb hMemO
      have hFin := finishLockFd_trace hCap h name.val mode nonBlocking held eintrFuel hWfX
      cases hRf : (SysBridge.finishLockFd cap.files h name.val mode nonBlocking eintrFuel sX) with
      | mk fRes sY =>
        simp only [StateT.run, hRf] at hFin ⊢
        obtain ⟨hWfY, hTmpY, hOutF⟩ := hFin
        cases fRes with
        | ok h' =>
          obtain ⟨hEq, rawSt, trL, hStL, hFdL, hConfL, hMemFs, hReg, hMemFl⟩ := hOutF
          subst hEq
          exact ⟨hWfY, hTmpY.trans hTmpX, rawSt, fl, modeArg, trO, trL,
            healthyFilesSteps_append hStO hStL, hFdO, hFdL, confined_append hConfO hConfL,
            hAcc, hNf, hCl, hNb, hMemO, hMemFs, hReg, hMemFl⟩
        | error e =>
          obtain ⟨trL, trC, hStLC, hFdL, hFdC, hConfLC, ⟨co, hCeq⟩, hErrCase⟩ := hOutF
          refine ⟨hWfY, hTmpY.trans hTmpX, trO ++ trL ++ trC,
            by simpa [List.append_assoc] using healthyFilesSteps_append hStO hStLC,
            traceFds_append (traceFds_append hFdO hFdL) hFdC,
            by simpa [List.append_assoc] using confined_append hConfO hConfLC, ?_⟩
          rcases hErrCase with hNl | ⟨hWb, hNbT, rawSt, hMemFs, hReg, hMemFl⟩
          · exact Or.inl hNl
          · subst hNbT
            exact Or.inr ⟨hWb, rfl, h, rawSt, fl, modeArg, trO, trL, trC, rfl,
              hAcc, hNf, hCl, hNb, hMemO, hMemFs, hReg, hMemFl, ⟨co, by simp [hCeq]⟩⟩
    cases r0 with
    | ok h =>
      simp only [Bind.bind, StateT.bind, Pure.pure, StateT.pure]
      exact hFinish baseFlags 0 hWf1 hTmp1 hSt0 (traceFds_append hFd0R (traceFds_open_step rfl rfl))
        hConf0 rfl rfl rfl rfl (by simp [outcomeOfOpened])
    | error e0 =>
      have hFd0E : TraceFds held (tr0 ++ [(.openat (some dirFd) name.val.toUTF8 baseFlags 0, .err e0)]) held :=
        traceFds_append hFd0R (traceFds_nonFd_step rfl rfl)
      by_cases hCr : (e0 == Errno.ENOENT && createIfMissing) = true
      · simp only [hCr, ↓reduceIte]
        let crFlags : OpenFlags := { baseFlags with creat := true }
        have hOp1 := retryEintr_single_req (cap.files.openat (some dirFd) name.val.toUTF8 crFlags 0o644)
          (.openat (some dirFd) name.val.toUTF8 crFlags 0o644) outcomeOfOpened
          (fun s' hW => cap_method_step hCap (.openat (some dirFd) name.val.toUTF8 crFlags 0o644)
            (cap.files.openat (some dirFd) name.val.toUTF8 crFlags 0o644) outcomeOfOpened rfl hW)
          (fun _ => rfl) eintrFuel hWf1
        cases hR1 : (retryEintr (cap.files.openat (some dirFd) name.val.toUTF8 crFlags 0o644) eintrFuel s1) with
        | mk r1 s2 =>
          rw [StateT.run] at hOp1; rw [hR1] at hOp1; dsimp only at hOp1
          obtain ⟨hWf2, hTmp2, tr1, hSt1, hAll1⟩ := hOp1
          have hR1' : retryEintr (cap.files.openat (some dirFd) name.val.toUTF8
              { access := .rdonly, creat := true, nofollow := true, cloexec := true, nonblock := true } 0o644) eintrFuel s1 =
              (r1, s2) := hR1
          simp only [Bind.bind, StateT.bind, hR1']
          have hFd1R : TraceFds held tr1 held := traceFds_eintr_retries (fun _ hc => by cases hc) hAll1
          have hConf1 : ∀ step ∈ tr1 ++ [(.openat (some dirFd) name.val.toUTF8 crFlags 0o644, outcomeOfOpened r1)],
              SubtreeConfinedReq step.1 :=
            confined_append (fun step hm => by rw [hAll1 step hm]; exact ⟨rfl, ⟨name, rfl⟩⟩)
              (confined_single ⟨rfl, ⟨name, rfl⟩⟩)
          cases r1 with
          | ok h =>
            exact hFinish crFlags 0o644 hWf2 (hTmp2.trans hTmp1) (healthyFilesSteps_append hSt0 hSt1)
              (traceFds_append hFd0E (traceFds_append hFd1R (traceFds_open_step rfl rfl)))
              (confined_append hConf0 hConf1) rfl rfl rfl rfl (by simp [outcomeOfOpened])
          | error e1 =>
            have hFd1E : TraceFds held (tr1 ++ [(.openat (some dirFd) name.val.toUTF8 crFlags 0o644, .err e1)]) held :=
              traceFds_append hFd1R (traceFds_nonFd_step rfl rfl)
            have hFdAll := traceFds_append hFd0E hFd1E
            by_cases hBad : (e1 == Errno.ELOOP || e1 == Errno.ENXIO) = true
            · simp only [hBad, ↓reduceIte, Pure.pure, StateT.pure]
              exact ⟨hWf2, hTmp2.trans hTmp1, _, healthyFilesSteps_append hSt0 hSt1, hFdAll,
                confined_append hConf0 hConf1, Or.inl (nonLockErrOk_mapErrno _ _ _)⟩
            · simp only [hBad, Bool.false_eq_true, ↓reduceIte, Pure.pure, StateT.pure]
              exact ⟨hWf2, hTmp2.trans hTmp1, _, healthyFilesSteps_append hSt0 hSt1, hFdAll,
                confined_append hConf0 hConf1, Or.inl (nonLockErrOk_mapErrno _ _ _)⟩
      · simp only [hCr, Bool.false_eq_true, ↓reduceIte, Bind.bind, StateT.bind, Pure.pure, StateT.pure]
        by_cases hBad : (e0 == Errno.ELOOP || e0 == Errno.ENXIO) = true
        · simp only [hBad, ↓reduceIte]
          exact ⟨hWf1, hTmp1, _, hSt0, hFd0E, hConf0, Or.inl (nonLockErrOk_mapErrno _ _ _)⟩
        · simp only [hBad, Bool.false_eq_true, ↓reduceIte]
          exact ⟨hWf1, hTmp1, _, hSt0, hFd0E, hConf0, Or.inl (nonLockErrOk_mapErrno _ _ _)⟩

/-- Confined trace specification for `(SysBridge.mkRawDirOpsM ...).fstatDir`. -/
theorem dirOps_fstatDir_trace {W : Type} {proj : W → FsWorld} {cap : HealthyFilesCapM (StateM W)}
    (hCap : Core.RefinesStep proj Model.fsWorldWf (Model.execFilesCapStep cap) Model.allowedFilesCapStep)
    (dirFd : HandleId) (held : List HandleId) {s : W} (hWf : fsWorldWf (proj s) = true) :
    let p := ((SysBridge.mkRawDirOpsM cap.files cap.nextTempSeq).fstatDir dirFd).run s
    fsWorldWf (proj p.2) = true ∧
    (proj p.2).tempSeq = (proj s).tempSeq ∧
    ∃ tr,
      HealthyFilesSteps (proj s).env tr (proj p.2).env ∧
      TraceFds held tr held ∧
      (∀ step ∈ tr, SubtreeConfinedReq step.1) ∧
      match p.1 with
      | .ok st => FstatTrace dirFd st tr
      | .error e => nonLockErrOk e := by
  have hFs := cap_method_step hCap (.fstat dirFd) (cap.files.fstat dirFd) outcomeOfStatted rfl hWf
  cases hR : cap.files.fstat dirFd s with
  | mk res s1 =>
    have hFs' : fsWorldWf (proj s1) = true ∧
        healthyStep (proj s).env (.fstat dirFd) (outcomeOfStatted res) = some (proj s1).env ∧
        (proj s1).tempSeq = (proj s).tempSeq := by
      simpa [StateT.run, hR] using hFs
    simp only [SysBridge.mkRawDirOpsM, Bind.bind, StateT.bind, StateT.run, hR]
    cases res with
    | ok rawSt =>
      simp only [Pure.pure, StateT.pure]
      exact ⟨hFs'.1, hFs'.2.2, [(.fstat dirFd, .statted rawSt)], healthyFilesSteps_single hFs'.2.1,
        traceFds_nonFd_step rfl rfl, confined_single trivial,
        ⟨rawSt, List.mem_singleton.mpr rfl, sysBridge_statInfoToFileStat_eq rawSt⟩⟩
    | error e =>
      simp only [Pure.pure, StateT.pure]
      exact ⟨hFs'.1, hFs'.2.2, [(.fstat dirFd, .err e)], healthyFilesSteps_single hFs'.2.1,
        traceFds_nonFd_step rfl rfl, confined_single trivial, nonLockErrOk_mapErrno _ _ _⟩

/-- Confined trace specification for `(SysBridge.mkRawDirOpsM ...).lstatAt`. -/
theorem dirOps_lstatAt_trace {W : Type} {proj : W → FsWorld} {cap : HealthyFilesCapM (StateM W)}
    (hCap : Core.RefinesStep proj Model.fsWorldWf (Model.execFilesCapStep cap) Model.allowedFilesCapStep)
    (dirFd : HandleId) (name : EntryName) (held : List HandleId) {s : W} (hWf : fsWorldWf (proj s) = true) :
    let p := ((SysBridge.mkRawDirOpsM cap.files cap.nextTempSeq).lstatAt dirFd name).run s
    fsWorldWf (proj p.2) = true ∧
    (proj p.2).tempSeq = (proj s).tempSeq ∧
    ∃ tr,
      HealthyFilesSteps (proj s).env tr (proj p.2).env ∧
      TraceFds held tr held ∧
      (∀ step ∈ tr, SubtreeConfinedReq step.1) ∧
      match p.1 with
      | .ok st => StatTrace (some dirFd) name.val.toUTF8 false st tr
      | .error e => nonLockErrOk e ∧ (e.kind = .notFound → ∃ r, (r, .err Errno.ENOENT) ∈ tr) := by
  have hFs := retryEintr_single_req (cap.files.fstatat (some dirFd) name.val.toUTF8 { symlinkNofollow := true })
    (.fstatat (some dirFd) name.val.toUTF8 { symlinkNofollow := true }) outcomeOfStatted
    (fun s' hW => cap_method_step hCap (.fstatat (some dirFd) name.val.toUTF8 { symlinkNofollow := true })
      (cap.files.fstatat (some dirFd) name.val.toUTF8 { symlinkNofollow := true }) outcomeOfStatted rfl hW)
    (fun _ => rfl) DEFAULT_EINTR_FUEL hWf
  cases hR : (retryEintr (cap.files.fstatat (some dirFd) name.val.toUTF8 { symlinkNofollow := true }) DEFAULT_EINTR_FUEL s) with
  | mk res s1 =>
    rw [StateT.run] at hFs; rw [hR] at hFs; dsimp only at hFs
    obtain ⟨hWf1, hTmp1, trR, hSt1, hAll1⟩ := hFs
    simp only [SysBridge.mkRawDirOpsM, Bind.bind, StateT.bind, StateT.run, hR]
    have hFd1 : TraceFds held (trR ++ [(.fstatat (some dirFd) name.val.toUTF8 { symlinkNofollow := true }, outcomeOfStatted res)]) held :=
      traceFds_append (traceFds_eintr_retries (fun _ hc => by cases hc) hAll1)
        (traceFds_nonFd_step (by cases res <;> rfl) rfl)
    have hConf1 : ∀ step ∈ trR ++ [(.fstatat (some dirFd) name.val.toUTF8 { symlinkNofollow := true }, outcomeOfStatted res)],
        SubtreeConfinedReq step.1 :=
      confined_append (fun step hm => by rw [hAll1 step hm]; exact ⟨rfl, ⟨name, rfl⟩⟩)
        (confined_single ⟨rfl, ⟨name, rfl⟩⟩)
    cases res with
    | ok rawSt =>
      simp only [Pure.pure, StateT.pure]
      exact ⟨hWf1, hTmp1, _, hSt1, hFd1, hConf1,
        ⟨rawSt, by simp [outcomeOfStatted], sysBridge_statInfoToFileStat_eq rawSt⟩⟩
    | error e =>
      simp only [Pure.pure, StateT.pure]
      refine ⟨hWf1, hTmp1, _, hSt1, hFd1, hConf1, nonLockErrOk_mapErrno _ _ _, fun hNf => ?_⟩
      have hEq := mapErrno_kind_notFound_eq _ _ _ hNf
      subst hEq
      exact ⟨.fstatat (some dirFd) name.val.toUTF8 { symlinkNofollow := true }, by simp [outcomeOfStatted]⟩

/-- Confined trace specification for `(SysBridge.mkRawDirOpsM ...).createDirAt`. -/
theorem dirOps_createDirAt_trace {W : Type} {proj : W → FsWorld} {cap : HealthyFilesCapM (StateM W)}
    (hCap : Core.RefinesStep proj Model.fsWorldWf (Model.execFilesCapStep cap) Model.allowedFilesCapStep)
    (dirFd : HandleId) (name : EntryName) (held : List HandleId) {s : W} (hWf : fsWorldWf (proj s) = true) :
    let p := ((SysBridge.mkRawDirOpsM cap.files cap.nextTempSeq).createDirAt dirFd name).run s
    fsWorldWf (proj p.2) = true ∧
    (proj p.2).tempSeq = (proj s).tempSeq ∧
    ∃ tr,
      HealthyFilesSteps (proj s).env tr (proj p.2).env ∧
      TraceFds held tr held ∧
      (∀ step ∈ tr, SubtreeConfinedReq step.1) ∧
      match p.1 with
      | .ok () => MkdirTrace (some dirFd) name.val.toUTF8 tr
      | .error e => nonLockErrOk e := by
  have hMk := retryEintr_single_req (cap.files.mkdirat (some dirFd) name.val.toUTF8 0o755)
    (.mkdirat (some dirFd) name.val.toUTF8 0o755) outcomeOfUnit
    (fun s' hW => cap_method_step hCap (.mkdirat (some dirFd) name.val.toUTF8 0o755)
      (cap.files.mkdirat (some dirFd) name.val.toUTF8 0o755) outcomeOfUnit rfl hW)
    (fun _ => rfl) DEFAULT_EINTR_FUEL hWf
  cases hR : (retryEintr (cap.files.mkdirat (some dirFd) name.val.toUTF8 0o755) DEFAULT_EINTR_FUEL s) with
  | mk res s1 =>
    rw [StateT.run] at hMk; rw [hR] at hMk; dsimp only at hMk
    obtain ⟨hWf1, hTmp1, trR, hSt1, hAll1⟩ := hMk
    simp only [SysBridge.mkRawDirOpsM, Bind.bind, StateT.bind, StateT.run, hR]
    have hFd1 : TraceFds held (trR ++ [(.mkdirat (some dirFd) name.val.toUTF8 0o755, outcomeOfUnit res)]) held :=
      traceFds_append (traceFds_eintr_retries (fun _ hc => by cases hc) hAll1)
        (traceFds_nonFd_step (by cases res <;> rfl) rfl)
    have hConf1 : ∀ step ∈ trR ++ [(.mkdirat (some dirFd) name.val.toUTF8 0o755, outcomeOfUnit res)],
        SubtreeConfinedReq step.1 :=
      confined_append (fun step hm => by rw [hAll1 step hm]; exact ⟨name, rfl⟩)
        (confined_single ⟨name, rfl⟩)
    cases res with
    | ok u => cases u; simp only [Pure.pure, StateT.pure]; exact ⟨hWf1, hTmp1, _, hSt1, hFd1, hConf1, by simp [MkdirTrace, outcomeOfUnit]⟩
    | error e => simp only [Pure.pure, StateT.pure]; exact ⟨hWf1, hTmp1, _, hSt1, hFd1, hConf1, nonLockErrOk_mapErrno _ _ _⟩

/-- Confined trace specification for `(SysBridge.mkRawDirOpsM ...).renameAt`. -/
theorem dirOps_renameAt_trace {W : Type} {proj : W → FsWorld} {cap : HealthyFilesCapM (StateM W)}
    (hCap : Core.RefinesStep proj Model.fsWorldWf (Model.execFilesCapStep cap) Model.allowedFilesCapStep)
    (srcFd : HandleId) (srcName : EntryName) (dstFd : HandleId) (dstName : EntryName)
    (held : List HandleId) {s : W} (hWf : fsWorldWf (proj s) = true) :
    let p := ((SysBridge.mkRawDirOpsM cap.files cap.nextTempSeq).renameAt srcFd srcName dstFd dstName).run s
    fsWorldWf (proj p.2) = true ∧
    (proj p.2).tempSeq = (proj s).tempSeq ∧
    ∃ tr,
      HealthyFilesSteps (proj s).env tr (proj p.2).env ∧
      TraceFds held tr held ∧
      (∀ step ∈ tr, SubtreeConfinedReq step.1) ∧
      match p.1 with
      | .ok () => RenameTrace (some srcFd) srcName.val.toUTF8 (some dstFd) dstName.val.toUTF8 tr
      | .error e => nonLockErrOk e := by
  have hRn := retryEintr_single_req (cap.files.renameat2 (some srcFd) srcName.val.toUTF8 (some dstFd) dstName.val.toUTF8 {})
    (.renameat2 (some srcFd) srcName.val.toUTF8 (some dstFd) dstName.val.toUTF8 {}) outcomeOfUnit
    (fun s' hW => cap_method_step hCap (.renameat2 (some srcFd) srcName.val.toUTF8 (some dstFd) dstName.val.toUTF8 {})
      (cap.files.renameat2 (some srcFd) srcName.val.toUTF8 (some dstFd) dstName.val.toUTF8 {}) outcomeOfUnit rfl hW)
    (fun _ => rfl) DEFAULT_EINTR_FUEL hWf
  cases hR : (retryEintr (cap.files.renameat2 (some srcFd) srcName.val.toUTF8 (some dstFd) dstName.val.toUTF8 {}) DEFAULT_EINTR_FUEL s) with
  | mk res s1 =>
    rw [StateT.run] at hRn; rw [hR] at hRn; dsimp only at hRn
    obtain ⟨hWf1, hTmp1, trR, hSt1, hAll1⟩ := hRn
    simp only [SysBridge.mkRawDirOpsM, Bind.bind, StateT.bind, StateT.run, hR]
    have hFd1 : TraceFds held (trR ++ [(.renameat2 (some srcFd) srcName.val.toUTF8 (some dstFd) dstName.val.toUTF8 {}, outcomeOfUnit res)]) held :=
      traceFds_append (traceFds_eintr_retries (fun _ hc => by cases hc) hAll1)
        (traceFds_nonFd_step (by cases res <;> rfl) rfl)
    have hConf1 : ∀ step ∈ trR ++ [(.renameat2 (some srcFd) srcName.val.toUTF8 (some dstFd) dstName.val.toUTF8 {}, outcomeOfUnit res)],
        SubtreeConfinedReq step.1 :=
      confined_append (fun step hm => by rw [hAll1 step hm]; exact ⟨⟨srcName, rfl⟩, ⟨dstName, rfl⟩⟩)
        (confined_single ⟨⟨srcName, rfl⟩, ⟨dstName, rfl⟩⟩)
    cases res with
    | ok u => cases u; simp only [Pure.pure, StateT.pure]; exact ⟨hWf1, hTmp1, _, hSt1, hFd1, hConf1, by simp [RenameTrace, outcomeOfUnit]⟩
    | error e => simp only [Pure.pure, StateT.pure]; exact ⟨hWf1, hTmp1, _, hSt1, hFd1, hConf1, nonLockErrOk_mapErrno _ _ _⟩

/-- Confined trace specification for `(SysBridge.mkRawDirOpsM ...).unlinkAt`. -/
theorem dirOps_unlinkAt_trace {W : Type} {proj : W → FsWorld} {cap : HealthyFilesCapM (StateM W)}
    (hCap : Core.RefinesStep proj Model.fsWorldWf (Model.execFilesCapStep cap) Model.allowedFilesCapStep)
    (dirFd : HandleId) (name : EntryName) (isDir : Bool) (held : List HandleId)
    {s : W} (hWf : fsWorldWf (proj s) = true) :
    let p := ((SysBridge.mkRawDirOpsM cap.files cap.nextTempSeq).unlinkAt dirFd name isDir).run s
    fsWorldWf (proj p.2) = true ∧
    (proj p.2).tempSeq = (proj s).tempSeq ∧
    ∃ tr,
      HealthyFilesSteps (proj s).env tr (proj p.2).env ∧
      TraceFds held tr held ∧
      (∀ step ∈ tr, SubtreeConfinedReq step.1) ∧
      match p.1 with
      | .ok () => UnlinkTrace (some dirFd) name.val.toUTF8 isDir tr
      | .error e => nonLockErrOk e ∧ (e.kind = .notFound → ∃ r, (r, .err Errno.ENOENT) ∈ tr) := by
  cases isDir with
  | true =>
    have hRm := removeDirAtOpt_trace hCap (some dirFd) name.val held DEFAULT_EINTR_FUEL hWf
    cases hR : (SysBridge.removeDirAtOpt cap.files (some dirFd) name.val DEFAULT_EINTR_FUEL s) with
    | mk res s1 =>
      rw [StateT.run] at hRm; rw [hR] at hRm; dsimp only at hRm
      obtain ⟨hWf1, hTmp1, tr, hSt, hFd, _, hAll, hOut⟩ := hRm
      simp only [SysBridge.mkRawDirOpsM, ↓reduceIte, StateT.run, hR]
      have hConf : ∀ step ∈ tr, SubtreeConfinedReq step.1 := fun step hm => by
        obtain ⟨o, hEq⟩ := hAll step hm; rw [hEq]; exact ⟨name, rfl⟩
      refine ⟨hWf1, hTmp1, tr, hSt, hFd, hConf, ?_⟩
      cases res with
      | ok u => cases u; exact hOut
      | error e => exact ⟨hOut.1, fun hNf => ⟨_, hOut.2 hNf⟩⟩
  | false =>
    have hUn := retryEintr_single_req (cap.files.unlinkat (some dirFd) name.val.toUTF8 false)
      (.unlinkat (some dirFd) name.val.toUTF8 false) outcomeOfUnit
      (fun s' hW => cap_method_step hCap (.unlinkat (some dirFd) name.val.toUTF8 false)
        (cap.files.unlinkat (some dirFd) name.val.toUTF8 false) outcomeOfUnit rfl hW)
      (fun _ => rfl) DEFAULT_EINTR_FUEL hWf
    cases hR : (retryEintr (cap.files.unlinkat (some dirFd) name.val.toUTF8 false) DEFAULT_EINTR_FUEL s) with
    | mk res s1 =>
      rw [StateT.run] at hUn; rw [hR] at hUn; dsimp only at hUn
      obtain ⟨hWf1, hTmp1, trR, hSt1, hAll1⟩ := hUn
      simp only [SysBridge.mkRawDirOpsM, Bool.false_eq_true, ↓reduceIte, Bind.bind, StateT.bind, StateT.run, hR]
      have hFd1 : TraceFds held (trR ++ [(.unlinkat (some dirFd) name.val.toUTF8 false, outcomeOfUnit res)]) held :=
        traceFds_append (traceFds_eintr_retries (fun _ hc => by cases hc) hAll1)
          (traceFds_nonFd_step (by cases res <;> rfl) rfl)
      have hConf1 : ∀ step ∈ trR ++ [(.unlinkat (some dirFd) name.val.toUTF8 false, outcomeOfUnit res)],
          SubtreeConfinedReq step.1 :=
        confined_append (fun step hm => by rw [hAll1 step hm]; exact ⟨name, rfl⟩)
          (confined_single ⟨name, rfl⟩)
      cases res with
      | ok u => cases u; simp only [Pure.pure, StateT.pure]; exact ⟨hWf1, hTmp1, _, hSt1, hFd1, hConf1, by simp [UnlinkTrace, outcomeOfUnit]⟩
      | error e =>
        simp only [Pure.pure, StateT.pure]
        refine ⟨hWf1, hTmp1, _, hSt1, hFd1, hConf1, nonLockErrOk_mapErrno _ _ _, fun hNf => ?_⟩
        have hEq := mapErrno_kind_notFound_eq _ _ _ hNf
        subst hEq
        exact ⟨.unlinkat (some dirFd) name.val.toUTF8 false, by simp [outcomeOfUnit]⟩

/-- Confined trace specification for `(SysBridge.mkRawDirOpsM ...).symlinkAt`. -/
theorem dirOps_symlinkAt_trace {W : Type} {proj : W → FsWorld} {cap : HealthyFilesCapM (StateM W)}
    (hCap : Core.RefinesStep proj Model.fsWorldWf (Model.execFilesCapStep cap) Model.allowedFilesCapStep)
    (target : String) (dirFd : HandleId) (name : EntryName) (held : List HandleId)
    {s : W} (hWf : fsWorldWf (proj s) = true) :
    let p := ((SysBridge.mkRawDirOpsM cap.files cap.nextTempSeq).symlinkAt target dirFd name).run s
    fsWorldWf (proj p.2) = true ∧
    (proj p.2).tempSeq = (proj s).tempSeq ∧
    ∃ tr,
      HealthyFilesSteps (proj s).env tr (proj p.2).env ∧
      TraceFds held tr held ∧
      (∀ step ∈ tr, SubtreeConfinedReq step.1) ∧
      match p.1 with
      | .ok () => SymlinkTrace target.toUTF8 (some dirFd) name.val.toUTF8 tr
      | .error e => nonLockErrOk e := by
  simp only [SysBridge.mkRawDirOpsM]
  by_cases hBad : (target.isEmpty || target.toList.contains (Char.ofNat 0)) = true
  · simp only [hBad, ↓reduceIte, Pure.pure, StateT.pure, StateT.run]
    exact ⟨hWf, trivial, [], HealthyFilesSteps.nil _, TraceFds.nil _, confined_nil,
      nonLockErrOk_mapErrno _ _ _⟩
  · simp only [hBad, Bool.false_eq_true, ↓reduceIte]
    have hSy := retryEintr_single_req (cap.files.symlinkat target.toUTF8 (some dirFd) name.val.toUTF8)
      (.symlinkat target.toUTF8 (some dirFd) name.val.toUTF8) outcomeOfUnit
      (fun s' hW => cap_method_step hCap (.symlinkat target.toUTF8 (some dirFd) name.val.toUTF8)
        (cap.files.symlinkat target.toUTF8 (some dirFd) name.val.toUTF8) outcomeOfUnit rfl hW)
      (fun _ => rfl) DEFAULT_EINTR_FUEL hWf
    cases hR : (retryEintr (cap.files.symlinkat target.toUTF8 (some dirFd) name.val.toUTF8) DEFAULT_EINTR_FUEL s) with
    | mk res s1 =>
      rw [StateT.run] at hSy; rw [hR] at hSy; dsimp only at hSy
      obtain ⟨hWf1, hTmp1, trR, hSt1, hAll1⟩ := hSy
      simp only [Bind.bind, StateT.bind, StateT.run, hR]
      have hFd1 : TraceFds held (trR ++ [(.symlinkat target.toUTF8 (some dirFd) name.val.toUTF8, outcomeOfUnit res)]) held :=
        traceFds_append (traceFds_eintr_retries (fun _ hc => by cases hc) hAll1)
          (traceFds_nonFd_step (by cases res <;> rfl) rfl)
      have hConf1 : ∀ step ∈ trR ++ [(.symlinkat target.toUTF8 (some dirFd) name.val.toUTF8, outcomeOfUnit res)],
          SubtreeConfinedReq step.1 :=
        confined_append (fun step hm => by rw [hAll1 step hm]; exact ⟨name, rfl⟩)
          (confined_single ⟨name, rfl⟩)
      cases res with
      | ok u => cases u; simp only [Pure.pure, StateT.pure]; exact ⟨hWf1, hTmp1, _, hSt1, hFd1, hConf1, by simp [SymlinkTrace, outcomeOfUnit]⟩
      | error e => simp only [Pure.pure, StateT.pure]; exact ⟨hWf1, hTmp1, _, hSt1, hFd1, hConf1, nonLockErrOk_mapErrno _ _ _⟩

/-- Confined zero-syscall trace specification for `(SysBridge.mkRawDirOpsM ...).freshTempName`. -/
theorem dirOps_freshTempName_trace {W : Type} {proj : W → FsWorld} {cap : HealthyFilesCapM (StateM W)}
    (hCap : Core.RefinesStep proj Model.fsWorldWf (Model.execFilesCapStep cap) Model.allowedFilesCapStep)
    (held : List HandleId) {s : W} (hWf : fsWorldWf (proj s) = true) :
    let p := ((SysBridge.mkRawDirOpsM cap.files cap.nextTempSeq).freshTempName).run s
    fsWorldWf (proj p.2) = true ∧
    (proj s).tempSeq ≤ (proj p.2).tempSeq ∧
    HealthyFilesSteps (proj s).env [] (proj p.2).env ∧
    TraceFds held [] held := by
  have hN := cap_nextTempSeq hCap hWf
  cases hR : cap.nextTempSeq s with
  | mk n s1 =>
    simp only [StateT.run, hR] at hN
    obtain ⟨hWf1, hEnv1, _, hTmp1⟩ := hN
    simp only [SysBridge.mkRawDirOpsM, Bind.bind, StateT.bind, Pure.pure, StateT.pure, StateT.run, hR]
    exact ⟨hWf1, by omega, hEnv1 ▸ HealthyFilesSteps.nil _, TraceFds.nil _⟩

end LeanSwe.Fs.Proofs
