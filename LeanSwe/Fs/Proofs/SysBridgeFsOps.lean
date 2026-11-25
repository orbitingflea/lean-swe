import LeanSwe.Fs.Proofs.SysBridgeFsProofs

namespace LeanSwe.Fs.Proofs

open LeanSwe.LinuxSyscall
open LeanSwe.LinuxSyscall.Files
open LeanSwe.Fs
open LeanSwe.Fs.Model

/-- Trace specification for `SysBridge.createFileNewPure`. -/
theorem createFileNewPure_trace {W fd : Type} {proj : W → FsWorld} {hidOf : fd → HandleId}
    {files : FilesOpsM (StateM W) fd} {nextNonce : StateM W Nat}
    (hCap : RefinesFsFilesFixed proj hidOf files nextNonce)
    (path : String) (bytes : ByteArray) (eintrFuel : Nat) {s : W} (hWf : fsWorldWf (proj s) = true) :
    let p := (SysBridge.createFileNewPure files path bytes eintrFuel).run s
    fsWorldWf (proj p.2) = true ∧
    (proj p.2).tempSeq = (proj s).tempSeq ∧
    ∃ tr,
      FsWorldTrace (proj s) tr (proj p.2) ∧
      match p.1 with
      | .ok () => WriteFileTrace none path.toUTF8 createNewOpenFlags 0o644 bytes tr
      | .error e => nonLockErrOk e ∧ (tr ≠ [] ∨ (isValidRawPath path = false ∧ e.kind = .invalidInput)) := by
  unfold SysBridge.createFileNewPure
  by_cases hVal : isValidRawPath path = true
  · simp only [hVal, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    have hOp := retryEintr_single_req (files.openat none path.toUTF8 createNewOpenFlags 0o644)
      (.openat none path.toUTF8 createNewOpenFlags 0o644) (outcomeOfOpenedFd hidOf)
      (fun s' hW => cap_opened_step hCap (.openat none path.toUTF8 createNewOpenFlags 0o644)
        (files.openat none path.toUTF8 createNewOpenFlags 0o644) rfl hW)
      (fun _ => rfl) eintrFuel hWf
    cases hR : (retryEintr (files.openat none path.toUTF8 createNewOpenFlags 0o644) eintrFuel s) with
    | mk oRes s1 =>
      rw [StateT.run] at hOp; rw [hR] at hOp; dsimp only at hOp
      obtain ⟨hWf1, hTmp1, trR, hStO, hAllO⟩ := hOp
      dsimp only [createNewOpenFlags] at hR
      simp only [Bind.bind, StateT.bind, StateT.run, hR]
      have hFdR : TraceFds [] trR [] := traceFds_eintr_retries (fun _ hc => by cases hc) hAllO
      cases oRes with
      | error e =>
        simp only [Pure.pure, StateT.pure]
        have hTrO : FsWorldTrace (proj s) (trR ++ [(.openat none path.toUTF8 createNewOpenFlags 0o644, .err e)]) (proj s1) :=
          ⟨hWf1, hStO, traceFds_append hFdR (traceFds_nonFd_step rfl rfl), by omega⟩
        exact ⟨hWf1, hTmp1, _, hTrO, nonLockErrOk_mapErrno _ _ _, Or.inl (by simp)⟩
      | ok h =>
        have hFdO : TraceFds [] (trR ++ [(.openat none path.toUTF8 createNewOpenFlags 0o644, .opened (hidOf h))]) [hidOf h] :=
          traceFds_append hFdR (traceFds_open_step rfl rfl)
        have hWr := writeAllAndClose_trace hCap h path bytes [] eintrFuel hWf1
        cases hRw : (SysBridge.writeAllAndClose files h path bytes eintrFuel s1) with
        | mk wRes s2 =>
          rw [StateT.run] at hWr; rw [hRw] at hWr; dsimp only at hWr
          obtain ⟨hWf2, hTmp2, trW, trC, hStWC, hFdW, hFdC, _, hCeq, hOutW⟩ := hWr
          simp only [Bind.bind, StateT.bind, hRw]
          let trOpen := trR ++ [(.openat none path.toUTF8 createNewOpenFlags 0o644, .opened (hidOf h))]
          have hTrOWC : FsWorldTrace (proj s) (trOpen ++ trW ++ trC) (proj s2) :=
            ⟨hWf2, by rw [List.append_assoc]; exact healthyFilesSteps_append hStO hStWC,
             by rw [List.append_assoc]; exact traceFds_append hFdO (traceFds_append hFdW hFdC), by omega⟩
          cases wRes with
          | ok u =>
            cases u
            simp only [Pure.pure, StateT.pure]
            obtain ⟨co, rfl⟩ := hCeq
            exact ⟨hWf2, hTmp2.trans hTmp1, trOpen ++ trW ++ [(.close (hidOf h), co)], hTrOWC,
              hidOf h, trOpen, trW, [(.close (hidOf h), co)], rfl, by simp [trOpen], hOutW, co, by simp⟩
          | error err =>
            have hUn := cap_unit_step hCap (.unlinkat none path.toUTF8 false)
              (files.unlinkat none path.toUTF8 false) rfl hWf2
            cases hRu : files.unlinkat none path.toUTF8 false s2 with
            | mk uRes s3 =>
              have hUn' : fsWorldWf (proj s3) = true ∧
                  healthyStep (proj s2).env (.unlinkat none path.toUTF8 false) (outcomeOfUnit uRes) = some (proj s3).env ∧
                  (proj s3).tempSeq = (proj s2).tempSeq := by
                rw [StateT.run] at hUn; rw [hRu] at hUn; exact hUn
              simp only [Bind.bind, StateT.bind, Pure.pure, StateT.pure, hRu]
              have hTrU : FsWorldTrace (proj s2) [(.unlinkat none path.toUTF8 false, outcomeOfUnit uRes)] (proj s3) :=
                ⟨hUn'.1, healthyFilesSteps_single hUn'.2.1,
                 traceFds_nonFd_step (by cases uRes <;> rfl) rfl, by omega⟩
              exact ⟨hUn'.1, hUn'.2.2.trans (hTmp2.trans hTmp1), _,
                fsWorldTrace_append hTrOWC hTrU, hOutW, Or.inl (by simp)⟩
  · have hValF : isValidRawPath path = false := Bool.eq_false_iff.mpr hVal
    simp only [hValF, Bool.not_false, ↓reduceIte, Pure.pure, StateT.pure, StateT.run]
    exact ⟨hWf, trivial, [], fsWorldTrace_nil hWf, nonLockErrOk_mapErrno _ _ _, Or.inr ⟨trivial, rfl⟩⟩

/-- Trace specification for `SysBridge.readDirPure`. -/
theorem readDirPure_trace {W fd : Type} {proj : W → FsWorld} {hidOf : fd → HandleId}
    {files : FilesOpsM (StateM W) fd} {nextNonce : StateM W Nat}
    (hCap : RefinesFsFilesFixed proj hidOf files nextNonce)
    (path : String) (eintrFuel streamFuel : Nat) {s : W} (hWf : fsWorldWf (proj s) = true) :
    let p := (SysBridge.readDirPure files path eintrFuel streamFuel).run s
    fsWorldWf (proj p.2) = true ∧
    (proj p.2).tempSeq = (proj s).tempSeq ∧
    ∃ tr,
      FsWorldTrace (proj s) tr (proj p.2) ∧
      match p.1 with
      | .ok xs => ReadDirTrace path.toUTF8 xs tr
      | .error e => nonLockErrOk e ∧ tr ≠ [] := by
  unfold SysBridge.readDirPure
  have hOp := retryEintr_single_req (files.openat none path.toUTF8 dirOpenFlags 0)
    (.openat none path.toUTF8 dirOpenFlags 0) (outcomeOfOpenedFd hidOf)
    (fun s' hW => cap_opened_step hCap (.openat none path.toUTF8 dirOpenFlags 0)
      (files.openat none path.toUTF8 dirOpenFlags 0) rfl hW)
    (fun _ => rfl) eintrFuel hWf
  cases hR : (retryEintr (files.openat none path.toUTF8 dirOpenFlags 0) eintrFuel s) with
  | mk oRes s1 =>
    rw [StateT.run] at hOp; rw [hR] at hOp; dsimp only at hOp
    obtain ⟨hWf1, hTmp1, trR, hStO, hAllO⟩ := hOp
    dsimp only [dirOpenFlags] at hR
    simp only [Bind.bind, StateT.bind, StateT.run, hR]
    have hFdR : TraceFds [] trR [] := traceFds_eintr_retries (fun _ hc => by cases hc) hAllO
    cases oRes with
    | error e =>
      simp only [Pure.pure, StateT.pure]
      have hTrO : FsWorldTrace (proj s) (trR ++ [(.openat none path.toUTF8 dirOpenFlags 0, .err e)]) (proj s1) :=
        ⟨hWf1, hStO, traceFds_append hFdR (traceFds_nonFd_step rfl rfl), by omega⟩
      exact ⟨hWf1, hTmp1, _, hTrO, nonLockErrOk_mapErrno _ _ _, by simp⟩
    | ok h =>
      let trOpen := trR ++ [(.openat none path.toUTF8 dirOpenFlags 0, .opened (hidOf h))]
      have hFdO : TraceFds [] trOpen [hidOf h] := traceFds_append hFdR (traceFds_open_step rfl rfl)
      have hRd := readDirStreamLoop_trace hCap h path [hidOf h] #[] streamFuel (fun _ hm => by simp at hm) hWf1
      cases hRl : (SysBridge.readDirStreamLoop files h path #[] streamFuel s1) with
      | mk dRes s2 =>
        rw [StateT.run] at hRd; rw [hRl] at hRd; dsimp only at hRd
        obtain ⟨hWf2, hTmp2, trB, hStB, hFdB, _, hOutB⟩ := hRd
        simp only [Bind.bind, StateT.bind, hRl]
        cases dRes with
        | error err =>
          have hQ := closeQuiet_trace hCap h [] hWf2
          cases hRq : (SysBridge.closeQuiet files h s2) with
          | mk u s3 =>
            rw [StateT.run] at hQ; rw [hRq] at hQ; dsimp only at hQ
            obtain ⟨hWf3, hTmp3, co, hStC, hFdC, _⟩ := hQ
            simp only [Pure.pure, StateT.bind, StateT.pure, hRq]
            have hTrAll : FsWorldTrace (proj s) (trOpen ++ trB ++ [(.close (hidOf h), co)]) (proj s3) :=
              ⟨hWf3, healthyFilesSteps_append (healthyFilesSteps_append hStO hStB) hStC,
               traceFds_append (traceFds_append hFdO hFdB) hFdC, by omega⟩
            exact ⟨hWf3, hTmp3.trans (hTmp2.trans hTmp1), _, hTrAll, hOutB, by simp [trOpen]⟩
        | ok entries =>
          have hCc := closeCheck_trace hCap h (some path) [] hWf2
          cases hRc : (SysBridge.closeCheck files h (some path) s2) with
          | mk cRes s3 =>
            rw [StateT.run] at hCc; rw [hRc] at hCc; dsimp only at hCc
            obtain ⟨hWf3, hTmp3, hErrC, co, hStC, hFdC, _⟩ := hCc
            simp only [StateT.bind, hRc]
            have hTrAll : FsWorldTrace (proj s) (trOpen ++ trB ++ [(.close (hidOf h), co)]) (proj s3) :=
              ⟨hWf3, healthyFilesSteps_append (healthyFilesSteps_append hStO hStB) hStC,
               traceFds_append (traceFds_append hFdO hFdB) hFdC, by omega⟩
            cases cRes with
            | error ce =>
              simp only [Pure.pure]
              exact ⟨hWf3, hTmp3.trans (hTmp2.trans hTmp1), _, hTrAll, hErrC, by simp [trOpen]⟩
            | ok u =>
              cases u
              simp only [Pure.pure]
              obtain ⟨hNoDot, ⟨eof, hMemE, hEz⟩, hNonEmp⟩ := hOutB
              exact ⟨hWf3, hTmp3.trans (hTmp2.trans hTmp1), _, hTrAll, hNoDot, hidOf h, eof, trOpen, trB,
                [(.close (hidOf h), co)], rfl, by simp [trOpen], hMemE, hEz,
                fun hGt => hNonEmp (by simpa using hGt), co, by simp⟩

/-- Trace specification for `SysBridge.acquireLockPure`. -/
theorem acquireLockPure_trace {W fd : Type} {proj : W → FsWorld} {hidOf : fd → HandleId}
    {files : FilesOpsM (StateM W) fd} {nextNonce : StateM W Nat}
    (hCap : RefinesFsFilesFixed proj hidOf files nextNonce)
    (path : String) (mode : LockMode) (createIfMissing nonBlocking : Bool) (eintrFuel : Nat)
    {s : W} (hWf : fsWorldWf (proj s) = true) :
    let p := (SysBridge.acquireLockPure files path mode createIfMissing nonBlocking eintrFuel).run s
    fsWorldWf (proj p.2) = true ∧
    (proj p.2).tempSeq = (proj s).tempSeq ∧
    match p.1 with
    | .ok h =>
      ∃ rawSt fl modeArg trOpen trLock,
        HealthyFilesSteps (proj s).env (trOpen ++ trLock) (proj p.2).env ∧
        TraceFds [] trOpen [hidOf h] ∧
        TraceFds [hidOf h] trLock [hidOf h] ∧
        fl.access = .rdonly ∧ fl.nofollow = true ∧ fl.cloexec = true ∧ fl.nonblock = true ∧
        (.openat none path.toUTF8 fl modeArg, .opened (hidOf h)) ∈ trOpen ∧
        (.fstat (hidOf h), .statted rawSt) ∈ trLock ∧ rawSt.kind = .reg ∧
        (.flock (hidOf h) (lockModeToFlockOp mode nonBlocking), .unit) ∈ trLock
    | .error e =>
      ∃ tr,
        FsWorldTrace (proj s) tr (proj p.2) ∧
        ((nonLockErrOk e ∧ (tr ≠ [] ∨ (isValidRawPath path = false ∧ e.kind = .invalidInput))) ∨
         (e.kind = .wouldBlock ∧ nonBlocking = true ∧ TryLockContendedTrace none path.toUTF8 mode tr)) := by
  unfold SysBridge.acquireLockPure
  by_cases hVal : isValidRawPath path = true
  · simp only [hVal, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    let baseFlags : OpenFlags := { access := .rdonly, nofollow := true, cloexec := true, nonblock := true }
    let creatFlags : OpenFlags := { access := .rdonly, creat := true, nofollow := true, cloexec := true, nonblock := true }
    have hAfterOpen : ∀ {sX : W} {fdRes : Except Errno fd} {trOpen : List KernelStep},
        fsWorldWf (proj sX) = true →
        (proj sX).tempSeq = (proj s).tempSeq →
        HealthyFilesSteps (proj s).env trOpen (proj sX).env →
        (match fdRes with
         | .ok h =>
           TraceFds [] trOpen [hidOf h] ∧
           ∃ fl modeArg, fl.access = .rdonly ∧ fl.nofollow = true ∧ fl.cloexec = true ∧ fl.nonblock = true ∧
             (.openat none path.toUTF8 fl modeArg, .opened (hidOf h)) ∈ trOpen
         | .error _ => TraceFds [] trOpen [] ∧ trOpen ≠ []) →
        let p := (match fdRes with
          | .error e =>
            if e == Errno.ELOOP || e == Errno.ENXIO then
              pure (.error (SysBridge.mapErrno (some path) "open" Errno.EINVAL))
            else
              pure (.error (SysBridge.mapErrno (some path) "open" e))
          | .ok h => SysBridge.finishLockFd files h path mode nonBlocking eintrFuel : StateM W (Except FsError fd)).run sX
        fsWorldWf (proj p.2) = true ∧ (proj p.2).tempSeq = (proj s).tempSeq ∧
        match p.1 with
        | .ok h =>
          ∃ rawSt fl modeArg trO trLock,
            HealthyFilesSteps (proj s).env (trO ++ trLock) (proj p.2).env ∧
            TraceFds [] trO [hidOf h] ∧ TraceFds [hidOf h] trLock [hidOf h] ∧
            fl.access = .rdonly ∧ fl.nofollow = true ∧ fl.cloexec = true ∧ fl.nonblock = true ∧
            (.openat none path.toUTF8 fl modeArg, .opened (hidOf h)) ∈ trO ∧
            (.fstat (hidOf h), .statted rawSt) ∈ trLock ∧ rawSt.kind = .reg ∧
            (.flock (hidOf h) (lockModeToFlockOp mode nonBlocking), .unit) ∈ trLock
        | .error e =>
          ∃ tr, FsWorldTrace (proj s) tr (proj p.2) ∧
            ((nonLockErrOk e ∧ (tr ≠ [] ∨ (true = false ∧ e.kind = .invalidInput))) ∨
             (e.kind = .wouldBlock ∧ nonBlocking = true ∧ TryLockContendedTrace none path.toUTF8 mode tr)) := by
      intro sX fdRes trOpen hWfX hTmpX hStX hFdX
      cases fdRes with
      | error e =>
        by_cases hBad : (e == Errno.ELOOP || e == Errno.ENXIO) = true <;>
          simp only [hBad, Bool.false_eq_true, ↓reduceIte, Pure.pure, StateT.pure, StateT.run]
        · exact ⟨hWfX, hTmpX, trOpen, ⟨hWfX, hStX, hFdX.1, by omega⟩,
            Or.inl ⟨nonLockErrOk_mapErrno _ _ _, Or.inl hFdX.2⟩⟩
        · exact ⟨hWfX, hTmpX, trOpen, ⟨hWfX, hStX, hFdX.1, by omega⟩,
            Or.inl ⟨nonLockErrOk_mapErrno _ _ _, Or.inl hFdX.2⟩⟩
      | ok h =>
        obtain ⟨hFdO, fl, modeArg, hAcc, hNf, hCl, hNb, hMemO⟩ := hFdX
        have hFin := finishLockFd_trace hCap h path mode nonBlocking [] eintrFuel hWfX
        cases hRf : (SysBridge.finishLockFd files h path mode nonBlocking eintrFuel sX) with
        | mk fRes sF =>
          simp only [StateT.run, hRf] at hFin ⊢
          obtain ⟨hWfF, hTmpF, hOutF⟩ := hFin
          cases fRes with
          | ok h' =>
            obtain ⟨rfl, rawSt, trL, hStL, hFdL, _, hMemFs, hReg, hMemFl⟩ := hOutF
            exact ⟨hWfF, hTmpF.trans hTmpX, rawSt, fl, modeArg, trOpen, trL,
              healthyFilesSteps_append hStX hStL, hFdO, hFdL, hAcc, hNf, hCl, hNb, hMemO, hMemFs, hReg, hMemFl⟩
          | error e =>
            obtain ⟨trL, trC, hStLC, hFdL, hFdC, _, ⟨co, rfl⟩, hErrCase⟩ := hOutF
            have hTrAll : FsWorldTrace (proj s) (trOpen ++ trL ++ [(.close (hidOf h), co)]) (proj sF) :=
              ⟨hWfF, by rw [List.append_assoc]; exact healthyFilesSteps_append hStX hStLC,
               by rw [List.append_assoc]; exact traceFds_append hFdO (traceFds_append hFdL hFdC), by omega⟩
            refine ⟨hWfF, hTmpF.trans hTmpX, _, hTrAll, ?_⟩
            rcases hErrCase with hNl | ⟨hWb, hNbT, rawSt, hMemFs, hReg, hMemAg⟩
            · exact Or.inl ⟨hNl, Or.inl (by simp)⟩
            · exact Or.inr ⟨hWb, hNbT, hidOf h, rawSt, fl, modeArg, trOpen, trL, [(.close (hidOf h), co)],
                rfl, hAcc, hNf, hCl, hNb, hMemO, hMemFs, hReg, hMemAg, co, by simp⟩
    have hOp1 := retryEintr_single_req (files.openat none path.toUTF8 baseFlags 0)
      (.openat none path.toUTF8 baseFlags 0) (outcomeOfOpenedFd hidOf)
      (fun s' hW => cap_opened_step hCap (.openat none path.toUTF8 baseFlags 0)
        (files.openat none path.toUTF8 baseFlags 0) rfl hW)
      (fun _ => rfl) eintrFuel hWf
    cases hR1 : (retryEintr (files.openat none path.toUTF8 baseFlags 0) eintrFuel s) with
    | mk oRes1 s1 =>
      rw [StateT.run] at hOp1; rw [hR1] at hOp1; dsimp only at hOp1
      obtain ⟨hWf1, hTmp1, trR1, hSt1, hAll1⟩ := hOp1
      dsimp only [baseFlags] at hR1
      simp only [Bind.bind, StateT.bind, StateT.run, hR1]
      have hFdR1 : TraceFds [] trR1 [] := traceFds_eintr_retries (fun _ hc => by cases hc) hAll1
      cases oRes1 with
      | ok h =>
        simp only [Pure.pure, StateT.bind, StateT.pure]
        exact hAfterOpen (sX := s1) (fdRes := .ok h) (trOpen := trR1 ++ [(.openat none path.toUTF8 baseFlags 0, .opened (hidOf h))])
          hWf1 hTmp1 hSt1 ⟨traceFds_append hFdR1 (traceFds_open_step rfl rfl),
            baseFlags, 0, rfl, rfl, rfl, rfl, by simp⟩
      | error e1 =>
        have hFd1 : TraceFds [] (trR1 ++ [(.openat none path.toUTF8 baseFlags 0, .err e1)]) [] :=
          traceFds_append hFdR1 (traceFds_nonFd_step rfl rfl)
        by_cases hCr : (e1 == Errno.ENOENT && createIfMissing) = true
        · simp only [hCr, ↓reduceIte]
          have hOp2 := retryEintr_single_req (files.openat none path.toUTF8 creatFlags 0o644)
            (.openat none path.toUTF8 creatFlags 0o644) (outcomeOfOpenedFd hidOf)
            (fun s' hW => cap_opened_step hCap (.openat none path.toUTF8 creatFlags 0o644)
              (files.openat none path.toUTF8 creatFlags 0o644) rfl hW)
            (fun _ => rfl) eintrFuel hWf1
          cases hR2 : (retryEintr (files.openat none path.toUTF8 creatFlags 0o644) eintrFuel s1) with
          | mk oRes2 s2 =>
            rw [StateT.run] at hOp2; rw [hR2] at hOp2; dsimp only at hOp2
            obtain ⟨hWf2, hTmp2, trR2, hSt2, hAll2⟩ := hOp2
            dsimp only [creatFlags] at hR2
            simp only [StateT.bind, hR2]
            have hFdR2 : TraceFds [] trR2 [] := traceFds_eintr_retries (fun _ hc => by cases hc) hAll2
            have hSt12 := healthyFilesSteps_append hSt1 hSt2
            cases oRes2 with
            | ok h =>
              exact hAfterOpen (sX := s2) (fdRes := .ok h)
                (trOpen := (trR1 ++ [(.openat none path.toUTF8 baseFlags 0, .err e1)]) ++
                  (trR2 ++ [(.openat none path.toUTF8 creatFlags 0o644, .opened (hidOf h))]))
                hWf2 (hTmp2.trans hTmp1) hSt12
                ⟨traceFds_append hFd1 (traceFds_append hFdR2 (traceFds_open_step rfl rfl)),
                 creatFlags, 0o644, rfl, rfl, rfl, rfl, by simp⟩
            | error e2 =>
              exact hAfterOpen (sX := s2) (fdRes := .error e2)
                (trOpen := (trR1 ++ [(.openat none path.toUTF8 baseFlags 0, .err e1)]) ++
                  (trR2 ++ [(.openat none path.toUTF8 creatFlags 0o644, .err e2)]))
                hWf2 (hTmp2.trans hTmp1) hSt12
                ⟨traceFds_append hFd1 (traceFds_append hFdR2 (traceFds_nonFd_step rfl rfl)), by simp⟩
        · simp only [hCr, Bool.false_eq_true, ↓reduceIte, Pure.pure, StateT.bind, StateT.pure]
          exact hAfterOpen (sX := s1) (fdRes := .error e1)
            (trOpen := trR1 ++ [(.openat none path.toUTF8 baseFlags 0, .err e1)])
            hWf1 hTmp1 hSt1 ⟨hFd1, by simp⟩
  · have hValF : isValidRawPath path = false := Bool.eq_false_iff.mpr hVal
    simp only [hValF, Bool.not_false, ↓reduceIte, Pure.pure, StateT.pure, StateT.run]
    exact ⟨hWf, trivial, [], fsWorldTrace_nil hWf, Or.inl ⟨nonLockErrOk_mapErrno _ _ _, Or.inr ⟨trivial, rfl⟩⟩⟩

end LeanSwe.Fs.Proofs
