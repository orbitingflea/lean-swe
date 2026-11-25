import LeanSwe.Fs.Proofs.SysBridgeCore

namespace LeanSwe.Fs.Proofs

open LeanSwe.LinuxSyscall
open LeanSwe.LinuxSyscall.Files
open LeanSwe.Fs
open LeanSwe.Fs.Model

/-- Trace specification for `SysBridge.writeAllLoop`: writes exact `data.extract off data.size` and always closes `h`. -/
theorem writeAllLoop_trace {W : Type} {proj : W → FsWorld} {cap : HealthyFilesCapM (StateM W)}
    (hCap : Core.ObeysStep proj Model.fsWorldWf (Model.execFilesCapStep cap) Model.allowedFilesCapStep)
    (h : HandleId) (path : String) (data : ByteArray) (held : List HandleId)
    (off fuel : Nat) (hOff : off ≤ data.size) {s : W} (hWf : fsWorldWf (proj s) = true) :
    let p := (SysBridge.writeAllLoop cap.files h path data off fuel).run s
    fsWorldWf (proj p.2) = true ∧
    (proj p.2).tempSeq = (proj s).tempSeq ∧
    ∃ trWrite trClose,
      HealthyFilesSteps (proj s).env (trWrite ++ trClose) (proj p.2).env ∧
      TraceFds (h :: held) trWrite (h :: held) ∧
      TraceFds (h :: held) trClose held ∧
      (∀ step ∈ trWrite ++ trClose, SubtreeConfinedReq step.1) ∧
      (∃ co, trClose = [(.close h, co)]) ∧
      match p.1 with
      | .ok () => writtenBytesOn h trWrite = data.extract off data.size
      | .error e => nonLockErrOk e := by
  induction fuel generalizing off s with
  | zero =>
    unfold SysBridge.writeAllLoop
    have hQ := closeQuiet_trace hCap h held hWf
    cases hRq : (SysBridge.closeQuiet cap.files h s) with
    | mk u s1 =>
      rw [StateT.run] at hQ; rw [hRq] at hQ; dsimp only at hQ
      obtain ⟨hWf1, hTmp1, co, hStC, hFdC, hConf⟩ := hQ
      simp only [Bind.bind, StateT.bind, StateT.run, Pure.pure, StateT.pure, hRq]
      exact ⟨hWf1, hTmp1, [], [(.close h, co)], hStC, TraceFds.nil _, hFdC,
        confined_single hConf, ⟨co, rfl⟩, nonLockErrOk_mapErrno _ _ _⟩
  | succ f ih =>
    unfold SysBridge.writeAllLoop
    by_cases hDone : off ≥ data.size
    · simp only [hDone, ↓reduceIte]
      have hEqOff : off = data.size := by omega
      have hCc := closeCheck_trace hCap h (some path) held hWf
      cases hRc : (SysBridge.closeCheck cap.files h (some path) s) with
      | mk cres s1 =>
        rw [StateT.run] at hCc; rw [hRc] at hCc; dsimp only at hCc
        obtain ⟨hWf1, hTmp1, hErrOk, co, hStC, hFdC, hConf⟩ := hCc
        simp only [StateT.run, hRc]
        cases cres with
        | error ce =>
          exact ⟨hWf1, hTmp1, [], [(.close h, co)], hStC, TraceFds.nil _, hFdC,
            confined_single hConf, ⟨co, rfl⟩, hErrOk⟩
        | ok u =>
          cases u
          refine ⟨hWf1, hTmp1, [], [(.close h, co)], hStC, TraceFds.nil _, hFdC,
            confined_single hConf, ⟨co, rfl⟩, ?_⟩
          subst hEqOff
          apply ByteArray.ext
          apply Array.ext'
          simp [writtenBytesOn, ByteArray.extract, ByteArray.copySlice]
    · simp only [hDone, ↓reduceIte]
      have hWr := cap_method_step hCap (.write h (data.extract off (min data.size (off + SysBridge.WRITE_CHUNK_SIZE))))
        (cap.files.write h (data.extract off (min data.size (off + SysBridge.WRITE_CHUNK_SIZE)))) outcomeOfU32 rfl hWf
      cases hR : cap.files.write h (data.extract off (min data.size (off + SysBridge.WRITE_CHUNK_SIZE))) s with
      | mk res s1 =>
        let sliceEnd := min data.size (off + SysBridge.WRITE_CHUNK_SIZE)
        let chunk := data.extract off sliceEnd
        have hWr' : fsWorldWf (proj s1) = true ∧
            healthyStep (proj s).env (.write h chunk) (outcomeOfU32 res) = some (proj s1).env ∧
            (proj s1).tempSeq = (proj s).tempSeq := by
          rw [StateT.run] at hWr; rw [hR] at hWr; exact hWr
        simp only [Bind.bind, StateT.bind, StateT.run, hR]
        cases res with
        | error e =>
          by_cases hEin : (e == Errno.EINTR) = true
          · simp only [hEin, ↓reduceIte]
            have hIh := ih off hOff hWr'.1
            cases hO : (SysBridge.writeAllLoop cap.files h path data off f s1) with
            | mk r2 s2 =>
              simp only [StateT.run, hO] at hIh ⊢
              obtain ⟨hWf2, hTmp2, trW, trC, hSt2, hFdW, hFdC, hConf2, hCeq, hOut2⟩ := hIh
              refine ⟨hWf2, hTmp2.trans hWr'.2.2, (.write h chunk, .err e) :: trW, trC,
                HealthyFilesSteps.cons _ _ _ hWr'.2.1 hSt2, TraceFds.step (by rfl) hFdW, hFdC,
                confined_cons trivial hConf2, hCeq, ?_⟩
              cases r2 with
              | error err => exact hOut2
              | ok u =>
                cases u
                have hMiss : writtenBytesOn h [(.write h chunk, .err e)] = ByteArray.empty :=
                  writtenBytesOn_step_miss h _ (fun _ _ hc => by cases hc)
                change writtenBytesOn h ([(.write h chunk, .err e)] ++ trW) = _
                rw [writtenBytesOn_append, hMiss, byteArray_empty_append]
                exact hOut2
          · simp only [hEin, Bool.false_eq_true, ↓reduceIte]
            have hQ := closeQuiet_trace hCap h held hWr'.1
            cases hRq : (SysBridge.closeQuiet cap.files h s1) with
            | mk u s2 =>
              rw [StateT.run] at hQ; rw [hRq] at hQ; dsimp only at hQ
              obtain ⟨hWf2, hTmp2, co, hStC, hFdC, _⟩ := hQ
              simp only [Bind.bind, StateT.bind, Pure.pure, StateT.pure, hRq]
              exact ⟨hWf2, hTmp2.trans hWr'.2.2, [(.write h chunk, .err e)], [(.close h, co)],
                HealthyFilesSteps.cons _ _ _ hWr'.2.1 hStC, traceFds_nonFd_step rfl rfl, hFdC,
                confined_cons trivial (confined_single trivial), ⟨co, rfl⟩, nonLockErrOk_mapErrno _ _ _⟩
        | ok n =>
          by_cases hZ : (n == 0) = true
          · simp only [hZ, ↓reduceIte]
            have hQ := closeQuiet_trace hCap h held hWr'.1
            cases hRq : (SysBridge.closeQuiet cap.files h s1) with
            | mk u s2 =>
              rw [StateT.run] at hQ; rw [hRq] at hQ; dsimp only at hQ
              obtain ⟨hWf2, hTmp2, co, hStC, hFdC, _⟩ := hQ
              simp only [Bind.bind, StateT.bind, Pure.pure, StateT.pure, hRq]
              exact ⟨hWf2, hTmp2.trans hWr'.2.2, [(.write h chunk, .u32 n)], [(.close h, co)],
                HealthyFilesSteps.cons _ _ _ hWr'.2.1 hStC, traceFds_nonFd_step rfl rfl, hFdC,
                confined_cons trivial (confined_single trivial), ⟨co, rfl⟩, nonLockErrOk_mapErrno _ _ _⟩
          · simp only [hZ, Bool.false_eq_true, ↓reduceIte]
            have hNLe : n.toNat ≤ chunk.size := healthyStep_write_le hWr'.2.1
            have hChunkSz : chunk.size ≤ sliceEnd - off := by
              have hSzEq : chunk.size = (data.extract off sliceEnd).data.toList.length := rfl
              have hL : (data.extract off sliceEnd).data.toList = (data.data.toList.drop off).take (sliceEnd - off) := by
                have h1 : (data.extract off sliceEnd).data = data.data.extract off (off + (sliceEnd - off)) := by
                  simp only [ByteArray.extract, ByteArray.copySlice, ByteArray.data_empty, ByteArray.size_data,
                    Array.extract_zero, Array.empty_append, Array.extract_empty, Array.append_empty]
                rw [h1, Array.toList_extract, List.extract_eq_take_drop, Nat.add_sub_cancel_left]
              rw [hSzEq, hL, List.length_take]
              exact Nat.min_le_left _ _
            have hSliceLe : sliceEnd ≤ data.size := Nat.min_le_left _ _
            have hOffNext : off + n.toNat ≤ sliceEnd := by omega
            have hOffNextData : off + n.toNat ≤ data.size := Nat.le_trans hOffNext hSliceLe
            have hIh := ih (off + n.toNat) hOffNextData hWr'.1
            cases hO : (SysBridge.writeAllLoop cap.files h path data (off + n.toNat) f s1) with
            | mk r2 s2 =>
              simp only [StateT.run, hO] at hIh ⊢
              obtain ⟨hWf2, hTmp2, trW, trC, hSt2, hFdW, hFdC, hConf2, hCeq, hOut2⟩ := hIh
              refine ⟨hWf2, hTmp2.trans hWr'.2.2, (.write h chunk, .u32 n) :: trW, trC,
                HealthyFilesSteps.cons _ _ _ hWr'.2.1 hSt2, TraceFds.step (by rfl) hFdW, hFdC,
                confined_cons trivial hConf2, hCeq, ?_⟩
              cases r2 with
              | error err => exact hOut2
              | ok u =>
                cases u
                change writtenBytesOn h ([(.write h chunk, .u32 n)] ++ trW) = _
                rw [writtenBytesOn_append, writtenBytesOn_write_hit, hOut2]
                rw [byteArray_extract_extract_zero data hOffNext]
                exact byteArray_extract_append data (Nat.le_add_right _ _) hOffNextData

/-- Trace specification for `SysBridge.writeAllAndClose`: writes exact `data` and always closes `h`. -/
theorem writeAllAndClose_trace {W : Type} {proj : W → FsWorld} {cap : HealthyFilesCapM (StateM W)}
    (hCap : Core.ObeysStep proj Model.fsWorldWf (Model.execFilesCapStep cap) Model.allowedFilesCapStep)
    (h : HandleId) (path : String) (data : ByteArray) (held : List HandleId) (eintrFuel : Nat)
    {s : W} (hWf : fsWorldWf (proj s) = true) :
    let p := (SysBridge.writeAllAndClose cap.files h path data eintrFuel).run s
    fsWorldWf (proj p.2) = true ∧
    (proj p.2).tempSeq = (proj s).tempSeq ∧
    ∃ trWrite trClose,
      HealthyFilesSteps (proj s).env (trWrite ++ trClose) (proj p.2).env ∧
      TraceFds (h :: held) trWrite (h :: held) ∧
      TraceFds (h :: held) trClose held ∧
      (∀ step ∈ trWrite ++ trClose, SubtreeConfinedReq step.1) ∧
      (∃ co, trClose = [(.close h, co)]) ∧
      match p.1 with
      | .ok () => writtenBytesOn h trWrite = data
      | .error e => nonLockErrOk e := by
  simpa [SysBridge.writeAllAndClose, byteArray_extract_zero_size] using
    writeAllLoop_trace hCap h path data held 0 (data.size + eintrFuel + 1) (Nat.zero_le _) hWf

/-- Trace specification for `SysBridge.readDirStreamLoop`: scans `getdents64` to 0-byte EOF, excludes `.`/`..`, and stays confined. -/
theorem readDirStreamLoop_trace {W : Type} {proj : W → FsWorld} {cap : HealthyFilesCapM (StateM W)}
    (hCap : Core.ObeysStep proj Model.fsWorldWf (Model.execFilesCapStep cap) Model.allowedFilesCapStep)
    (h : HandleId) (path : String) (held : List HandleId)
    (acc : Array String) (fuel : Nat) (hAcc : ∀ nm ∈ acc.toList, nm ≠ "." ∧ nm ≠ "..")
    {s : W} (hWf : fsWorldWf (proj s) = true) :
    let p := (SysBridge.readDirStreamLoop cap.files h path acc fuel).run s
    fsWorldWf (proj p.2) = true ∧
    (proj p.2).tempSeq = (proj s).tempSeq ∧
    ∃ tr,
      HealthyFilesSteps (proj s).env tr (proj p.2).env ∧
      TraceFds held tr held ∧
      (∀ step ∈ tr, SubtreeConfinedReq step.1) ∧
      match p.1 with
      | .ok xs =>
        (∀ nm ∈ xs.toList, nm ≠ "." ∧ nm ≠ "..") ∧
        (∃ eof, (.getdents64 h 8192, .bytes eof) ∈ tr ∧ eof.size = 0) ∧
        (xs.size > acc.size → ∃ buf, (.getdents64 h 8192, .bytes buf) ∈ tr ∧ buf.size > 0)
      | .error e => nonLockErrOk e := by
  induction fuel generalizing acc s with
  | zero =>
    unfold SysBridge.readDirStreamLoop
    simp only [Pure.pure, StateT.pure, StateT.run]
    exact ⟨hWf, trivial, [], HealthyFilesSteps.nil _, TraceFds.nil _, confined_nil,
      nonLockErrOk_mapErrno _ _ _⟩
  | succ f ih =>
    unfold SysBridge.readDirStreamLoop
    have hGd := cap_method_step hCap (.getdents64 h SysBridge.GETDENTS_BUF_SIZE)
      (cap.files.getdents64 h SysBridge.GETDENTS_BUF_SIZE) outcomeOfBytes rfl hWf
    cases hR : cap.files.getdents64 h SysBridge.GETDENTS_BUF_SIZE s with
    | mk res s1 =>
      have hGd' : fsWorldWf (proj s1) = true ∧
          healthyStep (proj s).env (.getdents64 h 8192) (outcomeOfBytes res) = some (proj s1).env ∧
          (proj s1).tempSeq = (proj s).tempSeq := by
        rw [StateT.run] at hGd; rw [hR] at hGd; simpa [SysBridge.GETDENTS_BUF_SIZE] using hGd
      simp only [Bind.bind, StateT.bind, StateT.run, hR]
      cases res with
      | error e =>
        by_cases hEin : (e == Errno.EINTR) = true
        · simp only [hEin, ↓reduceIte]
          have hIh := ih acc hAcc hGd'.1
          cases hO : (SysBridge.readDirStreamLoop cap.files h path acc f s1) with
          | mk r2 s2 =>
            simp only [StateT.run, hO] at hIh ⊢
            obtain ⟨hWf2, hTmp2, tr2, hSt2, hFd2, hConf2, hOut2⟩ := hIh
            refine ⟨hWf2, hTmp2.trans hGd'.2.2, (.getdents64 h 8192, .err e) :: tr2,
              HealthyFilesSteps.cons _ _ _ hGd'.2.1 hSt2, TraceFds.step (by rfl) hFd2,
              confined_cons trivial hConf2, ?_⟩
            cases r2 with
            | error err => exact hOut2
            | ok xs =>
              obtain ⟨hNoDot, ⟨eof, hMemE, hEz⟩, hNonEmp⟩ := hOut2
              exact ⟨hNoDot, ⟨eof, List.mem_cons_of_mem _ hMemE, hEz⟩,
                fun hGt => let ⟨b, hm, hp⟩ := hNonEmp hGt; ⟨b, List.mem_cons_of_mem _ hm, hp⟩⟩
        · simp only [hEin, Bool.false_eq_true, ↓reduceIte, Pure.pure, StateT.pure]
          exact ⟨hGd'.1, hGd'.2.2, [(.getdents64 h 8192, .err e)],
            healthyFilesSteps_single hGd'.2.1, traceFds_nonFd_step rfl rfl,
            confined_single trivial, nonLockErrOk_mapErrno _ _ _⟩
      | ok buf =>
        by_cases hZ : (buf.size == 0) = true
        · simp only [hZ, ↓reduceIte, Pure.pure, StateT.pure]
          have hZ0 : buf.size = 0 := beq_iff_eq.mp hZ
          exact ⟨hGd'.1, hGd'.2.2, [(.getdents64 h 8192, .bytes buf)],
            healthyFilesSteps_single hGd'.2.1, traceFds_nonFd_step rfl rfl,
            confined_single trivial, hAcc, ⟨buf, List.mem_singleton.mpr rfl, hZ0⟩, fun hGt => by omega⟩
        · simp only [hZ, Bool.false_eq_true, ↓reduceIte]
          have hBufPos : buf.size > 0 := by
            have : buf.size ≠ 0 := by simpa using hZ
            omega
          have hP := parseDirents64Aux_props buf 0 acc path (buf.size + 1) hAcc
          cases hPr : SysBridge.parseDirents64Aux buf 0 acc path (buf.size + 1) with
          | error pe =>
            rw [hPr] at hP
            simp only [Pure.pure, StateT.pure]
            exact ⟨hGd'.1, hGd'.2.2, [(.getdents64 h 8192, .bytes buf)],
              healthyFilesSteps_single hGd'.2.1, traceFds_nonFd_step rfl rfl,
              confined_single trivial, hP⟩
          | ok acc' =>
            rw [hPr] at hP
            have hIh := ih acc' hP.1 hGd'.1
            cases hO : (SysBridge.readDirStreamLoop cap.files h path acc' f s1) with
            | mk r2 s2 =>
              simp only [StateT.run, hO] at hIh ⊢
              obtain ⟨hWf2, hTmp2, tr2, hSt2, hFd2, hConf2, hOut2⟩ := hIh
              refine ⟨hWf2, hTmp2.trans hGd'.2.2, (.getdents64 h 8192, .bytes buf) :: tr2,
                HealthyFilesSteps.cons _ _ _ hGd'.2.1 hSt2, TraceFds.step (by rfl) hFd2,
                confined_cons trivial hConf2, ?_⟩
              cases r2 with
              | error err => exact hOut2
              | ok xs =>
                obtain ⟨hNoDot, ⟨eof, hMemE, hEz⟩, _⟩ := hOut2
                exact ⟨hNoDot, ⟨eof, List.mem_cons_of_mem _ hMemE, hEz⟩,
                  fun _ => ⟨buf, List.mem_cons_self .., hBufPos⟩⟩

/-- Trace specification for `SysBridge.finishLockFd`: verifies `.reg` via `fstat`, applies `flock`, closes `h` on failure, and stays confined. -/
theorem finishLockFd_trace {W : Type} {proj : W → FsWorld} {cap : HealthyFilesCapM (StateM W)}
    (hCap : Core.ObeysStep proj Model.fsWorldWf (Model.execFilesCapStep cap) Model.allowedFilesCapStep)
    (h : HandleId) (path : String) (mode : LockMode) (nonBlocking : Bool)
    (held : List HandleId) (eintrFuel : Nat) {s : W} (hWf : fsWorldWf (proj s) = true) :
    let p := (SysBridge.finishLockFd cap.files h path mode nonBlocking eintrFuel).run s
    fsWorldWf (proj p.2) = true ∧
    (proj p.2).tempSeq = (proj s).tempSeq ∧
    match p.1 with
    | .ok h' =>
      h' = h ∧
      ∃ rawSt tr,
        HealthyFilesSteps (proj s).env tr (proj p.2).env ∧
        TraceFds (h :: held) tr (h :: held) ∧
        (∀ step ∈ tr, SubtreeConfinedReq step.1) ∧
        (.fstat h, .statted rawSt) ∈ tr ∧ rawSt.kind = .reg ∧
        (.flock h (lockModeToFlockOp mode nonBlocking), .unit) ∈ tr
    | .error e =>
      ∃ trLock trClose,
        HealthyFilesSteps (proj s).env (trLock ++ trClose) (proj p.2).env ∧
        TraceFds (h :: held) trLock (h :: held) ∧
        TraceFds (h :: held) trClose held ∧
        (∀ step ∈ trLock ++ trClose, SubtreeConfinedReq step.1) ∧
        (∃ co, trClose = [(.close h, co)]) ∧
        (nonLockErrOk e ∨
         (e.kind = .wouldBlock ∧ nonBlocking = true ∧
          ∃ rawSt, (.fstat h, .statted rawSt) ∈ trLock ∧ rawSt.kind = .reg ∧
            (.flock h (lockModeToFlockOp mode true), .err Errno.EAGAIN) ∈ trLock)) := by
  unfold SysBridge.finishLockFd
  have hFs := cap_method_step hCap (.fstat h) (cap.files.fstat h) outcomeOfStatted rfl hWf
  cases hR : cap.files.fstat h s with
  | mk res s1 =>
    have hFs' : fsWorldWf (proj s1) = true ∧
        healthyStep (proj s).env (.fstat h) (outcomeOfStatted res) = some (proj s1).env ∧
        (proj s1).tempSeq = (proj s).tempSeq := by
      simpa [StateT.run, hR] using hFs
    simp only [Bind.bind, StateT.bind, StateT.run, hR]
    cases res with
    | error e =>
      have hQ := closeQuiet_trace hCap h held hFs'.1
      cases hRq : (SysBridge.closeQuiet cap.files h s1) with
      | mk u s2 =>
        rw [StateT.run] at hQ; rw [hRq] at hQ; dsimp only at hQ
        obtain ⟨hWf2, hTmp2, co, hStC, hFdC, _⟩ := hQ
        simp only [Bind.bind, StateT.bind, Pure.pure, StateT.pure, hRq]
        exact ⟨hWf2, hTmp2.trans hFs'.2.2, [(.fstat h, .err e)], [(.close h, co)],
          HealthyFilesSteps.cons _ _ _ hFs'.2.1 hStC, traceFds_nonFd_step rfl rfl, hFdC,
          confined_cons trivial (confined_single trivial), ⟨co, rfl⟩, Or.inl (nonLockErrOk_mapErrno _ _ _)⟩
    | ok st =>
      by_cases hDir : (st.kind == .dir) = true
      · simp only [hDir, ↓reduceIte]
        have hQ := closeQuiet_trace hCap h held hFs'.1
        cases hRq : (SysBridge.closeQuiet cap.files h s1) with
        | mk u s2 =>
          rw [StateT.run] at hQ; rw [hRq] at hQ; dsimp only at hQ
          obtain ⟨hWf2, hTmp2, co, hStC, hFdC, _⟩ := hQ
          simp only [Bind.bind, StateT.bind, Pure.pure, StateT.pure, hRq]
          exact ⟨hWf2, hTmp2.trans hFs'.2.2, [(.fstat h, .statted st)], [(.close h, co)],
            HealthyFilesSteps.cons _ _ _ hFs'.2.1 hStC, traceFds_nonFd_step rfl rfl, hFdC,
            confined_cons trivial (confined_single trivial), ⟨co, rfl⟩, Or.inl (nonLockErrOk_mapErrno _ _ _)⟩
      · by_cases hNReg : (st.kind != .reg) = true
        · simp only [hDir, Bool.false_eq_true, ↓reduceIte, hNReg]
          have hQ := closeQuiet_trace hCap h held hFs'.1
          cases hRq : (SysBridge.closeQuiet cap.files h s1) with
          | mk u s2 =>
            rw [StateT.run] at hQ; rw [hRq] at hQ; dsimp only at hQ
            obtain ⟨hWf2, hTmp2, co, hStC, hFdC, _⟩ := hQ
            simp only [Bind.bind, StateT.bind, Pure.pure, StateT.pure, hRq]
            exact ⟨hWf2, hTmp2.trans hFs'.2.2, [(.fstat h, .statted st)], [(.close h, co)],
              HealthyFilesSteps.cons _ _ _ hFs'.2.1 hStC, traceFds_nonFd_step rfl rfl, hFdC,
              confined_cons trivial (confined_single trivial), ⟨co, rfl⟩, Or.inl (nonLockErrOk_mapErrno _ _ _)⟩
        · simp only [hDir, Bool.false_eq_true, ↓reduceIte, hNReg]
          have hKindReg : st.kind = .reg := by
            cases hK : st.kind <;> rw [hK] at hNReg <;> first | rfl | exact absurd (by decide) hNReg
          cases mode with
          | shared =>
            dsimp only [lockModeToFlockOp]
            have hFl := retryEintr_single_req (cap.files.flock h (.shared nonBlocking))
              (.flock h (.shared nonBlocking)) outcomeOfUnit
              (fun s' hW => cap_method_step hCap (.flock h (.shared nonBlocking))
                (cap.files.flock h (.shared nonBlocking)) outcomeOfUnit rfl hW)
              (fun _ => rfl) eintrFuel hFs'.1
            cases hRf : (retryEintr (cap.files.flock h (.shared nonBlocking)) eintrFuel s1) with
            | mk flRes s2 =>
              rw [StateT.run] at hFl; rw [hRf] at hFl; dsimp only at hFl
              obtain ⟨hWf2, hTmp2, trR, hStFl, hAllFl⟩ := hFl
              simp only [Bind.bind, StateT.bind, hRf]
              have hFdR : TraceFds (h :: held) trR (h :: held) :=
                traceFds_eintr_retries (fun _ hc => by cases hc) hAllFl
              have hConfR : ∀ step ∈ trR, SubtreeConfinedReq step.1 := fun step hm => by
                rw [hAllFl step hm]; trivial
              cases flRes with
              | ok u =>
                cases u
                simp only [Pure.pure, StateT.pure]
                exact ⟨hWf2, hTmp2.trans hFs'.2.2, trivial, st,
                  (.fstat h, .statted st) :: (trR ++ [(.flock h (.shared nonBlocking), .unit)]),
                  HealthyFilesSteps.cons _ _ _ hFs'.2.1 hStFl,
                  TraceFds.step (by rfl) (traceFds_append hFdR (traceFds_nonFd_step rfl rfl)),
                  confined_cons trivial (confined_append hConfR (confined_single (s := (.flock h (.shared nonBlocking), .unit)) trivial)),
                  List.mem_cons_self .., hKindReg, by simp⟩
              | error fe =>
                have hQ := closeQuiet_trace hCap h held hWf2
                cases hRq : (SysBridge.closeQuiet cap.files h s2) with
                | mk u s3 =>
                  rw [StateT.run] at hQ; rw [hRq] at hQ; dsimp only at hQ
                  obtain ⟨hWf3, hTmp3, co, hStC, hFdC, _⟩ := hQ
                  simp only [Bind.bind, StateT.bind, hRq]
                  let trL := (.fstat h, .statted st) :: (trR ++ [(.flock h (.shared nonBlocking), .err fe)])
                  have hStAll : HealthyFilesSteps (proj s).env (trL ++ [(.close h, co)]) (proj s3).env :=
                    HealthyFilesSteps.cons _ _ _ hFs'.2.1 (healthyFilesSteps_append hStFl hStC)
                  have hFdL : TraceFds (h :: held) trL (h :: held) :=
                    TraceFds.step (by rfl) (traceFds_append hFdR (traceFds_nonFd_step rfl rfl))
                  have hConfAll := confined_append (confined_cons (s := (.fstat h, .statted st)) trivial
                    (confined_append hConfR (confined_single (s := (.flock h (.shared nonBlocking), .err fe)) trivial)))
                    (confined_single (s := (.close h, co)) trivial)
                  by_cases hAg : (nonBlocking && fe == Errno.EAGAIN) = true
                  · simp only [Bool.and_eq_true, beq_iff_eq] at hAg
                    rcases hAg with ⟨hNb, hFeEq⟩
                    subst hNb; subst hFeEq
                    simp only [Bool.true_and, beq_self_eq_true, ↓reduceIte, Pure.pure, StateT.pure]
                    exact ⟨hWf3, hTmp3.trans (hTmp2.trans hFs'.2.2), trL, [(.close h, co)],
                      hStAll, hFdL, hFdC, hConfAll, ⟨co, rfl⟩,
                      Or.inr ⟨rfl, trivial, st, List.mem_cons_self .., hKindReg, by simp [trL]⟩⟩
                  · simp only [hAg, Bool.false_eq_true, ↓reduceIte, Pure.pure, StateT.pure]
                    exact ⟨hWf3, hTmp3.trans (hTmp2.trans hFs'.2.2), trL, [(.close h, co)],
                      hStAll, hFdL, hFdC, hConfAll, ⟨co, rfl⟩, Or.inl (nonLockErrOk_mapErrno _ _ _)⟩
          | exclusive =>
            dsimp only [lockModeToFlockOp]
            have hFl := retryEintr_single_req (cap.files.flock h (.exclusive nonBlocking))
              (.flock h (.exclusive nonBlocking)) outcomeOfUnit
              (fun s' hW => cap_method_step hCap (.flock h (.exclusive nonBlocking))
                (cap.files.flock h (.exclusive nonBlocking)) outcomeOfUnit rfl hW)
              (fun _ => rfl) eintrFuel hFs'.1
            cases hRf : (retryEintr (cap.files.flock h (.exclusive nonBlocking)) eintrFuel s1) with
            | mk flRes s2 =>
              rw [StateT.run] at hFl; rw [hRf] at hFl; dsimp only at hFl
              obtain ⟨hWf2, hTmp2, trR, hStFl, hAllFl⟩ := hFl
              simp only [Bind.bind, StateT.bind, hRf]
              have hFdR : TraceFds (h :: held) trR (h :: held) :=
                traceFds_eintr_retries (fun _ hc => by cases hc) hAllFl
              have hConfR : ∀ step ∈ trR, SubtreeConfinedReq step.1 := fun step hm => by
                rw [hAllFl step hm]; trivial
              cases flRes with
              | ok u =>
                cases u
                simp only [Pure.pure, StateT.pure]
                exact ⟨hWf2, hTmp2.trans hFs'.2.2, trivial, st,
                  (.fstat h, .statted st) :: (trR ++ [(.flock h (.exclusive nonBlocking), .unit)]),
                  HealthyFilesSteps.cons _ _ _ hFs'.2.1 hStFl,
                  TraceFds.step (by rfl) (traceFds_append hFdR (traceFds_nonFd_step rfl rfl)),
                  confined_cons trivial (confined_append hConfR (confined_single (s := (.flock h (.exclusive nonBlocking), .unit)) trivial)),
                  List.mem_cons_self .., hKindReg, by simp⟩
              | error fe =>
                have hQ := closeQuiet_trace hCap h held hWf2
                cases hRq : (SysBridge.closeQuiet cap.files h s2) with
                | mk u s3 =>
                  rw [StateT.run] at hQ; rw [hRq] at hQ; dsimp only at hQ
                  obtain ⟨hWf3, hTmp3, co, hStC, hFdC, _⟩ := hQ
                  simp only [Bind.bind, StateT.bind, hRq]
                  let trL := (.fstat h, .statted st) :: (trR ++ [(.flock h (.exclusive nonBlocking), .err fe)])
                  have hStAll : HealthyFilesSteps (proj s).env (trL ++ [(.close h, co)]) (proj s3).env :=
                    HealthyFilesSteps.cons _ _ _ hFs'.2.1 (healthyFilesSteps_append hStFl hStC)
                  have hFdL : TraceFds (h :: held) trL (h :: held) :=
                    TraceFds.step (by rfl) (traceFds_append hFdR (traceFds_nonFd_step rfl rfl))
                  have hConfAll := confined_append (confined_cons (s := (.fstat h, .statted st)) trivial
                    (confined_append hConfR (confined_single (s := (.flock h (.exclusive nonBlocking), .err fe)) trivial)))
                    (confined_single (s := (.close h, co)) trivial)
                  by_cases hAg : (nonBlocking && fe == Errno.EAGAIN) = true
                  · simp only [Bool.and_eq_true, beq_iff_eq] at hAg
                    rcases hAg with ⟨hNb, hFeEq⟩
                    subst hNb; subst hFeEq
                    simp only [Bool.true_and, beq_self_eq_true, ↓reduceIte, Pure.pure, StateT.pure]
                    exact ⟨hWf3, hTmp3.trans (hTmp2.trans hFs'.2.2), trL, [(.close h, co)],
                      hStAll, hFdL, hFdC, hConfAll, ⟨co, rfl⟩,
                      Or.inr ⟨rfl, trivial, st, List.mem_cons_self .., hKindReg, by simp [trL]⟩⟩
                  · simp only [hAg, Bool.false_eq_true, ↓reduceIte, Pure.pure, StateT.pure]
                    exact ⟨hWf3, hTmp3.trans (hTmp2.trans hFs'.2.2), trL, [(.close h, co)],
                      hStAll, hFdL, hFdC, hConfAll, ⟨co, rfl⟩, Or.inl (nonLockErrOk_mapErrno _ _ _)⟩

/-- Trace specification for `SysBridge.releaseLockPure`: runs `flock(LOCK_UN)` then `close`, popping `h` from `h :: held`, and stays confined. -/
theorem releaseLockPure_trace {W : Type} {proj : W → FsWorld} {cap : HealthyFilesCapM (StateM W)}
    (hCap : Core.ObeysStep proj Model.fsWorldWf (Model.execFilesCapStep cap) Model.allowedFilesCapStep)
    (h : HandleId) (held : List HandleId) (eintrFuel : Nat)
    {s : W} (hWf : fsWorldWf (proj s) = true) :
    let p := (SysBridge.releaseLockPure cap.files h eintrFuel).run s
    fsWorldWf (proj p.2) = true ∧
    (proj p.2).tempSeq = (proj s).tempSeq ∧
    ∃ trRel,
      HealthyFilesSteps (proj s).env trRel (proj p.2).env ∧
      TraceFds (h :: held) trRel held ∧
      (∀ step ∈ trRel, SubtreeConfinedReq step.1) ∧
      (∃ uo, (.flock h .unlock, uo) ∈ trRel ∧ (p.1.isOk = true → uo = .unit)) ∧
      (∃ co, (.close h, co) ∈ trRel) ∧
      (match p.1 with | .ok () => True | .error e => nonLockErrOk e) := by
  unfold SysBridge.releaseLockPure
  have hFl := retryEintr_single_req (cap.files.flock h .unlock) (.flock h .unlock) outcomeOfUnit
    (fun s' hW => cap_method_step hCap (.flock h .unlock) (cap.files.flock h .unlock) outcomeOfUnit rfl hW)
    (fun _ => rfl) eintrFuel hWf
  cases hR : (retryEintr (cap.files.flock h .unlock) eintrFuel s) with
  | mk uRes s1 =>
    rw [StateT.run] at hFl; rw [hR] at hFl; dsimp only at hFl
    obtain ⟨hWf1, hTmp1, trR, hStFl, hAllFl⟩ := hFl
    have hCc := closeCheck_trace hCap h none held hWf1
    cases hRc : (SysBridge.closeCheck cap.files h none s1) with
    | mk cRes s2 =>
      rw [StateT.run] at hCc; rw [hRc] at hCc; dsimp only at hCc
      obtain ⟨hWf2, hTmp2, hErrC, co, hStC, hFdC, _⟩ := hCc
      simp only [Bind.bind, StateT.bind, StateT.run, hR, hRc]
      have hFdFl : TraceFds (h :: held) (trR ++ [(.flock h .unlock, outcomeOfUnit uRes)]) (h :: held) :=
        traceFds_append (traceFds_eintr_retries (fun _ hc => by cases hc) hAllFl)
          (traceFds_nonFd_step (by cases uRes <;> rfl) rfl)
      have hConfR : ∀ step ∈ trR, SubtreeConfinedReq step.1 := fun step hm => by
        rw [hAllFl step hm]; trivial
      have hConfRel := confined_append (confined_append hConfR (confined_single (s := (.flock h .unlock, outcomeOfUnit uRes)) trivial))
        (confined_single (s := (.close h, co)) trivial)
      have hStAll := healthyFilesSteps_append hStFl hStC
      have hFdAll := traceFds_append hFdFl hFdC
      cases uRes with
      | error e =>
        simp only [Pure.pure, StateT.pure]
        refine ⟨hWf2, hTmp2.trans hTmp1, _, hStAll, hFdAll, hConfRel,
          ⟨.err e, by simp [outcomeOfUnit], fun hc => by cases hc⟩, ⟨co, by simp⟩,
          nonLockErrOk_mapErrno _ _ _⟩
      | ok u =>
        cases u
        simp only [Pure.pure, StateT.pure]
        refine ⟨hWf2, hTmp2.trans hTmp1, _, hStAll, hFdAll, hConfRel,
          ⟨.unit, by simp [outcomeOfUnit], fun _ => rfl⟩, ⟨co, by simp⟩, hErrC⟩

end LeanSwe.Fs.Proofs
