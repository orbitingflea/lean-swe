import LeanSwe.Fs.Proofs.SysBridgeFsOps

namespace LeanSwe.Fs.Proofs

open LeanSwe.LinuxSyscall
open LeanSwe.LinuxSyscall.Files
open LeanSwe.Fs
open LeanSwe.Fs.Model

private theorem fsErrorKind_beq_iff (a b : FsErrorKind) : (a == b) = true ↔ a = b := by
  cases a <;> cases b <;> decide

private theorem bracketLockM_pure_run {W α lockH : Type}
    (ops : RawFsOpsM (StateM W) lockH) (h : lockH) (actRes : Except FsError α) (s : W) :
    (Internal.bracketLockM ops h (pure actRes)).run s =
      let r := (ops.releaseLock h).run s
      (match actRes with
       | .error e => .error e
       | .ok a => match r.1 with | .ok () => .ok a | .error re => .error re, r.2) := by
  unfold Internal.bracketLockM
  cases hRel : ops.releaseLock h s with
  | mk r1 s1 =>
    cases actRes with
    | error e =>
      change (match (ops.releaseLock h s) with | (_, s') => (Except.error e, s')) = _
      simp only [StateT.run, hRel]
    | ok a =>
      change (match ops.releaseLock h s with
        | (relRes, s') => (match relRes with
          | Except.ok () => StateT.pure (Except.ok a)
          | Except.error re => StateT.pure (Except.error re)) s') = _
      simp only [StateT.run, hRel]
      cases r1 with
      | ok u => cases u; rfl
      | error re => rfl

/-- End-to-end refinement of `toScopedRawFsOpsM (SysBridge.mkRawFsOpsM cap.files cap.nextTempSeq)` against `allowedScopedRawFsStep` directly from `LinuxSyscall.Files.healthyStep`. -/
theorem refinesScopedRawFs_of_refinesFilesCap
    {W : Type} {proj : W → FsWorld} {cap : HealthyFilesCapM (StateM W)}
    (hCap : Core.ObeysStep proj Model.fsWorldWf (Model.execFilesCapStep cap) Model.allowedFilesCapStep) :
    Core.ObeysStep proj Model.fsWorldWf
      (Model.execScopedRawFsStep (Internal.toScopedRawFsOpsM (SysBridge.mkRawFsOpsM cap.files cap.nextTempSeq)))
      Model.allowedScopedRawFsStep := by
  intro s req hWf
  cases req with
  | mapRawError raw =>
    simp only [execScopedRawFsStep, Internal.toScopedRawFsOpsM, SysBridge.mkRawFsOpsM,
      Pure.pure, StateT.pure, StateT.run, allowedScopedRawFsStep]
    exact ⟨fsWorldTrace_nil hWf, trivial, trivial⟩
  | stat follow path =>
    simp only [execScopedRawFsStep, Internal.toScopedRawFsOpsM, SysBridge.mkRawFsOpsM,
      Functor.map, StateT.map, StateT.run]
    have hFs := retryEintr_single_req (cap.files.fstatat none path.toUTF8 { symlinkNofollow := !follow })
      (.fstatat none path.toUTF8 { symlinkNofollow := !follow }) outcomeOfStatted
      (fun s' hW => cap_method_step hCap (.fstatat none path.toUTF8 { symlinkNofollow := !follow })
        (cap.files.fstatat none path.toUTF8 { symlinkNofollow := !follow }) outcomeOfStatted rfl hW)
      (fun _ => rfl) DEFAULT_EINTR_FUEL hWf
    cases hR : (retryEintr (cap.files.fstatat none path.toUTF8 { symlinkNofollow := !follow }) DEFAULT_EINTR_FUEL s) with
    | mk res s1 =>
      rw [StateT.run] at hFs; rw [hR] at hFs; dsimp only at hFs
      obtain ⟨hWf1, hTmp1, trR, hSt1, hAll1⟩ := hFs
      simp only [Bind.bind, StateT.bind, hR]
      have hTr1 : FsWorldTrace (proj s) (trR ++ [(.fstatat none path.toUTF8 { symlinkNofollow := !follow }, outcomeOfStatted res)]) (proj s1) :=
        ⟨hWf1, hSt1, traceFds_append (traceFds_eintr_retries (fun _ hc => by cases hc) hAll1)
          (traceFds_nonFd_step (by cases res <;> rfl) rfl), by omega⟩
      cases res with
      | ok st =>
        simp only [Pure.pure, StateT.pure, allowedScopedRawFsStep]
        exact ⟨_, hTr1, hTmp1, st, by simp [outcomeOfStatted], rfl⟩
      | error e =>
        simp only [Pure.pure, StateT.pure, allowedScopedRawFsStep]
        refine ⟨_, hTr1, hTmp1, nonLockErrOk_mapErrno _ _ _, e, by simp [outcomeOfStatted],
          fun hNf => mapErrno_kind_notFound_eq _ _ _ hNf⟩
  | readDir path =>
    simp only [execScopedRawFsStep, Internal.toScopedRawFsOpsM, SysBridge.mkRawFsOpsM,
      Functor.map, StateT.map, StateT.run]
    have hRd := readDirPure_trace hCap path DEFAULT_EINTR_FUEL SysBridge.DEFAULT_STREAM_FUEL hWf
    cases hR : (SysBridge.readDirPure cap.files path DEFAULT_EINTR_FUEL SysBridge.DEFAULT_STREAM_FUEL s) with
    | mk res s1 =>
      simp only [StateT.run, hR] at hRd ⊢
      obtain ⟨_, hTmp1, tr, hTr, hOut⟩ := hRd
      exact ⟨tr, hTr, hTmp1, hOut⟩
  | createDir path =>
    simp only [execScopedRawFsStep, Internal.toScopedRawFsOpsM, SysBridge.mkRawFsOpsM,
      Functor.map, StateT.map, StateT.run]
    have hMk := retryEintr_single_req (cap.files.mkdirat none path.toUTF8 0o777)
      (.mkdirat none path.toUTF8 0o777) outcomeOfUnit
      (fun s' hW => cap_method_step hCap (.mkdirat none path.toUTF8 0o777)
        (cap.files.mkdirat none path.toUTF8 0o777) outcomeOfUnit rfl hW)
      (fun _ => rfl) DEFAULT_EINTR_FUEL hWf
    cases hR : (retryEintr (cap.files.mkdirat none path.toUTF8 0o777) DEFAULT_EINTR_FUEL s) with
    | mk res s1 =>
      rw [StateT.run] at hMk; rw [hR] at hMk; dsimp only at hMk
      obtain ⟨hWf1, hTmp1, trR, hSt1, hAll1⟩ := hMk
      simp only [Bind.bind, StateT.bind, hR]
      have hTr1 : FsWorldTrace (proj s) (trR ++ [(.mkdirat none path.toUTF8 0o777, outcomeOfUnit res)]) (proj s1) :=
        ⟨hWf1, hSt1, traceFds_append (traceFds_eintr_retries (fun _ hc => by cases hc) hAll1)
          (traceFds_nonFd_step (by cases res <;> rfl) rfl), by omega⟩
      cases res with
      | ok u =>
        cases u; simp only [Pure.pure, StateT.pure, allowedScopedRawFsStep]
        exact ⟨_, hTr1, hTmp1, by simp [MkdirTrace, outcomeOfUnit]⟩
      | error e =>
        simp only [Pure.pure, StateT.pure, allowedScopedRawFsStep]
        exact ⟨_, hTr1, hTmp1, nonLockErrOk_mapErrno _ _ _, by simp⟩
  | removeDir path =>
    simp only [execScopedRawFsStep, Internal.toScopedRawFsOpsM, SysBridge.mkRawFsOpsM,
      Functor.map, StateT.map, StateT.run]
    have hRm := removeDirAtOpt_trace hCap none path [] DEFAULT_EINTR_FUEL hWf
    cases hR : (SysBridge.removeDirAtOpt cap.files none path DEFAULT_EINTR_FUEL s) with
    | mk res s1 =>
      simp only [StateT.run, hR] at hRm ⊢
      obtain ⟨hWf1, hTmp1, tr, hSt, hFd, hNe, _, hOut⟩ := hRm
      have hTr : FsWorldTrace (proj s) tr (proj s1) := ⟨hWf1, hSt, hFd, by omega⟩
      cases res with
      | ok u => cases u; exact ⟨tr, hTr, hTmp1, hOut⟩
      | error e => exact ⟨tr, hTr, hTmp1, hOut.1, hNe⟩
  | unlinkFile path =>
    simp only [execScopedRawFsStep, Internal.toScopedRawFsOpsM, SysBridge.mkRawFsOpsM,
      Functor.map, StateT.map, StateT.run]
    have hUn := retryEintr_single_req (cap.files.unlinkat none path.toUTF8 false)
      (.unlinkat none path.toUTF8 false) outcomeOfUnit
      (fun s' hW => cap_method_step hCap (.unlinkat none path.toUTF8 false)
        (cap.files.unlinkat none path.toUTF8 false) outcomeOfUnit rfl hW)
      (fun _ => rfl) DEFAULT_EINTR_FUEL hWf
    cases hR : (retryEintr (cap.files.unlinkat none path.toUTF8 false) DEFAULT_EINTR_FUEL s) with
    | mk res s1 =>
      rw [StateT.run] at hUn; rw [hR] at hUn; dsimp only at hUn
      obtain ⟨hWf1, hTmp1, trR, hSt1, hAll1⟩ := hUn
      simp only [Bind.bind, StateT.bind, hR]
      have hTr1 : FsWorldTrace (proj s) (trR ++ [(.unlinkat none path.toUTF8 false, outcomeOfUnit res)]) (proj s1) :=
        ⟨hWf1, hSt1, traceFds_append (traceFds_eintr_retries (fun _ hc => by cases hc) hAll1)
          (traceFds_nonFd_step (by cases res <;> rfl) rfl), by omega⟩
      cases res with
      | ok u =>
        cases u; simp only [Pure.pure, StateT.pure, allowedScopedRawFsStep]
        exact ⟨_, hTr1, hTmp1, by simp [UnlinkTrace, outcomeOfUnit]⟩
      | error e =>
        simp only [Pure.pure, StateT.pure, allowedScopedRawFsStep]
        exact ⟨_, hTr1, hTmp1, nonLockErrOk_mapErrno _ _ _, by simp⟩
  | readBytes path =>
    simp only [execScopedRawFsStep, Internal.toScopedRawFsOpsM, SysBridge.mkRawFsOpsM,
      Functor.map, StateT.map, StateT.run]
    have hRd := readBytesPure_trace hCap path DEFAULT_EINTR_FUEL SysBridge.DEFAULT_STREAM_FUEL hWf
    cases hR : (SysBridge.readBytesPure cap.files path DEFAULT_EINTR_FUEL SysBridge.DEFAULT_STREAM_FUEL s) with
    | mk res s1 =>
      simp only [StateT.run, hR] at hRd ⊢
      obtain ⟨_, hTmp1, tr, hTr, hOut⟩ := hRd
      exact ⟨tr, hTr, hTmp1, hOut⟩
  | writeBytes path data =>
    simp only [execScopedRawFsStep, Internal.toScopedRawFsOpsM, SysBridge.mkRawFsOpsM,
      Functor.map, StateT.map, StateT.run]
    have hOp := retryEintr_single_req (cap.files.openat none path.toUTF8 writeOpenFlags 0o666)
      (.openat none path.toUTF8 writeOpenFlags 0o666) outcomeOfOpened
      (fun s' hW => cap_method_step hCap (.openat none path.toUTF8 writeOpenFlags 0o666)
        (cap.files.openat none path.toUTF8 writeOpenFlags 0o666) outcomeOfOpened rfl hW)
      (fun _ => rfl) DEFAULT_EINTR_FUEL hWf
    cases hR : (retryEintr (cap.files.openat none path.toUTF8 writeOpenFlags 0o666) DEFAULT_EINTR_FUEL s) with
    | mk oRes s1 =>
      rw [StateT.run] at hOp; rw [hR] at hOp; dsimp only at hOp
      obtain ⟨hWf1, hTmp1, trR, hStO, hAllO⟩ := hOp
      dsimp only [writeOpenFlags] at hR
      simp only [Bind.bind, StateT.bind, hR]
      have hFdR : TraceFds [] trR [] := traceFds_eintr_retries (fun _ hc => by cases hc) hAllO
      cases oRes with
      | error e =>
        simp only [Pure.pure, StateT.pure, allowedScopedRawFsStep]
        exact ⟨_, ⟨hWf1, hStO, traceFds_append hFdR (traceFds_nonFd_step rfl rfl), by omega⟩,
          hTmp1, nonLockErrOk_mapErrno _ _ _, by simp⟩
      | ok h =>
        let trOpen := trR ++ [(.openat none path.toUTF8 writeOpenFlags 0o666, .opened h)]
        have hFdO : TraceFds [] trOpen [h] := traceFds_append hFdR (traceFds_open_step rfl rfl)
        have hWr := writeAllAndClose_trace hCap h path data [] DEFAULT_EINTR_FUEL hWf1
        cases hRw : (SysBridge.writeAllAndClose cap.files h path data DEFAULT_EINTR_FUEL s1) with
        | mk wRes s2 =>
          simp only [StateT.run, hRw] at hWr ⊢
          obtain ⟨hWf2, hTmp2, trW, trC, hStWC, hFdW, hFdC, _, ⟨co, rfl⟩, hOutW⟩ := hWr
          have hTrAll : FsWorldTrace (proj s) (trOpen ++ trW ++ [(.close h, co)]) (proj s2) :=
            ⟨hWf2, by rw [List.append_assoc]; exact healthyFilesSteps_append hStO hStWC,
             by rw [List.append_assoc]; exact traceFds_append hFdO (traceFds_append hFdW hFdC), by omega⟩
          cases wRes with
          | ok u =>
            cases u
            exact ⟨_, hTrAll, hTmp2.trans hTmp1, h, trOpen, trW, [(.close h, co)],
              rfl, by simp [trOpen], hOutW, co, by simp⟩
          | error e => exact ⟨_, hTrAll, hTmp2.trans hTmp1, hOutW, by simp [trOpen]⟩
  | createFileNew path data =>
    simp only [execScopedRawFsStep, Internal.toScopedRawFsOpsM, SysBridge.mkRawFsOpsM,
      Functor.map, StateT.map, StateT.run]
    have hCr := createFileNewPure_trace hCap path data DEFAULT_EINTR_FUEL hWf
    cases hR : (SysBridge.createFileNewPure cap.files path data DEFAULT_EINTR_FUEL s) with
    | mk res s1 =>
      simp only [StateT.run, hR] at hCr ⊢
      obtain ⟨_, hTmp1, tr, hTr, hOut⟩ := hCr
      cases res with
      | ok u => cases u; exact ⟨tr, hTr, hTmp1, hOut⟩
      | error e => exact ⟨tr, hTr, hTmp1, hOut⟩
  | appendText path content =>
    simp only [execScopedRawFsStep, Internal.toScopedRawFsOpsM, SysBridge.mkRawFsOpsM,
      Functor.map, StateT.map, StateT.run]
    have hOp := retryEintr_single_req (cap.files.openat none path.toUTF8 appendOpenFlags 0o666)
      (.openat none path.toUTF8 appendOpenFlags 0o666) outcomeOfOpened
      (fun s' hW => cap_method_step hCap (.openat none path.toUTF8 appendOpenFlags 0o666)
        (cap.files.openat none path.toUTF8 appendOpenFlags 0o666) outcomeOfOpened rfl hW)
      (fun _ => rfl) DEFAULT_EINTR_FUEL hWf
    cases hR : (retryEintr (cap.files.openat none path.toUTF8 appendOpenFlags 0o666) DEFAULT_EINTR_FUEL s) with
    | mk oRes s1 =>
      rw [StateT.run] at hOp; rw [hR] at hOp; dsimp only at hOp
      obtain ⟨hWf1, hTmp1, trR, hStO, hAllO⟩ := hOp
      dsimp only [appendOpenFlags] at hR
      simp only [Bind.bind, StateT.bind, hR]
      have hFdR : TraceFds [] trR [] := traceFds_eintr_retries (fun _ hc => by cases hc) hAllO
      cases oRes with
      | error e =>
        simp only [Pure.pure, StateT.pure, allowedScopedRawFsStep]
        exact ⟨_, ⟨hWf1, hStO, traceFds_append hFdR (traceFds_nonFd_step rfl rfl), by omega⟩,
          hTmp1, nonLockErrOk_mapErrno _ _ _, by simp⟩
      | ok h =>
        let trOpen := trR ++ [(.openat none path.toUTF8 appendOpenFlags 0o666, .opened h)]
        have hFdO : TraceFds [] trOpen [h] := traceFds_append hFdR (traceFds_open_step rfl rfl)
        have hWr := writeAllAndClose_trace hCap h path content.toUTF8 [] DEFAULT_EINTR_FUEL hWf1
        cases hRw : (SysBridge.writeAllAndClose cap.files h path content.toUTF8 DEFAULT_EINTR_FUEL s1) with
        | mk wRes s2 =>
          simp only [StateT.run, hRw] at hWr ⊢
          obtain ⟨hWf2, hTmp2, trW, trC, hStWC, hFdW, hFdC, _, ⟨co, rfl⟩, hOutW⟩ := hWr
          have hTrAll : FsWorldTrace (proj s) (trOpen ++ trW ++ [(.close h, co)]) (proj s2) :=
            ⟨hWf2, by rw [List.append_assoc]; exact healthyFilesSteps_append hStO hStWC,
             by rw [List.append_assoc]; exact traceFds_append hFdO (traceFds_append hFdW hFdC), by omega⟩
          cases wRes with
          | ok u =>
            cases u
            exact ⟨_, hTrAll, hTmp2.trans hTmp1, h, trOpen, trW, [(.close h, co)],
              rfl, by simp [trOpen], hOutW, co, by simp⟩
          | error e => exact ⟨_, hTrAll, hTmp2.trans hTmp1, hOutW, by simp [trOpen]⟩
  | rename src dst =>
    simp only [execScopedRawFsStep, Internal.toScopedRawFsOpsM, SysBridge.mkRawFsOpsM,
      Functor.map, StateT.map, StateT.run]
    have hRn := retryEintr_single_req (cap.files.renameat2 none src.toUTF8 none dst.toUTF8 {})
      (.renameat2 none src.toUTF8 none dst.toUTF8 {}) outcomeOfUnit
      (fun s' hW => cap_method_step hCap (.renameat2 none src.toUTF8 none dst.toUTF8 {})
        (cap.files.renameat2 none src.toUTF8 none dst.toUTF8 {}) outcomeOfUnit rfl hW)
      (fun _ => rfl) DEFAULT_EINTR_FUEL hWf
    cases hR : (retryEintr (cap.files.renameat2 none src.toUTF8 none dst.toUTF8 {}) DEFAULT_EINTR_FUEL s) with
    | mk res s1 =>
      rw [StateT.run] at hRn; rw [hR] at hRn; dsimp only at hRn
      obtain ⟨hWf1, hTmp1, trR, hSt1, hAll1⟩ := hRn
      simp only [Bind.bind, StateT.bind, hR]
      have hTr1 : FsWorldTrace (proj s) (trR ++ [(.renameat2 none src.toUTF8 none dst.toUTF8 {}, outcomeOfUnit res)]) (proj s1) :=
        ⟨hWf1, hSt1, traceFds_append (traceFds_eintr_retries (fun _ hc => by cases hc) hAll1)
          (traceFds_nonFd_step (by cases res <;> rfl) rfl), by omega⟩
      cases res with
      | ok u =>
        cases u; simp only [Pure.pure, StateT.pure, allowedScopedRawFsStep]
        exact ⟨_, hTr1, hTmp1, by simp [RenameTrace, outcomeOfUnit]⟩
      | error e =>
        simp only [Pure.pure, StateT.pure, allowedScopedRawFsStep]
        exact ⟨_, hTr1, hTmp1, nonLockErrOk_mapErrno _ _ _, by simp⟩
  | chmod path mode =>
    simp only [execScopedRawFsStep, Internal.toScopedRawFsOpsM, SysBridge.mkRawFsOpsM,
      Functor.map, StateT.map, StateT.run]
    have hCh := retryEintr_single_req (cap.files.fchmodat none path.toUTF8 (UInt32.ofNat mode))
      (.fchmodat none path.toUTF8 (UInt32.ofNat mode)) outcomeOfUnit
      (fun s' hW => cap_method_step hCap (.fchmodat none path.toUTF8 (UInt32.ofNat mode))
        (cap.files.fchmodat none path.toUTF8 (UInt32.ofNat mode)) outcomeOfUnit rfl hW)
      (fun _ => rfl) DEFAULT_EINTR_FUEL hWf
    cases hR : (retryEintr (cap.files.fchmodat none path.toUTF8 (UInt32.ofNat mode)) DEFAULT_EINTR_FUEL s) with
    | mk res s1 =>
      rw [StateT.run] at hCh; rw [hR] at hCh; dsimp only at hCh
      obtain ⟨hWf1, hTmp1, trR, hSt1, hAll1⟩ := hCh
      simp only [Bind.bind, StateT.bind, hR]
      have hTr1 : FsWorldTrace (proj s) (trR ++ [(.fchmodat none path.toUTF8 (UInt32.ofNat mode), outcomeOfUnit res)]) (proj s1) :=
        ⟨hWf1, hSt1, traceFds_append (traceFds_eintr_retries (fun _ hc => by cases hc) hAll1)
          (traceFds_nonFd_step (by cases res <;> rfl) rfl), by omega⟩
      cases res with
      | ok u =>
        cases u; simp only [Pure.pure, StateT.pure, allowedScopedRawFsStep]
        exact ⟨_, hTr1, hTmp1, by simp [ChmodTrace, outcomeOfUnit]⟩
      | error e =>
        simp only [Pure.pure, StateT.pure, allowedScopedRawFsStep]
        exact ⟨_, hTr1, hTmp1, nonLockErrOk_mapErrno _ _ _, by simp⟩
  | symlink target linkPath =>
    simp only [execScopedRawFsStep, Internal.toScopedRawFsOpsM, SysBridge.mkRawFsOpsM,
      Functor.map, StateT.map, StateT.run]
    have hSy := retryEintr_single_req (cap.files.symlinkat target.toUTF8 none linkPath.toUTF8)
      (.symlinkat target.toUTF8 none linkPath.toUTF8) outcomeOfUnit
      (fun s' hW => cap_method_step hCap (.symlinkat target.toUTF8 none linkPath.toUTF8)
        (cap.files.symlinkat target.toUTF8 none linkPath.toUTF8) outcomeOfUnit rfl hW)
      (fun _ => rfl) DEFAULT_EINTR_FUEL hWf
    cases hR : (retryEintr (cap.files.symlinkat target.toUTF8 none linkPath.toUTF8) DEFAULT_EINTR_FUEL s) with
    | mk res s1 =>
      rw [StateT.run] at hSy; rw [hR] at hSy; dsimp only at hSy
      obtain ⟨hWf1, hTmp1, trR, hSt1, hAll1⟩ := hSy
      simp only [Bind.bind, StateT.bind, hR]
      have hTr1 : FsWorldTrace (proj s) (trR ++ [(.symlinkat target.toUTF8 none linkPath.toUTF8, outcomeOfUnit res)]) (proj s1) :=
        ⟨hWf1, hSt1, traceFds_append (traceFds_eintr_retries (fun _ hc => by cases hc) hAll1)
          (traceFds_nonFd_step (by cases res <;> rfl) rfl), by omega⟩
      cases res with
      | ok u =>
        cases u; simp only [Pure.pure, StateT.pure, allowedScopedRawFsStep]
        exact ⟨_, hTr1, hTmp1, by simp [SymlinkTrace, outcomeOfUnit]⟩
      | error e =>
        simp only [Pure.pure, StateT.pure, allowedScopedRawFsStep]
        exact ⟨_, hTr1, hTmp1, nonLockErrOk_mapErrno _ _ _, by simp⟩
  | readLink path =>
    simp only [execScopedRawFsStep, Internal.toScopedRawFsOpsM, SysBridge.mkRawFsOpsM,
      Functor.map, StateT.map, StateT.run]
    have hRl := readLinkLoop_trace hCap path 256 DEFAULT_EINTR_FUEL 13 hWf
    cases hR : (SysBridge.readLinkLoop cap.files path 256 DEFAULT_EINTR_FUEL 13 s) with
    | mk res s1 =>
      simp only [StateT.run, hR] at hRl ⊢
      obtain ⟨_, hTmp1, tr, hTr, hOut⟩ := hRl
      cases res with
      | ok tgt => exact ⟨tr, hTr, hTmp1, hOut.1⟩
      | error e => exact ⟨tr, hTr, hTmp1, hOut.1, hOut.2 (by omega)⟩
  | realPath path =>
    simp only [execScopedRawFsStep, Internal.toScopedRawFsOpsM, SysBridge.mkRawFsOpsM,
      Functor.map, StateT.map, StateT.run]
    have hRp := realPathPure_trace hCap path DEFAULT_EINTR_FUEL hWf
    cases hR : (SysBridge.realPathPure cap.files path DEFAULT_EINTR_FUEL s) with
    | mk res s1 =>
      simp only [StateT.run, hR] at hRp ⊢
      obtain ⟨_, hTmp1, tr, hTr, hOut⟩ := hRp
      cases res with
      | ok rp => exact ⟨tr, hTr, hTmp1, hOut⟩
      | error e => exact ⟨tr, hTr, hTmp1, hOut⟩
  | cwd =>
    simp only [execScopedRawFsStep, Internal.toScopedRawFsOpsM, SysBridge.mkRawFsOpsM,
      Functor.map, StateT.map, StateT.run]
    have hGc := getcwdLoop_trace hCap 4096 DEFAULT_EINTR_FUEL 9 hWf
    cases hR : (SysBridge.getcwdLoop cap.files 4096 DEFAULT_EINTR_FUEL 9 s) with
    | mk res s1 =>
      simp only [StateT.run, hR] at hGc ⊢
      obtain ⟨_, hTmp1, tr, hTr, hOut⟩ := hGc
      cases res with
      | ok cwdStr => exact ⟨tr, hTr, hTmp1, hOut.1⟩
      | error e => exact ⟨tr, hTr, hTmp1, hOut.1, hOut.2 (by omega)⟩
  | monotonicNonce =>
    simp only [execScopedRawFsStep, Internal.toScopedRawFsOpsM, SysBridge.mkRawFsOpsM,
      Functor.map, StateT.map, StateT.run, allowedScopedRawFsStep]
    have hN := cap_nextTempSeq hCap hWf
    cases hR : cap.nextTempSeq s with
    | mk n s1 =>
      simp only [Bind.bind, Pure.pure, StateT.run, hR] at hN ⊢
      obtain ⟨hWf1, hEnv1, hEqN, hTmp1⟩ := hN
      exact ⟨⟨hWf1, hEnv1 ▸ HealthyFilesSteps.nil _, TraceFds.nil [], by omega⟩, hEnv1, hEqN, hTmp1⟩
  | withFileLock path mode createIfMissing actRes =>
    simp only [execScopedRawFsStep, Internal.toScopedRawFsOpsM, Internal.withFileLockImplM,
      SysBridge.mkRawFsOpsM, Functor.map, StateT.map, StateT.run]
    have hAcq := acquireLockPure_trace hCap path mode createIfMissing false DEFAULT_EINTR_FUEL hWf
    cases hRa : (SysBridge.acquireLockPure cap.files path mode createIfMissing false DEFAULT_EINTR_FUEL s) with
    | mk aRes s1 =>
      rw [StateT.run] at hAcq; rw [hRa] at hAcq; dsimp only at hAcq
      obtain ⟨hWf1, hTmp1, hOutA⟩ := hAcq
      simp only [Bind.bind, StateT.bind, hRa]
      cases aRes with
      | error e =>
        simp only [Pure.pure, StateT.pure, allowedScopedRawFsStep]
        obtain ⟨tr, hTr, hErrCase⟩ := hOutA
        rcases hErrCase with hNl | ⟨_, hFalse, _⟩
        · exact ⟨tr, hTr, hTmp1, Or.inl hNl⟩
        · cases hFalse
      | ok h =>
        obtain ⟨rawSt, fl, modeArg, trO, trL, hStOL, hFdO, hFdL, hAcc, hNf, hCl, hNb, hMemO, hMemFs, hReg, hMemFl⟩ := hOutA
        have hBr := bracketLockM_pure_run (SysBridge.mkRawFsOpsM cap.files cap.nextTempSeq) h actRes s1
        change allowedScopedRawFsStep (proj s) (.withFileLock path mode createIfMissing actRes)
          (ScopedRawFsStepOut.lockVal ((Internal.bracketLockM (SysBridge.mkRawFsOpsM cap.files cap.nextTempSeq) h (pure actRes)).run s1).1)
          (proj ((Internal.bracketLockM (SysBridge.mkRawFsOpsM cap.files cap.nextTempSeq) h (pure actRes)).run s1).2)
        rw [hBr]
        have hRel := releaseLockPure_trace hCap h [] DEFAULT_EINTR_FUEL hWf1
        cases hRr : (SysBridge.releaseLockPure cap.files h DEFAULT_EINTR_FUEL s1) with
        | mk rRes s2 =>
          rw [StateT.run] at hRel; rw [hRr] at hRel; dsimp only at hRel
          obtain ⟨hWf2, hTmp2, trRel, hStR, hFdR, _, ⟨uo, hMemU, hUOk⟩, ⟨co, hMemC⟩, hErrR⟩ := hRel
          have hRelEq : ((SysBridge.mkRawFsOpsM cap.files cap.nextTempSeq).releaseLock h).run s1 = (rRes, s2) := hRr
          rw [hRelEq]; dsimp only
          have hTrAll : FsWorldTrace (proj s) (trO ++ trL ++ trRel) (proj s2) :=
            ⟨hWf2, healthyFilesSteps_append hStOL hStR,
             traceFds_append (traceFds_append hFdO hFdL) hFdR, by omega⟩
          cases actRes with
          | error ae =>
            exact ⟨_, hTrAll, hTmp2.trans hTmp1, Or.inr ⟨rfl, h, rawSt, fl, modeArg, trO, trL, trRel,
              rfl, hAcc, hNf, hCl, hNb, hMemO, hMemFs, hReg, hMemFl, ⟨uo, hMemU, fun hc => by cases hc⟩, co, hMemC⟩⟩
          | ok v =>
            cases rRes with
            | error re =>
              have hNe : trO ++ trL ++ trRel ≠ [] := by
                intro hN; have hRnil := (List.append_eq_nil_iff.mp hN).2; rw [hRnil] at hMemC; cases hMemC
              exact ⟨_, hTrAll, hTmp2.trans hTmp1, Or.inl ⟨hErrR, Or.inl hNe⟩⟩
            | ok u =>
              cases u
              exact ⟨_, hTrAll, hTmp2.trans hTmp1, rfl, h, rawSt, fl, modeArg, trO, trL, trRel,
                rfl, hAcc, hNf, hCl, hNb, hMemO, hMemFs, hReg, hMemFl, ⟨uo, hMemU, fun _ => hUOk rfl⟩, co, hMemC⟩
  | tryWithFileLock path mode createIfMissing actRes =>
    simp only [execScopedRawFsStep, Internal.toScopedRawFsOpsM, Internal.tryWithFileLockImplM,
      Functor.map, StateT.map, StateT.run]
    have hAcq := acquireLockPure_trace hCap path mode createIfMissing true DEFAULT_EINTR_FUEL hWf
    cases hRa : (SysBridge.acquireLockPure cap.files path mode createIfMissing true DEFAULT_EINTR_FUEL s) with
    | mk aRes s1 =>
      rw [StateT.run] at hAcq; rw [hRa] at hAcq; dsimp only at hAcq
      obtain ⟨hWf1, hTmp1, hOutA⟩ := hAcq
      have hRa' : (SysBridge.mkRawFsOpsM cap.files cap.nextTempSeq).acquireLock path mode createIfMissing true s = (aRes, s1) := hRa
      simp only [Bind.bind, StateT.bind, hRa']
      cases aRes with
      | error e =>
        obtain ⟨tr, hTr, hErrCase⟩ := hOutA
        by_cases hWb : (e.kind == .wouldBlock) = true
        · simp only [hWb, ↓reduceIte, Pure.pure, StateT.pure, allowedScopedRawFsStep]
          rcases hErrCase with ⟨hNl, _⟩ | ⟨_, _, hCont⟩
          · exact False.elim (hNl.2 ((fsErrorKind_beq_iff _ _).mp hWb))
          · exact ⟨tr, hTr, hTmp1, hCont⟩
        · simp only [hWb, Bool.false_eq_true, ↓reduceIte, Pure.pure, StateT.pure, allowedScopedRawFsStep]
          rcases hErrCase with hNl | ⟨hWbEq, _, _⟩
          · exact ⟨tr, hTr, hTmp1, Or.inl hNl⟩
          · exact False.elim (hWb ((fsErrorKind_beq_iff _ _).mpr hWbEq))
      | ok h =>
        obtain ⟨rawSt, fl, modeArg, trO, trL, hStOL, hFdO, hFdL, hAcc, hNf, hCl, hNb, hMemO, hMemFs, hReg, hMemFl⟩ := hOutA
        have hBr := bracketLockM_pure_run (SysBridge.mkRawFsOpsM cap.files cap.nextTempSeq) h actRes s1
        have hRel := releaseLockPure_trace hCap h [] DEFAULT_EINTR_FUEL hWf1
        cases hRr : (SysBridge.releaseLockPure cap.files h DEFAULT_EINTR_FUEL s1) with
        | mk rRes s2 =>
          rw [StateT.run] at hRel; rw [hRr] at hRel; dsimp only at hRel
          obtain ⟨hWf2, hTmp2, trRel, hStR, hFdR, _, ⟨uo, hMemU, hUOk⟩, ⟨co, hMemC⟩, hErrR⟩ := hRel
          have hRelEq : ((SysBridge.mkRawFsOpsM cap.files cap.nextTempSeq).releaseLock h).run s1 = (rRes, s2) := hRr
          rw [hRelEq] at hBr; simp only [StateT.run] at hBr
          simp only [StateT.bind, hBr]
          have hTrAll : FsWorldTrace (proj s) (trO ++ trL ++ trRel) (proj s2) :=
            ⟨hWf2, healthyFilesSteps_append hStOL hStR,
             traceFds_append (traceFds_append hFdO hFdL) hFdR, by omega⟩
          cases actRes with
          | error ae =>
            simp only [Pure.pure, allowedScopedRawFsStep]
            exact ⟨_, hTrAll, hTmp2.trans hTmp1, Or.inr ⟨rfl, h, rawSt, fl, modeArg, trO, trL, trRel,
              rfl, hAcc, hNf, hCl, hNb, hMemO, hMemFs, hReg, hMemFl, ⟨uo, hMemU, fun hc => by cases hc⟩, co, hMemC⟩⟩
          | ok v =>
            cases rRes with
            | error re =>
              simp only [Pure.pure, allowedScopedRawFsStep]
              have hNe : trO ++ trL ++ trRel ≠ [] := by
                intro hN; have hRnil := (List.append_eq_nil_iff.mp hN).2; rw [hRnil] at hMemC; cases hMemC
              exact ⟨_, hTrAll, hTmp2.trans hTmp1, Or.inl ⟨hErrR, Or.inl hNe⟩⟩
            | ok u =>
              cases u
              simp only [Pure.pure, allowedScopedRawFsStep]
              exact ⟨_, hTrAll, hTmp2.trans hTmp1, rfl, h, rawSt, fl, modeArg, trO, trL, trRel,
                rfl, hAcc, hNf, hCl, hNb, hMemO, hMemFs, hReg, hMemFl, ⟨uo, hMemU, fun _ => hUOk rfl⟩, co, hMemC⟩

end LeanSwe.Fs.Proofs
