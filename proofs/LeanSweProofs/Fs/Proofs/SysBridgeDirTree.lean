import LeanSweProofs.Fs.Proofs.SysBridgeDirMkdirWalk

namespace LeanSwe.Fs.Proofs

open LeanSwe.LinuxSyscall
open LeanSwe.LinuxSyscall.Files
open LeanSwe.Fs
open LeanSwe.Fs.Model

/-- Confined trace specification for `Internal.atomicWriteAtAuxM`. -/
theorem atomicWriteAtAuxM_trace {W fd : Type} {proj : W → FsWorld} {hidOf : fd → HandleId}
    {files : FilesOpsM (StateM W) fd} {nextNonce : StateM W Nat}
    (hCap : RefinesFsFilesFixed proj hidOf files nextNonce)
    (parDh : fd) (leaf : EntryName) (bytes : ByteArray) (held : List HandleId) (attempts : Nat)
    {s : W} (hWf : fsWorldWf (proj s) = true) :
    let p := (Internal.atomicWriteAtAuxM (SysBridge.mkRawDirOpsM files nextNonce) parDh leaf bytes attempts).run s
    fsWorldWf (proj p.2) = true ∧
    (proj s).tempSeq ≤ (proj p.2).tempSeq ∧
    ∃ tr,
      HealthyFilesSteps (proj s).env tr (proj p.2).env ∧
      TraceFds held tr held ∧
      (∀ step ∈ tr, SubtreeConfinedReq step.1) ∧
      match p.1 with
      | .ok () =>
        ∃ tmp : EntryName, ∃ sub1 sub2,
          Subtrace (sub1 ++ sub2) tr ∧
          WriteFileTrace (some (hidOf parDh)) tmp.val.toUTF8 createNewOpenFlags 0o644 bytes sub1 ∧
          RenameTrace (some (hidOf parDh)) tmp.val.toUTF8 (some (hidOf parDh)) leaf.val.toUTF8 sub2
      | .error e => nonLockErrOk e := by
  induction attempts generalizing s with
  | zero =>
    unfold Internal.atomicWriteAtAuxM
    simp only [Pure.pure, StateT.pure, StateT.run]
    exact ⟨hWf, Nat.le_refl _, [], HealthyFilesSteps.nil _, TraceFds.nil _, confined_nil,
      ⟨by simp, by intro h; cases h⟩⟩
  | succ a ih =>
    unfold Internal.atomicWriteAtAuxM
    have hTmp := dirOps_freshTempName_trace hCap held hWf
    cases hRt : ((SysBridge.mkRawDirOpsM files nextNonce).freshTempName s) with
    | mk tmp s1 =>
      rw [StateT.run] at hTmp; rw [hRt] at hTmp; dsimp only at hTmp
      obtain ⟨hWf1, hSeq1, hSt0, _⟩ := hTmp
      simp only [Bind.bind, StateT.bind, StateT.run, hRt]
      have hCr := createFileAtPure_trace hCap parDh tmp bytes held DEFAULT_EINTR_FUEL hWf1
      cases hRc : (SysBridge.createFileAtPure files parDh tmp bytes DEFAULT_EINTR_FUEL s1) with
      | mk crRes s2 =>
        rw [StateT.run] at hCr; rw [hRc] at hCr; dsimp only at hCr
        obtain ⟨hWf2, hTmp2, trC, hStC, hFdC, hConfC, hOutC⟩ := hCr
        have hRc' : (SysBridge.mkRawDirOpsM files nextNonce).createFileAt parDh tmp bytes s1 = (crRes, s2) := hRc
        rw [hRc']; dsimp only
        have hSt0C := healthyFilesSteps_append hSt0 hStC
        cases crRes with
        | ok u =>
          cases u
          have hRn := dirOps_renameAt_trace hCap parDh tmp parDh leaf held hWf2
          cases hRr : ((SysBridge.mkRawDirOpsM files nextNonce).renameAt parDh tmp parDh leaf s2) with
          | mk rnRes s3 =>
            rw [StateT.run] at hRn; rw [hRr] at hRn; dsimp only at hRn
            obtain ⟨hWf3, hTmp3, trR, hStR, hFdR, hConfR, hOutR⟩ := hRn
            simp only [Bind.bind, StateT.bind, hRr]
            cases rnRes with
            | ok u2 =>
              cases u2
              simp only [Pure.pure, StateT.pure]
              exact ⟨hWf3, by omega, trC ++ trR, healthyFilesSteps_append hSt0C hStR,
                traceFds_append hFdC hFdR, confined_append hConfC hConfR,
                tmp, trC, trR, subtrace_refl _, hOutC, hOutR⟩
            | error re =>
              have hUn := dirOps_unlinkAt_trace hCap parDh tmp false held hWf3
              cases hRu : ((SysBridge.mkRawDirOpsM files nextNonce).unlinkAt parDh tmp false s3) with
              | mk uRes s4 =>
                rw [StateT.run] at hUn; rw [hRu] at hUn; dsimp only at hUn
                obtain ⟨hWf4, hTmp4, trU, hStU, hFdU, hConfU, _⟩ := hUn
                simp only [Bind.bind, StateT.bind, Pure.pure, StateT.pure, hRu]
                exact ⟨hWf4, by omega, (trC ++ trR) ++ trU,
                  healthyFilesSteps_append (healthyFilesSteps_append hSt0C hStR) hStU,
                  traceFds_append (traceFds_append hFdC hFdR) hFdU,
                  confined_append (confined_append hConfC hConfR) hConfU, hOutR⟩
        | error ce =>
          by_cases hRetry : (ce.kind == .alreadyExists && decide (a > 0)) = true
          · simp only [hRetry, ↓reduceIte]
            have hIh := ih hWf2
            cases hO : (Internal.atomicWriteAtAuxM (SysBridge.mkRawDirOpsM files nextNonce) parDh leaf bytes a s2) with
            | mk r3 s3 =>
              simp only [StateT.run, hO] at hIh ⊢
              obtain ⟨hWf3, hTmp3, tr3, hSt3, hFd3, hConf3, hOut3⟩ := hIh
              refine ⟨hWf3, by omega, trC ++ tr3, healthyFilesSteps_append hSt0C hSt3,
                traceFds_append hFdC hFd3, confined_append hConfC hConf3, ?_⟩
              cases r3 with
              | error e => exact hOut3
              | ok u =>
                cases u
                obtain ⟨tmp', sub1, sub2, hSub, hW, hR⟩ := hOut3
                exact ⟨tmp', sub1, sub2, subtrace_append_right trC hSub, hW, hR⟩
          · simp only [hRetry, Bool.false_eq_true, ↓reduceIte, Pure.pure, StateT.pure]
            exact ⟨hWf2, by omega, trC, hSt0C, hFdC, hConfC, hOutC⟩

/-- Confined trace and sortedness specification for `Internal.walkRecM`. -/
theorem walkRecM_trace {W fd : Type} {proj : W → FsWorld} {hidOf : fd → HandleId}
    {files : FilesOpsM (StateM W) fd} {nextNonce : StateM W Nat}
    (hCap : RefinesFsFilesFixed proj hidOf files nextNonce)
    (rootDh : fd) (fuel : Nat) :
    ∀ (relSegs : List EntryName) (relLabel : String) (acc : Array WalkEntry) (s : W),
      fsWorldWf (proj s) = true →
      (∀ e ∈ acc.toList, WalkEntrySorted e) →
      let p := (Internal.walkRecM (SysBridge.mkRawDirOpsM files nextNonce) rootDh relSegs relLabel acc fuel).run s
      fsWorldWf (proj p.2) = true ∧
      (proj s).tempSeq ≤ (proj p.2).tempSeq ∧
      ∃ tr,
        HealthyFilesSteps (proj s).env tr (proj p.2).env ∧
        TraceFds [hidOf rootDh] tr [hidOf rootDh] ∧
        (∀ step ∈ tr, SubtreeConfinedReq step.1) ∧
        match p.1 with
        | .ok entries =>
          (∀ e ∈ entries.toList, WalkEntrySorted e) ∧
          entries.size > acc.size ∧
          ∃ h eof, (.getdents64 h 8192, .bytes eof) ∈ tr ∧ eof.size = 0
        | .error e => nonLockErrOk e := by
  induction fuel with
  | zero =>
    intro relSegs relLabel acc s hWf _
    unfold Internal.walkRecM
    simp only [Pure.pure, StateT.pure, StateT.run]
    exact ⟨hWf, Nat.le_refl _, [], HealthyFilesSteps.nil _, TraceFds.nil _, confined_nil,
      ⟨nonEmpty_append_left (by decide), by intro h; cases h⟩⟩
  | succ f ih =>
    have hChildren : ∀ (relSegs : List EntryName) (relLabel : String)
        (dirs : List EntryName) (acc : Array WalkEntry) (s : W),
        fsWorldWf (proj s) = true →
        (∀ e ∈ acc.toList, WalkEntrySorted e) →
        let q := (Internal.walkChildrenM (SysBridge.mkRawDirOpsM files nextNonce) rootDh relSegs relLabel f acc dirs).run s
        fsWorldWf (proj q.2) = true ∧
        (proj s).tempSeq ≤ (proj q.2).tempSeq ∧
        ∃ tr,
          HealthyFilesSteps (proj s).env tr (proj q.2).env ∧
          TraceFds [hidOf rootDh] tr [hidOf rootDh] ∧
          (∀ step ∈ tr, SubtreeConfinedReq step.1) ∧
          match q.1 with
          | .ok entries =>
            (∀ e ∈ entries.toList, WalkEntrySorted e) ∧ entries.size ≥ acc.size
          | .error e => nonLockErrOk e := by
      intro relSegs relLabel dirs
      induction dirs with
      | nil =>
        intro acc s hWf hAcc
        unfold Internal.walkChildrenM
        simp only [Pure.pure, StateT.pure, StateT.run]
        exact ⟨hWf, Nat.le_refl _, [], HealthyFilesSteps.nil _, TraceFds.nil _, confined_nil, hAcc, Nat.le_refl _⟩
      | cons d rest ihD =>
        intro acc s hWf hAcc
        unfold Internal.walkChildrenM
        have hSub := ih (relSegs ++ [d]) (if (relLabel == ".") = true then d.val else relLabel ++ "/" ++ d.val) acc s hWf hAcc
        cases hR : (Internal.walkRecM (SysBridge.mkRawDirOpsM files nextNonce) rootDh
            (relSegs ++ [d]) (if (relLabel == ".") = true then d.val else relLabel ++ "/" ++ d.val) acc f s) with
        | mk r1 s1 =>
          rw [StateT.run] at hSub; rw [hR] at hSub; dsimp only at hSub
          obtain ⟨hWf1, hTmp1, tr1, hSt1, hFd1, hConf1, hOut1⟩ := hSub
          simp only [Bind.bind, StateT.bind, StateT.run, hR]
          cases r1 with
          | error e =>
            simp only [Pure.pure, StateT.pure]
            exact ⟨hWf1, hTmp1, tr1, hSt1, hFd1, hConf1, hOut1⟩
          | ok acc' =>
            have hRest := ihD acc' s1 hWf1 hOut1.1
            cases hR2 : (Internal.walkChildrenM (SysBridge.mkRawDirOpsM files nextNonce) rootDh relSegs relLabel f acc' rest s1) with
            | mk r2 s2 =>
              simp only [StateT.run, hR2] at hRest ⊢
              obtain ⟨hWf2, hTmp2, tr2, hSt2, hFd2, hConf2, hOut2⟩ := hRest
              refine ⟨hWf2, by omega, tr1 ++ tr2, healthyFilesSteps_append hSt1 hSt2,
                traceFds_append hFd1 hFd2, confined_append hConf1 hConf2, ?_⟩
              cases r2 with
              | error e => exact hOut2
              | ok entries => exact ⟨hOut2.1, by have := hOut1.2.1; have := hOut2.2; omega⟩
    intro relSegs relLabel acc s hWf hAcc
    let readClassify : fd → StateM W (Except FsError (List EntryName × List String)) := fun dirDh => do
      match ← (SysBridge.mkRawDirOpsM files nextNonce).readDirAt dirDh with
      | .error e => pure (.error e)
      | .ok rawNames =>
        Internal.classifyChildrenM (SysBridge.mkRawDirOpsM files nextNonce) dirDh (Internal.sortEntryNames rawNames) [] []
    have hWalk := walkDescendAuxM_trace hCap (fun _ => (none : Option fd))
      (fun _ res tr =>
        List.Pairwise (· ≤ ·) (res.1.map (·.val)) ∧ List.Pairwise (· ≤ ·) res.2 ∧
        ∃ h eof, (.getdents64 h 8192, .bytes eof) ∈ tr ∧ eof.size = 0)
      (fun e _ => nonLockErrOk e)
      (fun _ _ _ _ h => h)
      (fun _ _ h _ => h)
      readClassify
      (fun dirDh held s0 hW0 => by
        dsimp only [readClassify]
        have hRd := readDirAtPure_trace hCap dirDh held DEFAULT_EINTR_FUEL SysBridge.DEFAULT_STREAM_FUEL hW0
        cases hR0 : (SysBridge.readDirAtPure files dirDh DEFAULT_EINTR_FUEL SysBridge.DEFAULT_STREAM_FUEL s0) with
        | mk rdRes s1 =>
          rw [StateT.run] at hRd; rw [hR0] at hRd; dsimp only at hRd
          obtain ⟨hWf1, hTmp1, trRd, hStRd, hFdRd, hConfRd, hOutRd⟩ := hRd
          have hR0' : (SysBridge.mkRawDirOpsM files nextNonce).readDirAt dirDh s0 = (rdRes, s1) := hR0
          simp only [Bind.bind, StateT.bind, StateT.run, hR0']
          cases rdRes with
          | error e =>
            simp only [Pure.pure, StateT.pure]
            exact ⟨hWf1, by omega, trRd, hStRd, hConfRd, hFdRd, hOutRd⟩
          | ok rawNames =>
            have hCl := classifyChildrenM_trace hCap dirDh held (Internal.sortEntryNames rawNames) [] []
              (sortEntryNames_pairwise rawNames) List.Pairwise.nil List.Pairwise.nil
              (fun _ hm => nomatch hm) (fun _ hm => nomatch hm) hWf1
            cases hRc : (Internal.classifyChildrenM (SysBridge.mkRawDirOpsM files nextNonce) dirDh
                (Internal.sortEntryNames rawNames) [] [] s1) with
            | mk clRes s2 =>
              simp only [StateT.run, hRc] at hCl ⊢
              obtain ⟨hWf2, hTmp2, trCl, hStCl, hFdCl, hConfCl, hOutCl⟩ := hCl
              refine ⟨hWf2, by omega, trRd ++ trCl, healthyFilesSteps_append hStRd hStCl,
                confined_append hConfRd hConfCl, ?_⟩
              cases clRes with
              | error e => exact ⟨traceFds_append hFdRd hFdCl, hOutCl⟩
              | ok pair =>
                obtain ⟨h, eof, hMemE, hEz, _⟩ := hOutRd
                exact ⟨traceFds_append hFdRd hFdCl, hOutCl.1, hOutCl.2,
                  h, eof, List.mem_append_left _ hMemE, hEz⟩)
      true rootDh [hidOf rootDh] relSegs hWf
    cases hRw : (Internal.walkDescendM (SysBridge.mkRawDirOpsM files nextNonce) rootDh relSegs readClassify s) with
    | mk rRead s1 =>
      have hRw' : Internal.walkDescendAuxM (SysBridge.mkRawDirOpsM files nextNonce) true rootDh relSegs readClassify s = (rRead, s1) := hRw
      rw [StateT.run] at hWalk; rw [hRw'] at hWalk; simp only [↓reduceIte] at hWalk
      obtain ⟨hWf1, hTmp1, tr1, hSt1, hConf1, hOut1⟩ := hWalk
      have hStepEq : (Internal.walkRecM (SysBridge.mkRawDirOpsM files nextNonce) rootDh relSegs relLabel acc (f + 1)).run s =
          (match rRead with
           | .error e => (Except.error e, s1)
           | .ok (dirs, outFiles) =>
             (Internal.walkChildrenM (SysBridge.mkRawDirOpsM files nextNonce) rootDh relSegs relLabel f
               (acc.push { root := relLabel, dirs := (dirs.map (·.val)).toArray, files := outFiles.toArray }) dirs).run s1) := by
        conv => lhs; unfold Internal.walkRecM
        refine Eq.trans ?_ (show (Internal.walkDescendM (SysBridge.mkRawDirOpsM files nextNonce) rootDh relSegs readClassify >>= fun r =>
          match r with
          | .error e => pure (Except.error e)
          | .ok (dirs, outFiles) => Internal.walkChildrenM (SysBridge.mkRawDirOpsM files nextNonce) rootDh relSegs relLabel f
              (acc.push { root := relLabel, dirs := (dirs.map (·.val)).toArray, files := outFiles.toArray }) dirs).run s = _ from by
          simp only [Bind.bind, StateT.bind, StateT.run, hRw]; cases rRead <;> rfl)
        have hF : ∀ (a b : fd → StateM W (Except FsError (List EntryName × List String)))
            (g1 g2 : Except FsError (List EntryName × List String) → StateM W (Except FsError (Array WalkEntry))),
            a = b → g1 = g2 →
            (Internal.walkDescendM (SysBridge.mkRawDirOpsM files nextNonce) rootDh relSegs a >>= g1).run s =
            (Internal.walkDescendM (SysBridge.mkRawDirOpsM files nextNonce) rootDh relSegs b >>= g2).run s := by
          rintro _ _ _ _ rfl rfl; rfl
        refine hF _ _ _ _ (funext fun dirDh => funext fun s0 => ?_) (funext fun r => by cases r <;> rfl)
        simp only [readClassify, Bind.bind, StateT.bind]
        cases (SysBridge.mkRawDirOpsM files nextNonce).readDirAt dirDh s0 with
        | mk r0 _ => cases r0 <;> rfl
      dsimp only; rw [hStepEq]
      cases rRead with
      | error e =>
        dsimp only
        exact ⟨hWf1, hTmp1, tr1, hSt1, hOut1.1, hConf1, hOut1.2⟩
      | ok pair =>
        dsimp only
        obtain ⟨hFd1, _, sub, ⟨pre, post, rfl⟩, hDirS, hFileS, h, eof, hMemE, hEz⟩ := hOut1
        let entry : WalkEntry := {
          root := relLabel
          dirs := (pair.1.map (·.val)).toArray
          files := pair.2.toArray }
        have hEntrySorted : WalkEntrySorted entry := ⟨by simpa [entry] using hDirS, by simpa [entry] using hFileS⟩
        have hAcc' : ∀ e ∈ (acc.push entry).toList, WalkEntrySorted e := by
          intro e he
          rw [Array.toList_push, List.mem_append, List.mem_singleton] at he
          rcases he with hOld | rfl
          · exact hAcc e hOld
          · exact hEntrySorted
        have hCh := hChildren relSegs relLabel pair.1 (acc.push entry) s1 hWf1 hAcc'
        cases hRc : (Internal.walkChildrenM (SysBridge.mkRawDirOpsM files nextNonce) rootDh relSegs relLabel f (acc.push entry) pair.1 s1) with
        | mk r2 s2 =>
          simp only [StateT.run, hRc] at hCh
          dsimp only [entry] at hRc
          simp only [StateT.run, hRc]
          obtain ⟨hWf2, hTmp2, tr2, hSt2, hFd2, hConf2, hOut2⟩ := hCh
          refine ⟨hWf2, by omega, (pre ++ sub ++ post) ++ tr2, healthyFilesSteps_append hSt1 hSt2,
            traceFds_append hFd1 hFd2, confined_append hConf1 hConf2, ?_⟩
          cases r2 with
          | error e => exact hOut2
          | ok entries =>
            refine ⟨hOut2.1, ?_, h, eof, by simp [hMemE], hEz⟩
            have hSz := hOut2.2
            simp only [Array.size_push] at hSz
            omega

/-- Confined trace specification for `Internal.rmtreeNonDirPrefixM`. -/
theorem rmtreeNonDirPrefixM_trace {W fd : Type} {proj : W → FsWorld} {hidOf : fd → HandleId}
    {files : FilesOpsM (StateM W) fd} {nextNonce : StateM W Nat}
    (hCap : RefinesFsFilesFixed proj hidOf files nextNonce)
    (dirDh : fd) (held : List HandleId) (items : List EntryName)
    {s : W} (hWf : fsWorldWf (proj s) = true) :
    let p := (Internal.rmtreeNonDirPrefixM (SysBridge.mkRawDirOpsM files nextNonce) dirDh items).run s
    fsWorldWf (proj p.2) = true ∧
    (proj p.2).tempSeq = (proj s).tempSeq ∧
    ∃ tr,
      HealthyFilesSteps (proj s).env tr (proj p.2).env ∧
      TraceFds held tr held ∧
      (∀ step ∈ tr, SubtreeConfinedReq step.1) ∧
      match p.1 with
      | .ok _ => True
      | .error e => nonLockErrOk e := by
  induction items generalizing s with
  | nil =>
    unfold Internal.rmtreeNonDirPrefixM
    simp only [Pure.pure, StateT.pure, StateT.run]
    exact ⟨hWf, trivial, [], HealthyFilesSteps.nil _, TraceFds.nil _, confined_nil, trivial⟩
  | cons c rest ih =>
    unfold Internal.rmtreeNonDirPrefixM
    have hLs := dirOps_lstatAt_trace hCap dirDh c held hWf
    cases hR : ((SysBridge.mkRawDirOpsM files nextNonce).lstatAt dirDh c s) with
    | mk res s1 =>
      rw [StateT.run] at hLs; rw [hR] at hLs; dsimp only at hLs
      obtain ⟨hWf1, hTmp1, tr1, hSt1, hFd1, hConf1, hOut1⟩ := hLs
      simp only [Bind.bind, StateT.bind, StateT.run, hR]
      cases res with
      | error e =>
        by_cases hNf : (e.kind == .notFound) = true
        · simp only [hNf, ↓reduceIte]
          have hIh := ih hWf1
          cases hO : (Internal.rmtreeNonDirPrefixM (SysBridge.mkRawDirOpsM files nextNonce) dirDh rest s1) with
          | mk r2 s2 =>
            simp only [StateT.run, hO] at hIh ⊢
            obtain ⟨hWf2, hTmp2, tr2, hSt2, hFd2, hConf2, hOut2⟩ := hIh
            exact ⟨hWf2, hTmp2.trans hTmp1, tr1 ++ tr2, healthyFilesSteps_append hSt1 hSt2,
              traceFds_append hFd1 hFd2, confined_append hConf1 hConf2, hOut2⟩
        · simp only [hNf, Bool.false_eq_true, ↓reduceIte, Pure.pure, StateT.pure]
          exact ⟨hWf1, hTmp1, tr1, hSt1, hFd1, hConf1, hOut1.1⟩
      | ok info =>
        by_cases hDir : (info.kind == .dir) = true
        · simp only [hDir, ↓reduceIte, Pure.pure, StateT.pure]
          exact ⟨hWf1, hTmp1, tr1, hSt1, hFd1, hConf1, trivial⟩
        · simp only [hDir, Bool.false_eq_true, ↓reduceIte]
          have hUn := dirOps_unlinkAt_trace hCap dirDh c false held hWf1
          cases hRu : ((SysBridge.mkRawDirOpsM files nextNonce).unlinkAt dirDh c false s1) with
          | mk uRes s2 =>
            rw [StateT.run] at hUn; rw [hRu] at hUn; dsimp only at hUn
            obtain ⟨hWf2, hTmp2, trU, hStU, hFdU, hConfU, hOutU⟩ := hUn
            simp only [Bind.bind, StateT.bind, hRu]
            cases uRes with
            | ok u =>
              cases u
              have hIh := ih hWf2
              cases hO : (Internal.rmtreeNonDirPrefixM (SysBridge.mkRawDirOpsM files nextNonce) dirDh rest s2) with
              | mk r3 s3 =>
                simp only [StateT.run, hO] at hIh ⊢
                obtain ⟨hWf3, hTmp3, tr3, hSt3, hFd3, hConf3, hOut3⟩ := hIh
                exact ⟨hWf3, hTmp3.trans (hTmp2.trans hTmp1), (tr1 ++ trU) ++ tr3,
                  healthyFilesSteps_append (healthyFilesSteps_append hSt1 hStU) hSt3,
                  traceFds_append (traceFds_append hFd1 hFdU) hFd3,
                  confined_append (confined_append hConf1 hConfU) hConf3, hOut3⟩
            | error ue =>
              by_cases hNf : (ue.kind == .notFound) = true
              · simp only [hNf, ↓reduceIte]
                have hIh := ih hWf2
                cases hO : (Internal.rmtreeNonDirPrefixM (SysBridge.mkRawDirOpsM files nextNonce) dirDh rest s2) with
                | mk r3 s3 =>
                  simp only [StateT.run, hO] at hIh ⊢
                  obtain ⟨hWf3, hTmp3, tr3, hSt3, hFd3, hConf3, hOut3⟩ := hIh
                  exact ⟨hWf3, hTmp3.trans (hTmp2.trans hTmp1), (tr1 ++ trU) ++ tr3,
                    healthyFilesSteps_append (healthyFilesSteps_append hSt1 hStU) hSt3,
                    traceFds_append (traceFds_append hFd1 hFdU) hFd3,
                    confined_append (confined_append hConf1 hConfU) hConf3, hOut3⟩
              · simp only [hNf, Bool.false_eq_true, ↓reduceIte, Pure.pure, StateT.pure]
                exact ⟨hWf2, hTmp2.trans hTmp1, tr1 ++ trU, healthyFilesSteps_append hSt1 hStU,
                  traceFds_append hFd1 hFdU, confined_append hConf1 hConfU, hOutU.1⟩

/-- Confined trace specification for `Internal.rmtreeProcessM`. -/
theorem rmtreeProcessM_trace {W fd : Type} {proj : W → FsWorld} {hidOf : fd → HandleId}
    {files : FilesOpsM (StateM W) fd} {nextNonce : StateM W Nat}
    (hCap : RefinesFsFilesFixed proj hidOf files nextNonce)
    (rootDh : fd) (dirSegs : List EntryName)
    (subDirFn : EntryName → StateM W (Except FsError Unit))
    (hSub : ∀ (sub : EntryName) {s : W}, fsWorldWf (proj s) = true →
      let q := (subDirFn sub).run s
      fsWorldWf (proj q.2) = true ∧ (proj s).tempSeq ≤ (proj q.2).tempSeq ∧
      ∃ tr, HealthyFilesSteps (proj s).env tr (proj q.2).env ∧
        TraceFds [hidOf rootDh] tr [hidOf rootDh] ∧ (∀ step ∈ tr, SubtreeConfinedReq step.1) ∧
        match q.1 with | .ok () => True | .error e => nonLockErrOk e)
    (steps : Nat) (items : List EntryName) {s : W} (hWf : fsWorldWf (proj s) = true) :
    let p := (Internal.rmtreeProcessM (SysBridge.mkRawDirOpsM files nextNonce) rootDh dirSegs subDirFn steps items).run s
    fsWorldWf (proj p.2) = true ∧
    (proj s).tempSeq ≤ (proj p.2).tempSeq ∧
    ∃ tr,
      HealthyFilesSteps (proj s).env tr (proj p.2).env ∧
      TraceFds [hidOf rootDh] tr [hidOf rootDh] ∧
      (∀ step ∈ tr, SubtreeConfinedReq step.1) ∧
      match p.1 with
      | .ok () => True
      | .error e => nonLockErrOk e := by
  induction steps generalizing items s with
  | zero =>
    unfold Internal.rmtreeProcessM
    cases items <;> simp only [Pure.pure, StateT.pure, StateT.run] <;>
      exact ⟨hWf, Nat.le_refl _, [], HealthyFilesSteps.nil _, TraceFds.nil _, confined_nil, trivial⟩
  | succ k ih =>
    cases items with
    | nil =>
      unfold Internal.rmtreeProcessM
      simp only [Pure.pure, StateT.pure, StateT.run]
      exact ⟨hWf, Nat.le_refl _, [], HealthyFilesSteps.nil _, TraceFds.nil _, confined_nil, trivial⟩
    | cons hd tl =>
      unfold Internal.rmtreeProcessM
      have hBatch := walkDescendAuxM_trace hCap (fun _ => (none : Option fd)) (fun _ _ _ => True)
        (fun e _ => nonLockErrOk e) (fun _ _ _ _ h => h) (fun _ _ h _ => h)
        (fun dirDh => Internal.rmtreeNonDirPrefixM (SysBridge.mkRawDirOpsM files nextNonce) dirDh (hd :: tl))
        (fun dirDh held s0 hW0 => by
          have hP := rmtreeNonDirPrefixM_trace hCap dirDh held (hd :: tl) hW0
          cases hRp : (Internal.rmtreeNonDirPrefixM (SysBridge.mkRawDirOpsM files nextNonce) dirDh (hd :: tl) s0) with
          | mk r0 s1 =>
            simp only [StateT.run, hRp] at hP ⊢
            obtain ⟨hWf1, hTmp1, tr, hSt, hFd, hConf, hOut⟩ := hP
            exact ⟨hWf1, by omega, tr, hSt, hConf, by cases r0 <;> exact ⟨hFd, hOut⟩⟩)
        true rootDh [hidOf rootDh] dirSegs hWf
      cases hRb : (Internal.walkDescendM (SysBridge.mkRawDirOpsM files nextNonce) rootDh dirSegs
          (fun dirDh => Internal.rmtreeNonDirPrefixM (SysBridge.mkRawDirOpsM files nextNonce) dirDh (hd :: tl)) s) with
      | mk bRes s1 =>
        have hRb' : Internal.walkDescendAuxM (SysBridge.mkRawDirOpsM files nextNonce) true rootDh dirSegs
            (fun dirDh => Internal.rmtreeNonDirPrefixM (SysBridge.mkRawDirOpsM files nextNonce) dirDh (hd :: tl)) s = (bRes, s1) := hRb
        rw [StateT.run] at hBatch; rw [hRb'] at hBatch; simp only [↓reduceIte] at hBatch
        obtain ⟨hWf1, hTmp1, tr1, hSt1, hConf1, hOut1⟩ := hBatch
        simp only [Bind.bind, StateT.bind, StateT.run, hRb]
        cases bRes with
        | error e =>
          simp only [Pure.pure, StateT.pure]
          exact ⟨hWf1, hTmp1, tr1, hSt1, hOut1.1, hConf1, hOut1.2⟩
        | ok opt =>
          cases opt with
          | none =>
            simp only [Pure.pure, StateT.pure]
            exact ⟨hWf1, hTmp1, tr1, hSt1, hOut1.1, hConf1, trivial⟩
          | some pair =>
            have hS := hSub pair.1 hWf1
            cases hRs : subDirFn pair.1 s1 with
            | mk sRes s2 =>
              rw [StateT.run] at hS; rw [hRs] at hS; dsimp only at hS
              obtain ⟨hWf2, hTmp2, tr2, hSt2, hFd2, hConf2, hOut2⟩ := hS
              simp only [Bind.bind, StateT.bind, hRs]
              cases sRes with
              | error e =>
                simp only [Pure.pure, StateT.pure]
                exact ⟨hWf2, by omega, tr1 ++ tr2, healthyFilesSteps_append hSt1 hSt2,
                  traceFds_append hOut1.1 hFd2, confined_append hConf1 hConf2, hOut2⟩
              | ok u =>
                cases u
                have hIh := ih pair.2 hWf2
                cases hR3 : (Internal.rmtreeProcessM (SysBridge.mkRawDirOpsM files nextNonce) rootDh dirSegs subDirFn k pair.2 s2) with
                | mk r3 s3 =>
                  simp only [StateT.run, hR3] at hIh ⊢
                  obtain ⟨hWf3, hTmp3, tr3, hSt3, hFd3, hConf3, hOut3⟩ := hIh
                  exact ⟨hWf3, by omega, (tr1 ++ tr2) ++ tr3,
                    healthyFilesSteps_append (healthyFilesSteps_append hSt1 hSt2) hSt3,
                    traceFds_append (traceFds_append hOut1.1 hFd2) hFd3,
                    confined_append (confined_append hConf1 hConf2) hConf3, hOut3⟩

/-- Confined trace specification for `Internal.rmtreeDirAtM`. -/
theorem rmtreeDirAtM_trace {W fd : Type} {proj : W → FsWorld} {hidOf : fd → HandleId}
    {files : FilesOpsM (StateM W) fd} {nextNonce : StateM W Nat}
    (hCap : RefinesFsFilesFixed proj hidOf files nextNonce)
    (rootDh : fd) (fuel : Nat) :
    ∀ (parSegs : List EntryName) (leaf : EntryName) (s : W),
      fsWorldWf (proj s) = true →
      let p := (Internal.rmtreeDirAtM (SysBridge.mkRawDirOpsM files nextNonce) rootDh parSegs leaf fuel).run s
      fsWorldWf (proj p.2) = true ∧
      (proj s).tempSeq ≤ (proj p.2).tempSeq ∧
      ∃ tr,
        HealthyFilesSteps (proj s).env tr (proj p.2).env ∧
        TraceFds [hidOf rootDh] tr [hidOf rootDh] ∧
        (∀ step ∈ tr, SubtreeConfinedReq step.1) ∧
        match p.1 with
        | .ok () => ∃ d, UnlinkTrace (some d) leaf.val.toUTF8 true tr
        | .error e => nonLockErrOk e := by
  induction fuel with
  | zero =>
    intro parSegs leaf s hWf
    unfold Internal.rmtreeDirAtM
    simp only [Pure.pure, StateT.pure, StateT.run]
    exact ⟨hWf, Nat.le_refl _, [], HealthyFilesSteps.nil _, TraceFds.nil _, confined_nil,
      ⟨nonEmpty_append_left (by decide), by intro h; cases h⟩⟩
  | succ f ih =>
    intro parSegs leaf s hWf
    unfold Internal.rmtreeDirAtM
    have hRd := walkDescendAuxM_trace hCap (fun _ => (none : Option fd)) (fun _ _ _ => True)
      (fun e _ => nonLockErrOk e) (fun _ _ _ _ h => h) (fun _ _ h _ => h)
      (fun dirDh => (SysBridge.mkRawDirOpsM files nextNonce).readDirAt dirDh)
      (fun dirDh held s0 hW0 => by
        have hR := readDirAtPure_trace hCap dirDh held DEFAULT_EINTR_FUEL SysBridge.DEFAULT_STREAM_FUEL hW0
        cases hRo : (SysBridge.readDirAtPure files dirDh DEFAULT_EINTR_FUEL SysBridge.DEFAULT_STREAM_FUEL s0) with
        | mk res s1 =>
          simp only [SysBridge.mkRawDirOpsM, StateT.run, hRo] at hR ⊢
          obtain ⟨hWf1, hTmp1, tr, hSt, hFd, hConf, hOut⟩ := hR
          exact ⟨hWf1, by omega, tr, hSt, hConf, by cases res <;> exact ⟨hFd, by first | trivial | exact hOut⟩⟩)
      true rootDh [hidOf rootDh] (parSegs ++ [leaf]) hWf
    cases hRr : (Internal.walkDescendM (SysBridge.mkRawDirOpsM files nextNonce) rootDh (parSegs ++ [leaf])
        (fun dirDh => (SysBridge.mkRawDirOpsM files nextNonce).readDirAt dirDh) s) with
    | mk rRead s1 =>
      have hRr' : Internal.walkDescendAuxM (SysBridge.mkRawDirOpsM files nextNonce) true rootDh (parSegs ++ [leaf])
          (fun dirDh => (SysBridge.mkRawDirOpsM files nextNonce).readDirAt dirDh) s = (rRead, s1) := hRr
      rw [StateT.run] at hRd; rw [hRr'] at hRd; simp only [↓reduceIte] at hRd
      obtain ⟨hWf1, hTmp1, tr1, hSt1, hConf1, hOut1⟩ := hRd
      simp only [Bind.bind, StateT.bind, StateT.run, hRr]
      cases rRead with
      | error e =>
        simp only [Pure.pure, StateT.pure]
        exact ⟨hWf1, hTmp1, tr1, hSt1, hOut1.1, hConf1, hOut1.2⟩
      | ok rawNames =>
        have hProc := rmtreeProcessM_trace hCap rootDh (parSegs ++ [leaf])
          (fun subDir => Internal.rmtreeDirAtM (SysBridge.mkRawDirOpsM files nextNonce) rootDh (parSegs ++ [leaf]) subDir f)
          (fun sub s0 hW0 => by
            have hI := ih (parSegs ++ [leaf]) sub s0 hW0
            cases hRi : (Internal.rmtreeDirAtM (SysBridge.mkRawDirOpsM files nextNonce) rootDh (parSegs ++ [leaf]) sub f s0) with
            | mk r0 sX =>
              simp only [StateT.run, hRi] at hI ⊢
              obtain ⟨hWfX, hTmpX, trX, hStX, hFdX, hConfX, hOutX⟩ := hI
              exact ⟨hWfX, hTmpX, trX, hStX, hFdX, hConfX, by cases r0 with | ok u => cases u; trivial | error e => exact hOutX⟩)
          (Internal.sortEntryNames rawNames).length (Internal.sortEntryNames rawNames) hWf1
        cases hRp : (Internal.rmtreeProcessM (SysBridge.mkRawDirOpsM files nextNonce) rootDh (parSegs ++ [leaf])
            (fun subDir => Internal.rmtreeDirAtM (SysBridge.mkRawDirOpsM files nextNonce) rootDh (parSegs ++ [leaf]) subDir f)
            (Internal.sortEntryNames rawNames).length (Internal.sortEntryNames rawNames) s1) with
        | mk pRes s2 =>
          rw [StateT.run] at hProc; rw [hRp] at hProc; dsimp only at hProc
          obtain ⟨hWf2, hTmp2, tr2, hSt2, hFd2, hConf2, hOut2⟩ := hProc
          simp only [Bind.bind, StateT.bind, hRp]
          cases pRes with
          | error e =>
            simp only [Pure.pure, StateT.pure]
            exact ⟨hWf2, by omega, tr1 ++ tr2, healthyFilesSteps_append hSt1 hSt2,
              traceFds_append hOut1.1 hFd2, confined_append hConf1 hConf2, hOut2⟩
          | ok u =>
            cases u
            have hUn := walkDescendAuxM_trace hCap (fun _ => (none : Option fd))
              (fun parDh _ tr => UnlinkTrace (some parDh) leaf.val.toUTF8 true tr)
              (fun e _ => nonLockErrOk e) (fun _ _ _ _ h => h) (fun _ _ h _ => h)
              (fun parDh => (SysBridge.mkRawDirOpsM files nextNonce).unlinkAt parDh leaf true)
              (fun parDh held s0 hW0 => by
                have hU := dirOps_unlinkAt_trace hCap parDh leaf true held hW0
                cases hRu : ((SysBridge.mkRawDirOpsM files nextNonce).unlinkAt parDh leaf true s0) with
                | mk uRes sX =>
                  simp only [StateT.run, hRu] at hU ⊢
                  obtain ⟨hWfX, hTmpX, trX, hStX, hFdX, hConfX, hOutX⟩ := hU
                  exact ⟨hWfX, by omega, trX, hStX, hConfX, by cases uRes with | ok u => cases u; exact ⟨hFdX, hOutX⟩ | error e => exact ⟨hFdX, hOutX.1⟩⟩)
              true rootDh [hidOf rootDh] parSegs hWf2
            cases hRu : (Internal.walkDescendM (SysBridge.mkRawDirOpsM files nextNonce) rootDh parSegs
                (fun parDh => (SysBridge.mkRawDirOpsM files nextNonce).unlinkAt parDh leaf true) s2) with
            | mk uRes s3 =>
              have hRu' : Internal.walkDescendAuxM (SysBridge.mkRawDirOpsM files nextNonce) true rootDh parSegs
                  (fun parDh => (SysBridge.mkRawDirOpsM files nextNonce).unlinkAt parDh leaf true) s2 = (uRes, s3) := hRu
              rw [StateT.run] at hUn; rw [hRu'] at hUn; simp only [↓reduceIte] at hUn
              obtain ⟨hWf3, hTmp3, tr3, hSt3, hConf3, hOut3⟩ := hUn
              dsimp only; rw [hRu]; dsimp only
              refine ⟨hWf3, by omega, (tr1 ++ tr2) ++ tr3,
                healthyFilesSteps_append (healthyFilesSteps_append hSt1 hSt2) hSt3,
                traceFds_append (traceFds_append hOut1.1 hFd2) (by cases uRes <;> exact hOut3.1),
                confined_append (confined_append hConf1 hConf2) hConf3, ?_⟩
              cases uRes with
              | error e => exact hOut3.2
              | ok u2 =>
                cases u2
                obtain ⟨_, d, sub, ⟨pre, post, rfl⟩, hUnT⟩ := hOut3
                exact ⟨d, by simp [UnlinkTrace] at hUnT ⊢; simp [hUnT]⟩

end LeanSwe.Fs.Proofs
