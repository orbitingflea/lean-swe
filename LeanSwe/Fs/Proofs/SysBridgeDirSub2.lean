import LeanSwe.Fs.Proofs.SysBridgeDirSubMkdir

namespace LeanSwe.Fs.Proofs

open LeanSwe.LinuxSyscall
open LeanSwe.LinuxSyscall.Files
open LeanSwe.Fs
open LeanSwe.Fs.Model

/-- Confined step refinement for `SubtreeOpReq.unlink`. -/
theorem subtree_unlink_step {W fd : Type} {proj : W → FsWorld} {hidOf : fd → HandleId}
    {files : FilesOpsM (StateM W) fd} {nextNonce : StateM W Nat}
    (hCap : RefinesFsFilesFixed proj hidOf files nextNonce)
    (rootPath : String) (rel : RelPath) (missingOk : Bool) {s : W} (hWf : fsWorldWf (proj s) = true) :
    let r := (execSubtreeStep (Internal.mkSubtreeOpenerM (SysBridge.mkRawDirOpsM files nextNonce)) ⟨rootPath, .unlink rel missingOk⟩).run s
    allowedSubtreeStep (proj s) ⟨rootPath, .unlink rel missingOk⟩ r.1 (proj r.2) := by
  simp only [execSubtreeStep, Internal.mkSubtreeOpenerM, Functor.map, StateT.map, StateT.run]
  have hW := withSubtreeM_trace hCap rootPath
    (fun _ _ trInner =>
      ∃ pre leaf, splitLastAux rel.segments [] = some (pre, leaf) ∧
        ((∃ d, UnlinkTrace (some d) leaf.val.toUTF8 false trInner) ∨
         (missingOk = true ∧ ∃ r, (r, .err Errno.ENOENT) ∈ trInner)))
    (fun e _ _ => nonLockErrOk e)
    (fun _ _ tr1 tr2 h => by
      obtain ⟨pre, leaf, hSp, hCase⟩ := h
      refine ⟨pre, leaf, hSp, ?_⟩
      rcases hCase with ⟨d, hU⟩ | ⟨hM, r, hm⟩
      · exact Or.inl ⟨d, List.mem_append_right tr1 hU⟩
      · exact Or.inr ⟨hM, r, List.mem_append_right tr1 hm⟩)
    (fun _ _ _ _ h => h) (·.unlink rel missingOk)
    (fun dh s0 hW0 => by
      simp only [Internal.subtreeOpsM]
      cases hSp : splitLastAux rel.segments [] with
      | none =>
        simp only [Pure.pure, StateT.pure, StateT.run]
        exact ⟨hW0, Nat.le_refl _, [], HealthyFilesSteps.nil _, TraceFds.nil _, confined_nil, ⟨by simp, by intro h; cases h⟩⟩
      | some pair =>
        have hD := walkDescendAuxM_trace hCap (fun _ => (none : Option fd))
          (fun parDh _ tr => UnlinkTrace (some parDh) pair.2.val.toUTF8 false tr)
          (fun e tr => nonLockErrOk e ∧ (e.kind = .notFound → ∃ r, (r, .err Errno.ENOENT) ∈ tr))
          (fun e sub tr hSub h => by
            obtain ⟨pre, post, rfl⟩ := hSub
            exact ⟨h.1, fun hNf => let ⟨r, hm⟩ := h.2 hNf; ⟨r, by simp [hm]⟩⟩)
          (fun _ _ hNl hNf => ⟨hNl, hNf⟩)
          (fun parDh => (SysBridge.mkRawDirOpsM files nextNonce).unlinkAt parDh pair.2 false)
          (fun parDh held sX hWX => by
            have hU := dirOps_unlinkAt_trace hCap parDh pair.2 false held hWX
            cases hRu : ((SysBridge.mkRawDirOpsM files nextNonce).unlinkAt parDh pair.2 false sX) with
            | mk rU sY =>
              simp only [StateT.run, hRu] at hU ⊢
              obtain ⟨hWfY, hTmpY, tr, hSt, hFd, hConf, hOut⟩ := hU
              exact ⟨hWfY, by omega, tr, hSt, hConf, by cases rU with | ok u => cases u; exact ⟨hFd, hOut⟩ | error e => exact ⟨hFd, hOut⟩⟩)
          true dh [hidOf dh] pair.1 hW0
        cases hRd : (Internal.walkDescendM (SysBridge.mkRawDirOpsM files nextNonce) dh pair.1
            (fun parDh => (SysBridge.mkRawDirOpsM files nextNonce).unlinkAt parDh pair.2 false) s0) with
        | mk res s1 =>
          have hRd' : Internal.walkDescendAuxM (SysBridge.mkRawDirOpsM files nextNonce) true dh pair.1
              (fun parDh => (SysBridge.mkRawDirOpsM files nextNonce).unlinkAt parDh pair.2 false) s0 = (res, s1) := hRd
          rw [StateT.run] at hD; rw [hRd'] at hD; simp only [↓reduceIte] at hD
          obtain ⟨hWf1, hTmp1, tr, hSt, hConf, hOut⟩ := hD
          simp only [Bind.bind, StateT.bind, StateT.run, hRd]
          cases res with
          | ok u =>
            cases u; simp only [Pure.pure, StateT.pure]
            obtain ⟨hFd, d, sub, ⟨pre, post, rfl⟩, hU⟩ := hOut
            exact ⟨hWf1, hTmp1, _, hSt, hFd, hConf, pair.1, pair.2, rfl, Or.inl ⟨d, by simp [UnlinkTrace] at hU ⊢; simp [hU]⟩⟩
          | error e =>
            obtain ⟨hFd, hNl, hNf⟩ := hOut
            by_cases hM : (e.kind == .notFound && missingOk) = true
            · have hAnd := (Bool.and_eq_true _ _).mp hM
              have hNfEq : e.kind = .notFound := (fsErrorKind_beq_iff_eq _ _).mp hAnd.1
              simp only [hM, ↓reduceIte, Pure.pure, StateT.pure]
              exact ⟨hWf1, hTmp1, tr, hSt, hFd, hConf, pair.1, pair.2, rfl, Or.inr ⟨hAnd.2, hNf hNfEq⟩⟩
            · simp only [hM, Bool.false_eq_true, ↓reduceIte, Pure.pure, StateT.pure]
              exact ⟨hWf1, hTmp1, tr, hSt, hFd, hConf, hNl⟩)
    hWf
  cases hRw : (Internal.withSubtreeM (SysBridge.mkRawDirOpsM files nextNonce) rootPath (·.unlink rel missingOk) s) with
  | mk res s1 =>
    rw [StateT.run] at hW; rw [hRw] at hW; dsimp only at hW
    obtain ⟨tr, hTr, hOut⟩ := hW
    simp only [Bind.bind, Pure.pure, allowedSubtreeStep]
    exact ⟨tr, hTr, by cases res with | ok u => cases u; exact hOut | error e => exact nonLockErr_to_subtreeErr hOut⟩

/-- Confined step refinement for `SubtreeOpReq.rmdir`. -/
theorem subtree_rmdir_step {W fd : Type} {proj : W → FsWorld} {hidOf : fd → HandleId}
    {files : FilesOpsM (StateM W) fd} {nextNonce : StateM W Nat}
    (hCap : RefinesFsFilesFixed proj hidOf files nextNonce)
    (rootPath : String) (rel : RelPath) {s : W} (hWf : fsWorldWf (proj s) = true) :
    let r := (execSubtreeStep (Internal.mkSubtreeOpenerM (SysBridge.mkRawDirOpsM files nextNonce)) ⟨rootPath, .rmdir rel⟩).run s
    allowedSubtreeStep (proj s) ⟨rootPath, .rmdir rel⟩ r.1 (proj r.2) := by
  simp only [execSubtreeStep, Internal.mkSubtreeOpenerM, Functor.map, StateT.map, StateT.run]
  have hW := withSubtreeM_trace hCap rootPath
    (fun _ _ trInner =>
      ∃ pre leaf d, splitLastAux rel.segments [] = some (pre, leaf) ∧
        UnlinkTrace (some d) leaf.val.toUTF8 true trInner)
    (fun e _ _ => nonLockErrOk e)
    (fun _ _ tr1 tr2 ⟨pre, leaf, d, hSp, hU⟩ => ⟨pre, leaf, d, hSp, List.mem_append_right _ hU⟩)
    (fun _ _ _ _ h => h) (·.rmdir rel)
    (fun dh s0 hW0 => by
      simp only [Internal.subtreeOpsM]
      cases hSp : splitLastAux rel.segments [] with
      | none =>
        simp only [Pure.pure, StateT.pure, StateT.run]
        exact ⟨hW0, Nat.le_refl _, [], HealthyFilesSteps.nil _, TraceFds.nil _, confined_nil, ⟨by simp, by intro h; cases h⟩⟩
      | some pair =>
        have hD := walkDescendAuxM_trace hCap (fun _ => (none : Option fd))
          (fun parDh _ tr => UnlinkTrace (some parDh) pair.2.val.toUTF8 true tr)
          (fun e _ => nonLockErrOk e) (fun _ _ _ _ h => h) (fun _ _ h _ => h)
          (fun parDh => (SysBridge.mkRawDirOpsM files nextNonce).unlinkAt parDh pair.2 true)
          (fun parDh held sX hWX => by
            have hU := dirOps_unlinkAt_trace hCap parDh pair.2 true held hWX
            cases hRu : ((SysBridge.mkRawDirOpsM files nextNonce).unlinkAt parDh pair.2 true sX) with
            | mk rU sY =>
              simp only [StateT.run, hRu] at hU ⊢
              obtain ⟨hWfY, hTmpY, tr, hSt, hFd, hConf, hOut⟩ := hU
              exact ⟨hWfY, by omega, tr, hSt, hConf, by cases rU with | ok u => cases u; exact ⟨hFd, hOut⟩ | error e => exact ⟨hFd, hOut.1⟩⟩)
          true dh [hidOf dh] pair.1 hW0
        cases hRd : (Internal.walkDescendM (SysBridge.mkRawDirOpsM files nextNonce) dh pair.1
            (fun parDh => (SysBridge.mkRawDirOpsM files nextNonce).unlinkAt parDh pair.2 true) s0) with
        | mk res s1 =>
          have hRd' : Internal.walkDescendAuxM (SysBridge.mkRawDirOpsM files nextNonce) true dh pair.1
              (fun parDh => (SysBridge.mkRawDirOpsM files nextNonce).unlinkAt parDh pair.2 true) s0 = (res, s1) := hRd
          rw [StateT.run] at hD; rw [hRd'] at hD; simp only [↓reduceIte] at hD
          obtain ⟨hWf1, hTmp1, tr, hSt, hConf, hOut⟩ := hD
          simp only [StateT.run, hRd]
          refine ⟨hWf1, hTmp1, tr, hSt, by cases res <;> exact hOut.1, hConf, ?_⟩
          cases res with
          | error e => exact hOut.2
          | ok u =>
            cases u; obtain ⟨_, d, sub, ⟨pre, post, rfl⟩, hU⟩ := hOut
            exact ⟨pair.1, pair.2, d, rfl, by simp [UnlinkTrace] at hU ⊢; simp [hU]⟩)
    hWf
  cases hRw : (Internal.withSubtreeM (SysBridge.mkRawDirOpsM files nextNonce) rootPath (·.rmdir rel) s) with
  | mk res s1 =>
    rw [StateT.run] at hW; rw [hRw] at hW; dsimp only at hW
    obtain ⟨tr, hTr, hOut⟩ := hW
    simp only [Bind.bind, Pure.pure, allowedSubtreeStep]
    exact ⟨tr, hTr, by cases res with | ok u => cases u; exact hOut | error e => exact nonLockErr_to_subtreeErr hOut⟩

/-- Confined step refinement for `SubtreeOpReq.rmtree`. -/
theorem subtree_rmtree_step {W fd : Type} {proj : W → FsWorld} {hidOf : fd → HandleId}
    {files : FilesOpsM (StateM W) fd} {nextNonce : StateM W Nat}
    (hCap : RefinesFsFilesFixed proj hidOf files nextNonce)
    (rootPath : String) (rel : RelPath) (ignoreMissing : Bool) {s : W} (hWf : fsWorldWf (proj s) = true) :
    let r := (execSubtreeStep (Internal.mkSubtreeOpenerM (SysBridge.mkRawDirOpsM files nextNonce)) ⟨rootPath, .rmtree rel ignoreMissing⟩).run s
    allowedSubtreeStep (proj s) ⟨rootPath, .rmtree rel ignoreMissing⟩ r.1 (proj r.2) := by
  simp only [execSubtreeStep, Internal.mkSubtreeOpenerM, Functor.map, StateT.map, StateT.run]
  have hW := withSubtreeM_trace hCap rootPath
    (fun _ _ trInner =>
      ∃ pre leaf, splitLastAux rel.segments [] = some (pre, leaf) ∧
        ((∃ d, UnlinkTrace (some d) leaf.val.toUTF8 true trInner) ∨
         (ignoreMissing = true ∧ ∃ r, (r, .err Errno.ENOENT) ∈ trInner)))
    (fun e _ _ => nonLockErrOk e)
    (fun _ _ tr1 tr2 h => by
      obtain ⟨pre, leaf, hSp, hCase⟩ := h
      refine ⟨pre, leaf, hSp, ?_⟩
      rcases hCase with ⟨d, hU⟩ | ⟨hM, r, hm⟩
      · exact Or.inl ⟨d, List.mem_append_right tr1 hU⟩
      · exact Or.inr ⟨hM, r, List.mem_append_right tr1 hm⟩)
    (fun _ _ _ _ h => h) (·.rmtree rel ignoreMissing)
    (fun dh s0 hW0 => by
      simp only [Internal.subtreeOpsM]
      cases hSp : splitLastAux rel.segments [] with
      | none =>
        simp only [Pure.pure, StateT.pure, StateT.run]
        exact ⟨hW0, Nat.le_refl _, [], HealthyFilesSteps.nil _, TraceFds.nil _, confined_nil, ⟨by simp, by intro h; cases h⟩⟩
      | some pair =>
        have hD := walkDescendAuxM_trace hCap (fun _ => (none : Option fd)) (fun _ _ _ => True)
          (fun e tr => nonLockErrOk e ∧ (e.kind = .notFound → ∃ r, (r, .err Errno.ENOENT) ∈ tr))
          (fun e sub tr hSub h => by
            obtain ⟨pre, post, rfl⟩ := hSub
            exact ⟨h.1, fun hNf => let ⟨r, hm⟩ := h.2 hNf; ⟨r, by simp [hm]⟩⟩)
          (fun _ _ hNl hNf => ⟨hNl, hNf⟩)
          (fun parDh => (SysBridge.mkRawDirOpsM files nextNonce).lstatAt parDh pair.2)
          (fun parDh held sX hWX => by
            have hL := dirOps_lstatAt_trace hCap parDh pair.2 held hWX
            cases hRl : ((SysBridge.mkRawDirOpsM files nextNonce).lstatAt parDh pair.2 sX) with
            | mk rL sY =>
              simp only [StateT.run, hRl] at hL ⊢
              obtain ⟨hWfY, hTmpY, tr, hSt, hFd, hConf, hOut⟩ := hL
              exact ⟨hWfY, by omega, tr, hSt, hConf, by cases rL with | ok _ => exact ⟨hFd, trivial⟩ | error e => exact ⟨hFd, hOut⟩⟩)
          true dh [hidOf dh] pair.1 hW0
        cases hRd : (Internal.walkDescendM (SysBridge.mkRawDirOpsM files nextNonce) dh pair.1
            (fun parDh => (SysBridge.mkRawDirOpsM files nextNonce).lstatAt parDh pair.2) s0) with
        | mk res s1 =>
          have hRd' : Internal.walkDescendAuxM (SysBridge.mkRawDirOpsM files nextNonce) true dh pair.1
              (fun parDh => (SysBridge.mkRawDirOpsM files nextNonce).lstatAt parDh pair.2) s0 = (res, s1) := hRd
          rw [StateT.run] at hD; rw [hRd'] at hD; simp only [↓reduceIte] at hD
          obtain ⟨hWf1, hTmp1, tr1, hSt1, hConf1, hOut1⟩ := hD
          simp only [Bind.bind, StateT.bind, StateT.run, hRd]
          cases res with
          | error e =>
            obtain ⟨hFd1, hNl, hNf⟩ := hOut1
            by_cases hM : (e.kind == .notFound && ignoreMissing) = true
            · have hAnd := (Bool.and_eq_true _ _).mp hM
              have hNfEq : e.kind = .notFound := (fsErrorKind_beq_iff_eq _ _).mp hAnd.1
              simp only [hM, ↓reduceIte, Pure.pure, StateT.pure]
              exact ⟨hWf1, hTmp1, tr1, hSt1, hFd1, hConf1, pair.1, pair.2, rfl, Or.inr ⟨hAnd.2, hNf hNfEq⟩⟩
            · simp only [hM, Bool.false_eq_true, ↓reduceIte, Pure.pure, StateT.pure]
              exact ⟨hWf1, hTmp1, tr1, hSt1, hFd1, hConf1, hNl⟩
          | ok info =>
            by_cases hNd : (info.kind != .dir) = true
            · simp only [hNd, ↓reduceIte, Pure.pure, StateT.pure]
              exact ⟨hWf1, hTmp1, tr1, hSt1, hOut1.1, hConf1, ⟨nonEmpty_append_left (by decide), by intro h; cases h⟩⟩
            · simp only [hNd, Bool.false_eq_true, ↓reduceIte]
              have hRm := rmtreeDirAtM_trace hCap dh 4096 pair.1 pair.2 s1 hWf1
              cases hRr : (Internal.rmtreeDirAtM (SysBridge.mkRawDirOpsM files nextNonce) dh pair.1 pair.2 4096 s1) with
              | mk r2 s2 =>
                simp only [StateT.run, hRr] at hRm ⊢
                obtain ⟨hWf2, hTmp2, tr2, hSt2, hFd2, hConf2, hOut2⟩ := hRm
                refine ⟨hWf2, by omega, tr1 ++ tr2, healthyFilesSteps_append hSt1 hSt2,
                  traceFds_append hOut1.1 hFd2, confined_append hConf1 hConf2, ?_⟩
                cases r2 with
                | error e => exact hOut2
                | ok u => cases u; obtain ⟨d, hU⟩ := hOut2; exact ⟨pair.1, pair.2, rfl, Or.inl ⟨d, List.mem_append_right _ hU⟩⟩)
    hWf
  cases hRw : (Internal.withSubtreeM (SysBridge.mkRawDirOpsM files nextNonce) rootPath (·.rmtree rel ignoreMissing) s) with
  | mk res s1 =>
    rw [StateT.run] at hW; rw [hRw] at hW; dsimp only at hW
    obtain ⟨tr, hTr, hOut⟩ := hW
    simp only [Bind.bind, Pure.pure, allowedSubtreeStep]
    exact ⟨tr, hTr, by cases res with | ok u => cases u; exact hOut | error e => exact nonLockErr_to_subtreeErr hOut⟩

/-- Confined step refinement for `SubtreeOpReq.symlink`. -/
theorem subtree_symlink_step {W fd : Type} {proj : W → FsWorld} {hidOf : fd → HandleId}
    {files : FilesOpsM (StateM W) fd} {nextNonce : StateM W Nat}
    (hCap : RefinesFsFilesFixed proj hidOf files nextNonce)
    (rootPath target : String) (rel : RelPath) {s : W} (hWf : fsWorldWf (proj s) = true) :
    let r := (execSubtreeStep (Internal.mkSubtreeOpenerM (SysBridge.mkRawDirOpsM files nextNonce)) ⟨rootPath, .symlink target rel⟩).run s
    allowedSubtreeStep (proj s) ⟨rootPath, .symlink target rel⟩ r.1 (proj r.2) := by
  simp only [execSubtreeStep, Internal.mkSubtreeOpenerM, Functor.map, StateT.map, StateT.run]
  have hW := withSubtreeM_trace hCap rootPath
    (fun _ _ trInner =>
      ∃ pre leaf d, splitLastAux rel.segments [] = some (pre, leaf) ∧
        SymlinkTrace target.toUTF8 (some d) leaf.val.toUTF8 trInner)
    (fun e _ _ => nonLockErrOk e)
    (fun _ _ tr1 tr2 ⟨pre, leaf, d, hSp, hSy⟩ => ⟨pre, leaf, d, hSp, List.mem_append_right _ hSy⟩)
    (fun _ _ _ _ h => h) (·.symlink target rel)
    (fun dh s0 hW0 => by
      simp only [Internal.subtreeOpsM]
      cases hSp : splitLastAux rel.segments [] with
      | none =>
        simp only [Pure.pure, StateT.pure, StateT.run]
        exact ⟨hW0, Nat.le_refl _, [], HealthyFilesSteps.nil _, TraceFds.nil _, confined_nil, ⟨by simp, by intro h; cases h⟩⟩
      | some pair =>
        by_cases hBad : (target.isEmpty || decide (Char.ofNat 0 ∈ target.toList)) = true
        · simp only [hBad, ↓reduceIte, Pure.pure, StateT.pure, StateT.run]
          exact ⟨hW0, Nat.le_refl _, [], HealthyFilesSteps.nil _, TraceFds.nil _, confined_nil, ⟨by simp, by intro h; cases h⟩⟩
        · simp only [hBad, Bool.false_eq_true, ↓reduceIte]
          have hD := walkDescendAuxM_trace hCap (fun _ => (none : Option fd))
            (fun parDh _ tr => SymlinkTrace target.toUTF8 (some parDh) pair.2.val.toUTF8 tr)
            (fun e _ => nonLockErrOk e) (fun _ _ _ _ h => h) (fun _ _ h _ => h)
            (fun parDh => (SysBridge.mkRawDirOpsM files nextNonce).symlinkAt target parDh pair.2)
            (fun parDh held sX hWX => by
              have hS := dirOps_symlinkAt_trace hCap target parDh pair.2 held hWX
              cases hRs : ((SysBridge.mkRawDirOpsM files nextNonce).symlinkAt target parDh pair.2 sX) with
              | mk rS sY =>
                simp only [StateT.run, hRs] at hS ⊢
                obtain ⟨hWfY, hTmpY, tr, hSt, hFd, hConf, hOut⟩ := hS
                exact ⟨hWfY, by omega, tr, hSt, hConf, by cases rS with | ok u => cases u; exact ⟨hFd, hOut⟩ | error e => exact ⟨hFd, hOut⟩⟩)
            true dh [hidOf dh] pair.1 hW0
          cases hRd : (Internal.walkDescendM (SysBridge.mkRawDirOpsM files nextNonce) dh pair.1
              (fun parDh => (SysBridge.mkRawDirOpsM files nextNonce).symlinkAt target parDh pair.2) s0) with
          | mk res s1 =>
            have hRd' : Internal.walkDescendAuxM (SysBridge.mkRawDirOpsM files nextNonce) true dh pair.1
                (fun parDh => (SysBridge.mkRawDirOpsM files nextNonce).symlinkAt target parDh pair.2) s0 = (res, s1) := hRd
            rw [StateT.run] at hD; rw [hRd'] at hD; simp only [↓reduceIte] at hD
            obtain ⟨hWf1, hTmp1, tr, hSt, hConf, hOut⟩ := hD
            simp only [StateT.run, hRd]
            refine ⟨hWf1, hTmp1, tr, hSt, by cases res <;> exact hOut.1, hConf, ?_⟩
            cases res with
            | error e => exact hOut.2
            | ok u =>
              cases u; obtain ⟨_, d, sub, ⟨pre, post, rfl⟩, hSy⟩ := hOut
              exact ⟨pair.1, pair.2, d, rfl, List.mem_append_left _ (List.mem_append_right _ hSy)⟩)
    hWf
  cases hRw : (Internal.withSubtreeM (SysBridge.mkRawDirOpsM files nextNonce) rootPath (·.symlink target rel) s) with
  | mk res s1 =>
    rw [StateT.run] at hW; rw [hRw] at hW; dsimp only at hW
    obtain ⟨tr, hTr, hOut⟩ := hW
    simp only [Bind.bind, Pure.pure, allowedSubtreeStep]
    exact ⟨tr, hTr, by cases res with | ok u => cases u; exact hOut | error e => exact nonLockErr_to_subtreeErr hOut⟩

/-- Confined step refinement for `SubtreeOpReq.listDir`. -/
theorem subtree_listDir_step {W fd : Type} {proj : W → FsWorld} {hidOf : fd → HandleId}
    {files : FilesOpsM (StateM W) fd} {nextNonce : StateM W Nat}
    (hCap : RefinesFsFilesFixed proj hidOf files nextNonce)
    (rootPath : String) (rel : RelPath) {s : W} (hWf : fsWorldWf (proj s) = true) :
    let r := (execSubtreeStep (Internal.mkSubtreeOpenerM (SysBridge.mkRawDirOpsM files nextNonce)) ⟨rootPath, .listDir rel⟩).run s
    allowedSubtreeStep (proj s) ⟨rootPath, .listDir rel⟩ r.1 (proj r.2) := by
  simp only [execSubtreeStep, Internal.mkSubtreeOpenerM, Functor.map, StateT.map, StateT.run]
  have hW := withSubtreeM_trace hCap rootPath
    (fun xs _ trInner =>
      List.Pairwise (fun a b => a.val ≤ b.val) xs.toList ∧
      ∃ h eof, (.getdents64 h 8192, .bytes eof) ∈ trInner ∧ eof.size = 0 ∧
        (xs.size > 0 → ∃ buf, (.getdents64 h 8192, .bytes buf) ∈ trInner ∧ buf.size > 0))
    (fun e _ _ => nonLockErrOk e)
    (fun xs _ tr1 tr2 ⟨hPw, h, eof, hMemE, hEz, hPos⟩ =>
      ⟨hPw, h, eof, List.mem_append_right _ hMemE, hEz,
        fun hGt => let ⟨b, hm, hp⟩ := hPos hGt; ⟨b, List.mem_append_right _ hm, hp⟩⟩)
    (fun _ _ _ _ h => h) (·.listDir rel)
    (fun dh s0 hW0 => by
      simp only [Internal.subtreeOpsM]
      let readSort : fd → StateM W (Except FsError (Array EntryName)) := fun dirDh => do
        match ← (SysBridge.mkRawDirOpsM files nextNonce).readDirAt dirDh with
        | .error e => pure (.error e)
        | .ok names => pure (.ok (Internal.sortEntryNames names).toArray)
      have hD := walkDescendAuxM_trace hCap (fun _ => (none : Option fd))
        (fun _ xs tr =>
          List.Pairwise (fun a b => a.val ≤ b.val) xs.toList ∧
          ∃ h eof, (.getdents64 h 8192, .bytes eof) ∈ tr ∧ eof.size = 0 ∧
            (xs.size > 0 → ∃ buf, (.getdents64 h 8192, .bytes buf) ∈ tr ∧ buf.size > 0))
        (fun e _ => nonLockErrOk e) (fun _ _ _ _ h => h) (fun _ _ h _ => h) readSort
        (fun dirDh held sX hWX => by
          dsimp only [readSort]
          have hR := readDirAtPure_trace hCap dirDh held DEFAULT_EINTR_FUEL SysBridge.DEFAULT_STREAM_FUEL hWX
          cases hRo : (SysBridge.readDirAtPure files dirDh DEFAULT_EINTR_FUEL SysBridge.DEFAULT_STREAM_FUEL sX) with
          | mk rR sY =>
            rw [StateT.run] at hR; rw [hRo] at hR; dsimp only at hR
            obtain ⟨hWfY, hTmpY, tr, hSt, hFd, hConf, hOut⟩ := hR
            have hRo' : (SysBridge.mkRawDirOpsM files nextNonce).readDirAt dirDh sX = (rR, sY) := hRo
            simp only [Bind.bind, StateT.bind, StateT.run, hRo']
            cases rR with
            | error e => simp only [Pure.pure, StateT.pure]; exact ⟨hWfY, by omega, tr, hSt, hConf, hFd, hOut⟩
            | ok names =>
              simp only [Pure.pure, StateT.pure]
              obtain ⟨h, eof, hMemE, hEz, hPos⟩ := hOut
              refine ⟨hWfY, by omega, tr, hSt, hConf, hFd, ?_, h, eof, hMemE, hEz, fun hGt => hPos ?_⟩
              · simpa using sortEntryNames_pairwise names
              · have hLen := sortEntryNames_length names
                simp only [List.size_toArray] at hGt
                omega)
        true dh [hidOf dh] rel.segments hW0
      refine subAct_subst
        (r2 := ((Internal.walkDescendM (SysBridge.mkRawDirOpsM files nextNonce) dh rel.segments readSort).run s0).1)
        (s2 := ((Internal.walkDescendM (SysBridge.mkRawDirOpsM files nextNonce) dh rel.segments readSort).run s0).2) ?_ ?_
      · exact congrArg (fun f => (Internal.walkDescendM (SysBridge.mkRawDirOpsM files nextNonce) dh rel.segments f).run s0)
          (funext fun dirDh => funext fun sX => by
            simp only [readSort, Bind.bind, StateT.bind]
            cases (SysBridge.mkRawDirOpsM files nextNonce).readDirAt dirDh sX with
            | mk r0 _ => cases r0 <;> rfl)
      · cases hRd : (Internal.walkDescendM (SysBridge.mkRawDirOpsM files nextNonce) dh rel.segments readSort s0) with
        | mk res s1 =>
          have hRd' : Internal.walkDescendAuxM (SysBridge.mkRawDirOpsM files nextNonce) true dh rel.segments readSort s0 = (res, s1) := hRd
          rw [StateT.run] at hD; rw [hRd'] at hD; simp only [↓reduceIte] at hD
          obtain ⟨hWf1, hTmp1, tr, hSt, hConf, hOut⟩ := hD
          simp only [StateT.run, hRd]
          refine ⟨hWf1, hTmp1, tr, hSt, by cases res <;> exact hOut.1, hConf, ?_⟩
          cases res with
          | error e => exact hOut.2
          | ok xs =>
            obtain ⟨_, _, sub, ⟨pre, post, rfl⟩, hPw, h, eof, hMemE, hEz, hPos⟩ := hOut
            exact ⟨hPw, h, eof, List.mem_append_left _ (List.mem_append_right _ hMemE), hEz,
              fun hGt => let ⟨b, hm, hp⟩ := hPos hGt; ⟨b, List.mem_append_left _ (List.mem_append_right _ hm), hp⟩⟩)
    hWf
  cases hRw : (Internal.withSubtreeM (SysBridge.mkRawDirOpsM files nextNonce) rootPath (·.listDir rel) s) with
  | mk res s1 =>
    rw [StateT.run] at hW; rw [hRw] at hW; dsimp only at hW
    obtain ⟨tr, hTr, hOut⟩ := hW
    simp only [Bind.bind, Pure.pure, allowedSubtreeStep]
    cases res with
    | error e => exact ⟨tr, hTr, nonLockErr_to_subtreeErr hOut⟩
    | ok xs =>
      obtain ⟨dh, trO, trI, trC, hEq, hMemO, hAllO, hFdI, hConfI, hC, hPw, hGd⟩ := hOut
      exact ⟨tr, hTr, hPw, dh, trO, trI, trC, hEq, hMemO, hAllO, hFdI, hConfI, hC, hGd⟩

/-- Confined step refinement for `SubtreeOpReq.walk`. -/
theorem subtree_walk_step {W fd : Type} {proj : W → FsWorld} {hidOf : fd → HandleId}
    {files : FilesOpsM (StateM W) fd} {nextNonce : StateM W Nat}
    (hCap : RefinesFsFilesFixed proj hidOf files nextNonce)
    (rootPath : String) (rel : RelPath) {s : W} (hWf : fsWorldWf (proj s) = true) :
    let r := (execSubtreeStep (Internal.mkSubtreeOpenerM (SysBridge.mkRawDirOpsM files nextNonce)) ⟨rootPath, .walk rel⟩).run s
    allowedSubtreeStep (proj s) ⟨rootPath, .walk rel⟩ r.1 (proj r.2) := by
  simp only [execSubtreeStep, Internal.mkSubtreeOpenerM, Functor.map, StateT.map, StateT.run]
  have hW := withSubtreeM_trace hCap rootPath
    (fun entries _ trInner =>
      (∀ e ∈ entries.toList, WalkEntrySorted e) ∧ entries.size > 0 ∧
      ∃ h eof, (.getdents64 h 8192, .bytes eof) ∈ trInner ∧ eof.size = 0)
    (fun e _ _ => nonLockErrOk e)
    (fun entries _ tr1 tr2 ⟨hS, hSz, h, eof, hMemE, hEz⟩ =>
      ⟨hS, hSz, h, eof, List.mem_append_right _ hMemE, hEz⟩)
    (fun _ _ _ _ h => h) (·.walk rel)
    (fun dh s0 hW0 => by
      simp only [Internal.subtreeOpsM]
      have hWr := walkRecM_trace hCap dh 4096 rel.segments "." #[] s0 hW0 (fun _ hm => nomatch hm)
      cases hR : (Internal.walkRecM (SysBridge.mkRawDirOpsM files nextNonce) dh rel.segments "." #[] 4096 s0) with
      | mk res s1 =>
        simp only [StateT.run, hR] at hWr ⊢
        obtain ⟨hWf1, hTmp1, tr, hSt, hFd, hConf, hOut⟩ := hWr
        exact ⟨hWf1, hTmp1, tr, hSt, hFd, hConf, by cases res with | ok es => exact hOut | error e => exact hOut⟩)
    hWf
  cases hRw : (Internal.withSubtreeM (SysBridge.mkRawDirOpsM files nextNonce) rootPath (·.walk rel) s) with
  | mk res s1 =>
    rw [StateT.run] at hW; rw [hRw] at hW; dsimp only at hW
    obtain ⟨tr, hTr, hOut⟩ := hW
    simp only [Bind.bind, Pure.pure, allowedSubtreeStep]
    cases res with
    | error e => exact ⟨tr, hTr, nonLockErr_to_subtreeErr hOut⟩
    | ok es =>
      obtain ⟨dh, trO, trI, trC, hEq, hMemO, hAllO, hFdI, hConfI, hC, hS, hSz, hGd⟩ := hOut
      exact ⟨tr, hTr, hS, hSz, dh, trO, trI, trC, hEq, hMemO, hAllO, hFdI, hConfI, hC, hGd⟩

end LeanSwe.Fs.Proofs
