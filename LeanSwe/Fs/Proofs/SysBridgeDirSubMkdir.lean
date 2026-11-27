import LeanSwe.Fs.Proofs.SysBridgeDirSub1

namespace LeanSwe.Fs.Proofs

open LeanSwe.LinuxSyscall
open LeanSwe.LinuxSyscall.Files
open LeanSwe.Fs
open LeanSwe.Fs.Model

/-- Confined step refinement for `SubtreeOpReq.mkdir`. -/
theorem subtree_mkdir_step {W fd : Type} {proj : W → FsWorld} {hidOf : fd → HandleId}
    {files : FilesOpsM (StateM W) fd} {nextNonce : StateM W Nat}
    (hCap : RefinesFsFilesFixed proj hidOf files nextNonce)
    (rootPath : String) (rel : RelPath) (parents existOk : Bool) {s : W} (hWf : fsWorldWf (proj s) = true) :
    let r := (execSubtreeStep (Internal.mkSubtreeOpenerM (SysBridge.mkRawDirOpsM files nextNonce)) ⟨rootPath, .mkdir rel parents existOk⟩).run s
    allowedSubtreeStep (proj s) ⟨rootPath, .mkdir rel parents existOk⟩ r.1 (proj r.2) := by
  simp only [execSubtreeStep, Internal.mkSubtreeOpenerM, Functor.map, StateT.map, StateT.run]
  have hW := withSubtreeM_trace hCap rootPath
    (fun _ rootDh trInner =>
      match splitLastAux rel.segments [] with
      | none => existOk = true ∧ ∃ rawSt, (.fstat rootDh, .statted rawSt) ∈ trInner ∧ rawSt.kind = .dir
      | some (_, leaf) =>
        ∃ d, MkdirTrace (some d) leaf.val.toUTF8 0o755 trInner ∨
          (existOk = true ∧ ∃ rawSt, (.fstatat (some d) leaf.val.toUTF8 { symlinkNofollow := true }, .statted rawSt) ∈ trInner ∧ rawSt.kind = .dir))
    (fun e _ _ => nonLockErrOk e)
    (fun _ dh tr1 tr2 h => by
      cases hSp : splitLastAux rel.segments [] with
      | none => rw [hSp] at h; exact ⟨h.1, let ⟨rawSt, hm, hd⟩ := h.2; ⟨rawSt, List.mem_append_right _ hm, hd⟩⟩
      | some pair =>
        rw [hSp] at h; obtain ⟨d, hCase⟩ := h; refine ⟨d, ?_⟩
        rcases hCase with hMk | ⟨hEx, rawSt, hm, hd⟩
        · exact Or.inl (List.mem_append_right _ hMk)
        · exact Or.inr ⟨hEx, rawSt, List.mem_append_right _ hm, hd⟩)
    (fun _ _ _ _ h => h) (·.mkdir rel parents existOk)
    (fun dh s0 hW0 => by
      simp only [Internal.subtreeOpsM, internal_splitLastAux_eq_model]
      cases hSp : splitLastAux rel.segments [] with
      | none =>
        have hFs := dirOps_fstatDir_trace hCap dh [hidOf dh] hW0
        cases hR : ((SysBridge.mkRawDirOpsM files nextNonce).fstatDir dh s0) with
        | mk res s1 =>
          rw [StateT.run] at hFs; rw [hR] at hFs; dsimp only at hFs
          obtain ⟨hWf1, hTmp1, tr, hSt, hFd, hConf, hOut⟩ := hFs
          simp only [Bind.bind, StateT.bind, StateT.run, hR]
          cases res with
          | error e => simp only [Pure.pure, StateT.pure]; exact ⟨hWf1, by omega, tr, hSt, hFd, hConf, hOut⟩
          | ok info =>
            by_cases hNd : (info.kind != .dir) = true
            · simp only [hNd, ↓reduceIte, Pure.pure, StateT.pure]; exact ⟨hWf1, by omega, tr, hSt, hFd, hConf, ⟨by simp, by intro h; cases h⟩⟩
            · cases existOk with
              | false => simp only [hNd, Bool.false_eq_true, ↓reduceIte, Pure.pure, StateT.pure]; exact ⟨hWf1, by omega, tr, hSt, hFd, hConf, ⟨by simp, by intro h; cases h⟩⟩
              | true =>
                simp only [hNd, Bool.false_eq_true, ↓reduceIte, Pure.pure, StateT.pure]
                obtain ⟨rawSt, hm, hEqSt⟩ := hOut
                have hKindDir : rawSt.kind = .dir := by
                  have hK : info.kind = .dir := by cases hIk : info.kind <;> rw [hIk] at hNd <;> first | rfl | exact absurd (by decide) hNd
                  rw [hEqSt] at hK; dsimp only [toFileStat] at hK
                  cases hRk : rawSt.kind <;> rw [hRk] at hK <;> first | rfl | cases hK
                exact ⟨hWf1, by omega, tr, hSt, hFd, hConf, trivial, rawSt, hm, hKindDir⟩
      | some pair =>
        let leafAct : fd → StateM W (Except FsError Unit) := fun parDh => do
          match ← (SysBridge.mkRawDirOpsM files nextNonce).createDirAt parDh pair.2 with
          | .ok () => pure (.ok ())
          | .error e =>
            if existOk && (e.kind == .alreadyExists || e.kind == .permissionDenied) then
              match ← (SysBridge.mkRawDirOpsM files nextNonce).lstatAt parDh pair.2 with
              | .error _ => pure (.error e)
              | .ok info =>
                if info.kind == .dir then pure (.ok ())
                else if e.kind == .alreadyExists then pure (.error e)
                else pure (.error { kind := .alreadyExists, path := some pair.2.val, message := s!"already exists: {pair.2.val}" })
            else pure (.error e)
        have hLeaf : ∀ (parDh : fd) (held : List HandleId) {sX : W}, fsWorldWf (proj sX) = true →
            let q := (leafAct parDh).run sX
            fsWorldWf (proj q.2) = true ∧ (proj sX).tempSeq ≤ (proj q.2).tempSeq ∧
            ∃ tr, HealthyFilesSteps (proj sX).env tr (proj q.2).env ∧ TraceFds held tr held ∧
              (∀ step ∈ tr, SubtreeConfinedReq step.1) ∧
              match q.1 with
              | .ok () =>
                MkdirTrace (some (hidOf parDh)) pair.2.val.toUTF8 0o755 tr ∨
                (existOk = true ∧ ∃ rawSt, (.fstatat (some (hidOf parDh)) pair.2.val.toUTF8 { symlinkNofollow := true }, .statted rawSt) ∈ tr ∧ rawSt.kind = .dir)
              | .error e => nonLockErrOk e := by
          intro parDh held sX hWX
          dsimp only [leafAct]
          have hCr := dirOps_createDirAt_trace hCap parDh pair.2 held hWX
          cases hRc : ((SysBridge.mkRawDirOpsM files nextNonce).createDirAt parDh pair.2 sX) with
          | mk cRes s1 =>
            rw [StateT.run] at hCr; rw [hRc] at hCr; dsimp only at hCr
            obtain ⟨hWf1, hTmp1, trC, hStC, hFdC, hConfC, hOutC⟩ := hCr
            simp only [Bind.bind, StateT.bind, StateT.run, hRc]
            cases cRes with
            | ok u => cases u; simp only [Pure.pure, StateT.pure]; exact ⟨hWf1, by omega, trC, hStC, hFdC, hConfC, Or.inl hOutC⟩
            | error e =>
              by_cases hEx : (existOk && (e.kind == .alreadyExists || e.kind == .permissionDenied)) = true
              · have hExT : existOk = true := (Bool.and_eq_true _ _).mp hEx |>.1
                simp only [hEx, ↓reduceIte]
                have hLs := dirOps_lstatAt_trace hCap parDh pair.2 held hWf1
                cases hRl : ((SysBridge.mkRawDirOpsM files nextNonce).lstatAt parDh pair.2 s1) with
                | mk lRes s2 =>
                  rw [StateT.run] at hLs; rw [hRl] at hLs; dsimp only at hLs
                  obtain ⟨hWf2, hTmp2, trL, hStL, hFdL, hConfL, hOutL⟩ := hLs
                  simp only [Bind.bind, StateT.bind, hRl]
                  have hStCL := healthyFilesSteps_append hStC hStL
                  have hFdCL := traceFds_append hFdC hFdL
                  have hConfCL := confined_append hConfC hConfL
                  cases lRes with
                  | error _ => simp only [Pure.pure, StateT.pure]; exact ⟨hWf2, by omega, trC ++ trL, hStCL, hFdCL, hConfCL, hOutC⟩
                  | ok info =>
                    by_cases hDir : (info.kind == .dir) = true
                    · simp only [hDir, ↓reduceIte, Pure.pure, StateT.pure]
                      obtain ⟨rawSt, hm, hEqSt⟩ := hOutL
                      have hKindDir : rawSt.kind = .dir := by
                        have hK : info.kind = .dir := by cases hIk : info.kind <;> rw [hIk] at hDir <;> first | rfl | exact absurd hDir (by decide)
                        rw [hEqSt] at hK; dsimp only [toFileStat] at hK
                        cases hRk : rawSt.kind <;> rw [hRk] at hK <;> first | rfl | cases hK
                      exact ⟨hWf2, by omega, trC ++ trL, hStCL, hFdCL, hConfCL, Or.inr ⟨hExT, rawSt, List.mem_append_right _ hm, hKindDir⟩⟩
                    · by_cases hAe : (e.kind == .alreadyExists) = true
                      · simp only [hDir, Bool.false_eq_true, ↓reduceIte, hAe, Pure.pure, StateT.pure]
                        exact ⟨hWf2, by omega, trC ++ trL, hStCL, hFdCL, hConfCL, hOutC⟩
                      · simp only [hDir, Bool.false_eq_true, ↓reduceIte, hAe, Pure.pure, StateT.pure]
                        exact ⟨hWf2, by omega, trC ++ trL, hStCL, hFdCL, hConfCL, ⟨nonEmpty_append_left (by decide), by intro h; cases h⟩⟩
              · simp only [hEx, Bool.false_eq_true, ↓reduceIte, Pure.pure, StateT.pure]
                exact ⟨hWf1, by omega, trC, hStC, hFdC, hConfC, hOutC⟩
        cases parents with
        | true =>
          simp only [↓reduceIte]
          refine subAct_subst
            (r2 := ((Internal.mkdirWalkM (SysBridge.mkRawDirOpsM files nextNonce) true dh pair.1 leafAct).run s0).1)
            (s2 := ((Internal.mkdirWalkM (SysBridge.mkRawDirOpsM files nextNonce) true dh pair.1 leafAct).run s0).2) ?_ ?_
          · exact congrArg (fun f => (Internal.mkdirWalkM (SysBridge.mkRawDirOpsM files nextNonce) true dh pair.1 f).run s0)
              (funext fun parDh => funext fun sX => by
                simp only [leafAct, Bind.bind, StateT.bind]
                cases (SysBridge.mkRawDirOpsM files nextNonce).createDirAt parDh pair.2 sX with
                | mk r0 sA =>
                  cases r0 with
                  | ok u => cases u; rfl
                  | error e =>
                    by_cases hEx : (existOk && (e.kind == .alreadyExists || e.kind == .permissionDenied)) = true
                    · simp only [hEx, ↓reduceIte]
                      cases (SysBridge.mkRawDirOpsM files nextNonce).lstatAt parDh pair.2 sA with
                      | mk r1 _ => cases r1 with | error _ => rfl | ok _ => rfl
                    · simp only [hEx, Bool.false_eq_true, ↓reduceIte])
          · have hMw := mkdirWalkM_trace hCap
              (fun parDh tr => MkdirTrace (some parDh) pair.2.val.toUTF8 0o755 tr ∨
                (existOk = true ∧ ∃ rawSt, (.fstatat (some parDh) pair.2.val.toUTF8 { symlinkNofollow := true }, .statted rawSt) ∈ tr ∧ rawSt.kind = .dir))
              leafAct hLeaf true dh [hidOf dh] pair.1 hW0
            cases hRm : (Internal.mkdirWalkM (SysBridge.mkRawDirOpsM files nextNonce) true dh pair.1 leafAct s0) with
            | mk res s1 =>
              simp only [StateT.run, hRm, ↓reduceIte] at hMw ⊢
              obtain ⟨hWf1, hTmp1, tr, hSt, hFd, hConf, hOut⟩ := hMw
              refine ⟨hWf1, hTmp1, tr, hSt, hFd, hConf, ?_⟩
              cases res with
              | error e => exact hOut
              | ok u =>
                cases u; obtain ⟨d, sub, ⟨pre, post, rfl⟩, hCase⟩ := hOut; refine ⟨d, ?_⟩
                rcases hCase with hMk | ⟨hEx, rawSt, hm, hd⟩
                · exact Or.inl (List.mem_append_left _ (List.mem_append_right _ hMk))
                · exact Or.inr ⟨hEx, rawSt, List.mem_append_left _ (List.mem_append_right _ hm), hd⟩
        | false =>
          simp only [Bool.false_eq_true, ↓reduceIte]
          refine subAct_subst
            (r2 := ((Internal.walkDescendM (SysBridge.mkRawDirOpsM files nextNonce) dh pair.1 leafAct).run s0).1)
            (s2 := ((Internal.walkDescendM (SysBridge.mkRawDirOpsM files nextNonce) dh pair.1 leafAct).run s0).2) ?_ ?_
          · exact congrArg (fun f => (Internal.walkDescendM (SysBridge.mkRawDirOpsM files nextNonce) dh pair.1 f).run s0)
              (funext fun parDh => funext fun sX => by
                simp only [leafAct, Bind.bind, StateT.bind]
                cases (SysBridge.mkRawDirOpsM files nextNonce).createDirAt parDh pair.2 sX with
                | mk r0 sA =>
                  cases r0 with
                  | ok u => cases u; rfl
                  | error e =>
                    by_cases hEx : (existOk && (e.kind == .alreadyExists || e.kind == .permissionDenied)) = true
                    · simp only [hEx, ↓reduceIte]
                      cases (SysBridge.mkRawDirOpsM files nextNonce).lstatAt parDh pair.2 sA with
                      | mk r1 _ => cases r1 with | error _ => rfl | ok _ => rfl
                    · simp only [hEx, Bool.false_eq_true, ↓reduceIte])
          · have hWd := walkDescendAuxM_trace hCap (fun _ => (none : Option fd))
              (fun parDh _ tr => MkdirTrace (some parDh) pair.2.val.toUTF8 0o755 tr ∨
                (existOk = true ∧ ∃ rawSt, (.fstatat (some parDh) pair.2.val.toUTF8 { symlinkNofollow := true }, .statted rawSt) ∈ tr ∧ rawSt.kind = .dir))
              (fun e _ => nonLockErrOk e) (fun _ _ _ _ h => h) (fun _ _ h _ => h) leafAct
              (fun parDh held sX hWX => by
                have hL := hLeaf parDh held hWX
                cases hRl : leafAct parDh sX with
                | mk rL sY =>
                  simp only [StateT.run, hRl] at hL ⊢
                  obtain ⟨hWfY, hTmpY, tr, hSt, hFd, hConf, hOut⟩ := hL
                  exact ⟨hWfY, hTmpY, tr, hSt, hConf, by cases rL with | ok u => cases u; exact ⟨hFd, hOut⟩ | error e => exact ⟨hFd, hOut⟩⟩)
              true dh [hidOf dh] pair.1 hW0
            cases hRw : (Internal.walkDescendM (SysBridge.mkRawDirOpsM files nextNonce) dh pair.1 leafAct s0) with
            | mk res s1 =>
              have hRw' : Internal.walkDescendAuxM (SysBridge.mkRawDirOpsM files nextNonce) true dh pair.1 leafAct s0 = (res, s1) := hRw
              rw [StateT.run] at hWd; rw [hRw'] at hWd; simp only [↓reduceIte] at hWd
              obtain ⟨hWf1, hTmp1, tr, hSt, hConf, hOut⟩ := hWd
              simp only [StateT.run, hRw]
              refine ⟨hWf1, hTmp1, tr, hSt, by cases res <;> exact hOut.1, hConf, ?_⟩
              cases res with
              | error e => exact hOut.2
              | ok u =>
                cases u; obtain ⟨_, d, sub, ⟨pre, post, rfl⟩, hCase⟩ := hOut; refine ⟨d, ?_⟩
                rcases hCase with hMk | ⟨hEx, rawSt, hm, hd⟩
                · exact Or.inl (List.mem_append_left _ (List.mem_append_right _ hMk))
                · exact Or.inr ⟨hEx, rawSt, List.mem_append_left _ (List.mem_append_right _ hm), hd⟩)
    hWf
  cases hRw : (Internal.withSubtreeM (SysBridge.mkRawDirOpsM files nextNonce) rootPath (·.mkdir rel parents existOk) s) with
  | mk res s1 =>
    rw [StateT.run] at hW; rw [hRw] at hW; dsimp only at hW
    obtain ⟨tr, hTr, hOut⟩ := hW
    simp only [Bind.bind, Pure.pure, allowedSubtreeStep]
    exact ⟨tr, hTr, by cases res with | ok u => cases u; exact hOut | error e => exact nonLockErr_to_subtreeErr hOut⟩

end LeanSwe.Fs.Proofs
