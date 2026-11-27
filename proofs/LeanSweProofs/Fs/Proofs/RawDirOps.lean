import LeanSweProofs.Fs.Proofs.SubtreeCore
import LeanSweProofs.Fs.Proofs.SubtreeIsolation
import LeanSweProofs.Fs.SpecTests

namespace LeanSwe.Fs.Proofs

open Core LeanSwe.Fs LeanSwe.Fs.Model

private theorem lookupDir_zero (st : VfsState) (p : String) :
    lookupDir st { handleId := 0, rootPath := p } = none := rfl

private theorem lookupDir_erase_self (st : VfsState) (dh : DirHandle) :
    lookupDir { st with openDirs := st.openDirs.filter (fun p => p.1 != dh.handleId) } dh = none := by
  unfold lookupDir
  dsimp only
  split
  · rfl
  · simp only [Option.map_eq_none_iff]
    rw [List.find?_eq_none]
    intro x hx
    simp only [List.mem_filter] at hx
    have hNe : (x.1 != dh.handleId) = true := hx.2
    simp only [bne_iff_ne, ne_eq] at hNe
    simp [beq_iff_eq, hNe]

/-- Removing `dh` via `closeDir` preserves `lookupDir` for any distinct handle `other`. -/
theorem lookupDir_erase_ne (st : VfsState) (dh other : DirHandle)
    (hNe : other.handleId ≠ dh.handleId) :
    lookupDir { st with openDirs := st.openDirs.filter (fun p => p.1 != dh.handleId) } other =
      lookupDir st other := by
  unfold lookupDir
  dsimp only
  split
  · rfl
  · congr 1
    induction st.openDirs with
    | nil => rfl
    | cons p ps ih =>
      simp only [List.filter_cons]
      by_cases hKeep : (p.1 != dh.handleId) = true
      · simp only [hKeep, ↓reduceIte, List.find?_cons]
        cases hMatch : (p.1 == other.handleId) with
        | true => rfl
        | false => exact ih
      · have hDrop : (p.1 != dh.handleId) = false := Bool.eq_false_iff.mpr hKeep
        have hEqDh : p.1 = dh.handleId := by simpa using hDrop
        have hNotOther : (p.1 == other.handleId) = false := beq_false_of_ne (hEqDh ▸ hNe.symm)
        simp only [hDrop, Bool.false_eq_true, ↓reduceIte, List.find?_cons, hNotOther]
        exact ih

/-- Prepending a fresh `(id, pos)` entry preserves `lookupDir` for any handle with a different `id`. -/
theorem lookupDir_cons_ne (st : VfsState) (id : Nat) (pos : List String) (dh : DirHandle)
    (hNe : id ≠ dh.handleId) :
    lookupDir { st with openDirs := (id, pos) :: st.openDirs } dh = lookupDir st dh := by
  unfold lookupDir
  dsimp only
  split
  · rfl
  · simp [beq_false_of_ne hNe]

/-- Prepending `(id, pos)` with `0 < id` makes `lookupDir` resolve `{ handleId := id, rootPath := rp }` to `some pos`. -/
theorem lookupDir_cons_self (st : VfsState) (id : Nat) (pos : List String) (rp : String)
    (hPos : 0 < id) :
    lookupDir { st with openDirs := (id, pos) :: st.openDirs } { handleId := id, rootPath := rp } =
      some pos := by
  unfold lookupDir
  have hZero : (id == 0) = false := beq_false_of_ne (Nat.ne_of_gt hPos)
  simp [hZero]

private theorem lookupDir_eq_of_handleId_eq (st : VfsState) (d1 d2 : DirHandle)
    (hId : d1.handleId = d2.handleId) : lookupDir st d1 = lookupDir st d2 := by
  unfold lookupDir
  rw [hId]

private noncomputable def openDirAtTpl (st : VfsState) (dh : DirHandle) (name : EntryName)
    (id : Nat) : Except FsError DirHandle × VfsState :=
  match lookupDir st dh with
  | none => (.error (mInvalidDirHandleErr dh), st)
  | some pos =>
    match nodeAt st.tree pos with
    | none =>
      (.error { kind := .notFound, path := some dh.rootPath, message := "directory no longer exists" }, st)
    | some (.dir parMode) =>
      if (parMode / 64) % 2 == 0 then
        (.error { kind := .permissionDenied, path := some name.val, message := s!"permission denied: {name.val}" }, st)
      else
        let childPos := pos ++ [name.val]
        match nodeAt st.tree childPos with
        | none =>
          (.error { kind := .notFound, path := some name.val, message := s!"no such file or directory: {name.val}" }, st)
        | some (.symlink _ _) =>
          (.error
            { kind := .invalidInput
              path := some name.val
              message := s!"symlink refused in subtree traversal: {name.val}" },
            st)
        | some (.dir mode) =>
          if (mode / 256) % 2 == 0 then
            (.error { kind := .permissionDenied, path := some name.val, message := s!"permission denied: {name.val}" }, st)
          else
            (.ok { handleId := id, rootPath := pathOfSegs childPos },
              { st with openDirs := (id, childPos) :: st.openDirs, nextDirId := id + 1 })
        | some _ =>
          (.error { kind := .notADirectory, path := some name.val, message := s!"not a directory: {name.val}" }, st)
    | some _ =>
      (.error { kind := .notADirectory, path := some dh.rootPath, message := s!"not a directory: {dh.rootPath}" }, st)

/-- `vfsDirOps.openDirAt` refuses a symlink child with `.invalidInput` without mutating state. -/
theorem vfsDirOps_openDirAt_symlink (st : VfsState) (dh : DirHandle) (name : EntryName)
    (pos : List String) (parMode : Nat) (tgt : String) (symMode : Nat)
    (hLd : lookupDir st dh = some pos)
    (hPar : nodeAt st.tree pos = some (.dir parMode))
    (hExec : (parMode / 64) % 2 ≠ 0)
    (hSym : nodeAt st.tree (pos ++ [name.val]) = some (.symlink tgt symMode)) :
    ∃ e, vfsDirOps.openDirAt dh name st = (.error e, st) ∧ e.kind = .invalidInput := by
  have hTpl : ∃ id, vfsDirOps.openDirAt dh name st = openDirAtTpl st dh name id := ⟨_, rfl⟩
  rcases hTpl with ⟨id, hEq⟩
  rw [hEq]
  unfold openDirAtTpl
  rw [hLd]
  dsimp only
  rw [hPar]
  have hExFalse : ((parMode / 64) % 2 == 0) = false := beq_false_of_ne hExec
  simp only [hExFalse, Bool.false_eq_true, ↓reduceIte]
  rw [hSym]
  exact ⟨_, rfl, rfl⟩

/-- `vfsDirOps.openDir "/"` resolves to the root path `[]` and opens a fresh handle to `[]`. -/
theorem vfsDirOps_openDir_root_ok (st : VfsState) (dh : DirHandle) (st' : VfsState)
    (h : vfsDirOps.openDir "/" st = (.ok dh, st')) :
    0 < dh.handleId ∧
      (∀ p ∈ st.openDirs, p.1 < dh.handleId) ∧
      ∃ m,
        nodeAt st.tree [] = some (.dir m) ∧
        (m / 256) % 2 ≠ 0 ∧
        st' = { st with openDirs := (dh.handleId, []) :: st.openDirs, nextDirId := dh.handleId + 1 } := by
  rcases vfsDirOps_openDir_ok_resolved "/" st dh st' h with
    ⟨hPos, _, hGt, canon, m, hRes, hm, hSt⟩
  have hNorm : vfsAbsNorm st.cwd "/" = "/" := by
    simp only [vfsAbsNorm, show Model.isAbsolute "/" = true from rfl, ↓reduceIte]
    rfl
  have hSplit : vfsSplitSegs (vfsAbsNorm st.cwd "/") = [] := by
    rw [hNorm]
    rfl
  rw [hSplit] at hRes
  have hNodeCanon : st.nodes canon = some (.dir m) :=
    subtreeVfsResolveSegs_ok_node st.nodes 1024 "/" [] true canon (.dir m) hRes
  have hNotDir : ∀ (hNd : ∀ m' ch', st.tree ≠ .dir m' ch'), False := by
    intro hNd
    change vfsTreeNodes st.tree canon = some (.dir m) at hNodeCanon
    cases hIs : isCanonPath canon with
    | false => simp [vfsTreeNodes, hIs] at hNodeCanon
    | true =>
      simp only [vfsTreeNodes, hIs, ↓reduceIte, nodeAt] at hNodeCanon
      cases hTr : st.tree with
      | dir dm ch => exact hNd dm ch hTr
      | file _ _ =>
        rw [hTr] at hNodeCanon
        cases hSeg : vfsSplitSegs canon <;> simp [vfsTreeGet, hSeg, vfsTreeTopNode] at hNodeCanon
      | symlink _ _ =>
        rw [hTr] at hNodeCanon
        cases hSeg : vfsSplitSegs canon <;> simp [vfsTreeGet, hSeg, vfsTreeTopNode] at hNodeCanon
  cases hT : st.tree with
  | file _ _ => exact absurd (fun _ _ he => by rw [hT] at he; cases he) hNotDir
  | symlink _ _ => exact absurd (fun _ _ he => by rw [hT] at he; cases he) hNotDir
  | dir rm ch =>
    have hRoot : st.nodes "/" = some (.dir rm) := by
      change vfsTreeNodes st.tree "/" = some (.dir rm)
      rw [hT]
      rfl
    unfold vfsResolveSegs at hRes
    rw [hRoot] at hRes
    dsimp only at hRes
    simp only [Except.ok.injEq, Prod.mk.injEq, VfsNode.dir.injEq] at hRes
    rcases hRes with ⟨rfl, rfl⟩
    have hNode : nodeAt (VfsTree.dir rm ch) [] = some (.dir rm) := rfl
    have hSplitRoot : vfsSplitSegs "/" = [] := rfl
    rw [hSplitRoot] at hSt
    exact ⟨hPos, hGt, rm, hNode, hm, by simpa [hT] using hSt⟩

/-- A live entry whose key is registered at `pos ++ [c]` makes `mDirHasLiveChild st pos = true`. -/
theorem mDirHasLiveChild_true_of_node (st : VfsState) (pos : List String) (c : String)
    (hPosValid : ∀ s ∈ pos, validSeg s = true)
    (hCValid : validSeg c = true)
    (hKey : pathOfSegs (pos ++ [c]) ∈ st.keys)
    (hLive : (nodeAt st.tree (pos ++ [c])).isSome = true) :
    mDirHasLiveChild st pos = true := by
  unfold mDirHasLiveChild
  dsimp only
  rw [List.any_eq_true]
  refine ⟨pathOfSegs (pos ++ [c]), hKey, ?_⟩
  have hAllValid : ∀ s ∈ pos ++ [c], validSeg s = true := by
    intro s hs
    simp only [List.mem_append, List.mem_singleton] at hs
    rcases hs with h | rfl
    · exact hPosValid s h
    · exact hCValid
  have hIsCanon : isCanonPath (pathOfSegs (pos ++ [c])) = true :=
    isCanonPath_pathOfSegs (pos ++ [c]) hAllValid
  have hSplit : vfsSplitSegs (pathOfSegs (pos ++ [c])) = pos ++ [c] :=
    vfsSplitSegs_pathOfSegs (pos ++ [c]) hAllValid
  have hNodeSome : (st.nodes (pathOfSegs (pos ++ [c]))).isSome = true := by
    change (vfsTreeNodes st.tree (pathOfSegs (pos ++ [c]))).isSome = true
    rw [vfsTreeNodes, if_pos_eq hIsCanon, hSplit]
    exact hLive
  have hNeq : (pathOfSegs (pos ++ [c]) != pathOfSegs pos) = true := by
    rw [bne_iff_ne]
    intro hEq
    have hSegs := pathOfSegs_inj hAllValid hPosValid hEq
    have hLen := congrArg List.length hSegs
    simp at hLen
  have hPrefix : (if pathOfSegs pos == "/" then "/" else pathOfSegs pos ++ "/").toList.isPrefixOf
      (pathOfSegs (pos ++ [c])).toList = true := by
    rw [pathOfSegs_snoc_toList pos c hPosValid]
    exact List.isPrefixOf_iff_prefix.mpr ⟨c.toList, rfl⟩
  simp only [Bool.and_eq_true]
  exact ⟨⟨hNodeSome, hNeq⟩, hPrefix⟩
where
  if_pos_eq {α : Type} {b : Bool} {a c : α} (hb : b = true) : (if b = true then a else c) = a := by
    simp [hb]

/-- `nodeAt` returns `none` on all descendants of a `none` path. -/
theorem nodeAt_none_desc (t : VfsTree) (p rest : List String)
    (hNone : nodeAt t p = none) : nodeAt t (p ++ rest) = none := by
  induction p generalizing t with
  | nil =>
    cases t <;> simp [nodeAt, vfsTreeGet] at hNone
  | cons a as ih =>
    cases t with
    | file _ _ => cases rest <;> rfl
    | symlink _ _ => cases rest <;> rfl
    | dir _ ch =>
      cases hCh : ch a with
      | none => simp [List.cons_append, nodeAt, vfsTreeGet, hCh]
      | some sub =>
        simp only [nodeAt, vfsTreeGet, hCh] at hNone
        simp only [List.cons_append, nodeAt, vfsTreeGet, hCh]
        exact ih sub hNone

/-- `nodeAt` returns `none` strictly below any `.file` node. -/
theorem nodeAt_file_none_desc (t : VfsTree) (p rest : List String)
    (bs : ByteArray) (m : Nat) (hFile : vfsTreeGet t p = some (.file bs m))
    (hNe : rest ≠ []) : nodeAt t (p ++ rest) = none := by
  induction p generalizing t with
  | nil =>
    cases rest with
    | nil => exact absurd rfl hNe
    | cons x xs =>
      simp only [vfsTreeGet, Option.some.injEq] at hFile
      subst hFile
      rfl
  | cons a as ih =>
    cases t with
    | file _ _ => simp [vfsTreeGet] at hFile
    | symlink _ _ => simp [vfsTreeGet] at hFile
    | dir _ ch =>
      simp only [vfsTreeGet] at hFile
      cases hCh : ch a with
      | none => rw [hCh] at hFile; cases hFile
      | some sub =>
        rw [hCh] at hFile
        simp only [List.cons_append, nodeAt, vfsTreeGet, hCh]
        exact ih sub hFile

/-- Setting child `leaf` under an existing directory updates `nodeAt` at `base ++ [leaf]`. -/
theorem nodeAt_vfsTreeSet_eq (t : VfsTree) (base : List String) (leaf : String)
    (v : Option VfsTree) (hDir : ∃ dm ch, vfsTreeGet t base = some (.dir dm ch)) :
    nodeAt (vfsTreeSet t (base ++ [leaf]) v) (base ++ [leaf]) = v.map vfsTreeTopNode := by
  unfold nodeAt
  rw [vfsTreeGet_vfsTreeSet_eq t base leaf v hDir]

private theorem fstatDir_ok_dir (st : VfsState) (dh : DirHandle) (dSt : FileStat)
    (hF : (vfsDirOps.fstatDir dh st).1 = .ok dSt)
    (hKind : dSt.kind = .dir) (hW : dSt.mode / 128 % 2 = 1) (hX : dSt.mode / 64 % 2 = 1) :
    ∃ pos parMode,
      lookupDir st dh = some pos ∧
      nodeAt st.tree pos = some (.dir parMode) ∧
      (parMode / 128 % 2 == 0) = false ∧
      (parMode / 64 % 2 == 0) = false := by
  rw [vfsDirOps_fstatDir_def] at hF
  cases hLd : lookupDir st dh with
  | none => rw [hLd] at hF; cases hF
  | some pos =>
    rw [hLd] at hF
    dsimp only at hF
    cases hNd : nodeAt st.tree pos with
    | none => rw [hNd] at hF; cases hF
    | some nd =>
      rw [hNd] at hF
      simp only [Except.ok.injEq] at hF
      subst hF
      cases nd with
      | file _ _ => cases hKind
      | symlink _ _ => cases hKind
      | dir pm =>
        simp only [vfsToStat] at hW hX
        refine ⟨pos, pm, rfl, hNd, ?_, ?_⟩
        · simp [hW]
        · simp [hX]

private def cleanVfsRootState : VfsState :=
  { tree := vfsEmptyDir 0o755
    keys := ["/"]
    cwd := "/"
    nonce := 0
    locks := []
    nextLockId := 1
    openDirs := [(1, [])]
    nextDirId := 2 }

private def cleanDh0 : DirHandle := { handleId := 1, rootPath := "/" }

private def sampleEntryA : EntryName := ⟨"a", by decide⟩
private def sampleEntryB : EntryName := ⟨"b", by decide⟩

/-- Locked model spec: every `vfsDirOps` operation refuses any invalid/closed `DirHandle` with `.invalidInput` and leaves `nodes` unchanged. -/
theorem spec_invalidHandleRefused : SpecInvalidHandleRefused := by
  intro st dh otherDh name otherName bytes b1 b2 target lockMode hNone
  dsimp only [StateT.run]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [vfsDirOps_openDirAt_none st dh name hNone]
    exact ⟨⟨_, rfl, rfl⟩, rfl⟩
  · rw [vfsDirOps_closeDir_def]
    unfold lookupDir at hNone
    by_cases hz : (dh.handleId == 0) = true
    · simp only [hz, ↓reduceIte]
      exact ⟨⟨_, rfl, rfl⟩, trivial⟩
    · have hzF : (dh.handleId == 0) = false := Bool.eq_false_iff.mpr hz
      simp only [hzF, Bool.false_eq_true, ↓reduceIte, Option.map_eq_none_iff] at hNone
      have hAnyFalse : (st.openDirs.any fun x => x.1 == dh.handleId) = false := by
        rw [Bool.eq_false_iff]
        intro hAny
        rw [List.any_eq_true] at hAny
        rcases hAny with ⟨p, hpMem, hpEq⟩
        exact absurd (List.find?_eq_none.mp hNone p hpMem) (by simp [hpEq])
      simp only [hzF, Bool.false_eq_true, ↓reduceIte, hAnyFalse]
      exact ⟨⟨_, rfl, rfl⟩, trivial⟩
  · rw [vfsDirOps_fstatDir_def, hNone]
    exact ⟨⟨_, rfl, rfl⟩, rfl⟩
  · rw [vfsDirOps_lstatAt_def, hNone]
    exact ⟨⟨_, rfl, rfl⟩, rfl⟩
  · rw [vfsDirOps_readDirAt_def, hNone]
    exact ⟨⟨_, rfl, rfl⟩, rfl⟩
  · rw [vfsDirOps_createDirAt_def, hNone]
    exact ⟨⟨_, rfl, rfl⟩, rfl⟩
  · rw [vfsDirOps_readRegularAt_def, hNone]
    exact ⟨⟨_, rfl, rfl⟩, rfl⟩
  · rw [vfsDirOps_createFileAt_def, hNone]
    exact ⟨⟨_, rfl, rfl⟩, rfl⟩
  · rw [vfsDirOps_renameAt_def, hNone]
    exact ⟨⟨_, rfl, rfl⟩, rfl⟩
  · rw [vfsDirOps_renameAt_def, hNone]
    cases lookupDir st otherDh <;> exact ⟨⟨_, rfl, rfl⟩, rfl⟩
  · rw [vfsDirOps_unlinkAt_def, hNone]
    exact ⟨⟨_, rfl, rfl⟩, rfl⟩
  · rw [vfsDirOps_symlinkAt_def]
    by_cases hBad : (target.isEmpty || target.toList.contains (Char.ofNat 0)) = true
    · simp only [hBad, ↓reduceIte]
      exact ⟨⟨_, rfl, rfl⟩, trivial⟩
    · have hGood : (target.isEmpty || target.toList.contains (Char.ofNat 0)) = false := Bool.eq_false_iff.mpr hBad
      simp only [hGood, Bool.false_eq_true, ↓reduceIte, hNone]
      exact ⟨⟨_, rfl, rfl⟩, trivial⟩
  · rw [vfsDirOps_acquireLockAt_none st dh name lockMode b1 b2 hNone]
    exact ⟨⟨_, rfl, rfl⟩, rfl⟩

/-- `AllPass` proof for `test_fs_vfsDirOps_invalidHandleRefused`. -/
theorem proof_fs_vfsDirOps_invalidHandleRefused :
    AllPass (test_fs_vfsDirOps_invalidHandleRefused SpecInvalidHandleRefused) := by
  dsimp only [AllPass, test_fs_vfsDirOps_invalidHandleRefused, NondetTest.assert]
  exact ⟨spec_invalidHandleRefused, trivial⟩

/-- `CanReach` witness for `test_fs_vfsDirOps_invalidHandleRefused`. -/
theorem reach_fs_vfsDirOps_invalidHandleRefused :
    CanReach (test_fs_vfsDirOps_invalidHandleRefused SpecInvalidHandleRefused) := by
  dsimp only [CanReach, test_fs_vfsDirOps_invalidHandleRefused, NondetTest.assert]
  exact ⟨spec_invalidHandleRefused, trivial⟩

/-- `AllPass` proof that `vfsDirOps.openDirAt` refuses symlinks and leaves state unchanged. -/
theorem proof_fsraw_rawDirOps_openDirAt_refusesSymlinkAndPreservesState :
    AllPass (test_fsraw_rawDirOps_openDirAt_refusesSymlinkAndPreservesState vfsDirOps) := by
  dsimp only [AllPass, test_fsraw_rawDirOps_openDirAt_refusesSymlinkAndPreservesState,
    NondetTest.nondet, NondetTest.assume, NondetTest.assert, Bind.bind, Pure.pure, bind, pure, StateT.run]
  intro s₀ dh child ⟨lst, hLst, hSym⟩
  rw [vfsDirOps_lstatAt_def] at hLst
  dsimp only at hLst
  cases hLd : lookupDir s₀ dh with
  | none => rw [hLd] at hLst; cases hLst
  | some pos =>
    rw [hLd] at hLst
    dsimp only at hLst
    cases hPar : nodeAt s₀.tree pos with
    | none => rw [hPar] at hLst; cases hLst
    | some pNode =>
      rw [hPar] at hLst
      cases pNode with
      | file _ _ => cases hLst
      | symlink _ _ => cases hLst
      | dir pm =>
        dsimp only at hLst
        by_cases hEx : (pm / 64) % 2 == 0
        · simp [hEx] at hLst
        · have hExF : ((pm / 64) % 2 == 0) = false := Bool.eq_false_iff.mpr hEx
          simp only [hExF, Bool.false_eq_true, ↓reduceIte] at hLst
          cases hNd : nodeAt s₀.tree (pos ++ [child.val]) with
          | none => rw [hNd] at hLst; cases hLst
          | some cNode =>
            rw [hNd] at hLst
            simp only [Except.ok.injEq] at hLst
            subst hLst
            cases cNode with
            | file _ _ => cases hSym
            | dir _ => cases hSym
            | symlink tgt sm =>
              have hExecNz : (pm / 64) % 2 ≠ 0 := by simpa using hEx
              rcases vfsDirOps_openDirAt_symlink s₀ dh child pos pm tgt sm hLd hPar hExecNz hNd with
                ⟨e, hOp, hKind⟩
              rw [hOp]
              exact ⟨⟨⟨e, rfl, hKind⟩, rfl⟩, trivial⟩

/-- `CanReach` witness for `test_fsraw_rawDirOps_openDirAt_refusesSymlinkAndPreservesState`. -/
theorem reach_fsraw_rawDirOps_openDirAt_refusesSymlinkAndPreservesState :
    CanReach (test_fsraw_rawDirOps_openDirAt_refusesSymlinkAndPreservesState vfsDirOps) := by
  dsimp only [CanReach, test_fsraw_rawDirOps_openDirAt_refusesSymlinkAndPreservesState,
    NondetTest.nondet, NondetTest.assume, NondetTest.assert, Bind.bind, Pure.pure, bind, pure, StateT.run]
  let st : VfsState :=
    { cleanVfsRootState with
      tree := vfsTreeSet cleanVfsRootState.tree ["a"] (some (.symlink "t" 511))
      keys := ["/a", "/"] }
  refine ⟨st, cleanDh0, sampleEntryA, ?_, ?_⟩
  · exact ⟨vfsToStat (.symlink "t" 511), rfl, rfl⟩
  · exact ⟨⟨⟨_, rfl, rfl⟩, rfl⟩, trivial⟩

/-- `AllPass` proof that `vfsDirOps.readRegularAt` refuses symlinks (`.invalidInput`) and dirs (`.isADirectory`) without state changes. -/
theorem proof_fsraw_rawDirOps_readRegularAt_refusesSymlinkAndDir :
    AllPass (test_fsraw_rawDirOps_readRegularAt_refusesSymlinkAndDir vfsDirOps) := by
  dsimp only [AllPass, test_fsraw_rawDirOps_readRegularAt_refusesSymlinkAndDir,
    NondetTest.nondet, NondetTest.assume, NondetTest.assert, Bind.bind, Pure.pure, bind, pure, StateT.run]
  intro s₀ dh child
  rw [vfsDirOps_lstatAt_def]
  dsimp only
  cases hLd : lookupDir s₀ dh with
  | none => trivial
  | some pos =>
    dsimp only
    cases hPar : nodeAt s₀.tree pos with
    | none => trivial
    | some pNode =>
      cases pNode with
      | file _ _ => trivial
      | symlink _ _ => trivial
      | dir pm =>
        dsimp only
        by_cases hEx : (pm / 64) % 2 == 0
        · simp [hEx]
        · have hExF : ((pm / 64) % 2 == 0) = false := Bool.eq_false_iff.mpr hEx
          simp only [hExF, Bool.false_eq_true, ↓reduceIte]
          cases hNd : nodeAt s₀.tree (pos ++ [child.val]) with
          | none => trivial
          | some cNode =>
            dsimp only
            cases cNode with
            | file _ _ =>
              simp [vfsToStat, show (EntryKind.file == EntryKind.symlink) = false from rfl,
                show (EntryKind.file == EntryKind.dir) = false from rfl]
            | symlink tgt sm =>
              simp only [vfsToStat, show (EntryKind.symlink == EntryKind.symlink) = true from rfl, ↓reduceIte]
              rw [vfsDirOps_readRegularAt_def, hLd]
              dsimp only
              rw [hPar]
              simp only [hExF, Bool.false_eq_true, ↓reduceIte, hNd]
              exact ⟨⟨⟨_, rfl, rfl⟩, trivial⟩, trivial⟩
            | dir dm =>
              simp only [vfsToStat, show (EntryKind.dir == EntryKind.symlink) = false from rfl,
                Bool.false_eq_true, ↓reduceIte, show (EntryKind.dir == EntryKind.dir) = true from rfl]
              rw [vfsDirOps_readRegularAt_def, hLd]
              dsimp only
              rw [hPar]
              simp only [hExF, Bool.false_eq_true, ↓reduceIte, hNd]
              exact ⟨⟨⟨_, rfl, rfl⟩, trivial⟩, trivial⟩

/-- `CanReach` witness for `test_fsraw_rawDirOps_readRegularAt_refusesSymlinkAndDir`. -/
theorem reach_fsraw_rawDirOps_readRegularAt_refusesSymlinkAndDir :
    CanReach (test_fsraw_rawDirOps_readRegularAt_refusesSymlinkAndDir vfsDirOps) := by
  dsimp only [CanReach, test_fsraw_rawDirOps_readRegularAt_refusesSymlinkAndDir,
    NondetTest.nondet, NondetTest.assume, NondetTest.assert, Bind.bind, Pure.pure, bind, pure, StateT.run]
  let st : VfsState :=
    { cleanVfsRootState with
      tree := vfsTreeSet cleanVfsRootState.tree ["a"] (some (.symlink "t" 511))
      keys := ["/a", "/"] }
  refine ⟨st, cleanDh0, sampleEntryA, ?_⟩
  exact ⟨⟨⟨_, rfl, rfl⟩, rfl⟩, trivial⟩

/-- `AllPass` proof that `vfsDirOps.createFileAt` enforces exclusive no-follow creation with mode `0o644` and exact round-trip bytes. -/
theorem proof_fsraw_rawDirOps_createFileAt_exclusiveNoFollow :
    AllPass (test_fsraw_rawDirOps_createFileAt_exclusiveNoFollow vfsDirOps) := by
  dsimp only [AllPass, test_fsraw_rawDirOps_createFileAt_exclusiveNoFollow,
    NondetTest.nondet, NondetTest.assume, NondetTest.assert, Bind.bind, Pure.pure, bind, pure, StateT.run]
  intro s₀ dh child bytes ⟨dSt, hF, hKind, hW, hX⟩
  rcases fstatDir_ok_dir s₀ dh dSt hF hKind hW hX with ⟨pos, pm, hLd, hPar, hWF, hXF⟩
  rw [vfsDirOps_lstatAt_def, hLd]
  dsimp only
  rw [hPar]
  simp only [hXF, Bool.false_eq_true, ↓reduceIte]
  cases hNd : nodeAt s₀.tree (pos ++ [child.val]) with
  | some cNode =>
    dsimp only
    rw [vfsDirOps_createFileAt_def, hLd]
    dsimp only
    rw [hPar]
    simp only [hWF, hXF, Bool.false_eq_true, Bool.or_self, ↓reduceIte, hNd]
    exact ⟨⟨⟨_, rfl, rfl⟩, trivial⟩, trivial⟩
  | none =>
    dsimp only
    intro _
    rw [vfsDirOps_createFileAt_def, hLd]
    dsimp only
    rw [hPar]
    simp only [hWF, hXF, Bool.false_eq_true, Bool.or_self, ↓reduceIte, hNd]
    have hDirGet : ∃ dm ch, vfsTreeGet s₀.tree pos = some (.dir dm ch) := ⟨pm, vfsTreeGet_dir_of_nodeAt hPar⟩
    have hNotPre : ¬ (pos ++ [child.val] <+: pos) := by
      intro hPre
      have hLen := List.IsPrefix.length_le hPre
      simp at hLen
      omega
    have hPar1 : nodeAt (vfsTreeSet s₀.tree (pos ++ [child.val]) (some (.file bytes 420))) pos = some (.dir pm) := by
      rw [nodeAt_vfsTreeSet_outside s₀.tree pos child.val _ pos hDirGet hNotPre, hPar]
    have hLeaf1 : nodeAt (vfsTreeSet s₀.tree (pos ++ [child.val]) (some (.file bytes 420))) (pos ++ [child.val]) =
        some (.file bytes 420) := by
      simpa [vfsTreeTopNode] using nodeAt_vfsTreeSet_eq s₀.tree pos child.val (some (.file bytes 420)) hDirGet
    let sNew : VfsState :=
      { s₀ with
        tree := vfsTreeSet s₀.tree (pos ++ [child.val]) (some (.file bytes 420))
        keys := pathOfSegs (pos ++ [child.val]) :: s₀.keys }
    have hLdNew : lookupDir sNew dh = some pos := hLd
    refine ⟨trivial, ?_, ?_, trivial⟩
    · refine ⟨vfsToStat (.file bytes 420), ?_, rfl, rfl, rfl⟩
      rw [vfsDirOps_lstatAt_def]
      dsimp only
      rw [hLdNew]
      dsimp only
      rw [hPar1]
      dsimp only
      rw [if_false_eq hXF, hLeaf1]
    · rw [vfsDirOps_readRegularAt_def]
      dsimp only
      rw [hLdNew]
      dsimp only
      rw [hPar1]
      dsimp only
      rw [if_false_eq hXF, hLeaf1]
      dsimp only
      simp [show (420 / 256 % 2 == 0) = false from rfl]
where
  if_false_eq {α : Type} {c : Bool} {a b : α} (hc : c = false) : (if c = true then a else b) = b := by
    simp [hc]

/-- `CanReach` witness for `test_fsraw_rawDirOps_createFileAt_exclusiveNoFollow`. -/
theorem reach_fsraw_rawDirOps_createFileAt_exclusiveNoFollow :
    CanReach (test_fsraw_rawDirOps_createFileAt_exclusiveNoFollow vfsDirOps) := by
  dsimp only [CanReach, test_fsraw_rawDirOps_createFileAt_exclusiveNoFollow,
    NondetTest.nondet, NondetTest.assume, NondetTest.assert, Bind.bind, Pure.pure, bind, pure, StateT.run]
  refine ⟨cleanVfsRootState, cleanDh0, sampleEntryA, ByteArray.empty, ?_, ?_⟩
  · exact ⟨vfsToStat (.dir 0o755), rfl, rfl, by decide, by decide⟩
  · exact ⟨rfl, rfl, ⟨vfsToStat (.file ByteArray.empty 420), rfl, rfl, rfl, rfl⟩, rfl, trivial⟩

/-- `AllPass` proof that `vfsDirOps.createDirAt` creates missing directories at mode `0o755` and rejects existing entries with `.alreadyExists`. -/
theorem proof_fsraw_rawDirOps_createDirAt_createsOrRejectsExisting :
    AllPass (test_fsraw_rawDirOps_createDirAt_createsOrRejectsExisting vfsDirOps) := by
  dsimp only [AllPass, test_fsraw_rawDirOps_createDirAt_createsOrRejectsExisting,
    NondetTest.nondet, NondetTest.assume, NondetTest.assert, Bind.bind, Pure.pure, bind, pure, StateT.run]
  intro s₀ dh child ⟨dSt, hF, hKind, hW, hX⟩
  rcases fstatDir_ok_dir s₀ dh dSt hF hKind hW hX with ⟨pos, pm, hLd, hPar, hWF, hXF⟩
  rw [vfsDirOps_lstatAt_def, hLd]
  dsimp only
  rw [hPar]
  simp only [hXF, Bool.false_eq_true, ↓reduceIte]
  cases hNd : nodeAt s₀.tree (pos ++ [child.val]) with
  | some cNode =>
    dsimp only
    rw [vfsDirOps_createDirAt_def, hLd]
    dsimp only
    rw [hPar]
    simp only [hWF, hXF, Bool.false_eq_true, Bool.or_self, ↓reduceIte, hNd]
    exact ⟨⟨⟨_, rfl, rfl⟩, trivial⟩, trivial⟩
  | none =>
    dsimp only
    intro _
    rw [vfsDirOps_createDirAt_def, hLd]
    dsimp only
    rw [hPar]
    simp only [hWF, hXF, Bool.false_eq_true, Bool.or_self, ↓reduceIte, hNd]
    have hDirGet : ∃ dm ch, vfsTreeGet s₀.tree pos = some (.dir dm ch) := ⟨pm, vfsTreeGet_dir_of_nodeAt hPar⟩
    have hNotPre : ¬ (pos ++ [child.val] <+: pos) := by
      intro hPre
      have hLen := List.IsPrefix.length_le hPre
      simp at hLen
      omega
    have hPar1 : nodeAt (vfsTreeSet s₀.tree (pos ++ [child.val]) (some (vfsEmptyDir 493))) pos = some (.dir pm) := by
      rw [nodeAt_vfsTreeSet_outside s₀.tree pos child.val _ pos hDirGet hNotPre, hPar]
    have hLeaf1 : nodeAt (vfsTreeSet s₀.tree (pos ++ [child.val]) (some (vfsEmptyDir 493))) (pos ++ [child.val]) =
        some (.dir 493) := by
      simpa [vfsEmptyDir, vfsTreeTopNode] using nodeAt_vfsTreeSet_eq s₀.tree pos child.val (some (vfsEmptyDir 493)) hDirGet
    let sNew : VfsState :=
      { s₀ with
        tree := vfsTreeSet s₀.tree (pos ++ [child.val]) (some (vfsEmptyDir 493))
        keys := pathOfSegs (pos ++ [child.val]) :: s₀.keys }
    have hLdNew : lookupDir sNew dh = some pos := hLd
    refine ⟨trivial, ?_, trivial⟩
    refine ⟨vfsToStat (.dir 493), ?_, rfl, rfl⟩
    rw [vfsDirOps_lstatAt_def]
    dsimp only
    rw [hLdNew]
    dsimp only
    rw [hPar1]
    simp only [hXF, Bool.false_eq_true, ↓reduceIte, hLeaf1]

/-- `CanReach` witness for `test_fsraw_rawDirOps_createDirAt_createsOrRejectsExisting`. -/
theorem reach_fsraw_rawDirOps_createDirAt_createsOrRejectsExisting :
    CanReach (test_fsraw_rawDirOps_createDirAt_createsOrRejectsExisting vfsDirOps) := by
  dsimp only [CanReach, test_fsraw_rawDirOps_createDirAt_createsOrRejectsExisting,
    NondetTest.nondet, NondetTest.assume, NondetTest.assert, Bind.bind, Pure.pure, bind, pure, StateT.run]
  refine ⟨cleanVfsRootState, cleanDh0, sampleEntryA, ?_, ?_⟩
  · exact ⟨vfsToStat (.dir 0o755), rfl, rfl, by decide, by decide⟩
  · exact ⟨rfl, rfl, ⟨vfsToStat (.dir 493), rfl, rfl, rfl⟩, trivial⟩

private abbrev unlinkAtJpTail (rootDh childDh : DirHandle) (child inner : EntryName)
    (s₄ : VfsState) : (Unit → Prop) → Prop :=
  match vfsDirOps.createFileAt childDh inner ByteArray.empty s₄ with
  | (rCf, s₅) => fun (post : Unit → Prop) =>
    rCf = Except.ok () ∧
      (match vfsDirOps.closeDir childDh s₅ with
      | (rCl, s₆) => fun (post : Unit → Prop) =>
        rCl = Except.ok () ∧
          (match vfsDirOps.unlinkAt rootDh child true s₆ with
          | (rNotEmpty, s₇) => fun (post : Unit → Prop) =>
            ((∃ e, rNotEmpty = Except.error e ∧ e.kind = FsErrorKind.notEmpty) ∧ s₇ = s₆) ∧ post ())
          post)
      post

private abbrev unlinkAtJpMid (rootDh : DirHandle) (child inner : EntryName)
    (sRoot : VfsState) : (Unit → Prop) → Prop :=
  match vfsDirOps.createDirAt rootDh child sRoot with
  | (rMk1, s₁) => fun (post : Unit → Prop) =>
    rMk1 = Except.ok () ∧
      (match vfsDirOps.unlinkAt rootDh child true s₁ with
      | (rRmEmpty, s₂) => fun (post : Unit → Prop) =>
        (rRmEmpty = Except.ok () ∧ ∃ e, (vfsDirOps.lstatAt rootDh child s₂).1 = Except.error e ∧ e.kind = FsErrorKind.notFound) ∧
          (match vfsDirOps.createDirAt rootDh child sRoot with
          | (rMk2, s₃) => fun (post : Unit → Prop) =>
            rMk2 = Except.ok () ∧
              (match vfsDirOps.openDirAt rootDh child s₃ with
              | (rOpen, s₄) =>
                match rOpen with
                | Except.error _ => fun (post : Unit → Prop) => False ∧ post ()
                | Except.ok childDh => unlinkAtJpTail rootDh childDh child inner s₄)
              post)
          post)
      post

private abbrev unlinkAtJpProp (s₀ : VfsState) (child : EntryName) : Prop :=
  (match vfsDirOps.openDir "/" s₀ with
  | (openRes, sRoot) =>
    match openRes with
    | Except.error _ => fun (post : Unit → Prop) => post ()
    | Except.ok rootDh => fun (post : Unit → Prop) =>
      ∀ inner : EntryName,
        (match (vfsDirOps.fstatDir rootDh sRoot).1, (vfsDirOps.lstatAt rootDh child sRoot).1 with
        | Except.ok rSt, Except.error mErr =>
          if (rSt.kind == EntryKind.dir && rSt.mode / 128 % 2 == 1 && rSt.mode / 64 % 2 == 1 && mErr.kind == FsErrorKind.notFound) = true then
            unlinkAtJpMid rootDh child inner sRoot
          else fun (post : Unit → Prop) => post ()
        | _, _ => fun (post : Unit → Prop) => post ()) post)
    fun _ => True

private theorem unlinkAt_jp_allPass (s₀ : VfsState) (child : EntryName) :
    unlinkAtJpProp s₀ child := by
  dsimp only [unlinkAtJpProp, unlinkAtJpMid, unlinkAtJpTail]
  cases hOp : vfsDirOps.openDir "/" s₀ with
  | mk openRes sRoot =>
    dsimp only
    cases openRes with
    | error _ => trivial
    | ok rootDh =>
      intro inner
      rcases vfsDirOps_openDir_root_ok s₀ rootDh sRoot hOp with
        ⟨hRootPos, _, _, _, _, hSR⟩
      have hLdRoot : lookupDir sRoot rootDh = some [] := by
        rw [hSR]
        exact lookupDir_cons_self s₀ rootDh.handleId [] rootDh.rootPath hRootPos
      cases hF : (vfsDirOps.fstatDir rootDh sRoot).1 with
      | error _ => trivial
      | ok rSt =>
        cases hL : (vfsDirOps.lstatAt rootDh child sRoot).1 with
        | ok _ => trivial
        | error mErr =>
          dsimp only
          by_cases hCond : (rSt.kind == .dir && rSt.mode / 128 % 2 == 1 && rSt.mode / 64 % 2 == 1 && mErr.kind == .notFound) = true
          · simp only [hCond, ↓reduceIte]
            have hC123 := (Bool.and_eq_true _ _).mp hCond
            have hC12 := (Bool.and_eq_true _ _).mp hC123.1
            have hC1 := (Bool.and_eq_true _ _).mp hC12.1
            have hKind : rSt.kind = .dir := by
              cases hK : rSt.kind <;> first | rfl | exact absurd hC1.1 (by rw [hK]; decide)
            have hW : rSt.mode / 128 % 2 = 1 := beq_iff_eq.mp hC1.2
            have hX : rSt.mode / 64 % 2 = 1 := beq_iff_eq.mp hC12.2
            rcases fstatDir_ok_dir sRoot rootDh rSt hF hKind hW hX with ⟨pos, pm, hLdP, hParP, hWF, hXF⟩
            have hPosEq : pos = [] := Option.some.inj (hLdP.symm.trans hLdRoot)
            subst hPosEq
            rw [vfsDirOps_lstatAt_def, hLdRoot] at hL
            dsimp only at hL
            rw [hParP] at hL
            simp only [hXF, Bool.false_eq_true, ↓reduceIte, List.nil_append] at hL
            have hMissing : nodeAt sRoot.tree [child.val] = none := by
              cases hNd : nodeAt sRoot.tree [child.val] with
              | none => rfl
              | some _ => rw [hNd] at hL; cases hL
            have hDirGet : ∃ dm ch, vfsTreeGet sRoot.tree [] = some (.dir dm ch) := ⟨pm, vfsTreeGet_dir_of_nodeAt hParP⟩
            have hPar1 : nodeAt (vfsTreeSet sRoot.tree [child.val] (some (vfsEmptyDir 493))) [] = some (.dir pm) := by
              rw [show [child.val] = [] ++ [child.val] from rfl,
                nodeAt_vfsTreeSet_outside sRoot.tree [] child.val _ [] hDirGet (by simp), hParP]
            have hEmpty1 : nodeAt (vfsTreeSet sRoot.tree [child.val] (some (vfsEmptyDir 493))) [child.val] =
                some (.dir 493) := by
              simpa [vfsEmptyDir, vfsTreeTopNode] using
                nodeAt_vfsTreeSet_eq sRoot.tree [] child.val (some (vfsEmptyDir 493)) hDirGet
            have hMk1 : vfsDirOps.createDirAt rootDh child sRoot =
                (.ok (), { sRoot with
                  tree := vfsTreeSet sRoot.tree [child.val] (some (vfsEmptyDir 493))
                  keys := pathOfSegs [child.val] :: sRoot.keys }) := by
              rw [vfsDirOps_createDirAt_def, hLdRoot]
              dsimp only
              rw [hParP]
              simp only [hWF, hXF, Bool.false_eq_true, Bool.or_self, ↓reduceIte, List.nil_append, hMissing]
            rw [hMk1]
            dsimp only
            refine ⟨rfl, ?_⟩
            let s1 : VfsState :=
              { sRoot with
                tree := vfsTreeSet sRoot.tree [child.val] (some (vfsEmptyDir 493))
                keys := pathOfSegs [child.val] :: sRoot.keys }
            have hEmptyChild : ∀ rest : List String, rest ≠ [] → nodeAt s1.tree ([child.val] ++ rest) = none := by
              intro rest hNe
              apply nodeAt_dir_empty_none_desc s1.tree [child.val] 493 (fun _ => none)
              · simpa [s1, vfsEmptyDir] using vfsTreeGet_vfsTreeSet_eq sRoot.tree [] child.val (some (vfsEmptyDir 493)) hDirGet
              · intro _; rfl
              · exact hNe
            have hNotLive1 : mDirHasLiveChild s1 [child.val] = false :=
              mDirHasLiveChild_false_of_treeEmpty s1 [child.val]
                (fun s hs => by simp only [List.mem_singleton] at hs; subst hs; exact child.valid)
                hEmptyChild
            have hEmpty1S1 : nodeAt s1.tree [child.val] = some (.dir 493) := hEmpty1
            have hRmEmpty : vfsDirOps.unlinkAt rootDh child true s1 =
                (.ok (), { s1 with tree := vfsTreeSet s1.tree [child.val] none }) := by
              rw [vfsDirOps_unlinkAt_def, show lookupDir s1 rootDh = some [] from hLdRoot]
              dsimp only
              rw [hPar1]
              simp only [hWF, hXF, Bool.false_eq_true, Bool.or_self, ↓reduceIte, List.nil_append, hEmpty1S1,
                Bool.not_true, hNotLive1]
            rw [hRmEmpty]
            dsimp only
            refine ⟨⟨rfl, ?_⟩, ?_⟩
            · let s2 := { s1 with tree := vfsTreeSet s1.tree [child.val] none }
              have hDirGet1 : ∃ dm ch, vfsTreeGet s1.tree [] = some (.dir dm ch) := ⟨pm, vfsTreeGet_dir_of_nodeAt hPar1⟩
              have hPar2 : nodeAt s2.tree [] = some (.dir pm) := by
                rw [show s2.tree = vfsTreeSet s1.tree ([] ++ [child.val]) none from rfl,
                  nodeAt_vfsTreeSet_outside s1.tree [] child.val none [] hDirGet1 (by simp), hPar1]
              have hNone2 : nodeAt s2.tree [child.val] = none := by
                simpa using nodeAt_vfsTreeSet_eq s1.tree [] child.val none hDirGet1
              refine ⟨{
                kind := .notFound
                path := some child.val
                message := toString "no such file or directory: " ++ toString child.val }, ?_, rfl⟩
              change (vfsDirOps.lstatAt rootDh child s2).1 = _
              rw [vfsDirOps_lstatAt_def, show lookupDir s2 rootDh = some [] from hLdRoot]
              dsimp only
              rw [hPar2]
              dsimp only
              rw [show ((pm / 64 % 2 == 0) = false) from hXF]
              simp [hNone2]
            · refine ⟨rfl, ?_⟩
              change (match vfsDirOps.openDirAt rootDh child s1 with
                | (rOpen, s₄) =>
                  match rOpen with
                  | Except.error _ => fun (post : Unit → Prop) => False ∧ post ()
                  | Except.ok childDh => unlinkAtJpTail rootDh childDh child inner s₄) fun _ => True
              cases hOpenChild : vfsDirOps.openDirAt rootDh child s1 with
              | mk rOpen s4 =>
                dsimp only
                cases rOpen with
                | error _ =>
                  have hErrEq : ∃ id, vfsDirOps.openDirAt rootDh child s1 = openDirAtTpl s1 rootDh child id := ⟨_, rfl⟩
                  rcases hErrEq with ⟨id, hEq⟩
                  rw [hOpenChild] at hEq
                  unfold openDirAtTpl at hEq
                  rw [show lookupDir s1 rootDh = some [] from hLdRoot] at hEq
                  dsimp only at hEq
                  rw [hPar1] at hEq
                  simp only [hXF, Bool.false_eq_true, ↓reduceIte, List.nil_append, hEmpty1S1,
                    show (493 / 256 % 2 == 0) = false from rfl] at hEq
                  cases hEq
                | ok childDh =>
                  dsimp only [unlinkAtJpTail]
                  rcases vfsDirOps_openDirAt_ok rootDh child s1 childDh s4 hOpenChild with
                    ⟨hChildPos, _, hChildGt, pPos, _, _, hLdC, _, _, _, _, _, hS4⟩
                  have hPPosEq : pPos = [] := Option.some.inj (hLdC.symm.trans hLdRoot)
                  subst hPPosEq
                  have hChildNeRoot : childDh.handleId ≠ rootDh.handleId := by
                    have hLt := hChildGt (rootDh.handleId, []) (by dsimp only [s1]; rw [hSR]; simp)
                    exact Nat.ne_of_gt hLt
                  have hLdChild4 : lookupDir s4 childDh = some [child.val] := by
                    rw [hS4]
                    exact lookupDir_cons_self s1 childDh.handleId [child.val] childDh.rootPath hChildPos
                  have hLdRoot4 : lookupDir s4 rootDh = some [] := by
                    rw [hS4]
                    exact show lookupDir { s1 with openDirs := (childDh.handleId, [] ++ [child.val]) :: s1.openDirs } rootDh = some [] by
                      rw [lookupDir_cons_ne s1 childDh.handleId ([] ++ [child.val]) rootDh hChildNeRoot]
                      exact hLdRoot
                  have hS4Tree : s4.tree = s1.tree := by rw [hS4]
                  have hChildMissing4 : nodeAt s4.tree [child.val, inner.val] = none := by
                    rw [hS4Tree]
                    exact hEmptyChild [inner.val] (by simp)
                  have hChildDir4 : nodeAt s4.tree [child.val] = some (.dir 493) := by
                    rw [hS4Tree]; exact hEmpty1
                  have hCf : vfsDirOps.createFileAt childDh inner ByteArray.empty s4 =
                      (.ok (), { s4 with
                        tree := vfsTreeSet s4.tree [child.val, inner.val] (some (.file ByteArray.empty 420))
                        keys := pathOfSegs [child.val, inner.val] :: s4.keys }) := by
                    rw [vfsDirOps_createFileAt_def, hLdChild4]
                    dsimp only
                    rw [hChildDir4]
                    simp only [show (493 / 128 % 2 == 0 || 493 / 64 % 2 == 0) = false from rfl,
                      Bool.false_eq_true, ↓reduceIte, List.cons_append, List.nil_append, hChildMissing4]
                  rw [hCf]
                  dsimp only
                  refine ⟨rfl, ?_⟩
                  let s5 : VfsState :=
                    { s4 with
                      tree := vfsTreeSet s4.tree [child.val, inner.val] (some (.file ByteArray.empty 420))
                      keys := pathOfSegs [child.val, inner.val] :: s4.keys }
                  have hAny5 : (s5.openDirs.any fun x => x.1 == childDh.handleId) = true := by
                    rw [List.any_eq_true]
                    refine ⟨(childDh.handleId, [child.val]), ?_, by simp⟩
                    rw [show s5.openDirs = s4.openDirs from rfl, hS4]
                    simp
                  have hClose : vfsDirOps.closeDir childDh s5 =
                      (.ok (), { s5 with openDirs := s5.openDirs.filter (fun x => x.1 != childDh.handleId) }) := by
                    rw [vfsDirOps_closeDir_def]
                    simp only [beq_false_of_ne (Nat.ne_of_gt hChildPos), Bool.false_eq_true, ↓reduceIte, hAny5]
                  rw [hClose]
                  dsimp only
                  refine ⟨rfl, ?_⟩
                  let s6 := { s5 with openDirs := s5.openDirs.filter (fun x => x.1 != childDh.handleId) }
                  have hLdRoot6 : lookupDir s6 rootDh = some [] := by
                    rw [lookupDir_erase_ne s5 childDh rootDh hChildNeRoot.symm]
                    exact hLdRoot4
                  have hCGet4 : ∃ dm ch, vfsTreeGet s4.tree [child.val] = some (.dir dm ch) :=
                    ⟨493, vfsTreeGet_dir_of_nodeAt hChildDir4⟩
                  have hPar6 : nodeAt s6.tree [] = some (.dir pm) := by
                    change nodeAt (vfsTreeSet s4.tree ([child.val] ++ [inner.val]) (some (.file ByteArray.empty 420))) [] = some (.dir pm)
                    rw [nodeAt_vfsTreeSet_outside s4.tree [child.val] inner.val _ [] hCGet4 (by simp), hS4Tree, hPar1]
                  have hChildDir6 : nodeAt s6.tree [child.val] = some (.dir 493) := by
                    change nodeAt (vfsTreeSet s4.tree ([child.val] ++ [inner.val]) (some (.file ByteArray.empty 420))) [child.val] = some (.dir 493)
                    have hNot : ¬ ([child.val] ++ [inner.val] <+: [child.val]) := by
                      intro hPre; have hL := List.IsPrefix.length_le hPre; simp at hL
                    rw [nodeAt_vfsTreeSet_outside s4.tree [child.val] inner.val _ [child.val] hCGet4 hNot, hChildDir4]
                  have hInner6 : nodeAt s6.tree [child.val, inner.val] = some (.file ByteArray.empty 420) := by
                    change nodeAt (vfsTreeSet s4.tree ([child.val] ++ [inner.val]) (some (.file ByteArray.empty 420))) ([child.val] ++ [inner.val]) = some (.file ByteArray.empty 420)
                    simpa [vfsTreeTopNode] using
                      nodeAt_vfsTreeSet_eq s4.tree [child.val] inner.val (some (.file ByteArray.empty 420)) hCGet4
                  have hLive6 : mDirHasLiveChild s6 [child.val] = true :=
                    mDirHasLiveChild_true_of_node s6 [child.val] inner.val
                      (fun s hs => by simp only [List.mem_singleton] at hs; subst hs; exact child.valid)
                      inner.valid (by simp [s6, s5]) (by simp [hInner6])
                  change (match vfsDirOps.unlinkAt rootDh child true s6 with
                    | (rNotEmpty, s₇) => fun (post : Unit → Prop) =>
                      ((∃ e, rNotEmpty = Except.error e ∧ e.kind = FsErrorKind.notEmpty) ∧ s₇ = s6) ∧ post ()) fun _ => True
                  rw [vfsDirOps_unlinkAt_def, hLdRoot6]
                  dsimp only
                  rw [hPar6]
                  simp only [hWF, hXF, Bool.false_eq_true, Bool.or_self, ↓reduceIte, List.nil_append, hChildDir6,
                    Bool.not_true, hLive6]
                  exact ⟨⟨⟨_, rfl, rfl⟩, trivial⟩, trivial⟩
          · have hCondF : (rSt.kind == .dir && rSt.mode / 128 % 2 == 1 && rSt.mode / 64 % 2 == 1 && mErr.kind == .notFound) = false :=
              Bool.eq_false_iff.mpr hCond
            simp only [hCondF, Bool.false_eq_true, ↓reduceIte]

/-- `AllPass` proof for `test_fsraw_rawDirOps_unlinkAt_dirFlagSemantics`. -/
theorem proof_fsraw_rawDirOps_unlinkAt_dirFlagSemantics :
    AllPass (test_fsraw_rawDirOps_unlinkAt_dirFlagSemantics vfsDirOps) := by
  dsimp only [AllPass, test_fsraw_rawDirOps_unlinkAt_dirFlagSemantics,
    NondetTest.nondet, NondetTest.assume, NondetTest.assert, Bind.bind, Pure.pure, bind, pure, StateT.run]
  intro s₀ dh child ⟨dSt, hF, hKind, hW, hX⟩
  rcases fstatDir_ok_dir s₀ dh dSt hF hKind hW hX with ⟨pos, pm, hLd, hPar, hWF, hXF⟩
  have hJp : unlinkAtJpProp s₀ child := unlinkAt_jp_allPass s₀ child
  rw [vfsDirOps_lstatAt_def, hLd]
  dsimp only
  rw [hPar]
  simp only [hXF, Bool.false_eq_true, ↓reduceIte]
  cases hNd : nodeAt s₀.tree (pos ++ [child.val]) with
  | none =>
    dsimp only
    rw [vfsDirOps_unlinkAt_def, hLd]
    dsimp only
    rw [hPar]
    simp only [hWF, hXF, Bool.false_eq_true, Bool.or_self, ↓reduceIte, hNd]
    rw [vfsDirOps_unlinkAt_def, hLd]
    dsimp only
    rw [hPar]
    simp only [hWF, hXF, Bool.false_eq_true, Bool.or_self, ↓reduceIte, hNd]
    exact ⟨⟨⟨_, rfl, rfl⟩, trivial⟩, ⟨⟨_, rfl, rfl⟩, trivial⟩, hJp⟩
  | some cNode =>
    dsimp only
    cases cNode with
    | file _ _ =>
      simp only [vfsToStat, show (EntryKind.file == EntryKind.symlink) = false from rfl,
        show (EntryKind.file == EntryKind.dir) = false from rfl, Bool.false_eq_true, ↓reduceIte]
      exact hJp
    | symlink tgt sm =>
      simp only [vfsToStat, show (EntryKind.symlink == EntryKind.symlink) = true from rfl, ↓reduceIte]
      rw [vfsDirOps_unlinkAt_def, hLd]
      dsimp only
      rw [hPar]
      simp only [hWF, hXF, Bool.false_eq_true, Bool.or_self, ↓reduceIte, hNd]
      rw [vfsDirOps_unlinkAt_def, hLd]
      dsimp only
      rw [hPar]
      simp only [hWF, hXF, Bool.false_eq_true, Bool.or_self, ↓reduceIte, hNd, Bool.false_eq_true]
      have hDirGet : ∃ dm ch, vfsTreeGet s₀.tree pos = some (.dir dm ch) := ⟨pm, vfsTreeGet_dir_of_nodeAt hPar⟩
      have hNotPre : ¬ (pos ++ [child.val] <+: pos) := by
        intro hPre; have hL := List.IsPrefix.length_le hPre; simp at hL; omega
      have hPar1 : nodeAt (vfsTreeSet s₀.tree (pos ++ [child.val]) none) pos = some (.dir pm) := by
        rw [nodeAt_vfsTreeSet_outside s₀.tree pos child.val none pos hDirGet hNotPre, hPar]
      have hNone1 : nodeAt (vfsTreeSet s₀.tree (pos ++ [child.val]) none) (pos ++ [child.val]) = none := by
        simpa using nodeAt_vfsTreeSet_eq s₀.tree pos child.val none hDirGet
      refine ⟨⟨⟨_, rfl, rfl⟩, trivial⟩, ⟨trivial, ?_⟩, hJp⟩
      refine ⟨{
        kind := .notFound
        path := some child.val
        message := toString "no such file or directory: " ++ toString child.val }, ?_, rfl⟩
      rw [vfsDirOps_lstatAt_def, show lookupDir { s₀ with tree := vfsTreeSet s₀.tree (pos ++ [child.val]) none } dh = some pos from hLd]
      dsimp only
      rw [hPar1]
      simp [hXF, hNone1]
    | dir dm =>
      simp only [vfsToStat, show (EntryKind.dir == EntryKind.symlink) = false from rfl,
        Bool.false_eq_true, ↓reduceIte, show (EntryKind.dir == EntryKind.dir) = true from rfl]
      rw [vfsDirOps_unlinkAt_def, hLd]
      dsimp only
      rw [hPar]
      simp only [hWF, hXF, Bool.false_eq_true, Bool.or_self, ↓reduceIte, hNd, Bool.not_false]
      exact ⟨⟨⟨_, rfl, rfl⟩, trivial⟩, hJp⟩

/-- `CanReach` witness for `test_fsraw_rawDirOps_unlinkAt_dirFlagSemantics`. -/
theorem reach_fsraw_rawDirOps_unlinkAt_dirFlagSemantics :
    CanReach (test_fsraw_rawDirOps_unlinkAt_dirFlagSemantics vfsDirOps) := by
  dsimp only [CanReach, test_fsraw_rawDirOps_unlinkAt_dirFlagSemantics,
    NondetTest.nondet, NondetTest.assume, NondetTest.assert, Bind.bind, Pure.pure, bind, pure, StateT.run]
  refine ⟨cleanVfsRootState, cleanDh0, sampleEntryA, ?_, ?_, ?_, ?_⟩
  · exact ⟨vfsToStat (.dir 0o755), rfl, rfl, by decide, by decide⟩
  · exact ⟨⟨_, rfl, rfl⟩, rfl⟩
  · exact ⟨⟨_, rfl, rfl⟩, rfl⟩
  · have hAll := unlinkAt_jp_allPass cleanVfsRootState sampleEntryA
    dsimp only [unlinkAtJpProp, unlinkAtJpMid, unlinkAtJpTail] at hAll
    have hOp : vfsDirOps.openDir "/" cleanVfsRootState =
        (.ok { handleId := 3, rootPath := "/" },
          { cleanVfsRootState with openDirs := (3, []) :: cleanVfsRootState.openDirs, nextDirId := 4 }) := rfl
    rw [hOp] at hAll ⊢
    dsimp only at hAll ⊢
    exact ⟨sampleEntryB, hAll sampleEntryB⟩

/-- `AllPass` proof for `test_fsraw_rawDirOps_closedHandleRejected`. -/
theorem proof_fsraw_rawDirOps_closedHandleRejected :
    AllPass (test_fsraw_rawDirOps_closedHandleRejected vfsDirOps) := by
  dsimp only [AllPass, test_fsraw_rawDirOps_closedHandleRejected,
    NondetTest.nondet, NondetTest.assume, NondetTest.assert, Bind.bind, Pure.pure, bind, pure, StateT.run]
  intro s₀ root child bytes
  have hZ : lookupDir s₀ { handleId := 0, rootPath := "/" } = none := lookupDir_zero s₀ "/"
  have hSpec0 := spec_invalidHandleRefused s₀ { handleId := 0, rootPath := "/" } cleanDh0 child child bytes false false "" .exclusive hZ
  refine ⟨hSpec0.2.2.1.1, hSpec0.2.1.1, ?_⟩
  cases hOp1 : vfsDirOps.openDir root s₀ with
  | mk openRes s1 =>
    dsimp only
    cases openRes with
    | error _ => trivial
    | ok dh =>
      dsimp only
      cases hOp2 : vfsDirOps.openDir root s1 with
      | mk liveRes s1' =>
        dsimp only
        cases hCl : vfsDirOps.closeDir dh s1' with
        | mk closeRes s2 =>
          dsimp only
          rcases vfsDirOps_openDir_ok root s₀ dh s1 hOp1 with ⟨hDhPos, _, _, _, hS1⟩
          have hAnyClose : (s1'.openDirs.any fun x => x.1 == dh.handleId) = true := by
            rw [List.any_eq_true]
            have hInS1 : ∃ p, (dh.handleId, p) ∈ s1.openDirs := ⟨_, by rw [hS1]; exact List.mem_cons_self⟩
            cases liveRes with
            | error _ =>
              rw [vfsDirOps_openDir_err root s1 _ s1' hOp2]
              exact ⟨_, hInS1.choose_spec, by simp⟩
            | ok liveDh =>
              rcases vfsDirOps_openDir_ok root s1 liveDh s1' hOp2 with ⟨_, _, _, _, hS1'⟩
              rw [hS1']
              exact ⟨_, List.mem_cons_of_mem _ hInS1.choose_spec, by simp⟩
          have hCloseDef : vfsDirOps.closeDir dh s1' =
              (.ok (), { s1' with openDirs := s1'.openDirs.filter (fun p => p.1 != dh.handleId) }) := by
            rw [vfsDirOps_closeDir_def]
            simp only [beq_false_of_ne (Nat.ne_of_gt hDhPos), Bool.false_eq_true, ↓reduceIte, hAnyClose]
          rw [hCloseDef] at hCl
          injection hCl with hResOk hS2Eq
          subst hS2Eq
          have hClosedNone : lookupDir { s1' with openDirs := s1'.openDirs.filter (fun p => p.1 != dh.handleId) } dh = none :=
            lookupDir_erase_self s1' dh
          have hSpec := spec_invalidHandleRefused _ dh dh child child bytes false true "t" .exclusive hClosedNone
          refine ⟨hResOk.symm,
            hSpec.2.2.1.1,
            hSpec.2.2.2.1.1,
            hSpec.2.2.2.2.1.1,
            hSpec.1.1,
            hSpec.2.2.2.2.2.1.1,
            hSpec.2.2.2.2.2.2.1.1,
            hSpec.2.2.2.2.2.2.2.1.1,
            hSpec.2.2.2.2.2.2.2.2.1.1,
            hSpec.2.2.2.2.2.2.2.2.2.2.1.1,
            hSpec.2.2.2.2.2.2.2.2.2.2.2.1.1,
            hSpec.2.2.2.2.2.2.2.2.2.2.2.2.1,
            hSpec.2.1.1,
            ?_⟩
          cases liveRes with
          | error _ => trivial
          | ok liveDh =>
            by_cases hNe : (liveDh.handleId != dh.handleId) = true
            · simp only [hNe, ↓reduceIte]
              have hSpecL := spec_invalidHandleRefused _ dh liveDh child child bytes false true "t" .exclusive hClosedNone
              exact ⟨hSpecL.2.2.2.2.2.2.2.2.1.1, hSpecL.2.2.2.2.2.2.2.2.2.1.1, trivial⟩
            · have hNeF : (liveDh.handleId != dh.handleId) = false := Bool.eq_false_iff.mpr hNe
              simp only [hNeF, Bool.false_eq_true, ↓reduceIte]

/-- `CanReach` witness for `test_fsraw_rawDirOps_closedHandleRejected`. -/
theorem reach_fsraw_rawDirOps_closedHandleRejected :
    CanReach (test_fsraw_rawDirOps_closedHandleRejected vfsDirOps) := by
  dsimp only [CanReach, test_fsraw_rawDirOps_closedHandleRejected,
    NondetTest.nondet, NondetTest.assume, NondetTest.assert, Bind.bind, Pure.pure, bind, pure, StateT.run]
  refine ⟨cleanVfsRootState, "/", sampleEntryA, ByteArray.empty, ?_⟩
  have hAll := proof_fsraw_rawDirOps_closedHandleRejected cleanVfsRootState "/" sampleEntryA ByteArray.empty
  dsimp only [AllPass, test_fsraw_rawDirOps_closedHandleRejected,
    NondetTest.nondet, NondetTest.assume, NondetTest.assert, Bind.bind, Pure.pure, bind, pure, StateT.run] at hAll
  rcases hAll with ⟨h1, h2, hRest⟩
  refine ⟨h1, h2, ?_⟩
  cases hOp1 : vfsDirOps.openDir "/" cleanVfsRootState with
  | mk r1 s1 =>
    dsimp only
    rw [hOp1] at hRest
    dsimp only at hRest
    cases r1 with
    | error _ => exact hRest
    | ok dh =>
      dsimp only
      cases hOp2 : vfsDirOps.openDir "/" s1 with
      | mk r2 s1' =>
        dsimp only
        rw [hOp2] at hRest
        dsimp only at hRest
        cases hCl : vfsDirOps.closeDir dh s1' with
        | mk rCl s2 =>
          dsimp only
          rw [hCl] at hRest
          dsimp only at hRest
          exact hRest

/-- `AllPass` proof for `test_fsraw_rawDirOps_fstatDir_validReturnsDir`. -/
theorem proof_fsraw_rawDirOps_fstatDir_validReturnsDir :
    AllPass (test_fsraw_rawDirOps_fstatDir_validReturnsDir vfsDirOps) := by
  dsimp only [AllPass, test_fsraw_rawDirOps_fstatDir_validReturnsDir,
    NondetTest.nondet, NondetTest.assume, NondetTest.assert, Bind.bind, Pure.pure, bind, pure, StateT.run]
  intro s₀ root
  cases hOp : vfsDirOps.openDir root s₀ with
  | mk openRes s1 =>
    cases openRes with
    | error _ => trivial
    | ok dh =>
      dsimp only
      rcases vfsDirOps_openDir_ok_resolved root s₀ dh s1 hOp with
        ⟨hPos, _, _, canon, m, hRes, _, hS1⟩
      have hNodeCanon : s1.nodes canon = some (.dir m) := by
        have hEq := subtreeVfsResolveSegs_ok_node s₀.nodes 1024 "/" (vfsSplitSegs (vfsAbsNorm s₀.cwd root)) true canon (.dir m) hRes
        change vfsTreeNodes s₀.tree canon = some (.dir m) at hEq
        change vfsTreeNodes s1.tree canon = some (.dir m)
        rw [hS1]
        exact hEq
      have hIsCanon : isCanonPath canon = true := by
        cases hNd : isCanonPath canon with
        | true => rfl
        | false =>
          change vfsTreeNodes s1.tree canon = some (.dir m) at hNodeCanon
          simp [vfsTreeNodes, hNd] at hNodeCanon
      have hNodeSplit : nodeAt s1.tree (vfsSplitSegs canon) = some (.dir m) := by
        change vfsTreeNodes s1.tree canon = some (.dir m) at hNodeCanon
        simpa [vfsTreeNodes, hIsCanon] using hNodeCanon
      have hLd : lookupDir s1 dh = some (vfsSplitSegs canon) := by
        rw [hS1]
        exact lookupDir_cons_self s₀ dh.handleId (vfsSplitSegs canon) dh.rootPath hPos
      rw [vfsDirOps_fstatDir_def, hLd]
      dsimp only
      rw [hNodeSplit]
      exact ⟨⟨⟨vfsToStat (.dir m), rfl, rfl⟩, rfl⟩, trivial⟩

/-- `CanReach` witness for `test_fsraw_rawDirOps_fstatDir_validReturnsDir`. -/
theorem reach_fsraw_rawDirOps_fstatDir_validReturnsDir :
    CanReach (test_fsraw_rawDirOps_fstatDir_validReturnsDir vfsDirOps) := by
  dsimp only [CanReach, test_fsraw_rawDirOps_fstatDir_validReturnsDir,
    NondetTest.nondet, NondetTest.assume, NondetTest.assert, Bind.bind, Pure.pure, bind, pure, StateT.run]
  refine ⟨cleanVfsRootState, "/", ?_⟩
  exact proof_fsraw_rawDirOps_fstatDir_validReturnsDir cleanVfsRootState "/"

/-- `AllPass` proof for `test_fsraw_rawDirOps_readDirAt_sortedUnique`. -/
theorem proof_fsraw_rawDirOps_readDirAt_sortedUnique :
    AllPass (test_fsraw_rawDirOps_readDirAt_sortedUnique vfsDirOps) := by
  dsimp only [AllPass, test_fsraw_rawDirOps_readDirAt_sortedUnique,
    NondetTest.nondet, NondetTest.assume, NondetTest.assert, Bind.bind, Pure.pure, bind, pure, StateT.run]
  intro s₀ dh
  rw [vfsDirOps_readDirAt_def]
  dsimp only
  cases lookupDir s₀ dh with
  | none => exact ⟨rfl, trivial⟩
  | some pos =>
    dsimp only
    cases hNd : nodeAt s₀.tree pos with
    | none => exact ⟨rfl, trivial⟩
    | some nd =>
      cases nd with
      | file _ _ => exact ⟨rfl, trivial⟩
      | symlink _ _ => exact ⟨rfl, trivial⟩
      | dir _ =>
        dsimp only
        split
        · exact ⟨rfl, trivial⟩
        · exact ⟨⟨mVfsReadDirAtEntries_nodup s₀ pos, rfl⟩, trivial⟩

/-- `CanReach` witness for `test_fsraw_rawDirOps_readDirAt_sortedUnique`. -/
theorem reach_fsraw_rawDirOps_readDirAt_sortedUnique :
    CanReach (test_fsraw_rawDirOps_readDirAt_sortedUnique vfsDirOps) := by
  dsimp only [CanReach, test_fsraw_rawDirOps_readDirAt_sortedUnique,
    NondetTest.nondet, NondetTest.assume, NondetTest.assert, Bind.bind, Pure.pure, bind, pure, StateT.run]
  exact ⟨cleanVfsRootState, cleanDh0, ⟨List.nodup_nil, rfl⟩, trivial⟩

/-- `AllPass` proof for `test_fsraw_rawDirOps_renameAt_moveAndTypeMismatch`. -/
theorem proof_fsraw_rawDirOps_renameAt_moveAndTypeMismatch :
    AllPass (test_fsraw_rawDirOps_renameAt_moveAndTypeMismatch vfsDirOps) := by
  dsimp only [AllPass, test_fsraw_rawDirOps_renameAt_moveAndTypeMismatch,
    NondetTest.nondet, NondetTest.assume, NondetTest.assert, Bind.bind, Pure.pure, bind, pure, StateT.run]
  intro s₀ srcDh srcName dstDh dstName ⟨sdSt, hSF, hSKind, hSW, hSX⟩ ⟨ddSt, hDF, hDKind, hDW, hDX⟩
  rcases fstatDir_ok_dir s₀ srcDh sdSt hSF hSKind hSW hSX with ⟨srcPos, srcMode, hSLd, hSPar, hSWF, hSXF⟩
  rcases fstatDir_ok_dir s₀ dstDh ddSt hDF hDKind hDW hDX with ⟨dstPos, dstMode, hDLd, hDPar, hDWF, hDXF⟩
  rw [vfsDirOps_lstatAt_def, hSLd]
  dsimp only
  rw [hSPar]
  dsimp only
  simp only [show ((srcMode / 64 % 2 == 0) = false) from hSXF, Bool.false_eq_true, ↓reduceIte]
  cases hSrcNd : nodeAt s₀.tree (srcPos ++ [srcName.val]) with
  | none =>
    dsimp only
    simp only [show (FsErrorKind.notFound == FsErrorKind.notFound) = true from rfl, ↓reduceIte]
    rw [vfsDirOps_renameAt_def, hSLd, hDLd]
    dsimp only
    rw [hSPar, hDPar]
    dsimp only
    simp only [hSWF, hSXF, hDWF, hDXF, Bool.false_eq_true, Bool.or_self, ↓reduceIte]
    have hSrcGetNone : vfsTreeGet s₀.tree (srcPos ++ [srcName.val]) = none := by
      cases hG : vfsTreeGet s₀.tree (srcPos ++ [srcName.val]) with
      | none => rfl
      | some sub => simp [nodeAt, hG] at hSrcNd
    rw [hSrcGetNone]
    exact ⟨⟨⟨_, rfl, rfl⟩, rfl⟩, trivial⟩
  | some srcNode =>
    dsimp only
    rw [vfsDirOps_lstatAt_def, hDLd]
    dsimp only
    rw [hDPar]
    dsimp only
    simp only [show ((dstMode / 64 % 2 == 0) = false) from hDXF, Bool.false_eq_true, ↓reduceIte]
    cases hDstNd : nodeAt s₀.tree (dstPos ++ [dstName.val]) with
    | some dstNode =>
      dsimp only
      by_cases hC1 : ((vfsToStat srcNode).kind == .dir && (vfsToStat dstNode).kind == .file) = true
      · simp only [hC1, ↓reduceIte]
        cases srcNode with
        | file _ _ =>
          simp [vfsToStat, show (EntryKind.file == EntryKind.dir) = false from rfl] at hC1
        | symlink _ _ =>
          simp [vfsToStat, show (EntryKind.symlink == EntryKind.dir) = false from rfl] at hC1
        | dir sm =>
          cases dstNode with
          | dir _ =>
            simp [vfsToStat, show (EntryKind.dir == EntryKind.file) = false from rfl] at hC1
          | symlink _ _ =>
            simp [vfsToStat, show (EntryKind.symlink == EntryKind.file) = false from rfl] at hC1
          | file bs fm =>
            rcases vfsTreeGet_dir_of_nodeAt hSrcNd with ⟨ch, hSG⟩
            have hNe : srcPos ++ [srcName.val] ≠ dstPos ++ [dstName.val] := by
              intro hEq; rw [hEq, hDstNd] at hSrcNd; cases hSrcNd
            rw [vfsDirOps_renameAt_def, hSLd, hDLd]
            dsimp only
            rw [hSPar, hDPar]
            dsimp only
            simp only [hSWF, hSXF, hDWF, hDXF, Bool.false_eq_true, Bool.or_self, ↓reduceIte, hSG,
              beq_false_of_ne hNe]
            by_cases hSameId : (srcDh.handleId == dstDh.handleId) = true
            · simp only [hSameId, ↓reduceIte]
              have hPosEq : srcPos = dstPos := by
                have hEq := lookupDir_eq_of_handleId_eq s₀ srcDh dstDh (beq_iff_eq.mp hSameId)
                rw [hSLd, hDLd] at hEq
                exact Option.some.inj hEq
              have hNotPref : (srcPos ++ [srcName.val]).isPrefixOf dstPos = false := by
                rw [Bool.eq_false_iff]
                intro hPre
                have hLen := List.IsPrefix.length_le (List.isPrefixOf_iff_prefix.mp hPre)
                rw [← hPosEq] at hLen
                simp at hLen
                omega
              simp only [hNotPref, Bool.false_eq_true, ↓reduceIte, hDstNd]
              exact ⟨⟨⟨_, rfl, rfl⟩, trivial⟩, trivial⟩
            · have hDiffId : (srcDh.handleId == dstDh.handleId) = false := Bool.eq_false_iff.mpr hSameId
              simp only [hDiffId, Bool.false_eq_true, ↓reduceIte]
              by_cases hPref : (srcPos ++ [srcName.val]).isPrefixOf dstPos = true
              · simp only [hPref, ↓reduceIte]
                exact ⟨⟨⟨_, rfl, Or.inr rfl⟩, trivial⟩, trivial⟩
              · have hPrefF : (srcPos ++ [srcName.val]).isPrefixOf dstPos = false := Bool.eq_false_iff.mpr hPref
                simp only [hPrefF, Bool.false_eq_true, ↓reduceIte, hDstNd]
                exact ⟨⟨⟨_, rfl, Or.inl rfl⟩, trivial⟩, trivial⟩
      · have hC1F : ((vfsToStat srcNode).kind == .dir && (vfsToStat dstNode).kind == .file) = false :=
          Bool.eq_false_iff.mpr hC1
        simp only [hC1F, Bool.false_eq_true, ↓reduceIte]
        by_cases hC2 : ((vfsToStat srcNode).kind == .file && (vfsToStat dstNode).kind == .dir) = true
        · simp only [hC2, ↓reduceIte]
          cases srcNode with
          | dir _ =>
            simp [vfsToStat, show (EntryKind.dir == EntryKind.file) = false from rfl] at hC2
          | symlink _ _ =>
            simp [vfsToStat, show (EntryKind.symlink == EntryKind.file) = false from rfl] at hC2
          | file bs fm =>
            cases dstNode with
            | file _ _ =>
              simp [vfsToStat, show (EntryKind.file == EntryKind.dir) = false from rfl] at hC2
            | symlink _ _ =>
              simp [vfsToStat, show (EntryKind.symlink == EntryKind.dir) = false from rfl] at hC2
            | dir dm =>
              have hSG : ∃ bs' fm', vfsTreeGet s₀.tree (srcPos ++ [srcName.val]) = some (.file bs' fm') := by
                cases hG : vfsTreeGet s₀.tree (srcPos ++ [srcName.val]) with
                | none => simp [nodeAt, hG] at hSrcNd
                | some fsub =>
                  simp only [nodeAt, hG, Option.map_some, Option.some.injEq] at hSrcNd
                  cases fsub <;> simp [vfsTreeTopNode] at hSrcNd
                  exact ⟨_, _, rfl⟩
              rcases hSG with ⟨bs', fm', hSG⟩
              have hNe : srcPos ++ [srcName.val] ≠ dstPos ++ [dstName.val] := by
                intro hEq; rw [hEq, hDstNd] at hSrcNd; cases hSrcNd
              have hPrefF : (srcPos ++ [srcName.val]).isPrefixOf dstPos = false := by
                rw [Bool.eq_false_iff]
                intro hPre
                rcases List.isPrefixOf_iff_prefix.mp hPre with ⟨rest, hDstEq⟩
                have hD : nodeAt s₀.tree ((srcPos ++ [srcName.val]) ++ rest) = some (.dir dstMode) := by
                  simpa [← hDstEq] using hDPar
                cases rest with
                | nil => simp only [List.append_nil] at hD; rw [hSrcNd] at hD; cases hD
                | cons _ _ =>
                  rw [nodeAt_file_none_desc s₀.tree _ (_ :: _) bs' fm' hSG (by simp)] at hD
                  cases hD
              rw [vfsDirOps_renameAt_def, hSLd, hDLd]
              dsimp only
              rw [hSPar, hDPar]
              dsimp only
              simp only [hSWF, hSXF, hDWF, hDXF, Bool.false_eq_true, Bool.or_self, ↓reduceIte, hSG,
                beq_false_of_ne hNe, hPrefF, hDstNd]
              exact ⟨⟨⟨_, rfl, rfl⟩, trivial⟩, trivial⟩
        · have hC2F : ((vfsToStat srcNode).kind == .file && (vfsToStat dstNode).kind == .dir) = false :=
            Bool.eq_false_iff.mpr hC2
          simp [hC2F]
    | none =>
      dsimp only
      rw [show (FsErrorKind.notFound == FsErrorKind.notFound) = true from rfl, Bool.true_and]
      by_cases hCond : ((vfsToStat srcNode).kind == .file && (srcDh.handleId != dstDh.handleId || srcName != dstName)) = true
      · simp only [hCond, ↓reduceIte]
        cases srcNode with
        | dir _ =>
          simp [vfsToStat, show (EntryKind.dir == EntryKind.file) = false from rfl] at hCond
        | symlink _ _ =>
          simp [vfsToStat, show (EntryKind.symlink == EntryKind.file) = false from rfl] at hCond
        | file bs fm =>
          have hSG : ∃ bs' fm', vfsTreeGet s₀.tree (srcPos ++ [srcName.val]) = some (.file bs' fm') := by
            cases hG : vfsTreeGet s₀.tree (srcPos ++ [srcName.val]) with
            | none => simp [nodeAt, hG] at hSrcNd
            | some sub =>
              simp only [nodeAt, hG, Option.map_some, Option.some.injEq] at hSrcNd
              cases sub <;> simp [vfsTreeTopNode] at hSrcNd
              exact ⟨_, _, rfl⟩
          rcases hSG with ⟨bs', fm', hSG⟩
          have hNe : srcPos ++ [srcName.val] ≠ dstPos ++ [dstName.val] := by
            intro hEq; rw [hEq, hDstNd] at hSrcNd; cases hSrcNd
          have hNotSrcPrefDstPos : ¬ (srcPos ++ [srcName.val] <+: dstPos) := by
            intro hPre
            rcases hPre with ⟨rest, hDstEq⟩
            have hD : nodeAt s₀.tree ((srcPos ++ [srcName.val]) ++ rest) = some (.dir dstMode) := by
              simpa [← hDstEq] using hDPar
            cases rest with
            | nil => simp only [List.append_nil] at hD; rw [hSrcNd] at hD; cases hD
            | cons _ _ =>
              rw [nodeAt_file_none_desc s₀.tree _ (_ :: _) bs' fm' hSG (by simp)] at hD
              cases hD
          have hPrefF : (srcPos ++ [srcName.val]).isPrefixOf dstPos = false := by
            rw [Bool.eq_false_iff]
            intro hPre
            exact hNotSrcPrefDstPos (List.isPrefixOf_iff_prefix.mp hPre)
          rw [vfsDirOps_renameAt_def, hSLd, hDLd]
          dsimp only
          rw [hSPar, hDPar]
          dsimp only
          simp only [hSWF, hSXF, hDWF, hDXF, Bool.false_eq_true, Bool.or_self, ↓reduceIte, hSG,
            beq_false_of_ne hNe, hPrefF, hDstNd]
          have hSrcDirGet : ∃ dm ch, vfsTreeGet s₀.tree srcPos = some (.dir dm ch) := ⟨srcMode, vfsTreeGet_dir_of_nodeAt hSPar⟩
          have hNotSrcPrefSrcPos : ¬ (srcPos ++ [srcName.val] <+: srcPos) := by
            intro hPre; have hL := List.IsPrefix.length_le hPre; simp at hL; omega
          have hNotDstPrefDstPos : ¬ (dstPos ++ [dstName.val] <+: dstPos) := by
            intro hPre; have hL := List.IsPrefix.length_le hPre; simp at hL; omega
          have hNotDstPrefSrcPos : ¬ (dstPos ++ [dstName.val] <+: srcPos) := by
            intro hPre
            rcases hPre with ⟨rest, hEq⟩
            have hN : nodeAt s₀.tree ((dstPos ++ [dstName.val]) ++ rest) = none :=
              nodeAt_none_desc s₀.tree (dstPos ++ [dstName.val]) rest hDstNd
            rw [hEq, hSPar] at hN
            cases hN
          have hNotDstPrefSrcFull : ¬ (dstPos ++ [dstName.val] <+: srcPos ++ [srcName.val]) := by
            intro hPre
            rcases hPre with ⟨rest, hEq⟩
            have hN : nodeAt s₀.tree ((dstPos ++ [dstName.val]) ++ rest) = none :=
              nodeAt_none_desc s₀.tree (dstPos ++ [dstName.val]) rest hDstNd
            rw [hEq, hSrcNd] at hN
            cases hN
          let tr1 := vfsTreeSet s₀.tree (srcPos ++ [srcName.val]) none
          let tr2 := vfsTreeSet tr1 (dstPos ++ [dstName.val]) (some (.file bs' fm'))
          have hDPar1 : nodeAt tr1 dstPos = some (.dir dstMode) := by
            rw [nodeAt_vfsTreeSet_outside s₀.tree srcPos srcName.val none dstPos hSrcDirGet hNotSrcPrefDstPos, hDPar]
          have hDDirGet1 : ∃ dm ch, vfsTreeGet tr1 dstPos = some (.dir dm ch) := ⟨dstMode, vfsTreeGet_dir_of_nodeAt hDPar1⟩
          have hDPar2 : nodeAt tr2 dstPos = some (.dir dstMode) := by
            rw [nodeAt_vfsTreeSet_outside tr1 dstPos dstName.val _ dstPos hDDirGet1 hNotDstPrefDstPos, hDPar1]
          have hSPar1 : nodeAt tr1 srcPos = some (.dir srcMode) := by
            rw [nodeAt_vfsTreeSet_outside s₀.tree srcPos srcName.val none srcPos hSrcDirGet hNotSrcPrefSrcPos, hSPar]
          have hSPar2 : nodeAt tr2 srcPos = some (.dir srcMode) := by
            rw [nodeAt_vfsTreeSet_outside tr1 dstPos dstName.val _ srcPos hDDirGet1 hNotDstPrefSrcPos, hSPar1]
          have hDstLeaf2 : nodeAt tr2 (dstPos ++ [dstName.val]) = some (.file bs' fm') := by
            simpa [tr2, vfsTreeTopNode] using
              nodeAt_vfsTreeSet_eq tr1 dstPos dstName.val (some (.file bs' fm')) hDDirGet1
          have hSrcLeaf1 : nodeAt tr1 (srcPos ++ [srcName.val]) = none := by
            simpa [tr1] using nodeAt_vfsTreeSet_eq s₀.tree srcPos srcName.val none hSrcDirGet
          have hSrcLeaf2 : nodeAt tr2 (srcPos ++ [srcName.val]) = none := by
            rw [nodeAt_vfsTreeSet_outside tr1 dstPos dstName.val _ (srcPos ++ [srcName.val]) hDDirGet1 hNotDstPrefSrcFull, hSrcLeaf1]
          let newKeys := pathOfSegs (dstPos ++ [dstName.val]) :: mRemapKeysAfterRename s₀.keys (srcPos ++ [srcName.val]) (dstPos ++ [dstName.val])
          let sNew : VfsState := { s₀ with tree := tr2, keys := newKeys }
          have hDstLdNew : lookupDir sNew dstDh = some dstPos := hDLd
          have hSrcLdNew : lookupDir sNew srcDh = some srcPos := hSLd
          dsimp only [tr2, tr1] at hDstLeaf2 hSrcLeaf2
          refine ⟨trivial, ?_, ?_, trivial⟩
          · refine ⟨vfsToStat (.file bs' fm'), ?_, rfl⟩
            rw [vfsDirOps_lstatAt_def]
            dsimp only
            rw [hDstLdNew]
            dsimp only
            rw [hDPar2]
            simp [hDXF, hDstLeaf2]
          · refine ⟨{
              kind := .notFound
              path := some srcName.val
              message := toString "no such file or directory: " ++ toString srcName.val }, ?_, rfl⟩
            rw [vfsDirOps_lstatAt_def]
            dsimp only
            rw [hSrcLdNew]
            dsimp only
            rw [hSPar2]
            simp [hSXF, hSrcLeaf2]
      · have hCondF : ((vfsToStat srcNode).kind == .file && (srcDh.handleId != dstDh.handleId || srcName != dstName)) = false :=
          Bool.eq_false_iff.mpr hCond
        simp only [hCondF, Bool.false_eq_true, ↓reduceIte]

/-- `CanReach` witness for `test_fsraw_rawDirOps_renameAt_moveAndTypeMismatch`. -/
theorem reach_fsraw_rawDirOps_renameAt_moveAndTypeMismatch :
    CanReach (test_fsraw_rawDirOps_renameAt_moveAndTypeMismatch vfsDirOps) := by
  dsimp only [CanReach, test_fsraw_rawDirOps_renameAt_moveAndTypeMismatch,
    NondetTest.nondet, NondetTest.assume, NondetTest.assert, Bind.bind, Pure.pure, bind, pure, StateT.run]
  let st : VfsState :=
    { cleanVfsRootState with
      tree := vfsTreeSet cleanVfsRootState.tree ["a"] (some (.file ByteArray.empty 0o644))
      keys := ["/a", "/"] }
  have hAll := proof_fsraw_rawDirOps_renameAt_moveAndTypeMismatch st cleanDh0 sampleEntryA cleanDh0 sampleEntryB
    ⟨vfsToStat (.dir 0o755), rfl, rfl, by decide, by decide⟩
    ⟨vfsToStat (.dir 0o755), rfl, rfl, by decide, by decide⟩
  dsimp only [AllPass, test_fsraw_rawDirOps_renameAt_moveAndTypeMismatch,
    NondetTest.nondet, NondetTest.assume, NondetTest.assert, Bind.bind, Pure.pure, bind, pure, StateT.run] at hAll
  refine ⟨st, cleanDh0, sampleEntryA, cleanDh0, sampleEntryB,
    ⟨vfsToStat (.dir 0o755), rfl, rfl, by decide, by decide⟩,
    ⟨vfsToStat (.dir 0o755), rfl, rfl, by decide, by decide⟩,
    hAll⟩

/-- `AllPass` proof for `test_fsraw_rawDirOps_symlinkAt_validAndRejectsInvalidTarget`. -/
theorem proof_fsraw_rawDirOps_symlinkAt_validAndRejectsInvalidTarget :
    AllPass (test_fsraw_rawDirOps_symlinkAt_validAndRejectsInvalidTarget vfsDirOps) := by
  dsimp only [AllPass, test_fsraw_rawDirOps_symlinkAt_validAndRejectsInvalidTarget,
    NondetTest.nondet, NondetTest.assume, NondetTest.assert, Bind.bind, Pure.pure, bind, pure, StateT.run]
  intro s₀ dh child target
  have hContains : target.contains (Char.ofNat 0) = target.toList.contains (Char.ofNat 0) := by
    simp [String.contains_char_eq]
  by_cases hBad : (target.isEmpty || target.contains (Char.ofNat 0)) = true
  · simp only [hBad, ↓reduceIte]
    rw [vfsDirOps_symlinkAt_def]
    have hBad' : (target.isEmpty || target.toList.contains (Char.ofNat 0)) = true := hContains ▸ hBad
    rw [hBad']
    dsimp only
    exact ⟨⟨⟨_, rfl, rfl⟩, rfl⟩, trivial⟩
  · have hGood : (target.isEmpty || target.contains (Char.ofNat 0)) = false := Bool.eq_false_iff.mpr hBad
    have hGood' : (target.isEmpty || target.toList.contains (Char.ofNat 0)) = false := hContains ▸ hGood
    simp only [hGood, Bool.false_eq_true, ↓reduceIte]
    intro ⟨dSt, hF, hKind, hW, hX⟩
    rcases fstatDir_ok_dir s₀ dh dSt hF hKind hW hX with ⟨pos, pm, hLd, hPar, hWF, hXF⟩
    rw [vfsDirOps_lstatAt_def, hLd]
    dsimp only
    rw [hPar]
    simp only [hXF, Bool.false_eq_true, ↓reduceIte]
    cases hNd : nodeAt s₀.tree (pos ++ [child.val]) with
    | some _ => trivial
    | none =>
      dsimp only
      simp only [show (FsErrorKind.notFound == FsErrorKind.notFound) = true from rfl, ↓reduceIte]
      rw [vfsDirOps_symlinkAt_def]
      simp only [hGood', Bool.false_eq_true, ↓reduceIte, hLd]
      rw [hPar]
      simp only [hWF, hXF, Bool.or_self, Bool.false_eq_true, ↓reduceIte, hNd]
      have hDirGet : ∃ dm ch, vfsTreeGet s₀.tree pos = some (.dir dm ch) := ⟨pm, vfsTreeGet_dir_of_nodeAt hPar⟩
      have hNotPre : ¬ (pos ++ [child.val] <+: pos) := by
        intro hPre; have hL := List.IsPrefix.length_le hPre; simp at hL; omega
      have hPar1 : nodeAt (vfsTreeSet s₀.tree (pos ++ [child.val]) (some (.symlink target 511))) pos = some (.dir pm) := by
        rw [nodeAt_vfsTreeSet_outside s₀.tree pos child.val _ pos hDirGet hNotPre, hPar]
      have hLeaf1 : nodeAt (vfsTreeSet s₀.tree (pos ++ [child.val]) (some (.symlink target 511))) (pos ++ [child.val]) =
          some (.symlink target 511) := by
        simpa [vfsTreeTopNode] using nodeAt_vfsTreeSet_eq s₀.tree pos child.val (some (.symlink target 511)) hDirGet
      let sNew : VfsState :=
        { s₀ with
          tree := vfsTreeSet s₀.tree (pos ++ [child.val]) (some (.symlink target 511))
          keys := pathOfSegs (pos ++ [child.val]) :: s₀.keys }
      have hLdNew : lookupDir sNew dh = some pos := hLd
      refine ⟨⟨trivial, vfsToStat (.symlink target 511), ?_, rfl⟩, trivial⟩
      rw [vfsDirOps_lstatAt_def]
      dsimp only
      rw [hLdNew]
      dsimp only
      rw [hPar1]
      simp [hXF, hLeaf1]

/-- `CanReach` witness for `test_fsraw_rawDirOps_symlinkAt_validAndRejectsInvalidTarget`. -/
theorem reach_fsraw_rawDirOps_symlinkAt_validAndRejectsInvalidTarget :
    CanReach (test_fsraw_rawDirOps_symlinkAt_validAndRejectsInvalidTarget vfsDirOps) := by
  dsimp only [CanReach, test_fsraw_rawDirOps_symlinkAt_validAndRejectsInvalidTarget,
    NondetTest.nondet, NondetTest.assume, NondetTest.assert, Bind.bind, Pure.pure, bind, pure, StateT.run]
  refine ⟨cleanVfsRootState, cleanDh0, sampleEntryA, "target", ?_⟩
  have hGood : ("target".isEmpty || "target".contains (Char.ofNat 0)) = false := by
    simp [String.contains_char_eq]
  simp only [hGood, Bool.false_eq_true, ↓reduceIte]
  exact ⟨⟨vfsToStat (.dir 0o755), rfl, rfl, by decide, by decide⟩,
    ⟨⟨rfl, vfsToStat (.symlink "target" 511), rfl, rfl⟩, trivial⟩⟩

/-- `AllPass` proof that `vfsDirOps.freshTempName` yields distinct valid segment names. -/
theorem proof_fsraw_rawDirOps_freshTempName_distinctAndValid :
    AllPass (test_fsraw_rawDirOps_freshTempName_distinctAndValid vfsDirOps) := by
  dsimp only [AllPass, test_fsraw_rawDirOps_freshTempName_distinctAndValid,
    NondetTest.nondet, NondetTest.assert, Bind.bind, Pure.pure, bind, pure, StateT.run]
  intro s₀
  rcases vfsDirOps_freshTempName_def s₀ with ⟨hn1, hs1⟩
  rcases vfsDirOps_freshTempName_def (vfsDirOps.freshTempName s₀).2 with ⟨hn2, _⟩
  rw [hs1] at hn2
  dsimp only at hn2
  refine ⟨⟨(vfsDirOps.freshTempName s₀).1.valid, (vfsDirOps.freshTempName (vfsDirOps.freshTempName s₀).2).1.valid, ?_⟩, trivial⟩
  intro hEq
  have hVal : (vfsDirOps.freshTempName s₀).1.val = (vfsDirOps.freshTempName (vfsDirOps.freshTempName s₀).2).1.val :=
    congrArg EntryName.val hEq
  rw [hn1, hs1, hn2] at hVal
  have hL : (".t." ++ toString s₀.nonce).toList = (".t." ++ toString (s₀.nonce + 1)).toList :=
    congrArg String.toList hVal
  simp only [String.toList_append] at hL
  have hStr : toString s₀.nonce = toString (s₀.nonce + 1) := String.ext (List.append_cancel_left hL)
  have hNat : s₀.nonce = s₀.nonce + 1 := nat_toString_inj hStr
  omega

/-- `CanReach` witness for `test_fsraw_rawDirOps_freshTempName_distinctAndValid`. -/
theorem reach_fsraw_rawDirOps_freshTempName_distinctAndValid :
    CanReach (test_fsraw_rawDirOps_freshTempName_distinctAndValid vfsDirOps) := by
  dsimp only [CanReach, test_fsraw_rawDirOps_freshTempName_distinctAndValid,
    NondetTest.nondet, NondetTest.assert, Bind.bind, Pure.pure, bind, pure, StateT.run]
  exact ⟨cleanVfsRootState, ⟨by decide, by decide, by intro h; cases h⟩, trivial⟩

end LeanSwe.Fs.Proofs
