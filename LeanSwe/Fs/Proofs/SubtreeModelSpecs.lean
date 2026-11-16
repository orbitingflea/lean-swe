import LeanSwe.Fs.Proofs.SubtreeWalkHelpers

namespace LeanSwe.Fs.Proofs

open Core LeanSwe.Fs LeanSwe.Fs.Raw LeanSwe.Fs.Model

/-- Splitting `pre ++ [leaf]` on its last element returns `some (pre, leaf)`. -/
theorem subtreeSplitLastAux_append_singleton (pre : List EntryName) (leaf : EntryName) :
    Internal.splitLastAux (pre ++ [leaf]) [] = some (pre, leaf) := by
  rcases splitLastAux_prefix_of_append_ne_nil pre [leaf] (List.cons_ne_nil _ _) with
    ⟨parent, leaf', tail, hSp, rfl, hRest⟩
  cases tail with
  | nil =>
    simp only [List.nil_append, List.cons.injEq, and_true] at hRest
    subst hRest
    simpa using hSp
  | cons _ _ =>
    simp at hRest

/-- `walkDescendM` refuses ancestor symlinks with `.invalidInput` and leaves `nodes`, `locks`, and `openDirs` clean. -/
theorem walkDescendM_symlink_err {α : Type} (dh : DirHandle) (pos : List String)
    (pre rest : List EntryName) (t : String) (lm : Nat) (st : VfsState)
    (act : DirHandle → StateM VfsState (Except FsError α))
    (hLd : lookupDir st dh = some pos)
    (hPosDir : ∃ dm, nodeAt st.tree pos = some (.dir dm) ∧ dm / 256 % 2 = 1 ∧ dm / 64 % 2 = 1)
    (hAnc : ∀ k < pre.length, ∃ dm, nodeAt st.tree (pos ++ (pre.take k).map (·.val)) = some (.dir dm) ∧
      dm / 256 % 2 = 1 ∧ dm / 64 % 2 = 1)
    (hSym : nodeAt st.tree (pos ++ pre.map (·.val)) = some (.symlink t lm)) :
    ∃ e st', Internal.walkDescendM vfsDirOps dh (pre ++ rest) act st = (.error e, st') ∧
      e.kind = .invalidInput ∧ st'.nodes = st.nodes ∧ st'.locks = st.locks ∧ st'.openDirs = st.openDirs := by
  rcases walkDescendAuxM_symlink_err pre rest true dh pos st t lm act hLd hPosDir hAnc hSym with
    ⟨e, st', hEq, hKind, hNodes, hLocks, hOpen⟩
  simp only [↓reduceIte] at hOpen
  exact ⟨e, st', hEq, hKind, hNodes, hLocks, hOpen⟩

private theorem walkDescendM_symlink_err_then {α β : Type} (dh : DirHandle) (pos : List String)
    (pre rest : List EntryName) (t : String) (lm : Nat) (st : VfsState)
    (act : DirHandle → StateM VfsState (Except FsError α))
    (cont : Except FsError α → StateM VfsState (Except FsError β))
    (hLd : lookupDir st dh = some pos)
    (hPosDir : ∃ dm, nodeAt st.tree pos = some (.dir dm) ∧ dm / 256 % 2 = 1 ∧ dm / 64 % 2 = 1)
    (hAnc : ∀ k < pre.length, ∃ dm, nodeAt st.tree (pos ++ (pre.take k).map (·.val)) = some (.dir dm) ∧
      dm / 256 % 2 = 1 ∧ dm / 64 % 2 = 1)
    (hSym : nodeAt st.tree (pos ++ pre.map (·.val)) = some (.symlink t lm))
    (hCont : ∀ e st1, cont (.error e) st1 = (.error e, st1)) :
    ∃ e st', (match Internal.walkDescendM vfsDirOps dh (pre ++ rest) act st with | (a, s) => cont a s) =
        (.error e, st') ∧
      e.kind = .invalidInput ∧ st'.nodes = st.nodes ∧ st'.locks = st.locks ∧ st'.openDirs = st.openDirs := by
  rcases walkDescendM_symlink_err dh pos pre rest t lm st act hLd hPosDir hAnc hSym with
    ⟨e, st', hW, hKind, hNodes, hLocks, hOpen⟩
  exact ⟨e, st', by rw [hW]; exact hCont e st', hKind, hNodes, hLocks, hOpen⟩

private theorem walkDescendM_symlink_err_post {α : Type} (dh : DirHandle) (pos : List String)
    (pre rest : List EntryName) (t : String) (lm : Nat) (st : VfsState)
    (act : DirHandle → StateM VfsState (Except FsError α))
    (hLd : lookupDir st dh = some pos)
    (hPosDir : ∃ dm, nodeAt st.tree pos = some (.dir dm) ∧ dm / 256 % 2 = 1 ∧ dm / 64 % 2 = 1)
    (hAnc : ∀ k < pre.length, ∃ dm, nodeAt st.tree (pos ++ (pre.take k).map (·.val)) = some (.dir dm) ∧
      dm / 256 % 2 = 1 ∧ dm / 64 % 2 = 1)
    (hSym : nodeAt st.tree (pos ++ pre.map (·.val)) = some (.symlink t lm)) :
    match Internal.walkDescendM vfsDirOps dh (pre ++ rest) act st with
    | (r, st') => (∃ e, r = .error e ∧ e.kind = .invalidInput) ∧ st'.nodes = st.nodes := by
  rcases walkDescendM_symlink_err dh pos pre rest t lm st act hLd hPosDir hAnc hSym with
    ⟨e, st', hW, hKind, hNodes, _⟩
  rw [hW]
  exact ⟨⟨e, rfl, hKind⟩, hNodes⟩

/-- `walkRecM` refuses ancestor or target symlinks via `walkDescendM` with `.invalidInput`. -/
theorem walkRecM_symlink_err (dh : DirHandle) (pos : List String)
    (pre rest : List EntryName) (t : String) (lm : Nat) (st : VfsState)
    (hLd : lookupDir st dh = some pos)
    (hPosDir : ∃ dm, nodeAt st.tree pos = some (.dir dm) ∧ dm / 256 % 2 = 1 ∧ dm / 64 % 2 = 1)
    (hAnc : ∀ k < pre.length, ∃ dm, nodeAt st.tree (pos ++ (pre.take k).map (·.val)) = some (.dir dm) ∧
      dm / 256 % 2 = 1 ∧ dm / 64 % 2 = 1)
    (hSym : nodeAt st.tree (pos ++ pre.map (·.val)) = some (.symlink t lm)) :
    ∃ e st', Internal.walkRecM vfsDirOps dh (pre ++ rest) "." #[] 4096 st = (.error e, st') ∧
      e.kind = .invalidInput ∧ st'.nodes = st.nodes ∧ st'.locks = st.locks ∧ st'.openDirs = st.openDirs := by
  rw [show (4096 : Nat) = Nat.succ 4095 from rfl, Internal.walkRecM.eq_2]
  simp only [Bind.bind, StateT.bind]
  exact walkDescendM_symlink_err_then dh pos pre rest t lm st _
    (fun (a : Except FsError (List EntryName × List String)) => match a with
      | Except.error e => pure (Except.error e)
      | Except.ok (dirs, files) =>
        Internal.walkChildrenM vfsDirOps dh (pre ++ rest) "." 4095
          (#[].push { root := ".", dirs := (List.map (fun (x : EntryName) => x.val) dirs).toArray, files := files.toArray }) dirs)
    hLd hPosDir hAnc hSym (fun _ _ => rfl)

private theorem rmtree_symlink_err (dh : DirHandle) (pos : List String)
    (pre rest : List EntryName) (hRest : rest ≠ []) (t : String) (lm : Nat) (st : VfsState)
    (ignoreMissing : Bool)
    (hLd : lookupDir st dh = some pos)
    (hPosDir : ∃ dm, nodeAt st.tree pos = some (.dir dm) ∧ dm / 256 % 2 = 1 ∧ dm / 64 % 2 = 1)
    (hAnc : ∀ k < pre.length, ∃ dm, nodeAt st.tree (pos ++ (pre.take k).map (·.val)) = some (.dir dm) ∧
      dm / 256 % 2 = 1 ∧ dm / 64 % 2 = 1)
    (hSym : nodeAt st.tree (pos ++ pre.map (·.val)) = some (.symlink t lm)) :
    ∃ e st', ((Internal.subtreeOpsM vfsDirOps dh).rmtree { segments := pre ++ rest } ignoreMissing st) = (.error e, st') ∧
      e.kind = .invalidInput ∧ st'.nodes = st.nodes ∧ st'.locks = st.locks ∧ st'.openDirs = st.openDirs := by
  rcases splitLastAux_prefix_of_append_ne_nil pre rest hRest with ⟨parent, leaf, tail, hSplit, rfl, _⟩
  dsimp only [Internal.subtreeOpsM]
  rw [hSplit]
  dsimp only
  simp only [Bind.bind, StateT.bind]
  rcases walkDescendM_symlink_err dh pos pre tail t lm st (fun parDh => vfsDirOps.lstatAt parDh leaf)
      hLd hPosDir hAnc hSym with
    ⟨e, st', hW, hKind, hNodes, hLocks, hOpen⟩
  rw [hW]
  dsimp only
  have hNeNotFound : (e.kind == .notFound && ignoreMissing) = false := by
    rw [hKind]
    simp [show (FsErrorKind.invalidInput == FsErrorKind.notFound) = false from rfl]
  simp only [hNeNotFound, Bool.false_eq_true, ↓reduceIte]
  exact ⟨e, st', rfl, hKind, hNodes, hLocks, hOpen⟩

/-- Subtree operations never follow ancestor symlinks and refuse traversal through them with `.invalidInput`. -/
theorem spec_noSymlinkFollowAncestors : SpecNoSymlinkFollowAncestors Internal.subtreeOpsM := by
  intro st dh pos pre rest t lm bytes b1 b2 target lockMode α pureRes rel hLd hRest hAnc hPosDir hSym sub check
  rcases splitLastAux_prefix_of_append_ne_nil pre rest hRest with
    ⟨parent, leaf, tail, hSplit, rfl, _⟩
  have hPreNe : pre ≠ [] := by
    intro h0
    subst h0
    rcases hPosDir with ⟨dm, hDir, _⟩
    rw [List.map_nil, List.append_nil, hDir] at hSym
    cases hSym
  dsimp only [rel, sub, check, StateT.run, Internal.subtreeOpsM]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hSplit]
    dsimp only
    rcases walkDescendM_symlink_err dh pos pre tail t lm st (fun parDh => vfsDirOps.lstatAt parDh leaf)
        hLd hPosDir hAnc hSym with
      ⟨e, st', hW, hKind, hNodes, _⟩
    rw [hW]
    exact ⟨⟨e, rfl, hKind⟩, hNodes⟩
  · rw [hSplit]
    dsimp only
    rcases walkDescendM_symlink_err dh pos pre tail t lm st (fun parDh => vfsDirOps.readRegularAt parDh leaf)
        hLd hPosDir hAnc hSym with
      ⟨e, st', hW, hKind, hNodes, _⟩
    rw [hW]
    exact ⟨⟨e, rfl, hKind⟩, hNodes⟩
  · rw [hSplit]
    dsimp only
    rcases walkDescendM_symlink_err dh pos pre tail t lm st
        (fun parDh => Internal.atomicWriteAtAuxM vfsDirOps parDh leaf bytes 16)
        hLd hPosDir hAnc hSym with
      ⟨e, st', hW, hKind, hNodes, _⟩
    rw [hW]
    exact ⟨⟨e, rfl, hKind⟩, hNodes⟩
  · rw [hSplit]
    dsimp only
    cases b1 with
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte]
      rcases walkDescendM_symlink_err dh pos pre tail t lm st _ hLd hPosDir hAnc hSym with
        ⟨e, st', hW, hKind, hNodes, _⟩
      rw [hW]
      exact ⟨⟨e, rfl, hKind⟩, hNodes⟩
    | true =>
      simp only [↓reduceIte]
      rcases mkdirWalkM_symlink_err pre tail hPreNe true dh pos st t lm _ hLd hPosDir hAnc hSym with
        ⟨e, st', hW, hKind, hNodes, _⟩
      rw [hW]
      exact ⟨⟨e, rfl, hKind⟩, hNodes⟩
  · rw [hSplit]
    dsimp only [bind, StateT.bind, pure, StateT.pure]
    rcases walkDescendM_symlink_err dh pos pre tail t lm st (fun parDh => vfsDirOps.unlinkAt parDh leaf false)
        hLd hPosDir hAnc hSym with
      ⟨e, st', hW, hKind, hNodes, _⟩
    rw [hW]
    dsimp only
    rw [hKind]
    simp only [show (FsErrorKind.invalidInput == FsErrorKind.notFound) = false from rfl,
      Bool.false_and, Bool.false_eq_true, ↓reduceIte]
    exact ⟨⟨e, rfl, hKind⟩, hNodes⟩
  · rw [hSplit]
    dsimp only
    rcases walkDescendM_symlink_err dh pos pre tail t lm st (fun parDh => vfsDirOps.unlinkAt parDh leaf true)
        hLd hPosDir hAnc hSym with
      ⟨e, st', hW, hKind, hNodes, _⟩
    rw [hW]
    exact ⟨⟨e, rfl, hKind⟩, hNodes⟩
  · rcases rmtree_symlink_err dh pos pre rest hRest t lm st b1 hLd hPosDir hAnc hSym with
      ⟨e, st', hW, hKind, hNodes, _⟩
    dsimp only [Internal.subtreeOpsM] at hW
    rw [hW]
    exact ⟨⟨e, rfl, hKind⟩, hNodes⟩
  · rw [hSplit]
    dsimp only
    by_cases hBadT : (target.isEmpty || decide (Char.ofNat 0 ∈ target.toList)) = true
    · simp only [hBadT, ↓reduceIte]
      exact ⟨⟨_, rfl, rfl⟩, rfl⟩
    · simp only [hBadT, Bool.false_eq_true, ↓reduceIte]
      rcases walkDescendM_symlink_err dh pos pre tail t lm st (fun parDh => vfsDirOps.symlinkAt target parDh leaf)
          hLd hPosDir hAnc hSym with
        ⟨e, st', hW, hKind, hNodes, _⟩
      rw [hW]
      exact ⟨⟨e, rfl, hKind⟩, hNodes⟩
  · exact walkDescendM_symlink_err_post dh pos pre rest t lm st _ hLd hPosDir hAnc hSym
  · rcases walkRecM_symlink_err dh pos pre rest t lm st hLd hPosDir hAnc hSym with
      ⟨e, st', hW, hKind, hNodes, _⟩
    rw [hW]
    exact ⟨⟨e, rfl, hKind⟩, hNodes⟩
  · rw [hSplit]
    dsimp only
    simp only [Bind.bind, StateT.bind]
    rcases walkDescendM_symlink_err dh pos pre tail t lm st
        (fun parDh => vfsDirOps.acquireLockAt parDh leaf lockMode b1 false)
        hLd hPosDir hAnc hSym with
      ⟨e, st', hW, hKind, hNodes, _⟩
    rw [hW]
    exact ⟨⟨e, rfl, hKind⟩, hNodes⟩
  · rw [hSplit]
    dsimp only
    simp only [Bind.bind, StateT.bind]
    rcases walkDescendM_symlink_err dh pos pre tail t lm st
        (fun parDh => vfsDirOps.acquireLockAt parDh leaf lockMode b1 true)
        hLd hPosDir hAnc hSym with
      ⟨e, st', hW, hKind, hNodes, _⟩
    rw [hW]
    dsimp only
    have hNeWb : (e.kind == .wouldBlock) = false := by
      rw [hKind]
      decide
    simp only [hNeWb, Bool.false_eq_true, ↓reduceIte]
    exact ⟨⟨e, rfl, hKind⟩, hNodes⟩

private theorem nodes_eq_of_tree_eq (s1 s2 : VfsState) (h : s1.tree = s2.tree) : s1.nodes = s2.nodes := by
  funext p
  change vfsTreeNodes s1.tree p = vfsTreeNodes s2.tree p
  rw [h]

/-- `atomicWriteBytes` replaces a leaf symlink atomically without following it, preserving everything outside `leafPos`. -/
theorem spec_atomicWriteLeafSymlink : SpecAtomicWriteLeafSymlink Internal.subtreeOpsM := by
  intro st dh pos pre leaf t lm bytes rel parentPos leafPos hLd hInv hAnc hPar hSym hTmpNone
  dsimp only [rel, parentPos, leafPos, StateT.run, Internal.subtreeOpsM]
  rw [subtreeSplitLastAux_append_singleton pre leaf]
  dsimp only
  rcases hPar with ⟨pm, hParNd, hW, hX⟩
  have hWalk := walkDescendM_ok pre dh pos st
    (fun parDh => Internal.atomicWriteAtAuxM vfsDirOps parDh leaf bytes 16)
    hLd hInv
    (fun k hk => by
      rcases hAnc k (Nat.le_of_lt hk) with ⟨dm, hD, hR, hEx⟩
      exact ⟨dm, hD, fun _ => hR, hEx⟩)
    (fun _ => by
      rcases hAnc pre.length (Nat.le_refl _) with ⟨dm, hD, hR, _⟩
      simp only [List.take_length] at hD
      exact ⟨dm, hD, hR⟩)
  by_cases hPre : pre = []
  · dsimp only [parentPos, leafPos] at hParNd hTmpNone hSym
    subst hPre
    rw [hWalk.1 rfl]
    simp only [List.map_nil, List.append_nil] at hParNd hTmpNone hSym ⊢
    have hAW := atomicWriteAtAuxM_ok_fresh dh pos leaf bytes 15 st pm hLd hParNd hW hX hTmpNone (by rw [hSym]; trivial)
    cases hRun : Internal.atomicWriteAtAuxM vfsDirOps dh leaf bytes 16 st with
    | mk res st' =>
      rw [hRun] at hAW
      rcases hAW with ⟨rfl, _, hLeaf, hSame, hOpen⟩
      exact ⟨rfl, hLeaf, hSame, hOpen⟩
  · rcases hWalk.2 hPre with
      ⟨leafDh, stMid, hPos, hLdMid, hTreeMid, _, _, hNonceMid, _, _, hLt, hOpenMid, hEq⟩
    rw [hEq, bracketCloseDirM_run]
    have hParMid : nodeAt stMid.tree (pos ++ pre.map (·.val)) = some (.dir pm) := by
      rw [hTreeMid]; exact hParNd
    have hTmpMid : nodeAt stMid.tree ((pos ++ pre.map (·.val)) ++ [".t." ++ toString stMid.nonce]) = none := by
      rw [hTreeMid, hNonceMid]; exact hTmpNone
    have hNotDirMid : match nodeAt stMid.tree ((pos ++ pre.map (·.val)) ++ [leaf.val]) with
        | some (.dir _) => False
        | _ => True := by
      rw [hTreeMid, hSym]
      trivial
    have hAW := atomicWriteAtAuxM_ok_fresh leafDh (pos ++ pre.map (·.val)) leaf bytes 15 stMid pm
      hLdMid hParMid hW hX hTmpMid hNotDirMid
    cases hRun : Internal.atomicWriteAtAuxM vfsDirOps leafDh leaf bytes 16 stMid with
    | mk resAW stAW =>
      rw [hRun] at hAW
      rcases hAW with ⟨rfl, _, hLeafAW, hSameAW, hOpenAW⟩
      dsimp only
      have hClose := vfsDirOps_closeDir_fresh leafDh stAW (pos ++ pre.map (·.val)) hPos st.openDirs
        (hOpenAW.trans hOpenMid) hLt
      rw [hClose]
      dsimp only
      refine ⟨rfl, hLeafAW, ?_, rfl⟩
      intro p hNotPref
      have hMidNodes : stMid.nodes = st.nodes := nodes_eq_of_tree_eq stMid st hTreeMid
      have hCloseNodes : ({ stAW with openDirs := st.openDirs } : VfsState).nodes p = stAW.nodes p := rfl
      change ({ stAW with openDirs := st.openDirs } : VfsState).nodes p = st.nodes p
      rw [hCloseNodes, hSameAW p hNotPref, hMidNodes]

/-- `atomicWriteBytes` followed by `readRegular` and `lstat` returns exact written bytes and mode `0o644`. -/
theorem spec_atomicWriteReadRegularRoundTrip : SpecAtomicWriteReadRegularRoundTrip Internal.subtreeOpsM := by
  intro st dh pos leaf bytes rel hLd hInv hPar hTmpNone hNotDir sub
  dsimp only [rel, sub, StateT.run, Internal.subtreeOpsM]
  rw [show Internal.splitLastAux [leaf] [] = some ([], leaf) from subtreeSplitLastAux_append_singleton [] leaf]
  dsimp only
  rcases hPar with ⟨pm, hParNd, hW, hX⟩
  have hDesc : Internal.walkDescendM vfsDirOps dh []
      (fun parDh => Internal.atomicWriteAtAuxM vfsDirOps parDh leaf bytes 16) st =
      Internal.atomicWriteAtAuxM vfsDirOps dh leaf bytes 16 st :=
    (walkDescendM_ok [] dh pos st _ hLd hInv (fun k hk => by simp at hk) (fun h => absurd rfl h)).1 rfl
  rw [hDesc]
  have hAW := atomicWriteAtAuxM_ok_fresh dh pos leaf bytes 15 st pm hLd hParNd hW hX hTmpNone hNotDir
  cases hRun : Internal.atomicWriteAtAuxM vfsDirOps dh leaf bytes 16 st with
  | mk wRes st₁ =>
    rw [hRun] at hAW
    rcases hAW with ⟨rfl, hPar₁, hLeaf₁, _, hOpen₁⟩
    dsimp only
    have hLd₁ : lookupDir st₁ dh = some pos := by
      unfold lookupDir at hLd ⊢
      rw [hOpen₁]
      exact hLd
    have hXF : (pm / 64 % 2 == 0) = false := by
      rw [hX]
      decide
    refine ⟨rfl, ?_, ?_⟩
    · have hRR : Internal.walkDescendM vfsDirOps dh [] (fun parDh => vfsDirOps.readRegularAt parDh leaf) st₁ =
          vfsDirOps.readRegularAt dh leaf st₁ :=
          rfl
      rw [hRR, vfsDirOps_readRegularAt_def, hLd₁]
      dsimp only
      rw [hPar₁]
      simp only [hXF, Bool.false_eq_true, ↓reduceIte, hLeaf₁]
      simp only [show (420 / 256 % 2 == 0) = false from by decide, Bool.false_eq_true, ↓reduceIte]
    · have hLS : Internal.walkDescendM vfsDirOps dh [] (fun parDh => vfsDirOps.lstatAt parDh leaf) st₁ =
          vfsDirOps.lstatAt dh leaf st₁ :=
        rfl
      rw [hLS, vfsDirOps_lstatAt_def, hLd₁]
      dsimp only
      rw [hPar₁]
      simp only [hXF, Bool.false_eq_true, ↓reduceIte, hLeaf₁]
      exact ⟨vfsToStat (.file bytes 420), rfl, rfl, rfl, rfl⟩

/-- On symlink-free paths inside the depth bound, `sub.readRegular` and `sub.lstat` match `vfsApi.readBytes` and `vfsApi.lstat`. -/
theorem spec_subtreeAgreesWithAmbientOnSymlinkFree : SpecSubtreeAgreesWithAmbientOnSymlinkFree Internal.subtreeOpsM := by
  intro st dh pos rel bs fm hLd hInv hPosValid hRelNe hLen hRelAnc hPosAnc hLeafFile hFilePerm fullPath sub
  have hSegsNe : rel.segments ≠ [] := fun h0 => hRelNe (by cases rel; simp_all [Raw.RelPath.root])
  rcases splitLastAux_prefix_of_append_ne_nil [] rel.segments hSegsNe with
    ⟨pre, leaf, tail, hSplit, hPreEq, hRest⟩
  simp only [List.nil_append] at hPreEq hSplit
  subst hPreEq
  dsimp only [fullPath, sub, StateT.run, Internal.subtreeOpsM]
  rw [hSplit]
  dsimp only
  have hRelValid : ∀ s ∈ rel.segments.map (·.val), validSeg s = true := by
    intro s hs
    simp only [List.mem_map] at hs
    rcases hs with ⟨e, _, rfl⟩
    exact e.valid
  have hFullSegsNe : pos ++ rel.segments.map (·.val) ≠ [] := by
    intro h0
    simp only [List.append_eq_nil_iff, List.map_eq_nil_iff] at h0
    exact hSegsNe h0.2
  have hFullValid : ∀ s ∈ pos ++ rel.segments.map (·.val), validSeg s = true := by
    intro s hs
    rcases List.mem_append.mp hs with hp | hr
    · exact hPosValid s hp
    · exact hRelValid s hr
  have hPreLenLt : pre.length < rel.segments.length := by
    rw [hRest, List.length_append, List.length_singleton]
    omega
  have hTakePre : rel.segments.take pre.length = pre := by
    rw [hRest, List.take_left]
  have hParDir : ∃ pm, nodeAt st.tree (pos ++ pre.map (·.val)) = some (.dir pm) ∧
      pm / 256 % 2 = 1 ∧ pm / 64 % 2 = 1 := by
    simpa [hTakePre] using hRelAnc pre.length (Nat.le_of_lt hPreLenLt) hPreLenLt
  rcases hParDir with ⟨pm, hParNd, hParR, hParX⟩
  have hParXF : (pm / 64 % 2 == 0) = false := by rw [hParX]; decide
  have hFileRF : (fm / 256 % 2 == 0) = false := by rw [hFilePerm]; decide
  have hLeafPosEq : (pos ++ pre.map (·.val)) ++ [leaf.val] = pos ++ rel.segments.map (·.val) := by
    rw [hRest, List.map_append, List.map_singleton, List.append_assoc]
  have hReadLHS : (Internal.walkDescendM vfsDirOps dh pre (fun parDh => vfsDirOps.readRegularAt parDh leaf) st).1 =
      .ok bs := by
    have hWalk := walkDescendM_ok pre dh pos st (fun parDh => vfsDirOps.readRegularAt parDh leaf) hLd hInv
      (fun k hk => by
        have hkRel : k < rel.segments.length := Nat.lt_trans hk hPreLenLt
        have hTakeEq : rel.segments.take k = pre.take k := by
          rw [hRest, List.take_append_of_le_length (Nat.le_of_lt hk)]
        rcases hRelAnc k (Nat.le_of_lt hkRel) hkRel with ⟨dm, hD, hR, hEx⟩
        rw [hTakeEq] at hD
        exact ⟨dm, hD, fun _ => hR, hEx⟩)
      (fun _ => ⟨pm, hParNd, hParR⟩)
    by_cases hT0 : pre = []
    · subst hT0
      simp only [List.map_nil, List.append_nil] at hParNd hLeafPosEq
      rw [hWalk.1 rfl, vfsDirOps_readRegularAt_def, hLd]
      dsimp only
      rw [hParNd]
      simp only [hParXF, Bool.false_eq_true, ↓reduceIte, hLeafPosEq, hLeafFile, hFileRF]
    · rcases hWalk.2 hT0 with ⟨leafDh, stMid, _, hLdMid, hTreeMid, _, _, _, _, _, _, _, hEq⟩
      rw [hEq, bracketCloseDirM_run, vfsDirOps_readRegularAt_def, hLdMid]
      dsimp only
      rw [hTreeMid, hParNd]
      simp only [hParXF, Bool.false_eq_true, ↓reduceIte, hLeafPosEq, hLeafFile, hFileRF]
  have hLstatLHS : (Internal.walkDescendM vfsDirOps dh pre (fun parDh => vfsDirOps.lstatAt parDh leaf) st).1 =
      .ok (vfsToStat (.file bs fm)) := by
    have hWalk := walkDescendM_ok pre dh pos st (fun parDh => vfsDirOps.lstatAt parDh leaf) hLd hInv
      (fun k hk => by
        have hkRel : k < rel.segments.length := Nat.lt_trans hk hPreLenLt
        have hTakeEq : rel.segments.take k = pre.take k := by
          rw [hRest, List.take_append_of_le_length (Nat.le_of_lt hk)]
        rcases hRelAnc k (Nat.le_of_lt hkRel) hkRel with ⟨dm, hD, hR, hEx⟩
        rw [hTakeEq] at hD
        exact ⟨dm, hD, fun _ => hR, hEx⟩)
      (fun _ => ⟨pm, hParNd, hParR⟩)
    by_cases hT0 : pre = []
    · subst hT0
      simp only [List.map_nil, List.append_nil] at hParNd hLeafPosEq
      rw [hWalk.1 rfl, vfsDirOps_lstatAt_def, hLd]
      dsimp only
      rw [hParNd]
      simp only [hParXF, Bool.false_eq_true, ↓reduceIte, hLeafPosEq, hLeafFile]
    · rcases hWalk.2 hT0 with ⟨leafDh, stMid, _, hLdMid, hTreeMid, _, _, _, _, _, _, _, hEq⟩
      rw [hEq, bracketCloseDirM_run, vfsDirOps_lstatAt_def, hLdMid]
      dsimp only
      rw [hTreeMid, hParNd]
      simp only [hParXF, Bool.false_eq_true, ↓reduceIte, hLeafPosEq, hLeafFile]
  let fullP := pathOfSegs (pos ++ rel.segments.map (·.val))
  have hValidRaw : isValidRawPath fullP = true := isValidRawPath_pathOfSegs hFullSegsNe hFullValid
  have hAbs : vfsAbsNorm st.cwd fullP = fullP := vfsAbsNorm_pathOfSegs st.cwd _ hFullValid
  have hSplitFull : vfsSplitSegs fullP = pos ++ rel.segments.map (·.val) :=
    vfsSplitSegs_pathOfSegs _ hFullValid
  have hInterFull : ∀ k < (pos ++ rel.segments.map (·.val)).length, ∃ dm,
      st.nodes (pathOfSegs ([] ++ (pos ++ rel.segments.map (·.val)).take k)) = some (.dir dm) ∧
        dm / 64 % 2 = 1 := by
    intro k hk
    have hTakeValid : ∀ s ∈ ([] ++ (pos ++ rel.segments.map (·.val)).take k), validSeg s = true := by
      intro s hs
      simp only [List.nil_append] at hs
      exact hFullValid s (List.mem_of_mem_take hs)
    rw [vfsState_nodes_pathOfSegs st _ hTakeValid, List.nil_append]
    by_cases hkPos : k < pos.length
    · rw [List.take_append_of_le_length (Nat.le_of_lt hkPos)]
      exact hPosAnc k hkPos
    · have hkGe : pos.length ≤ k := Nat.le_of_not_lt hkPos
      have hkSub : k - pos.length < rel.segments.length := by
        simp only [List.length_append, List.length_map] at hk
        omega
      rcases hRelAnc (k - pos.length) (Nat.le_of_lt hkSub) hkSub with ⟨dm, hD, _, hEx⟩
      refine ⟨dm, ?_, hEx⟩
      rw [List.take_append, List.take_of_length_le hkGe, ← List.map_take]
      exact hD
  have hFuelFull : (pos ++ rel.segments.map (·.val)).length < 1024 := by
    simpa [List.length_append, List.length_map] using hLen
  have hFuelRem : 1024 - (pos ++ rel.segments.map (·.val)).length =
      (1023 - (pos ++ rel.segments.map (·.val)).length) + 1 := by
    omega
  have hNode : st.nodes fullP = some (.file bs fm) := by
    change st.nodes (pathOfSegs (pos ++ rel.segments.map (·.val))) = some (.file bs fm)
    rw [vfsState_nodes_pathOfSegs st _ hFullValid]
    exact hLeafFile
  have hResAny : ∀ followLast,
      vfsResolveSegs st.nodes "/" (vfsSplitSegs (vfsAbsNorm st.cwd fullP)) followLast 1024 =
        .ok (fullP, .file bs fm) := by
    intro followLast
    rw [hAbs, hSplitFull]
    change vfsResolveSegs st.nodes (pathOfSegs []) (pos ++ rel.segments.map (·.val)) followLast 1024 = _
    rw [vfsResolveSegs_steps st.nodes (pos ++ rel.segments.map (·.val)) followLast 1024 [] hFuelFull
      (fun _ h => by cases h) hFullValid hInterFull, List.nil_append, hFuelRem, vfsResolveSegs.eq_2, hNode]
  have hReadRHS : (vfsApi.readBytes fullP st).1 = .ok bs := by
    change vfsReadBytesPure st fullP = .ok bs
    unfold vfsReadBytesPure
    simp only [hValidRaw, Bool.not_true, Bool.false_eq_true, ↓reduceIte, hResAny true]
  have hLstatRHS : (vfsApi.lstat fullP st).1 = .ok (vfsToStat (.file bs fm)) := by
    change (StateT.run (vfsOps.stat false fullP) st).1 = .ok (vfsToStat (.file bs fm))
    change vfsStatPure st false fullP = .ok (vfsToStat (.file bs fm))
    unfold vfsStatPure
    rw [hResAny false]
  exact ⟨hReadLHS.trans hReadRHS.symm, hLstatLHS.trans hLstatRHS.symm⟩

private theorem joinSlashChars_append_singleton (xs : List (List Char)) (hNe : xs ≠ []) (y : List Char) :
    Internal.joinSlashChars (xs ++ [y]) = Internal.joinSlashChars xs ++ '/' :: y := by
  induction xs with
  | nil => contradiction
  | cons x rest ih =>
    cases rest with
    | nil => rfl
    | cons z zs =>
      have hSub := ih (by simp)
      change x ++ '/' :: Internal.joinSlashChars ((z :: zs) ++ [y]) =
        (x ++ '/' :: Internal.joinSlashChars (z :: zs)) ++ '/' :: y
      rw [hSub]
      exact (List.append_assoc x ('/' :: Internal.joinSlashChars (z :: zs)) ('/' :: y)).symm

private theorem pathOfSegs_cons_ne_slash (a : String) (rest : List String)
    (ha : validSeg a = true) : pathOfSegs (a :: rest) ≠ "/" := by
  intro h0
  have hList := congrArg String.toList h0
  rw [pathOfSegs_eq_ofList_joinSlashChars (a :: rest)] at hList
  have hTail := congrArg List.tail hList
  simp only [String.toList_ofList, List.tail_cons] at hTail
  have hNe : a.toList ≠ [] := by
    unfold validSeg at ha
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at ha
    intro hN
    have hE : a.toList.isEmpty = true := by simp [hN]
    rw [hE] at ha
    cases ha.1.1.1.1
  cases rest with
  | nil =>
    simp only [List.map_cons, List.map_nil] at hTail
    change a.toList = "/".toList.tail at hTail
    have hT0 : "/".toList.tail = [] := rfl
    rw [hT0] at hTail
    exact hNe hTail
  | cons b bs =>
    simp only [List.map_cons] at hTail
    change a.toList ++ '/' :: Internal.joinSlashChars (b.toList :: bs.map String.toList) = "/".toList.tail at hTail
    have hT0 : "/".toList.tail = [] := rfl
    rw [hT0] at hTail
    exact hNe (List.append_eq_nil_iff.mp hTail).1

private theorem pathOfSegs_append_singleton_toList (pos : List String) (s : String)
    (hPosValid : ∀ seg ∈ pos, validSeg seg = true) :
    (pathOfSegs (pos ++ [s])).toList =
      (if pathOfSegs pos == "/" then "/" else pathOfSegs pos ++ "/").toList ++ s.toList := by
  cases pos with
  | nil =>
    have hP0 : pathOfSegs [] = "/" := rfl
    have hP1 : pathOfSegs [s] = "/" ++ s := rfl
    simp [hP0, hP1]
  | cons a rest =>
    have hNe : pathOfSegs (a :: rest) ≠ "/" :=
      pathOfSegs_cons_ne_slash a rest (hPosValid a List.mem_cons_self)
    have hBeqF : (pathOfSegs (a :: rest) == "/") = false := beq_false_of_ne hNe
    have hLHS : (pathOfSegs ((a :: rest) ++ [s])).toList =
        '/' :: (Internal.joinSlashChars ((a :: rest).map String.toList) ++ '/' :: s.toList) := by
      rw [pathOfSegs_eq_ofList_joinSlashChars ((a :: rest) ++ [s]), List.map_append, List.map_singleton,
        joinSlashChars_append_singleton _ (by simp) s.toList]
      simp
    have hRHS : (pathOfSegs (a :: rest) ++ "/").toList ++ s.toList =
        '/' :: (Internal.joinSlashChars ((a :: rest).map String.toList) ++ '/' :: s.toList) := by
      rw [String.toList_append, pathOfSegs_eq_ofList_joinSlashChars (a :: rest)]
      simp only [String.toList_ofList, List.cons_append, List.append_assoc]
      rfl
    rw [hBeqF]
    simp only [Bool.false_eq_true, ↓reduceIte]
    exact hLHS.trans hRHS.symm

/-- `t'` is obtained from `t` by only removing nodes. -/
def TreeShrunk (t' t : VfsTree) : Prop :=
  ∀ q, nodeAt t' q = none ∨ nodeAt t' q = nodeAt t q

/-- `TreeShrunk` is reflexive. -/
theorem treeShrunk_refl (t : VfsTree) : TreeShrunk t t := fun _ => Or.inr rfl

/-- `TreeShrunk` is transitive. -/
theorem treeShrunk_trans {t2 t1 t0 : VfsTree} (h21 : TreeShrunk t2 t1) (h10 : TreeShrunk t1 t0) :
    TreeShrunk t2 t0 := by
  intro q
  rcases h21 q with hNone | hEq
  · exact Or.inl hNone
  · rw [hEq]; exact h10 q

/-- Removing a subtree under `base ++ [leaf]` shrinks the tree. -/
theorem treeShrunk_set_none (t : VfsTree) (base : List String) (leaf : String)
    (hDir : ∃ dm ch, vfsTreeGet t base = some (.dir dm ch)) :
    TreeShrunk (vfsTreeSet t (base ++ [leaf]) none) t := by
  intro q
  by_cases hPre : base ++ [leaf] <+: q
  · rcases hPre with ⟨rest, rfl⟩
    left
    have hTopNone : nodeAt (vfsTreeSet t (base ++ [leaf]) none) (base ++ [leaf]) = none := by
      simpa using nodeAt_vfsTreeSet_eq t base leaf none hDir
    exact nodeAt_none_desc _ (base ++ [leaf]) rest hTopNone
  · right
    exact nodeAt_vfsTreeSet_outside t base leaf none q hDir hPre

/-- Shrinking a tree while keeping `keys` preserves `VfsKeysComplete`. -/
theorem vfsKeysComplete_treeShrunk (st st' : VfsState) (hKeys : VfsKeysComplete st)
    (hKeyEq : st'.keys = st.keys) (hShrunk : TreeShrunk st'.tree st.tree) : VfsKeysComplete st' := by
  intro segs hNe
  rw [hKeyEq]
  apply hKeys segs
  rcases hShrunk segs with hNone | hEq
  · exact absurd hNone hNe
  · rw [← hEq]; exact hNe

/-- Shrinking a tree preserves `VfsTreeValidSegs`. -/
theorem vfsTreeValidSegs_treeShrunk {t' t : VfsTree} (hV : VfsTreeValidSegs t)
    (hShrunk : TreeShrunk t' t) : VfsTreeValidSegs t' := by
  intro segs hNe s hs
  apply hV segs _ s hs
  rcases hShrunk segs with hNone | hEq
  · exact absurd hNone hNe
  · rw [← hEq]; exact hNe

/-- Shrinking a removable subtree preserves `VfsTreeRemovable`. -/
theorem vfsTreeRemovable_treeShrunk :
    ∀ (n : Nat) {t' t : VfsTree}, TreeShrunk t' t → VfsTreeRemovable n t → VfsTreeRemovable n t'
  | n, .file _ _, _, _, _ => by
    cases n <;> simp [VfsTreeRemovable]
  | n, .symlink _ _, _, _, _ => by
    cases n <;> simp [VfsTreeRemovable]
  | 0, .dir dm' ch', t, hShrunk, hRem => by
    have hTop : nodeAt t [] = some (.dir dm') := by
      rcases hShrunk [] with hNone | hEq
      · simp [nodeAt, vfsTreeGet, vfsTreeTopNode] at hNone
      · exact hEq.symm
    cases t with
    | file _ _ => simp [nodeAt, vfsTreeGet, vfsTreeTopNode] at hTop
    | symlink _ _ => simp [nodeAt, vfsTreeGet, vfsTreeTopNode] at hTop
    | dir dm ch =>
      rw [VfsTreeRemovable.eq_3] at hRem
      exact False.elim hRem
  | n + 1, .dir dm' ch', t, hShrunk, hRem => by
    have hTop : nodeAt t [] = some (.dir dm') := by
      rcases hShrunk [] with hNone | hEq
      · simp [nodeAt, vfsTreeGet, vfsTreeTopNode] at hNone
      · exact hEq.symm
    cases t with
    | file _ _ => simp [nodeAt, vfsTreeGet, vfsTreeTopNode] at hTop
    | symlink _ _ => simp [nodeAt, vfsTreeGet, vfsTreeTopNode] at hTop
    | dir dm ch =>
      have hDmEq : dm = dm' := by
        simp [nodeAt, vfsTreeGet, vfsTreeTopNode] at hTop
        exact hTop
      subst hDmEq
      rw [VfsTreeRemovable.eq_4] at hRem ⊢
      rcases hRem with ⟨hR, hW, hX, hSubRem⟩
      refine ⟨hR, hW, hX, fun s sub' hs' => ?_⟩
      have hNodeS' : nodeAt (.dir dm ch') [s] = some (vfsTreeTopNode sub') := by
        simp [nodeAt, vfsTreeGet, hs']
      have hNodeS : nodeAt (.dir dm ch) [s] = some (vfsTreeTopNode sub') := by
        rcases hShrunk [s] with hNone | hEq
        · rw [hNodeS'] at hNone; cases hNone
        · rw [← hEq]; exact hNodeS'
      cases hChS : ch s with
      | none =>
        simp [nodeAt, vfsTreeGet, hChS] at hNodeS
      | some sub =>
        have hSubShrunk : TreeShrunk sub' sub := by
          intro q
          have hAt := hShrunk (s :: q)
          have hL : nodeAt (.dir dm ch') (s :: q) = nodeAt sub' q := by
            simp [nodeAt, vfsTreeGet, hs']
          have hR' : nodeAt (.dir dm ch) (s :: q) = nodeAt sub q := by
            simp [nodeAt, vfsTreeGet, hChS]
          rw [hL, hR'] at hAt
          exact hAt
        exact vfsTreeRemovable_treeShrunk n hSubShrunk (hSubRem s sub hChS)

/-- `nodeAt t (p ++ q)` reduces to `nodeAt sub q` when `vfsTreeGet t p = some sub`. -/
theorem nodeAt_sub_of_vfsTreeGet {t : VfsTree} {p q : List String} {sub : VfsTree}
    (hGet : vfsTreeGet t p = some sub) : nodeAt t (p ++ q) = nodeAt sub q := by
  induction p generalizing t with
  | nil =>
    simp [vfsTreeGet] at hGet
    subst hGet
    rfl
  | cons a rest ih =>
    cases t with
    | file _ _ => simp [vfsTreeGet] at hGet
    | symlink _ _ => simp [vfsTreeGet] at hGet
    | dir m ch =>
      simp only [vfsTreeGet] at hGet
      cases hCa : ch a with
      | none => rw [hCa] at hGet; cases hGet
      | some subA =>
        rw [hCa] at hGet
        rw [List.cons_append]
        simp only [nodeAt, vfsTreeGet, hCa]
        exact ih hGet

/-- `vfsTreeGet t (p ++ q)` reduces to `vfsTreeGet sub q` when `vfsTreeGet t p = some sub`. -/
theorem vfsTreeGet_sub_of_vfsTreeGet {t : VfsTree} {p q : List String} {sub : VfsTree}
    (hGet : vfsTreeGet t p = some sub) : vfsTreeGet t (p ++ q) = vfsTreeGet sub q := by
  induction p generalizing t with
  | nil =>
    simp [vfsTreeGet] at hGet
    subst hGet
    rfl
  | cons a rest ih =>
    cases t with
    | file _ _ => simp [vfsTreeGet] at hGet
    | symlink _ _ => simp [vfsTreeGet] at hGet
    | dir m ch =>
      simp only [vfsTreeGet] at hGet
      cases hCa : ch a with
      | none => rw [hCa] at hGet; cases hGet
      | some subA =>
        rw [hCa] at hGet
        rw [List.cons_append]
        simp only [vfsTreeGet, hCa]
        exact ih hGet

private theorem treeShrunk_sub_of_vfsTreeGet {t' t sub' sub : VfsTree} {p : List String}
    (hShrunk : TreeShrunk t' t) (hG' : vfsTreeGet t' p = some sub') (hG : vfsTreeGet t p = some sub) :
    TreeShrunk sub' sub := by
  intro q
  have h := hShrunk (p ++ q)
  rw [nodeAt_sub_of_vfsTreeGet hG', nodeAt_sub_of_vfsTreeGet hG] at h
  exact h

private theorem mVfsReadDirAtEntries_filterMap_item (st : VfsState) (k dirCanon : String)
    (pfx : List Char) (child : EntryName)
    (hNodes : (st.nodes k).isSome = true) (hNe : k ≠ dirCanon)
    (hPfx : pfx.isPrefixOf k.toList = true) (hEqList : k.toList = pfx ++ child.val.toList) :
    (if (st.nodes k).isSome = true then
      if (k != dirCanon && pfx.isPrefixOf k.toList) = true then
        let restChars := k.toList.drop pfx.length
        let restStr := String.ofList restChars
        if h : validSeg restStr = true then some { val := restStr, valid := h } else none
      else none
    else none) = some child := by
  have hDrop : String.ofList (k.toList.drop pfx.length) = child.val := by
    rw [hEqList, List.drop_left, String.ofList_toList]
  have hCond : (k != dirCanon && pfx.isPrefixOf k.toList) = true := by
    simp [bne_iff_ne, hNe, hPfx]
  have hV : validSeg (String.ofList (k.toList.drop pfx.length)) = true := by
    rw [hDrop]; exact child.valid
  rw [ite_eq_left_iff.mpr (fun h => absurd hNodes h),
    ite_eq_left_iff.mpr (fun h => absurd hCond h)]
  dsimp only
  split
  · cases child; simp only [hDrop]
  · next h => exact absurd hV h

/-- A live child key under `pos` appears in `mVfsReadDirAtEntries st pos`. -/
theorem mVfsReadDirAtEntries_mem_of_key (st : VfsState) (pos : List String)
    (child : EntryName) (hPosValid : ∀ s ∈ pos, validSeg s = true)
    (hKey : pathOfSegs (pos ++ [child.val]) ∈ st.keys)
    (hLive : nodeAt st.tree (pos ++ [child.val]) ≠ none) :
    child ∈ (mVfsReadDirAtEntries st pos).toList := by
  unfold mVfsReadDirAtEntries
  rw [List.toList_toArray, List.mem_filterMap]
  have hValidAll : ∀ s ∈ pos ++ [child.val], validSeg s = true := by
    intro s hs
    rcases List.mem_append.mp hs with hp | hc
    · exact hPosValid s hp
    · simp only [List.mem_singleton] at hc; subst hc; exact child.valid
  refine ⟨pathOfSegs (pos ++ [child.val]), List.mem_eraseDups.mpr hKey, ?_⟩
  have hNodes : (st.nodes (pathOfSegs (pos ++ [child.val]))).isSome = true := by
    rw [vfsState_nodes_pathOfSegs st (pos ++ [child.val]) hValidAll]
    exact Option.isSome_iff_ne_none.mpr hLive
  have hToList := pathOfSegs_append_singleton_toList pos child.val hPosValid
  have hChildNe : child.val.toList ≠ [] := by
    have hV := child.valid
    unfold validSeg at hV
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at hV
    intro hNil
    have hEmp : child.val.toList.isEmpty = true := by simp [hNil]
    rw [hEmp] at hV
    cases hV.1.1.1.1
  have hPfxGe : (pathOfSegs pos).toList.length ≤
      (if pathOfSegs pos == "/" then "/" else pathOfSegs pos ++ "/").toList.length := by
    cases hD : (pathOfSegs pos == "/") with
    | true =>
      have hEq : pathOfSegs pos = "/" := beq_iff_eq.mp hD
      simp [hEq]
    | false =>
      simp [String.toList_append]
  have hChildPos : 0 < child.val.toList.length := by
    cases hC : child.val.toList with
    | nil => exact absurd hC hChildNe
    | cons _ _ => simp
  have hNeDir : pathOfSegs (pos ++ [child.val]) ≠ pathOfSegs pos := by
    intro hEq
    have hLen := congrArg (fun s : String => s.toList.length) hEq
    rw [hToList, List.length_append] at hLen
    omega
  have hPfx : (if pathOfSegs pos == "/" then "/" else pathOfSegs pos ++ "/").toList.isPrefixOf
      (pathOfSegs (pos ++ [child.val])).toList = true := by
    rw [hToList]
    exact List.isPrefixOf_iff_prefix.mpr ⟨child.val.toList, rfl⟩
  exact mVfsReadDirAtEntries_filterMap_item st (pathOfSegs (pos ++ [child.val])) (pathOfSegs pos)
    (if pathOfSegs pos == "/" then "/" else pathOfSegs pos ++ "/").toList child hNodes hNeDir hPfx hToList

private theorem splitCharList_joinSlashChars_append (segs : List String) (hNe : segs ≠ [])
    (hValid : ∀ s ∈ segs, validSeg s = true) (tailChars : List Char) :
    Internal.splitCharList '/' (Internal.joinSlashChars (segs.map String.toList) ++ '/' :: tailChars) =
      segs.map String.toList ++ Internal.splitCharList '/' tailChars := by
  induction segs with
  | nil => contradiction
  | cons s rest ih =>
    have hV : validSeg s = true := hValid s List.mem_cons_self
    have hNoSl : '/' ∉ s.toList := by
      unfold validSeg at hV
      simp only [Bool.and_eq_true, Bool.not_eq_true'] at hV
      intro hm
      have hc := List.contains_iff_mem.mpr hm
      rw [hc] at hV
      cases hV.1.1.1.2
    cases rest with
    | nil =>
      simp only [List.map_cons, List.map_nil]
      change Internal.splitCharList '/' (s.toList ++ '/' :: tailChars) = s.toList :: Internal.splitCharList '/' tailChars
      have hBase : ∀ cs : List Char, '/' ∉ cs →
          Internal.splitCharList '/' (cs ++ '/' :: tailChars) = cs :: Internal.splitCharList '/' tailChars := by
        intro cs hcs
        induction cs with
        | nil =>
          simp only [List.nil_append]
          change (if ('/' == '/') = true then [] :: Internal.splitCharList '/' tailChars else _) = _
          simp
        | cons c cs' ihc =>
          simp only [List.mem_cons, not_or] at hcs
          have hcNe : (c == '/') = false := beq_false_of_ne (Ne.symm hcs.1)
          have hSub := ihc hcs.2
          simp only [List.cons_append]
          change (if (c == '/') = true then _ else match Internal.splitCharList '/' (cs' ++ '/' :: tailChars) with
            | [] => [[c]]
            | seg :: rest => (c :: seg) :: rest) = _
          simp only [hcNe, Bool.false_eq_true, ↓reduceIte, hSub]
      exact hBase s.toList hNoSl
    | cons r rs =>
      have ihRest := ih (by simp) (fun t ht => hValid t (List.mem_cons_of_mem _ ht))
      have ihRest' : Internal.splitCharList '/' (Internal.joinSlashChars (r.toList :: rs.map String.toList) ++ '/' :: tailChars) =
          r.toList :: (rs.map String.toList ++ Internal.splitCharList '/' tailChars) := ihRest
      simp only [List.map_cons]
      have hJoinEq : Internal.joinSlashChars (s.toList :: r.toList :: rs.map String.toList) ++ '/' :: tailChars =
          s.toList ++ '/' :: (Internal.joinSlashChars (r.toList :: rs.map String.toList) ++ '/' :: tailChars) := by
        change (s.toList ++ '/' :: Internal.joinSlashChars (r.toList :: rs.map String.toList)) ++ '/' :: tailChars = _
        rw [List.append_assoc]
        rfl
      rw [hJoinEq]
      have hStep : ∀ cs : List Char, '/' ∉ cs → ∀ ys : List Char, ∀ hd tl,
          Internal.splitCharList '/' ys = hd :: tl →
          Internal.splitCharList '/' (cs ++ '/' :: ys) = cs :: hd :: tl := by
        intro cs hcs ys hd tl hYs
        induction cs with
        | nil =>
          simp only [List.nil_append]
          change (if ('/' == '/') = true then [] :: Internal.splitCharList '/' ys else _) = _
          simp [hYs]
        | cons c cs' ihc =>
          simp only [List.mem_cons, not_or] at hcs
          have hcNe : (c == '/') = false := beq_false_of_ne (Ne.symm hcs.1)
          have hSub := ihc hcs.2
          simp only [List.cons_append]
          change (if (c == '/') = true then _ else match Internal.splitCharList '/' (cs' ++ '/' :: ys) with
            | [] => [[c]]
            | seg :: rest => (c :: seg) :: rest) = _
          simp only [hcNe, Bool.false_eq_true, ↓reduceIte, hSub]
      exact hStep s.toList hNoSl _ r.toList (rs.map String.toList ++ Internal.splitCharList '/' tailChars) ihRest'

private theorem collapseChars_cons_eq (abs : Bool) (seg : List Char) (rest acc : List (List Char)) :
    Internal.collapseChars abs (seg :: rest) acc =
      if seg.isEmpty || seg == ['.'] then Internal.collapseChars abs rest acc
      else if seg == ['.', '.'] then
        match acc with
        | top :: tail =>
          if top != ['.', '.'] then Internal.collapseChars abs rest tail
          else Internal.collapseChars abs rest (if abs then acc else ['.', '.'] :: acc)
        | [] => Internal.collapseChars abs rest (if abs then [] else [['.', '.']])
      else Internal.collapseChars abs rest (seg :: acc) :=
  rfl

private theorem collapseChars_append_all_empty (abs : Bool) (xs ys acc : List (List Char))
    (hEmpty : ∀ s ∈ ys, s = []) :
    Internal.collapseChars abs (xs ++ ys) acc = Internal.collapseChars abs xs acc := by
  induction xs generalizing acc with
  | nil =>
    simp only [List.nil_append]
    induction ys with
    | nil => rfl
    | cons y rest ihy =>
      have hy : y = [] := hEmpty y List.mem_cons_self
      subst hy
      rw [collapseChars_cons_eq]
      exact ihy (fun s hs => hEmpty s (List.mem_cons_of_mem _ hs))
  | cons x xt ihx =>
    simp only [List.cons_append]
    rw [collapseChars_cons_eq, collapseChars_cons_eq]
    by_cases h1 : (x.isEmpty || x == ['.']) = true
    · simp only [h1, ↓reduceIte]
      exact ihx acc
    · have h1F : (x.isEmpty || x == ['.']) = false := Bool.eq_false_iff.mpr h1
      simp only [h1F, Bool.false_eq_true, ↓reduceIte]
      by_cases h2 : (x == ['.', '.']) = true
      · simp only [h2, ↓reduceIte]
        cases acc with
        | nil => exact ihx (if abs then [] else [['.', '.']])
        | cons top tail =>
          by_cases h3 : (top != ['.', '.']) = true
          · simp only [h3, ↓reduceIte]
            exact ihx tail
          · have h3F : (top != ['.', '.']) = false := Bool.eq_false_iff.mpr h3
            simp only [h3F, Bool.false_eq_true, ↓reduceIte]
            exact ihx (if abs then top :: tail else ['.', '.'] :: top :: tail)
      · have h2F : (x == ['.', '.']) = false := Bool.eq_false_iff.mpr h2
        simp only [h2F, Bool.false_eq_true, ↓reduceIte]
        exact ihx (x :: acc)

private theorem mDirHasLiveChild_false_of_empty (st : VfsState) (dirPos : List String)
    (hNe : dirPos ≠ []) (hValid : ∀ s ∈ dirPos, validSeg s = true)
    (hEmpty : ∀ s, nodeAt st.tree (dirPos ++ [s]) = none) :
    mDirHasLiveChild st dirPos = false := by
  unfold mDirHasLiveChild
  simp only [List.any_eq_false, Bool.and_eq_true, bne_iff_ne, ne_eq, not_and]
  intro k _ ⟨hNodes, hKNe⟩ hPfx
  have hDirNeSlash : pathOfSegs dirPos ≠ "/" := by
    cases dirPos with
    | nil => contradiction
    | cons a rest => exact pathOfSegs_cons_ne_slash a rest (hValid a List.mem_cons_self)
  have hDirBeqF : (pathOfSegs dirPos == "/") = false := beq_false_of_ne hDirNeSlash
  simp only [hDirBeqF, Bool.false_eq_true, ↓reduceIte] at hPfx
  rcases List.isPrefixOf_iff_prefix.mp hPfx with ⟨tailChars, hKEq⟩
  have hPfxToList : (pathOfSegs dirPos ++ "/").toList =
      '/' :: (Internal.joinSlashChars (dirPos.map String.toList) ++ ['/']) := by
    have hE := pathOfSegs_eq_ofList_joinSlashChars dirPos
    rw [String.toList_append, hE, String.toList_ofList]
    rfl
  have hKList : k.toList = '/' :: (Internal.joinSlashChars (dirPos.map String.toList) ++ '/' :: tailChars) := by
    rw [← hKEq, hPfxToList]
    simp [List.append_assoc]
  have hCanon : isCanonPath k = true := by
    change (vfsTreeNodes st.tree k).isSome = true at hNodes
    unfold vfsTreeNodes at hNodes
    by_cases hc : isCanonPath k = true
    · exact hc
    · simp [hc] at hNodes
  have hLiveNode : nodeAt st.tree (vfsSplitSegs k) ≠ none := by
    change (vfsTreeNodes st.tree k).isSome = true at hNodes
    unfold vfsTreeNodes at hNodes
    simp only [hCanon, ↓reduceIte] at hNodes
    exact Option.isSome_iff_ne_none.mp hNodes
  have hSplitTail := splitCharList_joinSlashChars_append dirPos hNe hValid tailChars
  have hVfsSplit : vfsSplitSegs k =
      dirPos ++ (Internal.splitCharList '/' tailChars).filterMap
        (fun cs => if cs.isEmpty then none else some (String.ofList cs)) := by
    have hSplitK : vfsSplitSegs k =
        (Internal.splitCharList '/' (Internal.joinSlashChars (dirPos.map String.toList) ++ '/' :: tailChars)).filterMap
          (fun cs => if cs.isEmpty then none else some (String.ofList cs)) := by
      unfold vfsSplitSegs
      rw [hKList]
      rfl
    rw [hSplitK, hSplitTail, List.filterMap_append]
    have hMapBack : (dirPos.map String.toList).filterMap
        (fun cs => if cs.isEmpty then none else some (String.ofList cs)) = dirPos := by
      have aux : ∀ xs : List String, (∀ s ∈ xs, validSeg s = true) →
          (xs.map String.toList).filterMap
            (fun cs => if cs.isEmpty then none else some (String.ofList cs)) = xs := by
        intro xs
        induction xs with
        | nil => intro _; rfl
        | cons d ds ihd =>
          intro hVxs
          have hdV := hVxs d List.mem_cons_self
          have hdNe : d.toList.isEmpty = false := by
            unfold validSeg at hdV
            simp only [Bool.and_eq_true, Bool.not_eq_true'] at hdV
            exact Bool.eq_false_iff.mpr (by intro h; rw [h] at hdV; cases hdV.1.1.1.1)
          simp only [List.map_cons, List.filterMap_cons, hdNe, Bool.false_eq_true, ↓reduceIte, String.ofList_toList]
          congr 1
          exact ihd (fun s hs => hVxs s (List.mem_cons_of_mem d hs))
      exact aux dirPos hValid
    rw [hMapBack]
  cases hRestSegs : (Internal.splitCharList '/' tailChars).filterMap
      (fun cs => if cs.isEmpty then none else some (String.ofList cs)) with
  | nil =>
    have hAllEmpty : ∀ s ∈ Internal.splitCharList '/' tailChars, s = [] := by
      intro s hs
      by_cases hsE : s.isEmpty = true
      · exact List.isEmpty_iff.mp hsE
      · have hsF : s.isEmpty = false := Bool.eq_false_iff.mpr hsE
        have hS : (if s.isEmpty = true then none else some (String.ofList s)) = some (String.ofList s) := by
          simp [hsF]
        have hMem : String.ofList s ∈ (Internal.splitCharList '/' tailChars).filterMap
            (fun cs => if cs.isEmpty then none else some (String.ofList cs)) :=
          List.mem_filterMap.mpr ⟨s, hs, hS⟩
        rw [hRestSegs] at hMem
        cases hMem
    have hNorm : Internal.normPath k = pathOfSegs dirPos := by
      unfold Internal.normPath
      rw [hKList]
      have hAbs : Internal.isAbsChars ('/' :: (Internal.joinSlashChars (dirPos.map String.toList) ++ '/' :: tailChars)) = true := rfl
      simp only [hAbs, ↓reduceIte]
      have hSplitK : Internal.splitCharList '/' ('/' :: (Internal.joinSlashChars (dirPos.map String.toList) ++ '/' :: tailChars)) =
          [] :: (dirPos.map String.toList ++ Internal.splitCharList '/' tailChars) := by
        change (if ('/' == '/') = true then [] :: _ else _) = _
        simp only [beq_self_eq_true, ↓reduceIte, hSplitTail]
      rw [hSplitK]
      have hDrop0 : Internal.collapseChars true ([] :: (dirPos.map String.toList ++ Internal.splitCharList '/' tailChars)) [] =
          Internal.collapseChars true (dirPos.map String.toList ++ Internal.splitCharList '/' tailChars) [] := rfl
      rw [hDrop0, collapseChars_append_all_empty true (dirPos.map String.toList) (Internal.splitCharList '/' tailChars) [] hAllEmpty]
      have hColValid : Internal.collapseChars true (dirPos.map String.toList) [] = dirPos.map String.toList := by
        clear hAllEmpty hRestSegs hVfsSplit hSplitTail hLiveNode hCanon hKList hKEq hPfx hKNe hNodes hDirBeqF hDirNeSlash
        have hCol : ∀ ps acc, (∀ p ∈ ps, p ≠ [] ∧ p ≠ ['.'] ∧ p ≠ ['.', '.']) →
            Internal.collapseChars true ps acc = acc.reverse ++ ps := by
          intro ps acc hp
          induction ps generalizing acc with
          | nil => simp [Internal.collapseChars]
          | cons p ps' ihp =>
            have hp0 := hp p List.mem_cons_self
            have hc1 : (p.isEmpty || p == ['.']) = false := by
              simp only [Bool.or_eq_false_iff, List.isEmpty_eq_false_iff_exists_mem]
              refine ⟨?_, beq_false_of_ne hp0.2.1⟩
              cases p with
              | nil => exact absurd rfl hp0.1
              | cons c _ => exact ⟨c, List.mem_cons_self⟩
            have hc2 : (p == ['.', '.']) = false := beq_false_of_ne hp0.2.2
            rw [collapseChars_cons_eq, hc1, hc2]
            simp only [Bool.false_eq_true, ↓reduceIte]
            rw [ihp (p :: acc) (fun q hq => hp q (List.mem_cons_of_mem _ hq))]
            simp [List.append_assoc]
        simpa using hCol (dirPos.map String.toList) [] (fun p hp => by
          simp only [List.mem_map] at hp
          rcases hp with ⟨s, hs, rfl⟩
          have hsV := hValid s hs
          unfold validSeg at hsV
          simp only [Bool.and_eq_true, Bool.not_eq_true', bne_iff_ne, ne_eq] at hsV
          exact ⟨by simpa [String.isEmpty_iff] using hsV.1.1.1.1, hsV.1.2, hsV.2⟩)
      rw [hColValid]
      exact (pathOfSegs_eq_ofList_joinSlashChars dirPos).symm
    have hNormSelf : Internal.normPath k = k := by
      unfold isCanonPath at hCanon
      simp only [Bool.and_eq_true, beq_iff_eq] at hCanon
      exact hCanon.2
    exact absurd (hNormSelf.symm.trans hNorm) hKNe
  | cons firstSeg restSegs =>
    rw [hRestSegs] at hVfsSplit
    rw [hVfsSplit] at hLiveNode
    have hEqList : dirPos ++ firstSeg :: restSegs = (dirPos ++ [firstSeg]) ++ restSegs := by
      simp [List.append_assoc]
    rw [hEqList] at hLiveNode
    exact hLiveNode (nodeAt_none_desc st.tree (dirPos ++ [firstSeg]) restSegs (hEmpty firstSeg))

/-- `rmtreeNonDirPrefixM` unlinks leading non-directory entries and stops at the first live directory. -/
theorem rmtreeNonDirPrefixM_ok (dirDh : DirHandle) (dirPos : List String)
    (items : List EntryName) (st : VfsState) (cm : Nat) (ch : String → Option VfsTree)
    (hLd : lookupDir st dirDh = some dirPos)
    (hGet : vfsTreeGet st.tree dirPos = some (.dir cm ch))
    (hW : cm / 128 % 2 = 1) (hX : cm / 64 % 2 = 1) :
    match Internal.rmtreeNonDirPrefixM vfsDirOps dirDh items st with
    | (Except.error _, _) => False
    | (Except.ok none, st') =>
      (∃ ch', vfsTreeGet st'.tree dirPos = some (.dir cm ch')) ∧
      (∀ e ∈ items, nodeAt st'.tree (dirPos ++ [e.val]) = none) ∧
      SameOutside dirPos st st' ∧
      TreeShrunk st'.tree st.tree ∧
      st'.keys = st.keys ∧
      st'.openDirs = st.openDirs ∧
      st'.nextDirId = st.nextDirId ∧
      st'.locks = st.locks ∧
      (VfsKeysComplete st → VfsKeysComplete st')
    | (Except.ok (some (subDir, rest)), st') =>
      rest.length < items.length ∧
      (∃ ch', vfsTreeGet st'.tree dirPos = some (.dir cm ch')) ∧
      (∃ dm, nodeAt st'.tree (dirPos ++ [subDir.val]) = some (.dir dm)) ∧
      (∀ e ∈ items, e ∈ subDir :: rest ∨ nodeAt st'.tree (dirPos ++ [e.val]) = none) ∧
      SameOutside dirPos st st' ∧
      TreeShrunk st'.tree st.tree ∧
      st'.keys = st.keys ∧
      st'.openDirs = st.openDirs ∧
      st'.nextDirId = st.nextDirId ∧
      st'.locks = st.locks ∧
      (VfsKeysComplete st → VfsKeysComplete st') := by
  induction items generalizing st ch with
  | nil =>
    rw [Internal.rmtreeNonDirPrefixM.eq_1]
    exact ⟨⟨ch, hGet⟩, (fun _ h => nomatch h), SameOutside_refl dirPos st,
      treeShrunk_refl st.tree, rfl, rfl, rfl, rfl, id⟩
  | cons c rest ih =>
    have hDirNd : nodeAt st.tree dirPos = some (.dir cm) := by
      simp only [nodeAt, hGet, vfsTreeTopNode, Option.map_some]
    have hXF : (cm / 64 % 2 == 0) = false := by rw [hX]; decide
    have hWF : (cm / 128 % 2 == 0 || cm / 64 % 2 == 0) = false := by simp [hW, hX]
    rw [Internal.rmtreeNonDirPrefixM.eq_2]
    simp only [Bind.bind, StateT.bind, Pure.pure]
    rw [vfsDirOps_lstatAt_def, hLd]
    dsimp only
    rw [hDirNd]
    simp only [hXF, Bool.false_eq_true, ↓reduceIte]
    cases hChild : nodeAt st.tree (dirPos ++ [c.val]) with
    | none =>
      dsimp only
      simp only [show (FsErrorKind.notFound == FsErrorKind.notFound) = true from rfl, ↓reduceIte]
      have hSub := ih st ch hLd hGet
      cases hRec : Internal.rmtreeNonDirPrefixM vfsDirOps dirDh rest st with
      | mk r st' =>
        rw [hRec] at hSub
        cases r with
        | error e => exact hSub
        | ok opt =>
          cases opt with
          | none =>
            rcases hSub with ⟨hDG', hAllNone, hSame, hShrunk, hKeys, hOpen, hNext, hLocks, hKC⟩
            refine ⟨hDG', fun e he => ?_, hSame, hShrunk, hKeys, hOpen, hNext, hLocks, hKC⟩
            rcases List.mem_cons.mp he with rfl | hR
            · rcases hShrunk (dirPos ++ [e.val]) with hN | hEq
              · exact hN
              · rw [hEq]; exact hChild
            · exact hAllNone e hR
          | some p =>
            rcases p with ⟨subDir, tail⟩
            rcases hSub with ⟨hLen, hDG', hSubD, hItems', hSame, hShrunk, hKeys, hOpen, hNext, hLocks, hKC⟩
            refine ⟨Nat.lt_trans hLen (Nat.lt_succ_self _), hDG', hSubD, fun e he => ?_,
              hSame, hShrunk, hKeys, hOpen, hNext, hLocks, hKC⟩
            rcases List.mem_cons.mp he with rfl | hR
            · right
              rcases hShrunk (dirPos ++ [e.val]) with hN | hEq
              · exact hN
              · rw [hEq]; exact hChild
            · exact hItems' e hR
    | some node =>
      cases node with
      | dir dm =>
        simp only [vfsToStat, show (EntryKind.dir == EntryKind.dir) = true from rfl, ↓reduceIte]
        exact ⟨Nat.lt_succ_self _, ⟨ch, hGet⟩, ⟨dm, hChild⟩,
          fun e he => Or.inl he, SameOutside_refl dirPos st, treeShrunk_refl st.tree, rfl, rfl, rfl, rfl, id⟩
      | file _ _ =>
        dsimp only
        simp only [vfsToStat, show (EntryKind.file == EntryKind.dir) = false from rfl, Bool.false_eq_true, ↓reduceIte]
        simp only [Bind.bind, StateT.bind]
        rw [vfsDirOps_unlinkAt_def, hLd]
        dsimp only
        rw [hDirNd]
        simp only [hWF, Bool.false_eq_true, ↓reduceIte, hChild]
        let st1 : VfsState :=
          { tree := vfsTreeSet st.tree (dirPos ++ [c.val]) none, keys := st.keys, cwd := st.cwd,
            nonce := st.nonce, locks := st.locks, nextLockId := st.nextLockId, openDirs := st.openDirs,
            nextDirId := st.nextDirId }
        have hLd1 : lookupDir st1 dirDh = some dirPos := hLd
        have hNotSelfPre : ¬ (dirPos ++ [c.val] <+: dirPos) := by
          intro hP
          have hLen := List.IsPrefix.length_le hP
          simp at hLen
          omega
        have hDirNd1 : nodeAt st1.tree dirPos = some (.dir cm) := by
          change nodeAt (vfsTreeSet st.tree (dirPos ++ [c.val]) none) dirPos = some (.dir cm)
          rw [nodeAt_vfsTreeSet_outside st.tree dirPos c.val none dirPos ⟨cm, ch, hGet⟩ hNotSelfPre]
          exact hDirNd
        rcases vfsTreeGet_dir_of_nodeAt hDirNd1 with ⟨ch1, hGet1⟩
        have hSub := ih st1 ch1 hLd1 hGet1
        have hSame01 : SameOutside dirPos st st1 := by
          apply SameOutside_mono ⟨[c.val], rfl⟩
          intro p hNot
          change vfsTreeNodes (vfsTreeSet st.tree (dirPos ++ [c.val]) none) p = vfsTreeNodes st.tree p
          unfold vfsTreeNodes
          split
          · exact nodeAt_vfsTreeSet_outside st.tree dirPos c.val none (vfsSplitSegs p) ⟨cm, ch, hGet⟩ hNot
          · rfl
        have hShrunk01 : TreeShrunk st1.tree st.tree := treeShrunk_set_none st.tree dirPos c.val ⟨cm, ch, hGet⟩
        have hCNone1 : nodeAt st1.tree (dirPos ++ [c.val]) = none := by
          simpa [st1] using nodeAt_vfsTreeSet_eq st.tree dirPos c.val none ⟨cm, ch, hGet⟩
        cases hRec : Internal.rmtreeNonDirPrefixM vfsDirOps dirDh rest st1 with
        | mk r st' =>
          rw [hRec] at hSub
          cases r with
          | error e => exact hSub
          | ok opt =>
            cases opt with
            | none =>
              rcases hSub with ⟨hDG', hAllNone, hSame1, hShrunk1, hKeys1, hOpen1, hNext1, hLocks1, hKC1⟩
              refine ⟨hDG', fun e he => ?_, SameOutside_trans hSame01 hSame1, treeShrunk_trans hShrunk1 hShrunk01,
                hKeys1, hOpen1, hNext1, hLocks1, fun hK => hKC1 (vfsKeysComplete_treeShrunk st st1 hK rfl hShrunk01)⟩
              rcases List.mem_cons.mp he with rfl | hR
              · rcases hShrunk1 (dirPos ++ [e.val]) with hN | hEq
                · exact hN
                · rw [hEq]; exact hCNone1
              · exact hAllNone e hR
            | some p =>
              rcases p with ⟨subDir, tail⟩
              rcases hSub with ⟨hLen, hDG', hSubD, hItems', hSame1, hShrunk1, hKeys1, hOpen1, hNext1, hLocks1, hKC1⟩
              refine ⟨Nat.lt_trans hLen (Nat.lt_succ_self _), hDG', hSubD, fun e he => ?_,
                SameOutside_trans hSame01 hSame1, treeShrunk_trans hShrunk1 hShrunk01,
                hKeys1, hOpen1, hNext1, hLocks1, fun hK => hKC1 (vfsKeysComplete_treeShrunk st st1 hK rfl hShrunk01)⟩
              rcases List.mem_cons.mp he with rfl | hR
              · right
                rcases hShrunk1 (dirPos ++ [e.val]) with hN | hEq
                · exact hN
                · rw [hEq]; exact hCNone1
              · exact hItems' e hR
      | symlink _ _ =>
        dsimp only
        simp only [vfsToStat, show (EntryKind.symlink == EntryKind.dir) = false from rfl, Bool.false_eq_true, ↓reduceIte]
        simp only [Bind.bind, StateT.bind]
        rw [vfsDirOps_unlinkAt_def, hLd]
        dsimp only
        rw [hDirNd]
        simp only [hWF, Bool.false_eq_true, ↓reduceIte, hChild]
        let st1 : VfsState :=
          { tree := vfsTreeSet st.tree (dirPos ++ [c.val]) none, keys := st.keys, cwd := st.cwd,
            nonce := st.nonce, locks := st.locks, nextLockId := st.nextLockId, openDirs := st.openDirs,
            nextDirId := st.nextDirId }
        have hLd1 : lookupDir st1 dirDh = some dirPos := hLd
        have hNotSelfPre : ¬ (dirPos ++ [c.val] <+: dirPos) := by
          intro hP
          have hLen := List.IsPrefix.length_le hP
          simp at hLen
          omega
        have hDirNd1 : nodeAt st1.tree dirPos = some (.dir cm) := by
          change nodeAt (vfsTreeSet st.tree (dirPos ++ [c.val]) none) dirPos = some (.dir cm)
          rw [nodeAt_vfsTreeSet_outside st.tree dirPos c.val none dirPos ⟨cm, ch, hGet⟩ hNotSelfPre]
          exact hDirNd
        rcases vfsTreeGet_dir_of_nodeAt hDirNd1 with ⟨ch1, hGet1⟩
        have hSub := ih st1 ch1 hLd1 hGet1
        have hSame01 : SameOutside dirPos st st1 := by
          apply SameOutside_mono ⟨[c.val], rfl⟩
          intro p hNot
          change vfsTreeNodes (vfsTreeSet st.tree (dirPos ++ [c.val]) none) p = vfsTreeNodes st.tree p
          unfold vfsTreeNodes
          split
          · exact nodeAt_vfsTreeSet_outside st.tree dirPos c.val none (vfsSplitSegs p) ⟨cm, ch, hGet⟩ hNot
          · rfl
        have hShrunk01 : TreeShrunk st1.tree st.tree := treeShrunk_set_none st.tree dirPos c.val ⟨cm, ch, hGet⟩
        have hCNone1 : nodeAt st1.tree (dirPos ++ [c.val]) = none := by
          simpa [st1] using nodeAt_vfsTreeSet_eq st.tree dirPos c.val none ⟨cm, ch, hGet⟩
        cases hRec : Internal.rmtreeNonDirPrefixM vfsDirOps dirDh rest st1 with
        | mk r st' =>
          rw [hRec] at hSub
          cases r with
          | error e => exact hSub
          | ok opt =>
            cases opt with
            | none =>
              rcases hSub with ⟨hDG', hAllNone, hSame1, hShrunk1, hKeys1, hOpen1, hNext1, hLocks1, hKC1⟩
              refine ⟨hDG', fun e he => ?_, SameOutside_trans hSame01 hSame1, treeShrunk_trans hShrunk1 hShrunk01,
                hKeys1, hOpen1, hNext1, hLocks1, fun hK => hKC1 (vfsKeysComplete_treeShrunk st st1 hK rfl hShrunk01)⟩
              rcases List.mem_cons.mp he with rfl | hR
              · rcases hShrunk1 (dirPos ++ [e.val]) with hN | hEq
                · exact hN
                · rw [hEq]; exact hCNone1
              · exact hAllNone e hR
            | some p =>
              rcases p with ⟨subDir, tail⟩
              rcases hSub with ⟨hLen, hDG', hSubD, hItems', hSame1, hShrunk1, hKeys1, hOpen1, hNext1, hLocks1, hKC1⟩
              refine ⟨Nat.lt_trans hLen (Nat.lt_succ_self _), hDG', hSubD, fun e he => ?_,
                SameOutside_trans hSame01 hSame1, treeShrunk_trans hShrunk1 hShrunk01,
                hKeys1, hOpen1, hNext1, hLocks1, fun hK => hKC1 (vfsKeysComplete_treeShrunk st st1 hK rfl hShrunk01)⟩
              rcases List.mem_cons.mp he with rfl | hR
              · right
                rcases hShrunk1 (dirPos ++ [e.val]) with hN | hEq
                · exact hN
                · rw [hEq]; exact hCNone1
              · exact hItems' e hR

private theorem dirHandleInvariant_of_subset {s1 s2 : VfsState}
    (hInv : DirHandleInvariant s1) (hSub : ∀ p ∈ s2.openDirs, p ∈ s1.openDirs) (hNext : s2.nextDirId = s1.nextDirId) :
    DirHandleInvariant s2 := by
  intro id pos hMem
  rw [hNext]
  exact hInv id pos (hSub (id, pos) hMem)

private theorem rmtreeProcessM_ok (rootDh : DirHandle) (pos : List String)
    (parSegs : List EntryName) (leaf : EntryName) (remFuel : Nat)
    (subDirFn : EntryName → StateM VfsState (Except FsError Unit))
    (hSubDirOk : ∀ (subDir : EntryName) (stS : VfsState) (cmS : Nat) (chS : String → Option VfsTree),
      VfsKeysComplete stS →
      lookupDir stS rootDh = some pos →
      DirHandleInvariant stS →
      (∀ s ∈ pos, validSeg s = true) →
      (∃ pm₀, nodeAt stS.tree pos = some (.dir pm₀) ∧ pm₀ / 64 % 2 = 1) →
      (∀ k, 0 < k → k ≤ (parSegs ++ [leaf]).length →
        ∃ dm, nodeAt stS.tree (pos ++ ((parSegs ++ [leaf]).take k).map (·.val)) = some (.dir dm) ∧
          dm / 256 % 2 = 1 ∧ dm / 128 % 2 = 1 ∧ dm / 64 % 2 = 1) →
      vfsTreeGet stS.tree (pos ++ (parSegs ++ [leaf] ++ [subDir]).map (·.val)) = some (.dir cmS chS) →
      VfsTreeValidSegs (.dir cmS chS) →
      VfsTreeRemovable remFuel (.dir cmS chS) →
      match subDirFn subDir stS with
      | (Except.error _, _) => False
      | (Except.ok (), stS') =>
        nodeAt stS'.tree (pos ++ (parSegs ++ [leaf] ++ [subDir]).map (·.val)) = none ∧
        SameOutside (pos ++ (parSegs ++ [leaf] ++ [subDir]).map (·.val)) stS stS' ∧
        TreeShrunk stS'.tree stS.tree ∧
        DirHandleInvariant stS' ∧
        stS'.openDirs = stS.openDirs ∧
        stS'.keys = stS.keys ∧
        stS'.locks = stS.locks ∧
        VfsKeysComplete stS')
    (steps : Nat) (items : List EntryName) (st : VfsState)
    (hSteps : items.length ≤ steps)
    (hKeys : VfsKeysComplete st)
    (hLd : lookupDir st rootDh = some pos)
    (hInv : DirHandleInvariant st)
    (hPosValid : ∀ s ∈ pos, validSeg s = true)
    (hPosDir : ∃ pm₀, nodeAt st.tree pos = some (.dir pm₀) ∧ pm₀ / 64 % 2 = 1)
    (hMidAnc : ∀ k, 0 < k → k ≤ parSegs.length →
      ∃ dm, nodeAt st.tree (pos ++ (parSegs.take k).map (·.val)) = some (.dir dm) ∧
        dm / 256 % 2 = 1 ∧ dm / 128 % 2 = 1 ∧ dm / 64 % 2 = 1)
    (hDir : ∃ cm ch, vfsTreeGet st.tree (pos ++ (parSegs ++ [leaf]).map (·.val)) = some (.dir cm ch) ∧
      VfsTreeValidSegs (.dir cm ch) ∧ VfsTreeRemovable (remFuel + 1) (.dir cm ch) ∧
      (∀ s, ch s ≠ none → ∃ e ∈ items, e.val = s)) :
    match Internal.rmtreeProcessM vfsDirOps rootDh (parSegs ++ [leaf]) subDirFn steps items st with
    | (Except.error _, _) => False
    | (Except.ok (), st') =>
      (∃ cm, nodeAt st'.tree (pos ++ (parSegs ++ [leaf]).map (·.val)) = some (.dir cm)) ∧
      (∀ s, nodeAt st'.tree (pos ++ (parSegs ++ [leaf]).map (·.val) ++ [s]) = none) ∧
      SameOutside (pos ++ (parSegs ++ [leaf]).map (·.val)) st st' ∧
      TreeShrunk st'.tree st.tree ∧
      DirHandleInvariant st' ∧
      st'.openDirs = st.openDirs ∧
      st'.keys = st.keys ∧
      st'.locks = st.locks ∧
      VfsKeysComplete st' := by
  induction steps generalizing items st with
  | zero =>
    have hNil : items = [] := by
      cases items with
      | nil => rfl
      | cons _ _ => simp at hSteps
    subst hNil
    rw [Internal.rmtreeProcessM.eq_1]
    rcases hDir with ⟨cm, ch, hGet, _, _, hCov⟩
    have hChNone : ∀ s, nodeAt st.tree (pos ++ (parSegs ++ [leaf]).map (·.val) ++ [s]) = none := by
      intro s
      have hSub := nodeAt_sub_of_vfsTreeGet hGet (q := [s])
      rw [hSub]
      cases hS : ch s with
      | none => simp [nodeAt, vfsTreeGet, hS]
      | some _ =>
        rcases hCov s (by simp [hS]) with ⟨e, he, _⟩
        cases he
    exact ⟨⟨cm, by simp only [nodeAt, hGet, vfsTreeTopNode, Option.map_some]⟩, hChNone,
      SameOutside_refl _ st, treeShrunk_refl st.tree, hInv, rfl, rfl, rfl, hKeys⟩
  | succ s' ih =>
    cases items with
    | nil =>
      rw [Internal.rmtreeProcessM.eq_1]
      rcases hDir with ⟨cm, ch, hGet, _, _, hCov⟩
      have hChNone : ∀ s, nodeAt st.tree (pos ++ (parSegs ++ [leaf]).map (·.val) ++ [s]) = none := by
        intro s
        have hSub := nodeAt_sub_of_vfsTreeGet hGet (q := [s])
        rw [hSub]
        cases hS : ch s with
        | none => simp [nodeAt, vfsTreeGet, hS]
        | some _ =>
          rcases hCov s (by simp [hS]) with ⟨e, he, _⟩
          cases he
      exact ⟨⟨cm, by simp only [nodeAt, hGet, vfsTreeTopNode, Option.map_some]⟩, hChNone,
        SameOutside_refl _ st, treeShrunk_refl st.tree, hInv, rfl, rfl, rfl, hKeys⟩
    | cons hd tl =>
      let dirSegs := parSegs ++ [leaf]
      let dirPos := pos ++ dirSegs.map (·.val)
      rcases hDir with ⟨cm, ch, hGet, hVS, hRem, hCov⟩
      have hRemCopy := hRem
      rw [VfsTreeRemovable.eq_4] at hRem
      rcases hRem with ⟨hCmR, hCmW, hCmX, _⟩
      have hDirNd : nodeAt st.tree dirPos = some (.dir cm) := by
        dsimp only [dirPos, dirSegs]
        simp only [nodeAt, hGet, vfsTreeTopNode, Option.map_some]
      have hWalk := walkDescendM_ok dirSegs rootDh pos st
        (fun dirDh => Internal.rmtreeNonDirPrefixM vfsDirOps dirDh (hd :: tl)) hLd hInv
        (fun k hk => by
          by_cases hk0 : k = 0
          · subst hk0
            rcases hPosDir with ⟨pm₀, hP0, hP0X⟩
            exact ⟨pm₀, by simpa using hP0, fun h => absurd rfl (Nat.ne_of_lt h), hP0X⟩
          · have hkPos : 0 < k := Nat.pos_of_ne_zero hk0
            have hkLePar : k ≤ parSegs.length := by
              simp only [dirSegs, List.length_append, List.length_singleton] at hk
              omega
            rcases hMidAnc k hkPos hkLePar with ⟨dm, hD, hR, _, hEx⟩
            have hTakeEq : dirSegs.take k = parSegs.take k := by
              dsimp [dirSegs]
              rw [List.take_append_of_le_length hkLePar]
            rw [← hTakeEq] at hD
            exact ⟨dm, hD, fun _ => hR, hEx⟩)
        (fun _ => ⟨cm, hDirNd, hCmR⟩)
      have hDirSegsNe : dirSegs ≠ [] := by simp [dirSegs]
      rcases hWalk.2 hDirSegsNe with
        ⟨dirDh, stMid, hPosDh, hLdMid, hTreeMid, hKeysMid, _, _, hLocksMid, hInvMid, hLtMid, hOpenMid, hWalkEq⟩
      have hGetMid : vfsTreeGet stMid.tree dirPos = some (.dir cm ch) := by rw [hTreeMid]; exact hGet
      have hPrefix := rmtreeNonDirPrefixM_ok dirDh dirPos (hd :: tl) stMid cm ch hLdMid hGetMid hCmW hCmX
      rw [Internal.rmtreeProcessM.eq_3 (x_2 := by simp)]
      simp only [Bind.bind, StateT.bind, Pure.pure]
      change match (match Internal.walkDescendM vfsDirOps rootDh dirSegs
              (fun dirDh => Internal.rmtreeNonDirPrefixM vfsDirOps dirDh (hd :: tl)) st with
            | (a, s) =>
              (match a with
                | Except.error e => pure (Except.error e)
                | Except.ok none => pure (Except.ok ())
                | Except.ok (some (subDir, rest)) =>
                  StateT.bind (subDirFn subDir) fun __do_lift =>
                    match __do_lift with
                    | Except.error e => pure (Except.error e)
                    | Except.ok () => Internal.rmtreeProcessM vfsDirOps rootDh dirSegs subDirFn s' rest) s) with
        | (Except.error _, _) => False
        | (Except.ok (), st') => _
      rw [hWalkEq, bracketCloseDirM_run]
      cases hRunPfx : Internal.rmtreeNonDirPrefixM vfsDirOps dirDh (hd :: tl) stMid with
      | mk rPfx stPfx =>
        rw [hRunPfx] at hPrefix
        cases rPfx with
        | error e => exact hPrefix
        | ok opt =>
          dsimp only
          have hMidNodes : stMid.nodes = st.nodes := nodes_eq_of_tree_eq stMid st hTreeMid
          have hKCMid : VfsKeysComplete stMid := by
            intro segs hNe
            rw [hKeysMid]
            apply hKeys segs
            rw [← hTreeMid]
            exact hNe
          cases opt with
          | none =>
            rcases hPrefix with ⟨hDG', hAllNonePfx, hSamePfx, hShrunkPfx, hKeysPfx, hOpenPfx, hNextPfx, hLocksPfx, hKCPfx⟩
            have hClosePfx := vfsDirOps_closeDir_fresh dirDh stPfx dirPos hPosDh st.openDirs
              (hOpenPfx.trans hOpenMid) hLtMid
            rw [hClosePfx]
            dsimp only
            let stClose : VfsState :=
              { tree := stPfx.tree, keys := stPfx.keys, cwd := stPfx.cwd, nonce := stPfx.nonce,
                locks := stPfx.locks, nextLockId := stPfx.nextLockId, openDirs := st.openDirs,
                nextDirId := stPfx.nextDirId }
            have hSameClose : SameOutside dirPos st stClose := by
              intro p hNot
              change stPfx.nodes p = st.nodes p
              rw [hSamePfx p hNot, hMidNodes]
            have hShrunkClose : TreeShrunk stClose.tree st.tree := by
              change TreeShrunk stPfx.tree st.tree
              rw [← hTreeMid]
              exact hShrunkPfx
            rcases hDG' with ⟨chPfx, hGetPfx⟩
            have hDirNdClose : nodeAt stClose.tree dirPos = some (.dir cm) := by
              change nodeAt stPfx.tree dirPos = some (.dir cm)
              simp [nodeAt, hGetPfx, vfsTreeTopNode]
            have hEmptyClose : ∀ s, nodeAt stClose.tree (dirPos ++ [s]) = none := by
              intro s
              change nodeAt stPfx.tree (dirPos ++ [s]) = none
              cases hSubP : chPfx s with
              | none =>
                rw [nodeAt_sub_of_vfsTreeGet hGetPfx]
                simp [nodeAt, vfsTreeGet, hSubP]
              | some _ =>
                have hNe : nodeAt stPfx.tree (dirPos ++ [s]) ≠ none := by
                  rw [nodeAt_sub_of_vfsTreeGet hGetPfx]
                  simp [nodeAt, vfsTreeGet, hSubP]
                have hOrigNe : nodeAt st.tree (dirPos ++ [s]) ≠ none := by
                  rcases hShrunkClose (dirPos ++ [s]) with hN | hEq
                  · exact absurd hN hNe
                  · change nodeAt stPfx.tree (dirPos ++ [s]) = nodeAt st.tree (dirPos ++ [s]) at hEq
                    rw [← hEq]; exact hNe
                have hChS : ch s ≠ none := by
                  rw [nodeAt_sub_of_vfsTreeGet hGet] at hOrigNe
                  intro hC0
                  simp [nodeAt, vfsTreeGet, hC0] at hOrigNe
                rcases hCov s hChS with ⟨e, he, hEVal⟩
                rw [← hEVal]
                exact hAllNonePfx e he
            have hInvClose : DirHandleInvariant stClose :=
              dirHandleInvariant_of_subset hInvMid (fun p hp => by
                change p ∈ st.openDirs at hp
                rw [hOpenMid]
                exact List.mem_cons_of_mem _ hp) hNextPfx
            exact ⟨⟨cm, hDirNdClose⟩, hEmptyClose, hSameClose, hShrunkClose, hInvClose, rfl,
              hKeysPfx.trans hKeysMid, hLocksPfx.trans hLocksMid, hKCPfx hKCMid⟩
          | some pair =>
            rcases pair with ⟨subDir, rest⟩
            rcases hPrefix with
              ⟨hRestLen, hDG', hSubDirNd, hItemsPfx, hSamePfx, hShrunkPfx, hKeysPfx, hOpenPfx, hNextPfx, hLocksPfx, hKCPfx⟩
            have hClosePfx := vfsDirOps_closeDir_fresh dirDh stPfx dirPos hPosDh st.openDirs
              (hOpenPfx.trans hOpenMid) hLtMid
            rw [hClosePfx]
            dsimp only
            let stClose : VfsState :=
              { tree := stPfx.tree, keys := stPfx.keys, cwd := stPfx.cwd, nonce := stPfx.nonce,
                locks := stPfx.locks, nextLockId := stPfx.nextLockId, openDirs := st.openDirs,
                nextDirId := stPfx.nextDirId }
            have hSameClose : SameOutside dirPos st stClose := by
              intro p hNot
              change stPfx.nodes p = st.nodes p
              rw [hSamePfx p hNot, hMidNodes]
            have hShrunkClose : TreeShrunk stClose.tree st.tree := by
              change TreeShrunk stPfx.tree st.tree
              rw [← hTreeMid]
              exact hShrunkPfx
            have hInvClose : DirHandleInvariant stClose :=
              dirHandleInvariant_of_subset hInvMid (fun p hp => by
                change p ∈ st.openDirs at hp
                rw [hOpenMid]
                exact List.mem_cons_of_mem _ hp) hNextPfx
            have hKCClose : VfsKeysComplete stClose := hKCPfx hKCMid
            have hLdClose : lookupDir stClose rootDh = some pos := hLd
            have hPosDirClose : ∃ pm₀, nodeAt stClose.tree pos = some (.dir pm₀) ∧ pm₀ / 64 % 2 = 1 := by
              rcases hPosDir with ⟨pm₀, hP0, hP0X⟩
              have hNotPrefPos : ¬ (dirPos <+: pos) := by
                intro hP
                have hLen := List.IsPrefix.length_le hP
                simp only [dirPos, dirSegs, List.length_append, List.length_map, List.length_singleton] at hLen
                omega
              refine ⟨pm₀, ?_, hP0X⟩
              rw [SameOutside_nodeAt_eq hSameClose hNotPrefPos hPosValid]
              exact hP0
            have hDirValid : ∀ s ∈ dirPos, validSeg s = true := by
              intro s hs
              rcases List.mem_append.mp hs with hp | hd_
              · exact hPosValid s hp
              · simp only [List.mem_map] at hd_
                rcases hd_ with ⟨e, _, rfl⟩
                exact e.valid
            have hAncClose : ∀ k, 0 < k → k ≤ dirSegs.length →
                ∃ dm, nodeAt stClose.tree (pos ++ (dirSegs.take k).map (·.val)) = some (.dir dm) ∧
                  dm / 256 % 2 = 1 ∧ dm / 128 % 2 = 1 ∧ dm / 64 % 2 = 1 := by
              intro k hkPos hkLe
              by_cases hkEq : k = dirSegs.length
              · subst hkEq
                simp only [List.take_length]
                rcases hDG' with ⟨chPfx, hGetPfx⟩
                exact ⟨cm, by change nodeAt stPfx.tree dirPos = some (.dir cm); simp [nodeAt, hGetPfx, vfsTreeTopNode],
                  hCmR, hCmW, hCmX⟩
              · have hkLePar : k ≤ parSegs.length := by
                  simp only [dirSegs, List.length_append, List.length_singleton] at hkLe hkEq
                  omega
                have hTakeEq : dirSegs.take k = parSegs.take k := by
                  dsimp [dirSegs]
                  rw [List.take_append_of_le_length hkLePar]
                rcases hMidAnc k hkPos hkLePar with ⟨dm, hD, hR, hW, hEx⟩
                refine ⟨dm, ?_, hR, hW, hEx⟩
                have hSubValid : ∀ s ∈ pos ++ (dirSegs.take k).map (·.val), validSeg s = true := by
                  intro s hs
                  rcases List.mem_append.mp hs with hp | ht
                  · exact hPosValid s hp
                  · simp only [List.mem_map] at ht
                    rcases ht with ⟨e, _, rfl⟩
                    exact e.valid
                have hNotPrefK : ¬ (dirPos <+: pos ++ (dirSegs.take k).map (·.val)) := by
                  intro hP
                  have hLen := List.IsPrefix.length_le hP
                  simp only [dirPos, dirSegs, List.length_append, List.length_map, List.length_singleton,
                    List.length_take] at hLen
                  omega
                rw [SameOutside_nodeAt_eq hSameClose hNotPrefK hSubValid, hTakeEq]
                exact hD
            rcases hDG' with ⟨chPfx, hGetPfx⟩
            have hGetClose : vfsTreeGet stClose.tree dirPos = some (.dir cm chPfx) := hGetPfx
            have hShrunkDir : TreeShrunk (.dir cm chPfx) (.dir cm ch) :=
              treeShrunk_sub_of_vfsTreeGet hShrunkClose hGetClose hGet
            have hVSClose : VfsTreeValidSegs (.dir cm chPfx) := vfsTreeValidSegs_treeShrunk hVS hShrunkDir
            have hRemClose : VfsTreeRemovable (remFuel + 1) (.dir cm chPfx) :=
              vfsTreeRemovable_treeShrunk (remFuel + 1) hShrunkDir hRemCopy
            rcases hSubDirNd with ⟨dmSub, hSubNd⟩
            have hSubTree : ∃ chS, chPfx subDir.val = some (.dir dmSub chS) := by
              have hN : nodeAt stClose.tree (dirPos ++ [subDir.val]) = some (.dir dmSub) := hSubNd
              rw [nodeAt_sub_of_vfsTreeGet hGetClose] at hN
              cases hC : chPfx subDir.val with
              | none => simp [nodeAt, vfsTreeGet, hC] at hN
              | some subT =>
                simp only [nodeAt, vfsTreeGet, hC, Option.map_some, Option.some.injEq] at hN
                cases subT with
                | file _ _ => cases hN
                | symlink _ _ => cases hN
                | dir mS chS =>
                  simp only [vfsTreeTopNode, VfsNode.dir.injEq] at hN
                  subst hN
                  exact ⟨chS, rfl⟩
            rcases hSubTree with ⟨chS, hChS⟩
            have hSubGet : vfsTreeGet stClose.tree (pos ++ (parSegs ++ [leaf] ++ [subDir]).map (·.val)) =
                some (.dir dmSub chS) := by
              have hPathEq : pos ++ (parSegs ++ [leaf] ++ [subDir]).map (·.val) = dirPos ++ [subDir.val] := by
                simp only [dirPos, dirSegs, List.map_append, List.map_singleton, List.append_assoc]
              rw [hPathEq, vfsTreeGet_sub_of_vfsTreeGet hGetClose]
              simp [vfsTreeGet, hChS]
            have hVSSub : VfsTreeValidSegs (.dir dmSub chS) := by
              intro segs hNe s hs
              apply hVSClose (subDir.val :: segs) _ s (List.mem_cons_of_mem _ hs)
              have hAtSub : nodeAt (.dir cm chPfx) (subDir.val :: segs) = nodeAt (.dir dmSub chS) segs := by
                simp only [nodeAt, vfsTreeGet, hChS]
              rw [hAtSub]
              exact hNe
            have hRemSub : VfsTreeRemovable remFuel (.dir dmSub chS) := by
              rw [VfsTreeRemovable.eq_4] at hRemClose
              exact hRemClose.2.2.2 subDir.val (.dir dmSub chS) hChS
            have hSubCall := hSubDirOk subDir stClose dmSub chS hKCClose hLdClose hInvClose hPosValid hPosDirClose
              hAncClose hSubGet hVSSub hRemSub
            simp only [StateT.bind]
            cases hSubRes : subDirFn subDir stClose with
            | mk rSub stSub =>
              rw [hSubRes] at hSubCall
              cases rSub with
              | error e => exact hSubCall
              | ok u =>
                cases u
                rcases hSubCall with
                  ⟨hSubGone, hSameSub, hShrunkSub, hInvSub, hOpenSub, hKeysSub, hLocksSub, hKCSub⟩
                have hPathSubEq : pos ++ (parSegs ++ [leaf] ++ [subDir]).map (·.val) = dirPos ++ [subDir.val] := by
                  simp only [dirPos, dirSegs, List.map_append, List.map_singleton, List.append_assoc]
                rw [hPathSubEq] at hSubGone hSameSub
                have hSameCloseSub : SameOutside dirPos stClose stSub :=
                  SameOutside_mono ⟨[subDir.val], rfl⟩ hSameSub
                have hLdSub : lookupDir stSub rootDh = some pos := by
                  unfold lookupDir at hLdClose ⊢
                  rw [hOpenSub]
                  exact hLdClose
                have hPosDirSub : ∃ pm₀, nodeAt stSub.tree pos = some (.dir pm₀) ∧ pm₀ / 64 % 2 = 1 := by
                  rcases hPosDirClose with ⟨pm₀, hP0, hP0X⟩
                  have hNotPrefPos : ¬ (dirPos <+: pos) := by
                    intro hP
                    have hLen := List.IsPrefix.length_le hP
                    simp only [dirPos, dirSegs, List.length_append, List.length_map, List.length_singleton] at hLen
                    omega
                  refine ⟨pm₀, ?_, hP0X⟩
                  rw [SameOutside_nodeAt_eq hSameCloseSub hNotPrefPos hPosValid]
                  exact hP0
                have hMidAncSub : ∀ k, 0 < k → k ≤ parSegs.length →
                    ∃ dm, nodeAt stSub.tree (pos ++ (parSegs.take k).map (·.val)) = some (.dir dm) ∧
                      dm / 256 % 2 = 1 ∧ dm / 128 % 2 = 1 ∧ dm / 64 % 2 = 1 := by
                  intro k hkPos hkLe
                  have hLtDir : k ≤ dirSegs.length := Nat.le_trans hkLe (by simp [dirSegs])
                  rcases hAncClose k hkPos hLtDir with ⟨dm, hD, hR, hW, hEx⟩
                  have hTakeEq : dirSegs.take k = parSegs.take k := by
                    dsimp [dirSegs]
                    rw [List.take_append_of_le_length hkLe]
                  rw [hTakeEq] at hD
                  have hSubValid : ∀ s ∈ pos ++ (parSegs.take k).map (·.val), validSeg s = true := by
                    intro s hs
                    rcases List.mem_append.mp hs with hp | ht
                    · exact hPosValid s hp
                    · simp only [List.mem_map] at ht
                      rcases ht with ⟨e, _, rfl⟩
                      exact e.valid
                  have hNotPrefK : ¬ (dirPos <+: pos ++ (parSegs.take k).map (·.val)) := by
                    intro hP
                    have hLen := List.IsPrefix.length_le hP
                    simp only [dirPos, dirSegs, List.length_append, List.length_map, List.length_singleton,
                      List.length_take] at hLen
                    omega
                  refine ⟨dm, ?_, hR, hW, hEx⟩
                  rw [SameOutside_nodeAt_eq hSameCloseSub hNotPrefK hSubValid]
                  exact hD
                have hDirNdSub : nodeAt stSub.tree dirPos = some (.dir cm) := by
                  have hNotPrefDir : ¬ (dirPos ++ [subDir.val] <+: dirPos) := by
                    intro hP
                    have hLen := List.IsPrefix.length_le hP
                    simp at hLen
                    omega
                  rw [SameOutside_nodeAt_eq hSameSub hNotPrefDir hDirValid]
                  change nodeAt stPfx.tree dirPos = some (.dir cm)
                  simp [nodeAt, hGetPfx, vfsTreeTopNode]
                rcases vfsTreeGet_dir_of_nodeAt hDirNdSub with ⟨chSub, hGetSub⟩
                have hShrunkDirSub : TreeShrunk (.dir cm chSub) (.dir cm chPfx) :=
                  treeShrunk_sub_of_vfsTreeGet hShrunkSub hGetSub hGetClose
                have hVSSub' : VfsTreeValidSegs (.dir cm chSub) := vfsTreeValidSegs_treeShrunk hVSClose hShrunkDirSub
                have hRemSub' : VfsTreeRemovable (remFuel + 1) (.dir cm chSub) :=
                  vfsTreeRemovable_treeShrunk (remFuel + 1) hShrunkDirSub hRemClose
                have hCovSub : ∀ s, chSub s ≠ none → ∃ e ∈ rest, e.val = s := by
                  intro s hsNe
                  have hSNe : nodeAt stSub.tree (dirPos ++ [s]) ≠ none := by
                    rw [nodeAt_sub_of_vfsTreeGet hGetSub]
                    intro hN
                    cases hC : chSub s with
                    | none => exact hsNe hC
                    | some _ => simp [nodeAt, vfsTreeGet, hC] at hN
                  have hNeSub : s ≠ subDir.val := by
                    intro hEqS
                    rw [hEqS] at hSNe
                    exact hSNe hSubGone
                  have hSCloseNe : nodeAt stClose.tree (dirPos ++ [s]) ≠ none := by
                    rcases hShrunkSub (dirPos ++ [s]) with hN | hEq
                    · exact absurd hN hSNe
                    · rw [← hEq]; exact hSNe
                  have hSOrigNe : nodeAt st.tree (dirPos ++ [s]) ≠ none := by
                    rcases hShrunkClose (dirPos ++ [s]) with hN | hEq
                    · exact absurd hN hSCloseNe
                    · rw [← hEq]; exact hSCloseNe
                  have hChOrig : ch s ≠ none := by
                    rw [nodeAt_sub_of_vfsTreeGet hGet] at hSOrigNe
                    intro hC0
                    simp [nodeAt, vfsTreeGet, hC0] at hSOrigNe
                  rcases hCov s hChOrig with ⟨e, he, hEVal⟩
                  rcases hItemsPfx e he with hIn | hGone
                  · rcases List.mem_cons.mp hIn with rfl | hInRest
                    · exact absurd hEVal.symm hNeSub
                    · exact ⟨e, hInRest, hEVal⟩
                  · rw [hEVal] at hGone
                    exact absurd hGone hSCloseNe
                have hNextStep := ih rest stSub (by omega) hKCSub hLdSub hInvSub hPosDirSub hMidAncSub
                  ⟨cm, chSub, hGetSub, hVSSub', hRemSub', hCovSub⟩
                simp only [Bind.bind]
                cases hRecNext : Internal.rmtreeProcessM vfsDirOps rootDh dirSegs subDirFn s' rest stSub with
                | mk rFinal stFinal =>
                  rw [hRecNext] at hNextStep
                  cases rFinal with
                  | error e => exact hNextStep
                  | ok uFinal =>
                    cases uFinal
                    rcases hNextStep with
                      ⟨hDirFinal, hEmptyFinal, hSameFinal, hShrunkFinal, hInvFinal, hOpenFinal, hKeysFinal, hLocksFinal, hKCFinal⟩
                    exact ⟨hDirFinal, hEmptyFinal,
                      SameOutside_trans hSameClose (SameOutside_trans hSameCloseSub hSameFinal),
                      treeShrunk_trans hShrunkFinal (treeShrunk_trans hShrunkSub hShrunkClose),
                      hInvFinal, hOpenFinal.trans hOpenSub,
                      hKeysFinal.trans (hKeysSub.trans (hKeysPfx.trans hKeysMid)),
                      hLocksFinal.trans (hLocksSub.trans (hLocksPfx.trans hLocksMid)),
                      hKCFinal⟩

private theorem rmtreeDirAtM_step (rootDh : DirHandle) (pos : List String)
    (remFuel : Nat)
    (hSubDirOk : ∀ (parSegs : List EntryName) (leaf : EntryName) (subDir : EntryName) (stS : VfsState)
      (cmS : Nat) (chS : String → Option VfsTree),
      VfsKeysComplete stS →
      lookupDir stS rootDh = some pos →
      DirHandleInvariant stS →
      (∀ s ∈ pos, validSeg s = true) →
      (∃ pm₀, nodeAt stS.tree pos = some (.dir pm₀) ∧ pm₀ / 64 % 2 = 1) →
      (∀ k, 0 < k → k ≤ (parSegs ++ [leaf]).length →
        ∃ dm, nodeAt stS.tree (pos ++ ((parSegs ++ [leaf]).take k).map (·.val)) = some (.dir dm) ∧
          dm / 256 % 2 = 1 ∧ dm / 128 % 2 = 1 ∧ dm / 64 % 2 = 1) →
      vfsTreeGet stS.tree (pos ++ (parSegs ++ [leaf] ++ [subDir]).map (·.val)) = some (.dir cmS chS) →
      VfsTreeValidSegs (.dir cmS chS) →
      VfsTreeRemovable remFuel (.dir cmS chS) →
      match Internal.rmtreeDirAtM vfsDirOps rootDh (parSegs ++ [leaf]) subDir remFuel stS with
      | (Except.error _, _) => False
      | (Except.ok (), stS') =>
        nodeAt stS'.tree (pos ++ (parSegs ++ [leaf] ++ [subDir]).map (·.val)) = none ∧
        SameOutside (pos ++ (parSegs ++ [leaf] ++ [subDir]).map (·.val)) stS stS' ∧
        TreeShrunk stS'.tree stS.tree ∧
        DirHandleInvariant stS' ∧
        stS'.openDirs = stS.openDirs ∧
        stS'.keys = stS.keys ∧
        stS'.locks = stS.locks ∧
        VfsKeysComplete stS')
    (parSegs : List EntryName) (leaf : EntryName) (st : VfsState)
    (hKeys : VfsKeysComplete st)
    (hLd : lookupDir st rootDh = some pos)
    (hInv : DirHandleInvariant st)
    (hPosValid : ∀ s ∈ pos, validSeg s = true)
    (hPosDir : ∃ pm₀, nodeAt st.tree pos = some (.dir pm₀) ∧
      (parSegs = [] → pm₀ / 128 % 2 = 1) ∧ pm₀ / 64 % 2 = 1)
    (hMidAnc : ∀ k, 0 < k → k ≤ parSegs.length →
      ∃ dm, nodeAt st.tree (pos ++ (parSegs.take k).map (·.val)) = some (.dir dm) ∧
        dm / 256 % 2 = 1 ∧ dm / 128 % 2 = 1 ∧ dm / 64 % 2 = 1)
    (hDir : ∃ cm ch, vfsTreeGet st.tree (pos ++ (parSegs ++ [leaf]).map (·.val)) = some (.dir cm ch) ∧
      VfsTreeValidSegs (.dir cm ch) ∧ VfsTreeRemovable (remFuel + 1) (.dir cm ch)) :
    match Internal.rmtreeDirAtM vfsDirOps rootDh parSegs leaf (remFuel + 1) st with
    | (Except.error _, _) => False
    | (Except.ok (), st') =>
      nodeAt st'.tree (pos ++ (parSegs ++ [leaf]).map (·.val)) = none ∧
      SameOutside (pos ++ (parSegs ++ [leaf]).map (·.val)) st st' ∧
      TreeShrunk st'.tree st.tree ∧
      DirHandleInvariant st' ∧
      st'.openDirs = st.openDirs ∧
      st'.keys = st.keys ∧
      st'.locks = st.locks ∧
      VfsKeysComplete st' := by
    rcases hDir with ⟨cm, ch, hGet, hVS, hRem⟩
    have hRemCopy := hRem
    rw [VfsTreeRemovable.eq_4] at hRem
    rcases hRem with ⟨hCmR, hCmW, hCmX, _⟩
    let dirSegs := parSegs ++ [leaf]
    let dirPos := pos ++ dirSegs.map (·.val)
    have hDirNd : nodeAt st.tree dirPos = some (.dir cm) := by
      dsimp only [dirPos, dirSegs]
      simp only [nodeAt, hGet, vfsTreeTopNode, Option.map_some]
    rw [Internal.rmtreeDirAtM.eq_2]
    simp only [Bind.bind, StateT.bind, Pure.pure]
    have hWalkRead := walkDescendM_ok dirSegs rootDh pos st
      (fun dirDh => vfsDirOps.readDirAt dirDh) hLd hInv
      (fun k hk => by
        by_cases hk0 : k = 0
        · subst hk0
          rcases hPosDir with ⟨pm₀, hP0, _, hP0X⟩
          exact ⟨pm₀, by simpa using hP0, fun h => absurd rfl (Nat.ne_of_lt h), hP0X⟩
        · have hkPos : 0 < k := Nat.pos_of_ne_zero hk0
          have hkLePar : k ≤ parSegs.length := by
            simp only [dirSegs, List.length_append, List.length_singleton] at hk
            omega
          rcases hMidAnc k hkPos hkLePar with ⟨dm, hD, hR, _, hEx⟩
          have hTakeEq : dirSegs.take k = parSegs.take k := by
            dsimp [dirSegs]
            rw [List.take_append_of_le_length hkLePar]
          rw [← hTakeEq] at hD
          exact ⟨dm, hD, fun _ => hR, hEx⟩)
      (fun _ => ⟨cm, hDirNd, hCmR⟩)
    have hDirSegsNe : dirSegs ≠ [] := by simp [dirSegs]
    rcases hWalkRead.2 hDirSegsNe with
      ⟨dirDh, stMid, hPosDh, hLdMid, hTreeMid, hKeysMid, _, _, hLocksMid, hInvMid, hLtMid, hOpenMid, hWalkReadEq⟩
    have hDirNdMid : nodeAt stMid.tree dirPos = some (.dir cm) := by rw [hTreeMid]; exact hDirNd
    have hCmRF : (cm / 256 % 2 == 0) = false := by rw [hCmR]; decide
    have hReadOk : vfsDirOps.readDirAt dirDh stMid = (.ok (mVfsReadDirAtEntries stMid dirPos), stMid) := by
      rw [vfsDirOps_readDirAt_def, hLdMid]
      dsimp only
      rw [hDirNdMid]
      simp only [hCmRF, Bool.false_eq_true, ↓reduceIte]
      rfl
    have hCloseMid := vfsDirOps_closeDir_fresh dirDh stMid dirPos hPosDh st.openDirs hOpenMid hLtMid
    let stClose : VfsState :=
      { tree := stMid.tree, keys := stMid.keys, cwd := stMid.cwd, nonce := stMid.nonce,
        locks := stMid.locks, nextLockId := stMid.nextLockId, openDirs := st.openDirs,
        nextDirId := stMid.nextDirId }
    have hDirValid : ∀ s ∈ dirPos, validSeg s = true := by
      intro s hs
      rcases List.mem_append.mp hs with hp | hd_
      · exact hPosValid s hp
      · simp only [List.mem_map] at hd_
        rcases hd_ with ⟨e, _, rfl⟩
        exact e.valid
    let sorted := Internal.sortEntryNames (mVfsReadDirAtEntries stMid dirPos)
    have hKCMid : VfsKeysComplete stMid := by
      intro segs hNe
      rw [hKeysMid]
      apply hKeys segs
      rw [← hTreeMid]
      exact hNe
    have hCovSorted : ∀ s, ch s ≠ none → ∃ e ∈ sorted, e.val = s := by
      intro s hsNe
      have hLiveMid : nodeAt stMid.tree (dirPos ++ [s]) ≠ none := by
        rw [hTreeMid, nodeAt_sub_of_vfsTreeGet hGet]
        intro hN
        cases hC : ch s with
        | none => exact hsNe hC
        | some _ => simp [nodeAt, vfsTreeGet, hC] at hN
      have hsValid : validSeg s = true := by
        apply hVS [s] _ s List.mem_cons_self
        rw [← nodeAt_sub_of_vfsTreeGet hGet, ← hTreeMid]
        exact hLiveMid
      let e : EntryName := { val := s, valid := hsValid }
      refine ⟨e, ?_, rfl⟩
      rw [(List.mergeSort_perm _ _).mem_iff]
      exact mVfsReadDirAtEntries_mem_of_key stMid dirPos e hDirValid (hKCMid _ hLiveMid) hLiveMid
    have hInvClose : DirHandleInvariant stClose :=
      dirHandleInvariant_of_subset hInvMid (fun p hp => by
        change p ∈ st.openDirs at hp
        rw [hOpenMid]
        exact List.mem_cons_of_mem _ hp) rfl
    have hKCClose : VfsKeysComplete stClose := hKCMid
    have hLdClose : lookupDir stClose rootDh = some pos := hLd
    have hPosDirClose : ∃ pm₀, nodeAt stClose.tree pos = some (.dir pm₀) ∧ pm₀ / 64 % 2 = 1 := by
      rcases hPosDir with ⟨pm₀, hP0, _, hP0X⟩
      exact ⟨pm₀, by change nodeAt stMid.tree pos = some (.dir pm₀); rw [hTreeMid]; exact hP0, hP0X⟩
    have hMidAncClose : ∀ k, 0 < k → k ≤ parSegs.length →
        ∃ dm, nodeAt stClose.tree (pos ++ (parSegs.take k).map (·.val)) = some (.dir dm) ∧
          dm / 256 % 2 = 1 ∧ dm / 128 % 2 = 1 ∧ dm / 64 % 2 = 1 := by
      intro k hkPos hkLe
      rcases hMidAnc k hkPos hkLe with ⟨dm, hD, hR, hW, hEx⟩
      exact ⟨dm, by change nodeAt stMid.tree _ = some (.dir dm); rw [hTreeMid]; exact hD, hR, hW, hEx⟩
    have hGetClose : vfsTreeGet stClose.tree dirPos = some (.dir cm ch) := by
      change vfsTreeGet stMid.tree dirPos = some (.dir cm ch)
      rw [hTreeMid]; exact hGet
    have hProc := rmtreeProcessM_ok rootDh pos parSegs leaf remFuel
      (fun subDir => Internal.rmtreeDirAtM vfsDirOps rootDh (parSegs ++ [leaf]) subDir remFuel)
      (hSubDirOk parSegs leaf)
      sorted.length sorted stClose (Nat.le_refl _) hKCClose hLdClose hInvClose hPosValid hPosDirClose hMidAncClose
      ⟨cm, ch, hGetClose, hVS, hRemCopy, hCovSorted⟩
    change match (match Internal.walkDescendM vfsDirOps rootDh dirSegs (fun dirDh => vfsDirOps.readDirAt dirDh) st with
        | (rRead, s0) =>
          (match rRead with
            | Except.error e => pure (Except.error e)
            | Except.ok rawNames =>
              have sorted := Internal.sortEntryNames rawNames;
              StateT.bind
                (Internal.rmtreeProcessM vfsDirOps rootDh dirSegs
                  (fun subDir => Internal.rmtreeDirAtM vfsDirOps rootDh dirSegs subDir remFuel) sorted.length sorted)
                fun __do_lift =>
                  match __do_lift with
                  | Except.error e => pure (Except.error e)
                  | Except.ok () => Internal.walkDescendM vfsDirOps rootDh parSegs fun parDh => vfsDirOps.unlinkAt parDh leaf true) s0) with
      | (Except.error _, _) => False
      | (Except.ok (), st') => _
    rw [hWalkReadEq, bracketCloseDirM_run, hReadOk]
    dsimp only
    rw [hCloseMid]
    dsimp only
    simp only [Bind.bind, StateT.bind, Pure.pure]
    cases hProcRes : Internal.rmtreeProcessM vfsDirOps rootDh dirSegs
        (fun subDir => Internal.rmtreeDirAtM vfsDirOps rootDh dirSegs subDir remFuel) sorted.length sorted stClose with
    | mk rProc stP =>
      rw [hProcRes] at hProc
      cases rProc with
      | error e => exact hProc
      | ok uP =>
        cases uP
        dsimp only
        rcases hProc with
          ⟨⟨cmP, hDirNdP⟩, hEmptyP, hSameP, hShrunkP, hInvP, hOpenP, hKeysP, hLocksP, hKCP⟩
        have hSameStClose : SameOutside dirPos st stClose := by
          intro p hNot
          change stMid.nodes p = st.nodes p
          rw [nodes_eq_of_tree_eq stMid st hTreeMid]
        have hShrunkStClose : TreeShrunk stClose.tree st.tree := by
          change TreeShrunk stMid.tree st.tree
          rw [hTreeMid]
          exact treeShrunk_refl st.tree
        have hSameAllP : SameOutside dirPos st stP := SameOutside_trans hSameStClose hSameP
        have hShrunkAllP : TreeShrunk stP.tree st.tree := treeShrunk_trans hShrunkP hShrunkStClose
        have hLdP : lookupDir stP rootDh = some pos := by
          unfold lookupDir at hLdClose ⊢
          rw [hOpenP]
          exact hLdClose
        have hParPosValid : ∀ s ∈ pos ++ parSegs.map (·.val), validSeg s = true := by
          intro s hs
          rcases List.mem_append.mp hs with hp | hr
          · exact hPosValid s hp
          · simp only [List.mem_map] at hr
            rcases hr with ⟨e, _, rfl⟩
            exact e.valid
        have hNotPrefPar : ¬ (dirPos <+: pos ++ parSegs.map (·.val)) := by
          intro hP
          have hLen := List.IsPrefix.length_le hP
          simp only [dirPos, dirSegs, List.length_append, List.length_map, List.length_singleton] at hLen
          omega
        have hParDirP : ∃ pmP, nodeAt stP.tree (pos ++ parSegs.map (·.val)) = some (.dir pmP) ∧
            pmP / 128 % 2 = 1 ∧ pmP / 64 % 2 = 1 := by
          by_cases hParNil : parSegs = []
          · subst hParNil
            rcases hPosDir with ⟨pm₀, hP0, hP0W, hP0X⟩
            refine ⟨pm₀, ?_, hP0W rfl, hP0X⟩
            simpa using SameOutside_nodeAt_eq hSameAllP (by simpa using hNotPrefPar) hPosValid |>.trans hP0
          · have hPosLen : 0 < parSegs.length := by cases parSegs <;> simp_all
            rcases hMidAnc parSegs.length hPosLen (Nat.le_refl _) with ⟨dm, hD, _, hW, hX⟩
            simp only [List.take_length] at hD
            refine ⟨dm, ?_, hW, hX⟩
            exact SameOutside_nodeAt_eq hSameAllP hNotPrefPar hParPosValid |>.trans hD
        rcases hParDirP with ⟨pmP, hParNdP, hParWP, hParXP⟩
        have hParWFP : (pmP / 128 % 2 == 0 || pmP / 64 % 2 == 0) = false := by simp [hParWP, hParXP]
        have hEmptyFalse : mDirHasLiveChild stP dirPos = false :=
          mDirHasLiveChild_false_of_empty stP dirPos (by simp [dirPos, dirSegs]) hDirValid hEmptyP
        have hWalkUnlink := walkDescendM_ok parSegs rootDh pos stP
          (fun parDh => vfsDirOps.unlinkAt parDh leaf true) hLdP hInvP
          (fun k hk => by
            by_cases hk0 : k = 0
            · subst hk0
              rcases hPosDir with ⟨pm₀, hP0, _, hP0X⟩
              have hP0P : nodeAt stP.tree pos = some (.dir pm₀) := by
                have hNot0 : ¬ (dirPos <+: pos) := by
                  intro hP
                  have hLen := List.IsPrefix.length_le hP
                  simp only [dirPos, dirSegs, List.length_append, List.length_map, List.length_singleton] at hLen
                  omega
                exact SameOutside_nodeAt_eq hSameAllP hNot0 hPosValid |>.trans hP0
              exact ⟨pm₀, by simpa using hP0P, fun h => absurd rfl (Nat.ne_of_lt h), hP0X⟩
            · have hkPos : 0 < k := Nat.pos_of_ne_zero hk0
              rcases hMidAnc k hkPos (Nat.le_of_lt hk) with ⟨dm, hD, hR, _, hEx⟩
              have hSubV : ∀ s ∈ pos ++ (parSegs.take k).map (·.val), validSeg s = true := by
                intro s hs
                rcases List.mem_append.mp hs with hp | hr
                · exact hPosValid s hp
                · simp only [List.mem_map] at hr
                  rcases hr with ⟨e, _, rfl⟩
                  exact e.valid
              have hNotK : ¬ (dirPos <+: pos ++ (parSegs.take k).map (·.val)) := by
                intro hP
                have hLen := List.IsPrefix.length_le hP
                simp only [dirPos, dirSegs, List.length_append, List.length_map, List.length_singleton,
                  List.length_take] at hLen
                omega
              exact ⟨dm, SameOutside_nodeAt_eq hSameAllP hNotK hSubV |>.trans hD, fun _ => hR, hEx⟩)
          (fun hParNe => by
            have hPosLen : 0 < parSegs.length := by cases parSegs <;> simp_all
            rcases hMidAnc parSegs.length hPosLen (Nat.le_refl _) with ⟨dm, hD, hR, _, _⟩
            simp only [List.take_length] at hD
            exact ⟨dm, SameOutside_nodeAt_eq hSameAllP hNotPrefPar hParPosValid |>.trans hD, hR⟩)
        have hDirPosEq : (pos ++ parSegs.map (·.val)) ++ [leaf.val] = dirPos := by
          simp only [dirPos, dirSegs, List.map_append, List.map_singleton, List.append_assoc]
        rcases vfsTreeGet_dir_of_nodeAt hParNdP with ⟨chParP, hGetParP⟩
        by_cases hParNil : parSegs = []
        · subst hParNil
          rw [hWalkUnlink.1 rfl, vfsDirOps_unlinkAt_def, hLdP]
          dsimp only
          simp only [List.map_nil, List.append_nil, List.nil_append, List.map_singleton] at hParNdP hDirPosEq hGetParP hDirNdP
          rw [hParNdP]
          rw [← hDirPosEq] at hEmptyFalse
          simp only [hParWFP, Bool.false_eq_true, ↓reduceIte, hDirNdP, Bool.not_true, hEmptyFalse]
          let stFinal : VfsState :=
            { tree := vfsTreeSet stP.tree dirPos none, keys := stP.keys, cwd := stP.cwd,
              nonce := stP.nonce, locks := stP.locks, nextLockId := stP.nextLockId,
              openDirs := stP.openDirs, nextDirId := stP.nextDirId }
          have hGone : nodeAt stFinal.tree dirPos = none := by
            change nodeAt (vfsTreeSet stP.tree (pos ++ [leaf.val]) none) (pos ++ [leaf.val]) = none
            simpa [hDirPosEq] using nodeAt_vfsTreeSet_eq stP.tree pos leaf.val none ⟨pmP, chParP, hGetParP⟩
          have hShrunkU : TreeShrunk stFinal.tree stP.tree := by
            change TreeShrunk (vfsTreeSet stP.tree (pos ++ [leaf.val]) none) stP.tree
            simpa [hDirPosEq] using treeShrunk_set_none stP.tree pos leaf.val ⟨pmP, chParP, hGetParP⟩
          have hSameU : SameOutside dirPos stP stFinal := by
            intro p hNot
            change vfsTreeNodes (vfsTreeSet stP.tree (pos ++ [leaf.val]) none) p = vfsTreeNodes stP.tree p
            unfold vfsTreeNodes
            split
            · exact nodeAt_vfsTreeSet_outside stP.tree pos leaf.val none (vfsSplitSegs p) ⟨pmP, chParP, hGetParP⟩ (by simpa [hDirPosEq] using hNot)
            · rfl
          exact ⟨hGone, SameOutside_trans hSameAllP hSameU, treeShrunk_trans hShrunkU hShrunkAllP,
            hInvP, hOpenP, hKeysP.trans hKeysMid, hLocksP.trans hLocksMid,
            vfsKeysComplete_treeShrunk stP stFinal hKCP rfl hShrunkU⟩
        · rcases hWalkUnlink.2 hParNil with
            ⟨parDh, stMidU, hPosDhU, hLdMidU, hTreeMidU, hKeysMidU, _, _, hLocksMidU, hInvMidU, hLtMidU, hOpenMidU, hEqU⟩
          rw [hEqU, bracketCloseDirM_run, vfsDirOps_unlinkAt_def, hLdMidU]
          dsimp only
          rw [hTreeMidU, hParNdP]
          have hEmptyMidU : mDirHasLiveChild stMidU dirPos = false := by
            change mDirHasLiveChild stMidU dirPos = false
            have hSameMidU : stMidU.nodes = stP.nodes := nodes_eq_of_tree_eq stMidU stP hTreeMidU
            unfold mDirHasLiveChild at hEmptyFalse ⊢
            rw [hKeysMidU, hSameMidU]
            exact hEmptyFalse
          have hDirNdPP : nodeAt stP.tree ((pos ++ parSegs.map (·.val)) ++ [leaf.val]) = some (.dir cmP) := by
            rw [hDirPosEq]; exact hDirNdP
          rw [← hDirPosEq] at hEmptyMidU
          simp only [hParWFP, Bool.false_eq_true, ↓reduceIte, hDirNdPP, Bool.not_true, hEmptyMidU]
          have hCloseU := vfsDirOps_closeDir_fresh parDh
            { tree := vfsTreeSet stMidU.tree dirPos none, keys := stMidU.keys, cwd := stMidU.cwd,
              nonce := stMidU.nonce, locks := stMidU.locks, nextLockId := stMidU.nextLockId,
              openDirs := stMidU.openDirs, nextDirId := stMidU.nextDirId }
            (pos ++ parSegs.map (·.val)) hPosDhU stP.openDirs hOpenMidU hLtMidU
          rw [← hTreeMidU, hDirPosEq]
          rw [hCloseU]
          dsimp only
          let stFinal : VfsState :=
            { tree := vfsTreeSet stMidU.tree dirPos none, keys := stMidU.keys, cwd := stMidU.cwd,
              nonce := stMidU.nonce, locks := stMidU.locks, nextLockId := stMidU.nextLockId,
              openDirs := stP.openDirs, nextDirId := stMidU.nextDirId }
          have hGetParMidU : vfsTreeGet stMidU.tree (pos ++ parSegs.map (·.val)) = some (.dir pmP chParP) := by
            rw [hTreeMidU]; exact hGetParP
          have hGone : nodeAt stFinal.tree dirPos = none := by
            dsimp only [stFinal]
            rw [← hDirPosEq]
            exact nodeAt_vfsTreeSet_eq stMidU.tree (pos ++ parSegs.map (·.val)) leaf.val none ⟨pmP, chParP, hGetParMidU⟩
          have hShrunkU : TreeShrunk stFinal.tree stP.tree := by
            dsimp only [stFinal]
            rw [← hDirPosEq, ← hTreeMidU]
            exact treeShrunk_set_none stMidU.tree (pos ++ parSegs.map (·.val)) leaf.val ⟨pmP, chParP, hGetParMidU⟩
          have hSameU : SameOutside dirPos stP stFinal := by
            intro p hNot
            dsimp only [stFinal]
            rw [← hDirPosEq, ← nodes_eq_of_tree_eq stMidU stP hTreeMidU]
            change vfsTreeNodes (vfsTreeSet stMidU.tree ((pos ++ parSegs.map (·.val)) ++ [leaf.val]) none) p =
              vfsTreeNodes stMidU.tree p
            unfold vfsTreeNodes
            split
            · exact nodeAt_vfsTreeSet_outside stMidU.tree (pos ++ parSegs.map (·.val)) leaf.val none
                (vfsSplitSegs p) ⟨pmP, chParP, hGetParMidU⟩ (by simpa [hDirPosEq] using hNot)
            · rfl
          have hInvFinal : DirHandleInvariant stFinal :=
            dirHandleInvariant_of_subset hInvMidU (fun p hp => by
              change p ∈ stP.openDirs at hp
              rw [hOpenMidU]
              exact List.mem_cons_of_mem _ hp) rfl
          have hKCFinal : VfsKeysComplete stFinal := by
            apply vfsKeysComplete_treeShrunk stP stFinal hKCP hKeysMidU hShrunkU
          exact ⟨hGone, SameOutside_trans hSameAllP hSameU, treeShrunk_trans hShrunkU hShrunkAllP,
            hInvFinal, hOpenP, hKeysMidU.trans (hKeysP.trans hKeysMid),
            hLocksMidU.trans (hLocksP.trans hLocksMid), hKCFinal⟩
/-- `rmtreeDirAtM` deletes a valid `VfsTreeRemovable (fuel + 1)` directory while preserving `SameOutside`, `openDirs`, and `VfsKeysComplete`. -/
theorem rmtreeDirAtM_ok (rootDh : DirHandle) (pos : List String) :
    ∀ (fuel : Nat) (parSegs : List EntryName) (leaf : EntryName) (st : VfsState),
      VfsKeysComplete st →
      lookupDir st rootDh = some pos →
      DirHandleInvariant st →
      (∀ s ∈ pos, validSeg s = true) →
      (∃ pm₀, nodeAt st.tree pos = some (.dir pm₀) ∧
        (parSegs = [] → pm₀ / 128 % 2 = 1) ∧ pm₀ / 64 % 2 = 1) →
      (∀ k, 0 < k → k ≤ parSegs.length →
        ∃ dm, nodeAt st.tree (pos ++ (parSegs.take k).map (·.val)) = some (.dir dm) ∧
          dm / 256 % 2 = 1 ∧ dm / 128 % 2 = 1 ∧ dm / 64 % 2 = 1) →
      (∃ cm ch, vfsTreeGet st.tree (pos ++ (parSegs ++ [leaf]).map (·.val)) = some (.dir cm ch) ∧
        VfsTreeValidSegs (.dir cm ch) ∧ VfsTreeRemovable (fuel + 1) (.dir cm ch)) →
      match Internal.rmtreeDirAtM vfsDirOps rootDh parSegs leaf (fuel + 1) st with
      | (Except.error _, _) => False
      | (Except.ok (), st') =>
        nodeAt st'.tree (pos ++ (parSegs ++ [leaf]).map (·.val)) = none ∧
        SameOutside (pos ++ (parSegs ++ [leaf]).map (·.val)) st st' ∧
        TreeShrunk st'.tree st.tree ∧
        DirHandleInvariant st' ∧
        st'.openDirs = st.openDirs ∧
        st'.keys = st.keys ∧
        st'.locks = st.locks ∧
        VfsKeysComplete st' := by
  intro fuel
  induction fuel with
  | zero =>
    intro parSegs leaf st hKeys hLd hInv hPosValid hPosDir hMidAnc hDir
    exact rmtreeDirAtM_step rootDh pos 0 (fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ hRem0 => by
      rw [VfsTreeRemovable.eq_3] at hRem0
      exact False.elim hRem0) parSegs leaf st hKeys hLd hInv hPosValid hPosDir hMidAnc hDir
  | succ n ih =>
    intro parSegs leaf st hKeys hLd hInv hPosValid hPosDir hMidAnc hDir
    exact rmtreeDirAtM_step rootDh pos (n + 1)
      (fun parSegs' leaf' subDir stS cmS chS hKCS hLdS hInvS hPVS ⟨pm₀, hP0, hP0X⟩ hAncS hGetS hVSS hRemS =>
        ih (parSegs' ++ [leaf']) subDir stS hKCS hLdS hInvS hPVS
          ⟨pm₀, hP0, fun h => absurd h (by simp), hP0X⟩ hAncS ⟨cmS, chS, hGetS, hVSS, hRemS⟩)
      parSegs leaf st hKeys hLd hInv hPosValid hPosDir hMidAnc hDir

/-- `VfsTreeRemovable` is monotone in its recursion fuel bound. -/
theorem vfsTreeRemovable_mono : ∀ (fuel fuel' : Nat) (t : VfsTree),
    fuel ≤ fuel' → VfsTreeRemovable fuel t → VfsTreeRemovable fuel' t := by
  intro fuel
  induction fuel with
  | zero =>
    intro fuel' t _ hR
    cases t with
    | file d m => rw [VfsTreeRemovable.eq_1]; trivial
    | symlink tgt m => rw [VfsTreeRemovable.eq_2]; trivial
    | dir m ch => rw [VfsTreeRemovable.eq_3] at hR; exact False.elim hR
  | succ f ih =>
    intro fuel' t hLe hR
    cases fuel' with
    | zero => omega
    | succ f' =>
      cases t with
      | file d m => rw [VfsTreeRemovable.eq_1]; trivial
      | symlink tgt m => rw [VfsTreeRemovable.eq_2]; trivial
      | dir m ch =>
        rw [VfsTreeRemovable.eq_4] at hR ⊢
        exact ⟨hR.1, hR.2.1, hR.2.2.1, fun nm sub hs => ih f' sub (Nat.le_of_succ_le_succ hLe) (hR.2.2.2 nm sub hs)⟩

/-- `mkdir` creates a child visible in `listDir .root`, and `rmtree` removes a bounded subtree so `lstat` returns `.notFound`. -/
theorem spec_mkdirVisibleAndRmtreeNotFound : SpecMkdirVisibleAndRmtreeNotFound Internal.subtreeOpsM := by
  constructor
  · intro st dh pos child hLd hInv hPosValid hLen hPar hNone sub
    rcases hPar with ⟨pm, hParNd, hParR, hParW, hParX⟩
    dsimp only [sub, StateT.run, Internal.subtreeOpsM]
    rw [show Internal.splitLastAux [child] [] = some ([], child) from subtreeSplitLastAux_append_singleton [] child]
    dsimp only
    simp only [Bool.false_eq_true, ↓reduceIte, Bind.bind, Pure.pure]
    change match (do
        let __do_lift ← vfsDirOps.createDirAt dh child
        match __do_lift with
        | Except.ok () => pure (Except.ok ())
        | Except.error e => pure (Except.error e)) st with
      | (mRes, st₁) =>
        mRes = Except.ok () ∧
          ∃ names, (Internal.walkDescendM vfsDirOps dh []
            (fun dirDh =>
              StateT.bind (vfsDirOps.readDirAt dirDh) fun __do_lift =>
                match __do_lift with
                | Except.error e => pure (Except.error e)
                | Except.ok names => pure (Except.ok (Internal.sortEntryNames names).toArray))
            st₁).1 = Except.ok names ∧ child ∈ names.toList
    simp only [Bind.bind, StateT.bind, Pure.pure]
    rw [vfsDirOps_createDirAt_def, hLd]
    dsimp only
    rw [hParNd]
    have hWF : (pm / 128 % 2 == 0 || pm / 64 % 2 == 0) = false := by simp [hParW, hParX]
    simp only [hWF, Bool.false_eq_true, ↓reduceIte, hNone]
    let st₁ : VfsState :=
      { tree := vfsTreeSet st.tree (pos ++ [child.val]) (some (vfsEmptyDir 493)),
        keys := pathOfSegs (pos ++ [child.val]) :: st.keys, cwd := st.cwd, nonce := st.nonce,
        locks := st.locks, nextLockId := st.nextLockId, openDirs := st.openDirs,
        nextDirId := st.nextDirId }
    have hLd₁ : lookupDir st₁ dh = some pos := hLd
    rcases vfsTreeGet_dir_of_nodeAt hParNd with ⟨chPar, hGetPar⟩
    have hNotSelfPre : ¬ (pos ++ [child.val] <+: pos) := by
      intro hP
      have hL := List.IsPrefix.length_le hP
      simp at hL
      omega
    have hParNd₁ : nodeAt st₁.tree pos = some (.dir pm) := by
      change nodeAt (vfsTreeSet st.tree (pos ++ [child.val]) (some (vfsEmptyDir 493))) pos = some (.dir pm)
      rw [nodeAt_vfsTreeSet_outside st.tree pos child.val (some (vfsEmptyDir 493)) pos ⟨pm, chPar, hGetPar⟩ hNotSelfPre]
      exact hParNd
    have hChildNd₁ : nodeAt st₁.tree (pos ++ [child.val]) = some (.dir 493) := by
      change nodeAt (vfsTreeSet st.tree (pos ++ [child.val]) (some (vfsEmptyDir 493))) (pos ++ [child.val]) = some (.dir 493)
      rw [nodeAt_vfsTreeSet_eq st.tree pos child.val (some (vfsEmptyDir 493)) ⟨pm, chPar, hGetPar⟩]
      rfl
    have hParRF : (pm / 256 % 2 == 0) = false := by rw [hParR]; decide
    refine ⟨rfl, (Internal.sortEntryNames (mVfsReadDirAtEntries st₁ pos)).toArray, ?_, ?_⟩
    · change ((StateT.bind (vfsDirOps.readDirAt dh) fun __do_lift =>
          match __do_lift with
          | Except.error e => pure (Except.error e)
          | Except.ok names => pure (Except.ok (Internal.sortEntryNames names).toArray)) st₁).1 = _
      simp only [StateT.bind, Pure.pure]
      rw [vfsDirOps_readDirAt_def, hLd₁]
      dsimp only
      rw [hParNd₁]
      simp only [hParRF, Bool.false_eq_true, ↓reduceIte]
      rfl
    · rw [List.toList_toArray, (List.mergeSort_perm _ _).mem_iff]
      exact mVfsReadDirAtEntries_mem_of_key st₁ pos child hPosValid List.mem_cons_self
        (by rw [hChildNd₁]; simp)
  · intro st dh pos child hKeys hLd hInv hPosValid hLen hPar hChild hTsub sub
    rcases hPar with ⟨pm, hParNd, hParW, hParX⟩
    rcases hChild with ⟨cm, hChildNd, hCmR, hCmW, hCmX⟩
    dsimp only [sub, StateT.run, Internal.subtreeOpsM]
    rw [show Internal.splitLastAux [child] [] = some ([], child) from subtreeSplitLastAux_append_singleton [] child]
    dsimp only
    simp only [Bind.bind, StateT.bind, Pure.pure]
    rw [show Internal.walkDescendM vfsDirOps dh [] (fun parDh => vfsDirOps.lstatAt parDh child) st =
        vfsDirOps.lstatAt dh child st from rfl,
      vfsDirOps_lstatAt_def, hLd]
    dsimp only
    rw [hParNd]
    have hParXF : (pm / 64 % 2 == 0) = false := by rw [hParX]; decide
    simp only [hParXF, Bool.false_eq_true, ↓reduceIte, hChildNd]
    simp only [vfsToStat, show (EntryKind.dir != EntryKind.dir) = false from rfl, Bool.false_eq_true, ↓reduceIte]
    rcases vfsTreeGet_dir_of_nodeAt hChildNd with ⟨chChild, hGetChild⟩
    have hTsubProps := hTsub (.dir cm chChild) hGetChild
    have hRm := rmtreeDirAtM_ok dh pos 4095 [] child st hKeys hLd hInv hPosValid
      ⟨pm, hParNd, fun _ => hParW, hParX⟩ (fun _ _ hkLen => by simp at hkLen; omega)
      ⟨cm, chChild, hGetChild, hTsubProps.1, vfsTreeRemovable_mono 4095 4096 _ (by omega) hTsubProps.2⟩
    cases hRmRun : Internal.rmtreeDirAtM vfsDirOps dh [] child 4096 st with
    | mk rRes st₁ =>
      rw [hRmRun] at hRm
      cases rRes with
      | error e => exact False.elim hRm
      | ok u =>
        cases u
        rcases hRm with ⟨hGone, hSame, _, _, hOpen, _, _, _⟩
        simp only [List.map_nil, List.nil_append, List.map_cons, List.nil_append] at hGone hSame
        have hLd₁ : lookupDir st₁ dh = some pos := by
          unfold lookupDir at hLd ⊢
          rw [hOpen]
          exact hLd
        have hNotPrefPos : ¬ (pos ++ [child.val] <+: pos) := by
          intro hP
          have hL := List.IsPrefix.length_le hP
          simp at hL
          omega
        have hParNd₁ : nodeAt st₁.tree pos = some (.dir pm) :=
          SameOutside_nodeAt_eq hSame hNotPrefPos hPosValid |>.trans hParNd
        refine ⟨rfl, ?_⟩
        rw [show Internal.walkDescendM vfsDirOps dh [] (fun parDh => vfsDirOps.lstatAt parDh child) st₁ =
            vfsDirOps.lstatAt dh child st₁ from rfl,
          vfsDirOps_lstatAt_def, hLd₁]
        dsimp only
        rw [hParNd₁]
        simp only [hParXF, Bool.false_eq_true, ↓reduceIte, hGone]
        exact ⟨_, rfl, rfl⟩

end LeanSwe.Fs.Proofs
