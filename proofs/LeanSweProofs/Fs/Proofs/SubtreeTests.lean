import LeanSweProofs.Fs.Proofs.SubtreeTestHelpers

namespace LeanSwe.Fs.Proofs

open Core Core.NondetTest LeanSwe.Fs LeanSwe.Fs.Model

private theorem entryName_ext {a b : EntryName} (h : a.val = b.val) : a = b := by
  cases a; cases b; cases h; rfl

private theorem stateM_bind_step {α β : Type} {m : StateM VfsState α} {k : α → StateM VfsState β}
    {s : VfsState} {a : α} {s' : VfsState} (hm : m s = (a, s')) :
    (m >>= k) s = k a s' := by
  simp only [Bind.bind, StateT.bind, hm]

private theorem walkDescendM_nil_eq {α : Type}
    (ops : RawDirOpsM (StateM VfsState)) (dh : DirHandle)
    (act : DirHandle → StateM VfsState (Except FsError α)) :
    Internal.walkDescendM ops dh [] act = act dh :=
  rfl

private theorem vfsTreeGet_append_none : ∀ (t : VfsTree) (p q : List String),
    vfsTreeGet t p = none → vfsTreeGet t (p ++ q) = none := by
  intro t p q hNone
  induction p generalizing t with
  | nil => simp [vfsTreeGet] at hNone
  | cons a rest ih =>
    cases t with
    | file _ _ | symlink _ _ => simp [List.cons_append, vfsTreeGet]
    | dir _ ch =>
      simp only [List.cons_append, vfsTreeGet] at hNone ⊢
      cases hc : ch a with
      | none => rfl
      | some sub => simp only [hc] at hNone; exact ih sub hNone

private theorem nodeAt_canon_of_nodes_some (st : VfsState) (canon : String) (nd : VfsNode)
    (h : st.nodes canon = some nd) :
    isCanonPath canon = true ∧ nodeAt st.tree (vfsSplitSegs canon) = some nd := by
  change vfsTreeNodes st.tree canon = some nd at h
  cases hc : isCanonPath canon with
  | false => simp [vfsTreeNodes, hc] at h
  | true =>
    simp only [vfsTreeNodes, hc, ↓reduceIte] at h
    exact ⟨rfl, h⟩

private noncomputable def openDirAtTpl' (st : VfsState) (dh : DirHandle) (name : EntryName)
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

private theorem closedHandle_walkDescendM_err {α : Type} (dh : DirHandle) (segs : List EntryName)
    (act : DirHandle → StateM VfsState (Except FsError α)) (st : VfsState)
    (hClosed : lookupDir st dh = none)
    (hAct : act dh st = (.error (mInvalidDirHandleErr dh), st)) :
    Internal.walkDescendM vfsDirOps dh segs act st = (.error (mInvalidDirHandleErr dh), st) := by
  cases segs with
  | nil => exact hAct
  | cons a rest =>
    rw [Internal.walkDescendM, walkDescendAuxM_cons]
    simp only [↓reduceIte, Bind.bind, StateT.bind]
    have hOp : vfsDirOps.openDirAt dh a st = (.error (mInvalidDirHandleErr dh), st) := by
      rcases (⟨_, rfl⟩ : ∃ d : Nat, vfsDirOps.openDirAt dh a st = openDirAtTpl' st dh a d) with ⟨d, hEq⟩
      rw [hEq]; unfold openDirAtTpl'; rw [hClosed]
    rw [hOp]
    rfl

private theorem closedHandle_mkdirWalkM_err (dh : DirHandle) (segs : List EntryName)
    (act : DirHandle → StateM VfsState (Except FsError Unit)) (st : VfsState)
    (hClosed : lookupDir st dh = none)
    (hAct : act dh st = (.error (mInvalidDirHandleErr dh), st)) :
    Internal.mkdirWalkM vfsDirOps true dh segs act st = (.error (mInvalidDirHandleErr dh), st) := by
  cases segs with
  | nil => exact hAct
  | cons a rest =>
    rw [mkdirWalkM_cons]
    simp only [↓reduceIte, Bind.bind, StateT.bind]
    have hOp : vfsDirOps.openDirAt dh a st = (.error (mInvalidDirHandleErr dh), st) := by
      rcases (⟨_, rfl⟩ : ∃ d : Nat, vfsDirOps.openDirAt dh a st = openDirAtTpl' st dh a d) with ⟨d, hEq⟩
      rw [hEq]; unfold openDirAtTpl'; rw [hClosed]
    rw [hOp]
    dsimp only
    simp only [show (FsErrorKind.invalidInput == FsErrorKind.notFound) = false from rfl,
      Bool.false_eq_true, ↓reduceIte]
    rfl

private theorem atomicWrite_collision_step (ops : RawDirOpsM (StateM VfsState))
    (hFresh : ops.freshTempName = vfsDirOps.freshTempName)
    (hCreate : ops.createFileAt = vfsDirOps.createFileAt)
    (dh : DirHandle) (pos : List String) (leaf : EntryName) (bytes : ByteArray)
    (st : VfsState) (pm : Nat) (nd : VfsNode)
    (hLd : lookupDir st dh = some pos)
    (hPar : nodeAt st.tree pos = some (.dir pm))
    (hW : pm / 128 % 2 = 1) (hX : pm / 64 % 2 = 1)
    (hTmp : nodeAt st.tree (pos ++ [".t." ++ toString st.nonce]) = some nd) :
    Internal.atomicWriteAtAuxM ops dh leaf bytes 16 st =
      Internal.atomicWriteAtAuxM ops dh leaf bytes 15 { st with nonce := st.nonce + 1 } := by
  rw [atomicWriteAtAuxM_succ]
  simp only [Bind.bind, StateT.bind, hFresh, hCreate]
  have hFrDef := vfsDirOps_freshTempName_def st
  cases hFr : vfsDirOps.freshTempName st with
  | mk tmp st1 =>
    dsimp only
    rw [hFr] at hFrDef
    dsimp only at hFrDef
    rcases hFrDef with ⟨hTmpVal, hSt1⟩
    have hTmp1 : nodeAt st1.tree (pos ++ [tmp.val]) = some nd := by
      rw [hSt1, hTmpVal]; exact hTmp
    have hWXF : (pm / 128 % 2 == 0 || pm / 64 % 2 == 0) = false := by rw [hW, hX]; decide
    have hCf : vfsDirOps.createFileAt dh tmp bytes st1 =
        (.error { kind := .alreadyExists, path := some tmp.val, message := s!"already exists: {tmp.val}" }, st1) := by
      rw [vfsDirOps_createFileAt_def, show lookupDir st1 dh = some pos from by rw [hSt1]; exact hLd]
      dsimp only
      rw [show nodeAt st1.tree pos = some (.dir pm) from by rw [hSt1]; exact hPar]
      simp only [hWXF, Bool.false_eq_true, ↓reduceIte, hTmp1]
    rw [hCf]
    dsimp only
    simp only [show (FsErrorKind.alreadyExists == FsErrorKind.alreadyExists) = true from rfl,
      show decide (15 > 0) = true from rfl, Bool.and_true, ↓reduceIte, hSt1]

private def deepSubdirTree (perm : Nat) : Nat → VfsTree
  | 0 => vfsEmptyDir perm
  | n + 1 => .dir perm (fun s => if s == "d" then some (deepSubdirTree perm n) else none)

private def deepKeysList : Nat → List String → List String
  | 0, pfx => [pathOfSegs pfx]
  | k + 1, pfx => pathOfSegs pfx :: deepKeysList k (pfx ++ ["d"])

private theorem mem_deepKeysList : ∀ (k : Nat) (pfx segs : List String),
    segs.length ≤ k → (∀ s ∈ segs, s = "d") → pathOfSegs (pfx ++ segs) ∈ deepKeysList k pfx := by
  intro k pfx segs
  induction segs generalizing k pfx with
  | nil =>
    intro _ _
    cases k with
    | zero => simp [deepKeysList]
    | succ k' => simp [deepKeysList]
  | cons s rest ih =>
    intro hLen hAll
    cases k with
    | zero => simp at hLen
    | succ k' =>
      rcases hAll s List.mem_cons_self with rfl
      rw [deepKeysList, List.mem_cons]
      right
      simpa [List.append_assoc] using ih k' (pfx ++ ["d"]) (by simp at hLen; omega)
        (fun x hx => hAll x (List.mem_cons_of_mem _ hx))

private theorem nodeAt_deepSubdirTree_props : ∀ (perm n : Nat) (segs : List String),
    nodeAt (deepSubdirTree perm n) segs ≠ none → segs.length ≤ n ∧ ∀ s ∈ segs, s = "d" := by
  intro perm n
  induction n with
  | zero =>
    intro segs hNe
    cases segs with
    | nil => exact ⟨Nat.le_refl _, fun _ h => nomatch h⟩
    | cons s rest =>
      exfalso; apply hNe
      cases rest <;> simp [deepSubdirTree, vfsEmptyDir, nodeAt, vfsTreeGet]
  | succ n' ih =>
    intro segs hNe
    cases segs with
    | nil => exact ⟨Nat.zero_le _, fun _ h => nomatch h⟩
    | cons s rest =>
      by_cases hs : s = "d"
      · subst hs
        have hSub : nodeAt (deepSubdirTree perm n') rest ≠ none := by
          intro h0; apply hNe
          simpa [deepSubdirTree, nodeAt, vfsTreeGet] using h0
        rcases ih rest hSub with ⟨hL, hA⟩
        exact ⟨Nat.succ_le_succ hL, fun x hx => by
          rcases List.mem_cons.mp hx with rfl | hr
          · rfl
          · exact hA x hr⟩
      · exfalso; apply hNe
        simp [deepSubdirTree, nodeAt, vfsTreeGet, hs]

private theorem deepSubdirTree_validSegs (perm n : Nat) : VfsTreeValidSegs (deepSubdirTree perm n) := by
  intro segs hNe s hs
  rcases nodeAt_deepSubdirTree_props perm n segs hNe with ⟨_, hAll⟩
  rw [hAll s hs]
  decide

private theorem deepSubdirTree_permWalkable : ∀ (n : Nat), vfsTreePermWalkable' (deepSubdirTree 0o555 n) := by
  intro n
  induction n with
  | zero =>
    intro segs m hm
    cases segs with
    | nil =>
      simp only [deepSubdirTree, vfsEmptyDir, nodeAt, vfsTreeGet, vfsTreeTopNode, Option.map_some,
        Option.some.injEq, VfsNode.dir.injEq] at hm
      subst hm
      exact ⟨by decide, by decide⟩
    | cons _ _ => simp [deepSubdirTree, vfsEmptyDir, nodeAt, vfsTreeGet] at hm
  | succ n' ih =>
    intro segs m hm
    cases segs with
    | nil =>
      simp only [deepSubdirTree, nodeAt, vfsTreeGet, vfsTreeTopNode, Option.map_some,
        Option.some.injEq, VfsNode.dir.injEq] at hm
      subst hm
      exact ⟨by decide, by decide⟩
    | cons s rest =>
      by_cases hs : s = "d"
      · subst hs
        apply ih rest m
        simpa [deepSubdirTree, nodeAt, vfsTreeGet] using hm
      · simp [deepSubdirTree, nodeAt, vfsTreeGet, hs] at hm

private theorem deepSubdirTree_permRemovable : ∀ (n : Nat), vfsTreePermRemovable' (deepSubdirTree 0o700 n) := by
  intro n
  induction n with
  | zero =>
    intro segs m hm
    cases segs with
    | nil =>
      simp only [deepSubdirTree, vfsEmptyDir, nodeAt, vfsTreeGet, vfsTreeTopNode, Option.map_some,
        Option.some.injEq, VfsNode.dir.injEq] at hm
      subst hm
      exact ⟨by decide, by decide, by decide⟩
    | cons _ _ => simp [deepSubdirTree, vfsEmptyDir, nodeAt, vfsTreeGet] at hm
  | succ n' ih =>
    intro segs m hm
    cases segs with
    | nil =>
      simp only [deepSubdirTree, nodeAt, vfsTreeGet, vfsTreeTopNode, Option.map_some,
        Option.some.injEq, VfsNode.dir.injEq] at hm
      subst hm
      exact ⟨by decide, by decide, by decide⟩
    | cons s rest =>
      by_cases hs : s = "d"
      · subst hs
        apply ih rest m
        simpa [deepSubdirTree, nodeAt, vfsTreeGet] using hm
      · simp [deepSubdirTree, nodeAt, vfsTreeGet, hs] at hm

private theorem deepSubdirTree_not_walkable : ∀ (k n : Nat), k ≤ n → ¬ VfsTreeWalkable k (deepSubdirTree 0o555 n) := by
  intro k
  induction k with
  | zero =>
    intro n _
    cases n with
    | zero => rw [deepSubdirTree, vfsEmptyDir, VfsTreeWalkable.eq_3]; exact False.elim
    | succ _ => rw [deepSubdirTree, VfsTreeWalkable.eq_3]; exact False.elim
  | succ k' ih =>
    intro n hk
    cases n with
    | zero => omega
    | succ n' =>
      rw [deepSubdirTree, VfsTreeWalkable.eq_4]
      intro ⟨_, _, hCh⟩
      exact ih n' (by omega) (hCh "d" (deepSubdirTree 0o555 n') (by simp))

private theorem deepSubdirTree_not_removable : ∀ (k n : Nat), k ≤ n → ¬ VfsTreeRemovable k (deepSubdirTree 0o700 n) := by
  intro k
  induction k with
  | zero =>
    intro n _
    cases n with
    | zero => rw [deepSubdirTree, vfsEmptyDir, VfsTreeRemovable.eq_3]; exact False.elim
    | succ _ => rw [deepSubdirTree, VfsTreeRemovable.eq_3]; exact False.elim
  | succ k' ih =>
    intro n hk
    cases n with
    | zero => omega
    | succ n' =>
      rw [deepSubdirTree, VfsTreeRemovable.eq_4]
      intro ⟨_, _, _, hCh⟩
      exact ih n' (by omega) (hCh "d" (deepSubdirTree 0o700 n') (by simp))

@[irreducible] private def deepSubdirState (perm n : Nat) : VfsState :=
  stateWithRootHandle (fun s => if s == "d" then some (deepSubdirTree perm n) else none)
    ("/" :: deepKeysList n ["d"])

private theorem deepSubdirState_openDirs (perm n : Nat) :
    (deepSubdirState perm n).openDirs = [(1, [])] := by
  unfold deepSubdirState stateWithRootHandle; rfl

private theorem deepSubdirState_tree (perm n : Nat) :
    (deepSubdirState perm n).tree = .dir 0o755 (fun s => if s == "d" then some (deepSubdirTree perm n) else none) := by
  unfold deepSubdirState stateWithRootHandle; rfl

private theorem deepSubdirState_nextDirId (perm n : Nat) :
    (deepSubdirState perm n).nextDirId = 2 := by
  unfold deepSubdirState stateWithRootHandle; rfl

private theorem deepSubdirState_lookup (perm n : Nat) :
    lookupDir (deepSubdirState perm n) rootHandle = some [] := by
  unfold deepSubdirState stateWithRootHandle rootHandle lookupDir; rfl

private theorem deepSubdirState_rootNode (perm n : Nat) :
    nodeAt (deepSubdirState perm n).tree [] = some (.dir 0o755) := by
  rw [deepSubdirState_tree]; rfl

private theorem deepSubdirState_childDir (perm n : Nat) :
    nodeAt (deepSubdirState perm n).tree ([] ++ [(EntryName.lit "d").val]) = some (.dir perm) := by
  rw [deepSubdirState_tree]
  cases n <;> simp [EntryName.lit, deepSubdirTree, vfsEmptyDir, nodeAt, vfsTreeGet, vfsTreeTopNode]

private theorem deepSubdirKeys_complete (perm n : Nat) :
    VfsKeysComplete (deepSubdirState perm n) := by
  unfold deepSubdirState
  intro segs hNe
  cases segs with
  | nil => simp [stateWithRootHandle, pathOfSegs]
  | cons a rest =>
    by_cases ha : a = "d"
    · subst ha
      have hSub : nodeAt (deepSubdirTree perm n) rest ≠ none := by
        intro h0; apply hNe
        simpa [stateWithRootHandle, nodeAt, vfsTreeGet] using h0
      rcases nodeAt_deepSubdirTree_props perm n rest hSub with ⟨hL, hA⟩
      exact List.mem_cons_of_mem _ (by simpa [stateWithRootHandle, pathOfSegs] using mem_deepKeysList n ["d"] rest hL hA)
    · exfalso; apply hNe
      simp [stateWithRootHandle, nodeAt, vfsTreeGet, ha]

/-- `Internal.subtreeOpsM` satisfies `test_fs_subtree_sameOutside_confinesAllOps`. -/
theorem proof_fs_subtree_sameOutside_confinesAllOps :
    Core.AllPass (test_fs_subtree_sameOutside_confinesAllOps Internal.subtreeOpsM) :=
  ⟨spec_subtreeSameOutside, trivial⟩

/-- Witness check for `test_fs_subtree_sameOutside_confinesAllOps`. -/
theorem reach_fs_subtree_sameOutside_confinesAllOps :
    Core.CanReach (test_fs_subtree_sameOutside_confinesAllOps Internal.subtreeOpsM) :=
  ⟨spec_subtreeSameOutside, trivial⟩

/-- `Internal.subtreeOpsM` satisfies `test_fs_subtree_noSymlinkFollowAncestors_refusesAllOps`. -/
theorem proof_fs_subtree_noSymlinkFollowAncestors_refusesAllOps :
    Core.AllPass (test_fs_subtree_noSymlinkFollowAncestors_refusesAllOps Internal.subtreeOpsM) :=
  ⟨spec_noSymlinkFollowAncestors, trivial⟩

/-- Witness check for `test_fs_subtree_noSymlinkFollowAncestors_refusesAllOps`. -/
theorem reach_fs_subtree_noSymlinkFollowAncestors_refusesAllOps :
    Core.CanReach (test_fs_subtree_noSymlinkFollowAncestors_refusesAllOps Internal.subtreeOpsM) :=
  ⟨spec_noSymlinkFollowAncestors, trivial⟩

/-- `Internal.mkSubtreeOpenerM` satisfies `test_fs_subtree_programSameOutsideInterleaved_confinesPrograms`. -/
theorem proof_fs_subtree_programSameOutsideInterleaved_confinesPrograms :
    Core.AllPass (test_fs_subtree_programSameOutsideInterleaved_confinesPrograms Internal.mkSubtreeOpenerM) :=
  ⟨spec_subtreeProgramSameOutsideInterleaved, trivial⟩

/-- Witness check for `test_fs_subtree_programSameOutsideInterleaved_confinesPrograms`. -/
theorem reach_fs_subtree_programSameOutsideInterleaved_confinesPrograms :
    Core.CanReach (test_fs_subtree_programSameOutsideInterleaved_confinesPrograms Internal.mkSubtreeOpenerM) :=
  ⟨spec_subtreeProgramSameOutsideInterleaved, trivial⟩

/-- `Internal.mkSubtreeOpenerM` and `Internal.subtreeOpsM` satisfy `test_fs_subtree_descriptorConservation_preservesOpenDirs`. -/
theorem proof_fs_subtree_descriptorConservation_preservesOpenDirs :
    Core.AllPass (test_fs_subtree_descriptorConservation_preservesOpenDirs Internal.mkSubtreeOpenerM Internal.subtreeOpsM) :=
  ⟨spec_descriptorConservation, trivial⟩

/-- Witness check for `test_fs_subtree_descriptorConservation_preservesOpenDirs`. -/
theorem reach_fs_subtree_descriptorConservation_preservesOpenDirs :
    Core.CanReach (test_fs_subtree_descriptorConservation_preservesOpenDirs Internal.mkSubtreeOpenerM Internal.subtreeOpsM) :=
  ⟨spec_descriptorConservation, trivial⟩

/-- `Internal.subtreeOpsM` satisfies `test_fs_subtree_atomicWriteReadRegularRoundTrip_exactBytesAndMode`. -/
theorem proof_fs_subtree_atomicWriteReadRegularRoundTrip_exactBytesAndMode :
    Core.AllPass (test_fs_subtree_atomicWriteReadRegularRoundTrip_exactBytesAndMode Internal.subtreeOpsM) :=
  ⟨spec_atomicWriteReadRegularRoundTrip, trivial⟩

/-- Witness check for `test_fs_subtree_atomicWriteReadRegularRoundTrip_exactBytesAndMode`. -/
theorem reach_fs_subtree_atomicWriteReadRegularRoundTrip_exactBytesAndMode :
    Core.CanReach (test_fs_subtree_atomicWriteReadRegularRoundTrip_exactBytesAndMode Internal.subtreeOpsM) :=
  ⟨spec_atomicWriteReadRegularRoundTrip, trivial⟩

/-- `Internal.subtreeOpsM` satisfies `test_fs_subtree_mkdirVisibleAndRmtreeNotFound_holds`. -/
theorem proof_fs_subtree_mkdirVisibleAndRmtreeNotFound_holds :
    Core.AllPass (test_fs_subtree_mkdirVisibleAndRmtreeNotFound_holds Internal.subtreeOpsM) :=
  ⟨spec_mkdirVisibleAndRmtreeNotFound, trivial⟩

/-- Witness check for `test_fs_subtree_mkdirVisibleAndRmtreeNotFound_holds`. -/
theorem reach_fs_subtree_mkdirVisibleAndRmtreeNotFound_holds :
    Core.CanReach (test_fs_subtree_mkdirVisibleAndRmtreeNotFound_holds Internal.subtreeOpsM) :=
  ⟨spec_mkdirVisibleAndRmtreeNotFound, trivial⟩

/-- `Internal.subtreeOpsM` satisfies `test_fs_subtree_agreesWithAmbientOnSymlinkFree_matchesFsApi`. -/
theorem proof_fs_subtree_agreesWithAmbientOnSymlinkFree_matchesFsApi :
    Core.AllPass (test_fs_subtree_agreesWithAmbientOnSymlinkFree_matchesFsApi Internal.subtreeOpsM) :=
  ⟨spec_subtreeAgreesWithAmbientOnSymlinkFree, trivial⟩

/-- Witness check for `test_fs_subtree_agreesWithAmbientOnSymlinkFree_matchesFsApi`. -/
theorem reach_fs_subtree_agreesWithAmbientOnSymlinkFree_matchesFsApi :
    Core.CanReach (test_fs_subtree_agreesWithAmbientOnSymlinkFree_matchesFsApi Internal.subtreeOpsM) :=
  ⟨spec_subtreeAgreesWithAmbientOnSymlinkFree, trivial⟩

/-- `Internal.mkSubtreeOpenerM` satisfies `test_fs_withSubtree_validatesRootAndAlwaysClosesHandle`. -/
theorem proof_fs_withSubtree_validatesRootAndAlwaysClosesHandle :
    Core.AllPass (test_fs_withSubtree_validatesRootAndAlwaysClosesHandle Internal.mkSubtreeOpenerM) := by
  intro st₀ root bodyRes hInv
  dsimp only [Internal.mkSubtreeOpenerM, Internal.withSubtreeM, StateT.run, Bind.bind, StateT.bind]
  rcases vfsDirOps_openDir_tpl st₀ root with ⟨d, hOp⟩
  by_cases hVal : Model.isValidRawPath root
  · have hValF : (!Model.isValidRawPath root) = false := by simp [hVal]
    simp only [hValF, Bool.false_eq_true, ↓reduceIte]
    cases hRes : vfsResolveSegs st₀.nodes "/" (vfsSplitSegs (vfsAbsNorm st₀.cwd root)) true 1024 with
    | error expectedErr =>
      have hOpenErr : vfsDirOps.openDir root st₀ = (.error expectedErr, st₀) := by
        rw [hOp]; unfold openDirTpl
        simp only [hValF, Bool.false_eq_true, ↓reduceIte, hRes]
      rw [hOpenErr]
      dsimp only
      exact ⟨⟨⟨expectedErr, rfl, rfl⟩, rfl, rfl⟩, trivial⟩
    | ok pair =>
      rcases pair with ⟨canon, nd⟩
      cases nd with
      | file bs fm =>
        have hOpenErr : vfsDirOps.openDir root st₀ = (.error { kind := .notADirectory, path := some root, message := s!"not a directory: {root}" }, st₀) := by
          rw [hOp]; unfold openDirTpl
          simp only [hValF, Bool.false_eq_true, ↓reduceIte, hRes]
        rw [hOpenErr]
        dsimp only
        exact ⟨⟨⟨_, rfl, rfl⟩, rfl, rfl⟩, trivial⟩
      | symlink t lm =>
        have hOpenErr : vfsDirOps.openDir root st₀ = (.error { kind := .notADirectory, path := some root, message := s!"not a directory: {root}" }, st₀) := by
          rw [hOp]; unfold openDirTpl
          simp only [hValF, Bool.false_eq_true, ↓reduceIte, hRes]
        rw [hOpenErr]
        dsimp only
        exact ⟨⟨⟨_, rfl, rfl⟩, rfl, rfl⟩, trivial⟩
      | dir m =>
        dsimp only
        have hNodeCanon : st₀.nodes canon = some (.dir m) :=
          subtreeVfsResolveSegs_ok_node st₀.nodes 1024 "/" (vfsSplitSegs (vfsAbsNorm st₀.cwd root)) true canon (.dir m) hRes
        rcases nodeAt_canon_of_nodes_some st₀ canon (.dir m) hNodeCanon with ⟨_, hNodeAt⟩
        by_cases hRead0 : (m / 256) % 2 == 0
        · have hOpenErr : vfsDirOps.openDir root st₀ = (.error { kind := .permissionDenied, path := some root, message := s!"permission denied: {root}" }, st₀) := by
            rw [hOp]; unfold openDirTpl
            simp only [hValF, Bool.false_eq_true, ↓reduceIte, hRes, hRead0, ↓reduceIte]
          have hReadNe : ((m / 256) % 2 == 1 && (m / 64) % 2 == 1) = false := by
            have h0 : (m / 256) % 2 = 0 := beq_iff_eq.mp hRead0
            simp [h0]
          rw [hOpenErr, hReadNe]
          dsimp only
          exact ⟨⟨⟨_, rfl, rfl⟩, rfl, rfl⟩, trivial⟩
        · have hRead1 : (m / 256) % 2 = 1 := by
            have hNe : (m / 256) % 2 ≠ 0 := fun h => hRead0 (beq_iff_eq.mpr h)
            omega
          have hRead0F : ((m / 256) % 2 == 0) = false := by rw [hRead1]; decide
          let id := max d st₀.nextDirId + 1
          let dh : DirHandle := { handleId := id, rootPath := root }
          let stMid : VfsState := { st₀ with openDirs := (id, vfsSplitSegs canon) :: st₀.openDirs, nextDirId := id + 1 }
          have hOpenOk : vfsDirOps.openDir root st₀ = (.ok dh, stMid) := by
            rw [hOp]; unfold openDirTpl
            simp only [hValF, Bool.false_eq_true, ↓reduceIte, hRes, hRead0F, Bool.false_eq_true, ↓reduceIte]
            rfl
          have hPosDh : 0 < dh.handleId := by dsimp [dh, id]; omega
          have hLt : ∀ p ∈ st₀.openDirs, p.1 < dh.handleId := fun p hp =>
            Nat.lt_of_lt_of_le (hInv p.1 p.2 hp).2 (by dsimp [dh, id]; omega)
          have hLdMid : lookupDir stMid dh = some (vfsSplitSegs canon) :=
            lookupDir_cons_self st₀ id (vfsSplitSegs canon) root (by dsimp [id]; omega)
          have hFstatMid : vfsDirOps.fstatDir dh stMid = (.ok (vfsToStat (.dir m)), stMid) := by
            rw [vfsDirOps_fstatDir_def, hLdMid]
            dsimp only [stMid]
            rw [hNodeAt]
          have hClMid : vfsDirOps.closeDir dh stMid = (.ok (), { stMid with openDirs := st₀.openDirs }) :=
            vfsDirOps_closeDir_fresh dh stMid (vfsSplitSegs canon) hPosDh st₀.openDirs rfl hLt
          by_cases hExec0 : (m / 64) % 2 == 0
          · have hExecNe : ((m / 256) % 2 == 1 && (m / 64) % 2 == 1) = false := by
              have h0 : (m / 64) % 2 = 0 := beq_iff_eq.mp hExec0
              simp [h0]
            rw [hExecNe]
            simp only [Bool.false_eq_true, ↓reduceIte]
            rw [hOpenOk]
            dsimp only
            rw [bracketCloseDirM_run]
            simp only [Bind.bind, StateT.bind, hFstatMid, vfsToStat,
              show (EntryKind.dir != EntryKind.dir) = false from rfl, Bool.false_eq_true,
              hRead0F, hExec0, Bool.false_or, ↓reduceIte]
            dsimp only [Pure.pure, StateT.pure]
            rw [hClMid]
            exact ⟨⟨⟨_, rfl, rfl⟩, rfl, rfl⟩, trivial⟩
          · have hExec1 : (m / 64) % 2 = 1 := by
              have hNe : (m / 64) % 2 ≠ 0 := fun h => hExec0 (beq_iff_eq.mpr h)
              omega
            have hBoth1 : ((m / 256) % 2 == 1 && (m / 64) % 2 == 1) = true := by rw [hRead1, hExec1]; decide
            have hExec0F : ((m / 64) % 2 == 0) = false := by rw [hExec1]; decide
            rw [hBoth1]
            simp only [↓reduceIte]
            rw [hOpenOk]
            dsimp only
            rw [bracketCloseDirM_run]
            simp only [Bind.bind, StateT.bind, hFstatMid, vfsToStat,
              show (EntryKind.dir != EntryKind.dir) = false from rfl, Bool.false_eq_true,
              hRead0F, hExec0F, Bool.or_false, ↓reduceIte, Internal.subtreeOpsM,
              show Internal.splitLastAux RelPath.root.segments [] = none from rfl,
              show (EntryKind.dir == EntryKind.dir) = true from rfl, Pure.pure, StateT.pure]
            rw [hClMid]
            exact ⟨⟨trivial, rfl⟩, trivial⟩
  · have hValF : Model.isValidRawPath root = false := Bool.eq_false_iff.mpr hVal
    have hValT : (!Model.isValidRawPath root) = true := by simp [hValF]
    have hOpenErr : vfsDirOps.openDir root st₀ = (.error { kind := .invalidInput, path := some root, message := s!"invalid path: {root}" }, st₀) := by
      rw [hOp]; unfold openDirTpl; simp [hValF]
    simp only [hValT, ↓reduceIte, hOpenErr]
    exact ⟨⟨⟨_, rfl, rfl⟩, rfl, rfl⟩, trivial⟩

/-- Witness check for `test_fs_withSubtree_validatesRootAndAlwaysClosesHandle`. -/
theorem reach_fs_withSubtree_validatesRootAndAlwaysClosesHandle :
    Core.CanReach (test_fs_withSubtree_validatesRootAndAlwaysClosesHandle Internal.mkSubtreeOpenerM) := by
  have hInv : DirHandleInvariant emptyVfsState := fun _ _ hm => by cases hm
  exact ⟨emptyVfsState, "/", .ok (), hInv,
    proof_fs_withSubtree_validatesRootAndAlwaysClosesHandle emptyVfsState "/" (.ok ()) hInv⟩

/-- `Internal.subtreeOpsM` satisfies `test_fs_subtree_rootPath_enforcesRootRules`. -/
theorem proof_fs_subtree_rootPath_enforcesRootRules :
    Core.AllPass (test_fs_subtree_rootPath_enforcesRootRules Internal.subtreeOpsM) := by
  intro st dh pos pm bytes lockMode b1 target hLd _ hPos
  dsimp only [Internal.subtreeOpsM, StateT.run, Bind.bind, StateT.bind, RelPath.root, Internal.splitLastAux]
  have hFstat : vfsDirOps.fstatDir dh st = (.ok (vfsToStat (.dir pm)), st) := by
    rw [vfsDirOps_fstatDir_def, hLd]
    dsimp only
    rw [hPos]
  rw [hFstat]
  dsimp only [vfsToStat, Pure.pure, StateT.pure]
  have hClosed : lookupDir st { handleId := 0, rootPath := dh.rootPath } = none := by
    simp [lookupDir]
  have hClosedFstat : vfsDirOps.fstatDir { handleId := 0, rootPath := dh.rootPath } st =
      (.error (mInvalidDirHandleErr { handleId := 0, rootPath := dh.rootPath }), st) := by
    rw [vfsDirOps_fstatDir_def, hClosed]
  refine ⟨rfl, ⟨⟨_, rfl, rfl⟩, rfl⟩, ⟨rfl, hPos, rfl⟩, ⟨⟨_, rfl, rfl⟩, rfl⟩, ⟨⟨_, rfl, rfl⟩, rfl⟩,
    ⟨⟨_, rfl, rfl⟩, rfl⟩, ⟨⟨_, rfl, rfl⟩, rfl⟩, ⟨⟨_, rfl, rfl⟩, rfl⟩, ⟨⟨_, rfl, rfl⟩, rfl⟩,
    ⟨⟨_, rfl, rfl⟩, rfl, rfl⟩, ⟨⟨_, rfl, rfl⟩, rfl, rfl⟩, ?_, ?_, trivial⟩
  · rw [hClosedFstat]
    exact ⟨_, rfl, rfl⟩
  · rw [hClosedFstat]
    exact ⟨_, rfl, rfl⟩

/-- Witness check for `test_fs_subtree_rootPath_enforcesRootRules`. -/
theorem reach_fs_subtree_rootPath_enforcesRootRules :
    Core.CanReach (test_fs_subtree_rootPath_enforcesRootRules Internal.subtreeOpsM) := by
  let st := stateWithRootHandle (fun _ => none)
  have hAll := proof_fs_subtree_rootPath_enforcesRootRules st rootHandle [] 0o755 ByteArray.empty .exclusive false "t"
    rfl (fun _ _ hm => by simp [st, stateWithRootHandle] at hm; rcases hm with ⟨rfl, rfl⟩; decide) rfl
  exact ⟨st, rootHandle, [], 0o755, ByteArray.empty, .exclusive, false, "t",
    rfl, (fun _ _ hm => by simp [st, stateWithRootHandle] at hm; rcases hm with ⟨rfl, rfl⟩; decide), rfl, hAll⟩

/-- `Internal.subtreeOpsM` satisfies `test_fs_subtree_leafSymlink_followsExactLeafTable`. -/
theorem proof_fs_subtree_leafSymlink_followsExactLeafTable :
    Core.AllPass (test_fs_subtree_leafSymlink_followsExactLeafTable Internal.subtreeOpsM) := by
  intro st dh pos pre leaf target lm bytes lockMode b existOk hLd hInv hPre hPar hSym hTmpNone
  let parentPos := pos ++ pre.map (·.val)
  rcases hPar with ⟨pm, hParNd, hW, hX⟩
  have hSplit := subtreeSplitLastAux_append_singleton pre leaf
  have hPosDir : ∃ dm, nodeAt st.tree pos = some (.dir dm) ∧ dm / 256 % 2 = 1 ∧ dm / 64 % 2 = 1 := by
    simpa [List.take] using hPre 0 (Nat.zero_le _)
  have hAncPar : ∀ k < pre.length, ∃ dm, nodeAt st.tree (pos ++ (pre.take k).map (·.val)) = some (.dir dm) ∧
      (0 < k → dm / 256 % 2 = 1) ∧ dm / 64 % 2 = 1 := fun k hk => by
    rcases hPre k (Nat.le_of_lt hk) with ⟨dm, hD, hR, hE⟩
    exact ⟨dm, hD, fun _ => hR, hE⟩
  have hAncAll : ∀ k < (pre ++ [leaf]).length,
      ∃ dm, nodeAt st.tree (pos ++ ((pre ++ [leaf]).take k).map (·.val)) = some (.dir dm) ∧
        dm / 256 % 2 = 1 ∧ dm / 64 % 2 = 1 := fun k hk => by
    rw [List.length_append, List.length_singleton] at hk
    have hLe : k ≤ pre.length := Nat.lt_succ_iff.mp hk
    rw [List.take_append_of_le_length hLe]
    exact hPre k hLe
  have hSymFull : nodeAt st.tree (pos ++ (pre ++ [leaf]).map (·.val)) = some (.symlink target lm) := by
    simpa [List.map_append, List.map_singleton, List.append_assoc] using hSym
  have hXF : (pm / 64 % 2 == 0) = false := by rw [hX]; decide
  have hWXF : (pm / 128 % 2 == 0 || pm / 64 % 2 == 0) = false := by rw [hW, hX]; decide
  have hParR : pm / 256 % 2 = 1 := by
    have hPm := hPre pre.length (Nat.le_refl _)
    rw [List.take_length] at hPm
    rcases hPm with ⟨dm, hDm, hR, _⟩
    rw [hParNd] at hDm
    cases hDm
    exact hR
  have hWalkConst : ∀ {α : Type} (act : DirHandle → StateM VfsState (Except FsError α)) (res : Except FsError α),
      (∀ parDh stM, lookupDir stM parDh = some parentPos → stM.tree = st.tree → stM.keys = st.keys →
        stM.locks = st.locks → act parDh stM = (res, stM)) →
      ∃ st', Internal.walkDescendAuxM vfsDirOps true dh pre act st = (res, st') ∧ st'.nodes = st.nodes ∧ st'.locks = st.locks := by
    intro α act res hAct
    have hWalk := walkDescendM_ok pre dh pos st act hLd hInv hAncPar (fun _ => ⟨pm, hParNd, hParR⟩)
    by_cases hPre0 : pre = []
    · subst hPre0
      have hW1 := hWalk.1 rfl
      rw [Internal.walkDescendM] at hW1
      rw [hW1]
      exact ⟨st, hAct dh st (by simpa [parentPos] using hLd) rfl rfl rfl, rfl, rfl⟩
    · rcases hWalk.2 hPre0 with
        ⟨leafDh, stMid, hPosDh, hLdMid, hTreeMid, hKeysMid, _, _, hLocksMid, _, hLtMid, hOpenMid, hWalkEq⟩
      rw [Internal.walkDescendM] at hWalkEq
      rw [hWalkEq, bracketCloseDirM_run, hAct leafDh stMid hLdMid hTreeMid hKeysMid hLocksMid]
      dsimp only
      rw [vfsDirOps_closeDir_fresh leafDh stMid parentPos hPosDh st.openDirs hOpenMid hLtMid]
      exact ⟨{ stMid with openDirs := st.openDirs }, rfl, nodes_eq_of_tree_eq' hTreeMid, hLocksMid⟩
  dsimp only [Internal.subtreeOpsM, StateT.run, Bind.bind, StateT.bind, Pure.pure, StateT.pure]
  rw [hSplit]
  simp only [Bind.bind, StateT.bind]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, trivial⟩
  · rcases hWalkConst (fun parDh => vfsDirOps.readRegularAt parDh leaf)
        (.error { kind := .invalidInput, path := some leaf.val, message := s!"symlink refused: {leaf.val}" })
        (fun parDh stM hLdM hTM _ _ => by
          rw [vfsDirOps_readRegularAt_def, hLdM]
          dsimp only
          rw [hTM]
          dsimp only [parentPos]
          rw [hParNd]
          simp only [hXF, Bool.false_eq_true, ↓reduceIte]
          rw [hSym]) with ⟨st', hW, hNodes, _⟩
    erw [hW]
    exact ⟨⟨_, rfl, rfl⟩, hNodes⟩
  · have hSymD := walkDescendM_symlink_err dh pos (pre ++ [leaf]) [] target lm st
        (fun dirDh => do
          match ← vfsDirOps.readDirAt dirDh with
          | .error e => pure (.error e)
          | .ok names => pure (.ok (Internal.sortEntryNames names).toArray))
        hLd hPosDir hAncAll hSymFull
    rcases hSymD with ⟨e, st', hW, hKind, hNodes, _⟩
    rw [Internal.walkDescendM] at hW
    simp only [List.append_nil] at hW
    erw [hW]
    exact ⟨⟨e, rfl, hKind⟩, hNodes⟩
  · rcases walkRecM_symlink_err dh pos (pre ++ [leaf]) [] target lm st hLd hPosDir hAncAll hSymFull with
      ⟨e, st', hW, hKind, hNodes, _⟩
    simp only [List.append_nil] at hW
    rw [hW]
    exact ⟨⟨e, rfl, hKind⟩, hNodes⟩
  · have hWLockAct : ∀ parDh stM, lookupDir stM parDh = some parentPos → stM.tree = st.tree → stM.keys = st.keys →
        stM.locks = st.locks →
        vfsDirOps.acquireLockAt parDh leaf lockMode b false stM =
          (.error { kind := .invalidInput, path := some leaf.val, message := s!"symlink rejected for lock: {leaf.val}" }, stM) := by
      intro parDh stM hLdM hTM _ _
      rcases vfsDirOps_acquireLockAt_tpl stM parDh leaf lockMode b false with ⟨d, hEq⟩
      rw [hEq]; unfold acquireLockAtTpl; rw [hLdM]
      dsimp only; rw [hTM]; dsimp only [parentPos]; rw [hParNd]
      simp only [hXF, Bool.false_eq_true, ↓reduceIte]
      rw [hSym]
    rcases hWalkConst (fun parDh => vfsDirOps.acquireLockAt parDh leaf lockMode b false)
        (.error { kind := .invalidInput, path := some leaf.val, message := s!"symlink rejected for lock: {leaf.val}" })
        hWLockAct with ⟨st', hW, hNodes, hLocks⟩
    erw [hW]
    exact ⟨⟨_, rfl, rfl⟩, hNodes, hLocks⟩
  · have hTLockAct : ∀ parDh stM, lookupDir stM parDh = some parentPos → stM.tree = st.tree → stM.keys = st.keys →
        stM.locks = st.locks →
        vfsDirOps.acquireLockAt parDh leaf lockMode b true stM =
          (.error { kind := .invalidInput, path := some leaf.val, message := s!"symlink rejected for lock: {leaf.val}" }, stM) := by
      intro parDh stM hLdM hTM _ _
      rcases vfsDirOps_acquireLockAt_tpl stM parDh leaf lockMode b true with ⟨d, hEq⟩
      rw [hEq]; unfold acquireLockAtTpl; rw [hLdM]
      dsimp only; rw [hTM]; dsimp only [parentPos]; rw [hParNd]
      simp only [hXF, Bool.false_eq_true, ↓reduceIte]
      rw [hSym]
    rcases hWalkConst (fun parDh => vfsDirOps.acquireLockAt parDh leaf lockMode b true)
        (.error { kind := .invalidInput, path := some leaf.val, message := s!"symlink rejected for lock: {leaf.val}" })
        hTLockAct with ⟨st', hW, hNodes, hLocks⟩
    erw [hW]
    dsimp only
    simp only [show (FsErrorKind.invalidInput == FsErrorKind.wouldBlock) = false from rfl, Bool.false_eq_true, ↓reduceIte]
    exact ⟨⟨_, rfl, rfl⟩, hNodes, hLocks⟩
  · let mkLeafAct : DirHandle → StateM VfsState (Except FsError Unit) := fun parDh => do
      match ← vfsDirOps.createDirAt parDh leaf with
      | .ok () => pure (.ok ())
      | .error e =>
        if existOk && (e.kind == .alreadyExists || e.kind == .permissionDenied) then
          match ← vfsDirOps.lstatAt parDh leaf with
          | .error _ => pure (.error e)
          | .ok info =>
            if info.kind == .dir then pure (.ok ())
            else if e.kind == .alreadyExists then pure (.error e)
            else pure (.error { kind := .alreadyExists, path := some leaf.val, message := s!"already exists: {leaf.val}" })
        else pure (.error e)
    have hMkLeaf : ∀ parDh stM, lookupDir stM parDh = some parentPos → stM.tree = st.tree → stM.keys = st.keys →
        stM.locks = st.locks →
        mkLeafAct parDh stM = (.error { kind := .alreadyExists, path := some leaf.val, message := s!"already exists: {leaf.val}" }, stM) := by
      intro parDh stM hLdM hTM _ _
      dsimp only [mkLeafAct, Bind.bind, StateT.bind]
      have hCr : vfsDirOps.createDirAt parDh leaf stM =
          (.error { kind := .alreadyExists, path := some leaf.val, message := s!"already exists: {leaf.val}" }, stM) := by
        rw [vfsDirOps_createDirAt_def, hLdM]; dsimp only; rw [hTM]; dsimp only [parentPos]; rw [hParNd]
        simp only [hWXF, Bool.false_eq_true, ↓reduceIte]
        rw [hSym]
      rw [hCr]
      dsimp only
      cases existOk
      · simp [Pure.pure, StateT.pure]
      · have hLst : vfsDirOps.lstatAt parDh leaf stM = (.ok (vfsToStat (.symlink target lm)), stM) := by
          rw [vfsDirOps_lstatAt_def, hLdM]; dsimp only; rw [hTM]; dsimp only [parentPos]; rw [hParNd]
          simp only [hXF, Bool.false_eq_true, ↓reduceIte]
          rw [hSym]
        simp only [Bool.true_and, show (FsErrorKind.alreadyExists == FsErrorKind.alreadyExists) = true from rfl,
          Bool.true_or, ↓reduceIte, Bind.bind, StateT.bind]
        rw [hLst]
        simp only [vfsToStat, show (EntryKind.symlink == EntryKind.dir) = false from rfl,
          Bool.false_eq_true, ↓reduceIte, Pure.pure, StateT.pure]
    rcases hWalkConst mkLeafAct
        (.error { kind := .alreadyExists, path := some leaf.val, message := s!"already exists: {leaf.val}" })
        hMkLeaf with ⟨st', hW, hNodes, _⟩
    cases b
    · change (∃ e, (Internal.walkDescendAuxM vfsDirOps true dh pre mkLeafAct st).1 = .error e ∧
          e.kind = .alreadyExists) ∧
        (Internal.walkDescendAuxM vfsDirOps true dh pre mkLeafAct st).2.nodes = st.nodes
      rw [hW]
      exact ⟨⟨_, rfl, rfl⟩, hNodes⟩
    · change (∃ e, (Internal.mkdirWalkM vfsDirOps true dh pre mkLeafAct st).1 = .error e ∧
          e.kind = .alreadyExists) ∧
        (Internal.mkdirWalkM vfsDirOps true dh pre mkLeafAct st).2.nodes = st.nodes
      rw [mkdirWalkM_eq_walkDescendAuxM pre true dh pos mkLeafAct st hLd hAncPar (fun _ => ⟨pm, hParNd, hParR⟩), hW]
      exact ⟨⟨_, rfl, rfl⟩, hNodes⟩
  · rcases hWalkConst (fun parDh => vfsDirOps.symlinkAt "other" parDh leaf)
        (.error { kind := .alreadyExists, path := some leaf.val, message := s!"already exists: {leaf.val}" })
        (fun parDh stM hLdM hTM _ _ => by
          rw [vfsDirOps_symlinkAt_def, hLdM]; dsimp only [parentPos]; rw [hTM, hParNd]
          simp only [show ("other".isEmpty || "other".toList.contains (Char.ofNat 0)) = false from by decide,
            hWXF, Bool.false_eq_true, ↓reduceIte]
          rw [hSym]) with ⟨st', hW, hNodes, _⟩
    change (∃ e, (Internal.walkDescendM vfsDirOps dh pre (fun parDh => vfsDirOps.symlinkAt "other" parDh leaf) st).fst = .error e ∧
          e.kind = .alreadyExists) ∧
      (Internal.walkDescendM vfsDirOps dh pre (fun parDh => vfsDirOps.symlinkAt "other" parDh leaf) st).snd.nodes = st.nodes
    rw [Internal.walkDescendM, hW]
    exact ⟨⟨_, rfl, rfl⟩, hNodes⟩
  · rcases hWalkConst (fun parDh => vfsDirOps.unlinkAt parDh leaf true)
        (.error { kind := .notADirectory, path := some leaf.val, message := s!"not a directory: {leaf.val}" })
        (fun parDh stM hLdM hTM _ _ => by
          rw [vfsDirOps_unlinkAt_def, hLdM]; dsimp only [parentPos]; rw [hTM, hParNd]
          simp only [hWXF, Bool.false_eq_true, ↓reduceIte]
          rw [hSym]) with ⟨st', hW, hNodes, _⟩
    erw [hW]
    exact ⟨⟨_, rfl, rfl⟩, hNodes⟩
  · rcases hWalkConst (fun parDh => vfsDirOps.lstatAt parDh leaf)
        (.ok (vfsToStat (.symlink target lm)))
        (fun parDh stM hLdM hTM _ _ => by
          rw [vfsDirOps_lstatAt_def, hLdM]; dsimp only; rw [hTM]; dsimp only [parentPos]; rw [hParNd]
          simp only [hXF, Bool.false_eq_true, ↓reduceIte]
          rw [hSym]) with ⟨st', hW, hNodes, _⟩
    erw [hW]
    dsimp only
    simp only [vfsToStat, show (EntryKind.symlink != EntryKind.dir) = true from rfl, ↓reduceIte]
    exact ⟨⟨_, rfl, rfl⟩, hNodes⟩
  · rcases hWalkConst (fun parDh => vfsDirOps.lstatAt parDh leaf)
        (.ok (vfsToStat (.symlink target lm)))
        (fun parDh stM hLdM hTM _ _ => by
          rw [vfsDirOps_lstatAt_def, hLdM]; dsimp only; rw [hTM]; dsimp only [parentPos]; rw [hParNd]
          simp only [hXF, Bool.false_eq_true, ↓reduceIte]
          rw [hSym]) with ⟨st', hW, hNodes, _⟩
    erw [hW]
    exact ⟨⟨vfsToStat (.symlink target lm), rfl, rfl⟩, hNodes⟩
  · have hWalk := walkDescendM_ok pre dh pos st (fun parDh => vfsDirOps.unlinkAt parDh leaf false)
      hLd hInv hAncPar (fun _ => ⟨pm, hParNd, hParR⟩)
    by_cases hPre0 : pre = []
    · subst hPre0
      have hWalk1 := hWalk.1 rfl
      rw [Internal.walkDescendM] at hWalk1
      erw [hWalk1]
      have hU : vfsDirOps.unlinkAt dh leaf false st =
          (.ok (), { st with tree := vfsTreeSet st.tree (pos ++ [leaf.val]) none }) := by
        have hPar0 : nodeAt st.tree pos = some (.dir pm) := by simpa using hParNd
        have hSym0 : nodeAt st.tree (pos ++ [leaf.val]) = some (.symlink target lm) := by simpa using hSym
        rw [vfsDirOps_unlinkAt_def, hLd]; dsimp only; rw [hPar0]
        simp only [hWXF, Bool.false_eq_true, ↓reduceIte, hSym0]
      rw [hU]
      dsimp only [Pure.pure, StateT.pure]
      have hDirGet : ∃ dm ch, vfsTreeGet st.tree pos = some (.dir dm ch) :=
        let ⟨ch, hG⟩ := vfsTreeGet_dir_of_nodeAt (by simpa using hParNd); ⟨pm, ch, hG⟩
      refine ⟨rfl, ?_, ?_⟩
      · unfold nodeAt; rw [show pos ++ ([] : List EntryName).map (·.val) ++ [leaf.val] = pos ++ [leaf.val] from by simp]
        rw [vfsTreeGet_vfsTreeSet_eq st.tree pos leaf.val none hDirGet]; rfl
      · intro p hNot
        change vfsTreeNodes (vfsTreeSet st.tree (pos ++ [leaf.val]) none) p = vfsTreeNodes st.tree p
        unfold vfsTreeNodes
        split
        · exact nodeAt_vfsTreeSet_outside st.tree pos leaf.val none (vfsSplitSegs p) hDirGet (by simpa using hNot)
        · rfl
    · rcases hWalk.2 hPre0 with
        ⟨leafDh, stMid, hPosDh, hLdMid, hTreeMid, _, _, _, _, _, hLtMid, hOpenMid, hWalkEq⟩
      rw [Internal.walkDescendM] at hWalkEq
      erw [hWalkEq, bracketCloseDirM_run]
      have hParMid : nodeAt stMid.tree parentPos = some (.dir pm) := by rw [hTreeMid]; exact hParNd
      have hSymMid : nodeAt stMid.tree (parentPos ++ [leaf.val]) = some (.symlink target lm) := by rw [hTreeMid]; exact hSym
      let stU : VfsState := { stMid with tree := vfsTreeSet stMid.tree (parentPos ++ [leaf.val]) none }
      have hU : vfsDirOps.unlinkAt leafDh leaf false stMid = (.ok (), stU) := by
        rw [vfsDirOps_unlinkAt_def, hLdMid]; dsimp only; rw [hParMid]
        simp only [hWXF, Bool.false_eq_true, ↓reduceIte]
        rw [hSymMid]
      rw [hU, vfsDirOps_closeDir_fresh leafDh stU parentPos hPosDh st.openDirs hOpenMid hLtMid]
      dsimp only [Pure.pure, StateT.pure]
      have hDirGetMid : ∃ dm ch, vfsTreeGet stMid.tree parentPos = some (.dir dm ch) :=
        let ⟨ch, hG⟩ := vfsTreeGet_dir_of_nodeAt hParMid; ⟨pm, ch, hG⟩
      refine ⟨rfl, ?_, ?_⟩
      · unfold nodeAt; rw [vfsTreeGet_vfsTreeSet_eq stMid.tree parentPos leaf.val none hDirGetMid]; rfl
      · intro p hNot
        change vfsTreeNodes (vfsTreeSet stMid.tree (parentPos ++ [leaf.val]) none) p = st.nodes p
        rw [← nodes_eq_of_tree_eq' hTreeMid]
        change vfsTreeNodes (vfsTreeSet stMid.tree (parentPos ++ [leaf.val]) none) p = vfsTreeNodes stMid.tree p
        unfold vfsTreeNodes
        split
        · exact nodeAt_vfsTreeSet_outside stMid.tree parentPos leaf.val none (vfsSplitSegs p) hDirGetMid hNot
        · rfl
  · have hWalk := walkDescendM_ok pre dh pos st (fun parDh => Internal.atomicWriteAtAuxM vfsDirOps parDh leaf bytes 16)
      hLd hInv hAncPar (fun _ => ⟨pm, hParNd, hParR⟩)
    by_cases hPre0 : pre = []
    · subst hPre0
      have hWalk1 := hWalk.1 rfl
      rw [Internal.walkDescendM] at hWalk1
      rw [hWalk1]
      have hPar0 : nodeAt st.tree pos = some (.dir pm) := by simpa using hParNd
      have hSym0 : nodeAt st.tree (pos ++ [leaf.val]) = some (.symlink target lm) := by simpa using hSym
      have hTmp0 : nodeAt st.tree (pos ++ [".t." ++ toString st.nonce]) = none := by simpa using hTmpNone
      have hNotDir : match nodeAt st.tree (pos ++ [leaf.val]) with | some (.dir _) => False | _ => True := by
        rw [hSym0]; trivial
      have hAW := atomicWriteAtAuxM_ok_fresh dh pos leaf bytes 15 st pm hLd hPar0 hW hX hTmp0 hNotDir
      cases hRun : Internal.atomicWriteAtAuxM vfsDirOps dh leaf bytes 16 st with
      | mk rWrite stWrite =>
        rw [hRun] at hAW
        simpa using And.intro hAW.1 (And.intro hAW.2.2.1 hAW.2.2.2.1)
    · rcases hWalk.2 hPre0 with
        ⟨leafDh, stMid, hPosDh, hLdMid, hTreeMid, _, _, hNonceMid, _, _, hLtMid, hOpenMid, hWalkEq⟩
      rw [Internal.walkDescendM] at hWalkEq
      rw [hWalkEq, bracketCloseDirM_run]
      have hParMid : nodeAt stMid.tree parentPos = some (.dir pm) := by rw [hTreeMid]; exact hParNd
      have hTmpMid : nodeAt stMid.tree (parentPos ++ [".t." ++ toString stMid.nonce]) = none := by
        rw [hTreeMid, hNonceMid]; exact hTmpNone
      have hNotDirMid : match nodeAt stMid.tree (parentPos ++ [leaf.val]) with | some (.dir _) => False | _ => True := by
        rw [hTreeMid, hSym]; trivial
      have hAW := atomicWriteAtAuxM_ok_fresh leafDh parentPos leaf bytes 15 stMid pm
        hLdMid hParMid hW hX hTmpMid hNotDirMid
      cases hRun : Internal.atomicWriteAtAuxM vfsDirOps leafDh leaf bytes 16 stMid with
      | mk rWrite stAW =>
        rw [hRun] at hAW
        rcases hAW with ⟨rfl, _, hLeafAW, hSameAW, hOpenAW⟩
        dsimp only
        rw [vfsDirOps_closeDir_fresh leafDh stAW parentPos hPosDh st.openDirs (hOpenAW.trans hOpenMid) hLtMid]
        dsimp only
        refine ⟨rfl, hLeafAW, ?_⟩
        intro p hNot
        change stAW.nodes p = st.nodes p
        rw [hSameAW p hNot, nodes_eq_of_tree_eq' hTreeMid]

/-- Witness check for `test_fs_subtree_leafSymlink_followsExactLeafTable`. -/
theorem reach_fs_subtree_leafSymlink_followsExactLeafTable :
    Core.CanReach (test_fs_subtree_leafSymlink_followsExactLeafTable Internal.subtreeOpsM) := by
  let st := stateWithRootHandle (fun s => if s == "sym" then some (.symlink "t" 0o777) else none) ["/", "/sym"]
  have hInv : DirHandleInvariant st := fun _ _ hm => by
    simp [st, stateWithRootHandle] at hm; rcases hm with ⟨rfl, rfl⟩; decide
  have hPre : ∀ k ≤ ([] : List EntryName).length,
      ∃ dm, nodeAt st.tree ([] ++ (([] : List EntryName).take k).map (·.val)) = some (.dir dm) ∧
        (dm / 256) % 2 = 1 ∧ (dm / 64) % 2 = 1 := fun k hk => by
    cases k with
    | zero => exact ⟨0o755, rfl, by decide, by decide⟩
    | succ _ => simp at hk
  have hPar : ∃ pm, nodeAt st.tree ([] ++ ([] : List EntryName).map (·.val)) = some (.dir pm) ∧
      (pm / 128) % 2 = 1 ∧ (pm / 64) % 2 = 1 := ⟨0o755, rfl, by decide, by decide⟩
  have hAll := proof_fs_subtree_leafSymlink_followsExactLeafTable st rootHandle [] [] (EntryName.lit "sym")
    "t" 0o777 ByteArray.empty .exclusive false false rfl hInv hPre hPar rfl rfl
  exact ⟨st, rootHandle, [], [], EntryName.lit "sym", "t", 0o777, ByteArray.empty, .exclusive, false, false,
    rfl, hInv, hPre, hPar, rfl, rfl, hAll⟩

private theorem atomicWriteAtAuxM_ok_fresh_outside
    (parDh : DirHandle) (parentPos : List String)
    (leaf : EntryName) (bytes : ByteArray) (attempts : Nat) (st : VfsState) (pm : Nat)
    (hLd : lookupDir st parDh = some parentPos)
    (hPar : nodeAt st.tree parentPos = some (.dir pm))
    (hW : pm / 128 % 2 = 1) (hX : pm / 64 % 2 = 1)
    (hTmpNone : nodeAt st.tree (parentPos ++ [".t." ++ toString st.nonce]) = none)
    (hLeafNe : leaf.val ≠ ".t." ++ toString st.nonce)
    (hLeafNotDir : match nodeAt st.tree (parentPos ++ [leaf.val]) with | some (.dir _) => False | _ => True) :
    match Internal.atomicWriteAtAuxM vfsDirOps parDh leaf bytes (attempts + 1) st with
    | (res, st') =>
      res = .ok () ∧
      nodeAt st'.tree (parentPos ++ [leaf.val]) = some (.file bytes 0o644) ∧
      (∀ q, ¬ (parentPos ++ [leaf.val] <+: q) → nodeAt st'.tree q = nodeAt st.tree q) := by
  rw [atomicWriteAtAuxM_succ]
  simp only [Bind.bind, Pure.pure, StateT.bind]
  cases hFr : vfsDirOps.freshTempName st with
  | mk tmp st1 =>
    have hFrDef := vfsDirOps_freshTempName_def st
    rw [hFr] at hFrDef
    dsimp only at hFrDef ⊢
    rcases hFrDef with ⟨hTmpVal, hSt1⟩
    have hWXF : (pm / 128 % 2 == 0 || pm / 64 % 2 == 0) = false := by rw [hW, hX]; decide
    have hTmpNone1 : nodeAt st1.tree (parentPos ++ [tmp.val]) = none := by
      rw [hSt1, hTmpVal]; exact hTmpNone
    have hPar1 : nodeAt st1.tree parentPos = some (.dir pm) := by rw [hSt1]; exact hPar
    have hLd1 : lookupDir st1 parDh = some parentPos := by rw [hSt1]; exact hLd
    have hDirGet : ∃ dm ch, vfsTreeGet st.tree parentPos = some (.dir dm ch) := ⟨pm, vfsTreeGet_dir_of_nodeAt hPar⟩
    have hDirGet1 : ∃ dm ch, vfsTreeGet st1.tree parentPos = some (.dir dm ch) := by rw [hSt1]; exact hDirGet
    have hCf : vfsDirOps.createFileAt parDh tmp bytes st1 =
        (.ok (), { st1 with
          tree := vfsTreeSet st1.tree (parentPos ++ [tmp.val]) (some (.file bytes 0o644))
          keys := pathOfSegs (parentPos ++ [tmp.val]) :: st1.keys }) := by
      rw [vfsDirOps_createFileAt_def, hLd1]; dsimp only; rw [hPar1]
      simp only [hWXF, Bool.false_eq_true, ↓reduceIte, hTmpNone1]
    rw [hCf]
    dsimp only
    let st2 : VfsState :=
      { st1 with
        tree := vfsTreeSet st1.tree (parentPos ++ [tmp.val]) (some (.file bytes 0o644))
        keys := pathOfSegs (parentPos ++ [tmp.val]) :: st1.keys }
    have hNotPreSelf : ¬ (parentPos ++ [tmp.val] <+: parentPos) := by
      intro hPre; have hL := List.IsPrefix.length_le hPre; simp at hL; omega
    have hPar2 : nodeAt st2.tree parentPos = some (.dir pm) := by
      change nodeAt (vfsTreeSet st1.tree (parentPos ++ [tmp.val]) (some (.file bytes 0o644))) parentPos = some (.dir pm)
      rw [nodeAt_vfsTreeSet_outside st1.tree parentPos tmp.val _ parentPos hDirGet1 hNotPreSelf, hPar1]
    have hTmpFile2 : vfsTreeGet st2.tree (parentPos ++ [tmp.val]) = some (.file bytes 0o644) :=
      vfsTreeGet_vfsTreeSet_eq st1.tree parentPos tmp.val (some (.file bytes 0o644)) hDirGet1
    have hNeTmpLeaf : tmp.val ≠ leaf.val := fun h => hLeafNe (hTmpVal ▸ h.symm)
    have hDiffPos : parentPos ++ [tmp.val] ≠ parentPos ++ [leaf.val] := fun h => by
      simp only [List.append_cancel_left_eq, List.cons.injEq, and_true] at h
      exact hNeTmpLeaf h
    have hBeqDiff : ((parentPos ++ [tmp.val]) == (parentPos ++ [leaf.val])) = false := beq_false_of_ne hDiffPos
    have hNotPrefDst : (parentPos ++ [tmp.val]).isPrefixOf parentPos = false := by
      rw [Bool.eq_false_iff]
      intro hP
      have hL := List.IsPrefix.length_le (List.isPrefixOf_iff_prefix.mp hP)
      simp at hL; omega
    have hNotPreTmpLeaf : ¬ (parentPos ++ [tmp.val] <+: parentPos ++ [leaf.val]) := by
      intro hP
      rcases hP with ⟨r, hr⟩
      cases r with
      | nil => simp at hr; exact hNeTmpLeaf hr
      | cons _ _ => have hL := congrArg List.length hr; simp at hL
    have hDst2NotDir : ∀ dm, nodeAt st2.tree (parentPos ++ [leaf.val]) ≠ some (.dir dm) := by
      intro dm hEq
      have hOrigEq : nodeAt st2.tree (parentPos ++ [leaf.val]) = nodeAt st.tree (parentPos ++ [leaf.val]) := by
        change nodeAt (vfsTreeSet st1.tree (parentPos ++ [tmp.val]) (some (.file bytes 0o644))) (parentPos ++ [leaf.val]) = _
        rw [nodeAt_vfsTreeSet_outside st1.tree parentPos tmp.val _ (parentPos ++ [leaf.val]) hDirGet1 hNotPreTmpLeaf, hSt1]
      rw [hOrigEq] at hEq
      rw [hEq] at hLeafNotDir
      exact hLeafNotDir
    have hLd2 : lookupDir st2 parDh = some parentPos := hLd1
    have hRen : vfsDirOps.renameAt parDh tmp parDh leaf st2 =
        (.ok (), { st2 with
          tree := vfsTreeSet (vfsTreeSet st2.tree (parentPos ++ [tmp.val]) none) (parentPos ++ [leaf.val]) (some (.file bytes 0o644))
          keys := pathOfSegs (parentPos ++ [leaf.val]) :: mRemapKeysAfterRename st2.keys (parentPos ++ [tmp.val]) (parentPos ++ [leaf.val]) }) := by
      rw [vfsDirOps_renameAt_def, hLd2]; dsimp only; rw [hPar2]
      simp only [hWXF, Bool.false_eq_true, ↓reduceIte, hTmpFile2, hBeqDiff, hNotPrefDst]
      cases hDN : nodeAt st2.tree (parentPos ++ [leaf.val]) with
      | none => rfl
      | some dn =>
        cases dn with
        | dir dm => exact absurd hDN (hDst2NotDir dm)
        | file _ _ => rfl
        | symlink _ _ => rfl
    simp only [StateT.bind]
    dsimp only [st2] at hRen
    rw [hRen]
    let trTmpRm := vfsTreeSet st2.tree (parentPos ++ [tmp.val]) none
    have hDirGet2 : ∃ dm ch, vfsTreeGet st2.tree parentPos = some (.dir dm ch) := ⟨pm, vfsTreeGet_dir_of_nodeAt hPar2⟩
    have hParRm : nodeAt trTmpRm parentPos = some (.dir pm) := by
      rw [nodeAt_vfsTreeSet_outside st2.tree parentPos tmp.val none parentPos hDirGet2 hNotPreSelf, hPar2]
    have hDirGetRm : ∃ dm ch, vfsTreeGet trTmpRm parentPos = some (.dir dm ch) := ⟨pm, vfsTreeGet_dir_of_nodeAt hParRm⟩
    have hLeafFinal : nodeAt (vfsTreeSet trTmpRm (parentPos ++ [leaf.val]) (some (.file bytes 0o644))) (parentPos ++ [leaf.val]) =
        some (.file bytes 0o644) := by
      simpa [vfsTreeTopNode] using nodeAt_vfsTreeSet_eq trTmpRm parentPos leaf.val (some (.file bytes 0o644)) hDirGetRm
    refine ⟨rfl, hLeafFinal, fun q hNotPreQ => ?_⟩
    change nodeAt (vfsTreeSet trTmpRm (parentPos ++ [leaf.val]) (some (.file bytes 0o644))) q = nodeAt st.tree q
    rw [nodeAt_vfsTreeSet_outside trTmpRm parentPos leaf.val _ q hDirGetRm hNotPreQ]
    change nodeAt (vfsTreeSet (vfsTreeSet st1.tree (parentPos ++ [tmp.val]) (some (.file bytes 0o644)))
      (parentPos ++ [tmp.val]) none) q = nodeAt st.tree q
    rw [nodeAt_vfsTreeSet_temp_roundtrip st1.tree parentPos tmp.val (.file bytes 0o644) hDirGet1 hTmpNone1, hSt1]

private theorem stateTBind_run {α β : Type} (x : StateM VfsState α) (f : α → StateM VfsState β) (s : VfsState) :
    StateT.bind x f s = f (x s).1 (x s).2 := by
  change (match x s with | (a, s') => f a s') = f (x s).1 (x s).2
  cases x s; rfl

private theorem atomicWriteAtAuxM_rename_err_cleanup
    (ops : RawDirOpsM (StateM VfsState))
    (hFresh : ops.freshTempName = vfsDirOps.freshTempName)
    (hCreate : ops.createFileAt = vfsDirOps.createFileAt)
    (hUnlink : ops.unlinkAt = vfsDirOps.unlinkAt)
    (parDh : DirHandle) (parentPos : List String) (leaf : EntryName) (bytes : ByteArray)
    (attempts : Nat) (st : VfsState) (pm : Nat) (err : FsError)
    (hLd : lookupDir st parDh = some parentPos)
    (hPar : nodeAt st.tree parentPos = some (.dir pm))
    (hW : pm / 128 % 2 = 1) (hX : pm / 64 % 2 = 1)
    (hTmpNone : nodeAt st.tree (parentPos ++ [".t." ++ toString st.nonce]) = none)
    (hRenErr : ∀ (tmp : EntryName) (st2 : VfsState),
      tmp.val = ".t." ++ toString st.nonce →
      lookupDir st2 parDh = some parentPos →
      nodeAt st2.tree parentPos = some (.dir pm) →
      st2.tree = vfsTreeSet st.tree (parentPos ++ [tmp.val]) (some (.file bytes 0o644)) →
      st2.openDirs = st.openDirs →
      ops.renameAt parDh tmp parDh leaf st2 = (.error err, st2)) :
    match Internal.atomicWriteAtAuxM ops parDh leaf bytes (attempts + 1) st with
    | (res, st') =>
      res = .error err ∧
      (∀ q, nodeAt st'.tree q = nodeAt st.tree q) ∧
      st'.openDirs = st.openDirs := by
  rw [atomicWriteAtAuxM_succ]
  simp only [Bind.bind, Pure.pure, StateT.bind]
  rw [hFresh, hCreate, hUnlink]
  cases hFr : vfsDirOps.freshTempName st with
  | mk tmp st1 =>
    have hFrDef := vfsDirOps_freshTempName_def st
    rw [hFr] at hFrDef
    dsimp only at hFrDef ⊢
    rcases hFrDef with ⟨hTmpVal, hSt1⟩
    have hWXF : (pm / 128 % 2 == 0 || pm / 64 % 2 == 0) = false := by rw [hW, hX]; decide
    have hTmpNone1 : nodeAt st1.tree (parentPos ++ [tmp.val]) = none := by
      rw [hSt1, hTmpVal]; exact hTmpNone
    have hPar1 : nodeAt st1.tree parentPos = some (.dir pm) := by rw [hSt1]; exact hPar
    have hLd1 : lookupDir st1 parDh = some parentPos := by rw [hSt1]; exact hLd
    have hCf : vfsDirOps.createFileAt parDh tmp bytes st1 =
        (.ok (), { st1 with
          tree := vfsTreeSet st1.tree (parentPos ++ [tmp.val]) (some (.file bytes 0o644))
          keys := pathOfSegs (parentPos ++ [tmp.val]) :: st1.keys }) := by
      rw [vfsDirOps_createFileAt_def, hLd1]; dsimp only; rw [hPar1]
      simp only [hWXF, Bool.false_eq_true, ↓reduceIte, hTmpNone1]
    rw [hCf]
    dsimp only
    let st2 : VfsState :=
      { st1 with
        tree := vfsTreeSet st1.tree (parentPos ++ [tmp.val]) (some (.file bytes 0o644))
        keys := pathOfSegs (parentPos ++ [tmp.val]) :: st1.keys }
    have hDirGet : ∃ dm ch, vfsTreeGet st.tree parentPos = some (.dir dm ch) := ⟨pm, vfsTreeGet_dir_of_nodeAt hPar⟩
    have hDirGet1 : ∃ dm ch, vfsTreeGet st1.tree parentPos = some (.dir dm ch) := by rw [hSt1]; exact hDirGet
    have hNotPreSelf : ¬ (parentPos ++ [tmp.val] <+: parentPos) := by
      intro hPre; have hL := List.IsPrefix.length_le hPre; simp at hL; omega
    have hPar2 : nodeAt st2.tree parentPos = some (.dir pm) := by
      change nodeAt (vfsTreeSet st1.tree (parentPos ++ [tmp.val]) (some (.file bytes 0o644))) parentPos = some (.dir pm)
      rw [nodeAt_vfsTreeSet_outside st1.tree parentPos tmp.val _ parentPos hDirGet1 hNotPreSelf, hPar1]
    have hTree2 : st2.tree = vfsTreeSet st.tree (parentPos ++ [tmp.val]) (some (.file bytes 0o644)) := by
      change vfsTreeSet st1.tree (parentPos ++ [tmp.val]) (some (.file bytes 0o644)) = _
      rw [hSt1]
    have hRen := hRenErr tmp st2 hTmpVal hLd1 hPar2 hTree2 (by simp [st2, hSt1])
    dsimp only [st2] at hRen
    rw [stateTBind_run, hRen]
    dsimp only
    have hTmpFile2 : nodeAt st2.tree (parentPos ++ [tmp.val]) = some (.file bytes 0o644) := by
      change nodeAt (vfsTreeSet st1.tree (parentPos ++ [tmp.val]) (some (.file bytes 0o644))) (parentPos ++ [tmp.val]) = _
      simpa [vfsTreeTopNode] using nodeAt_vfsTreeSet_eq st1.tree parentPos tmp.val (some (.file bytes 0o644)) hDirGet1
    have hLd2 : lookupDir st2 parDh = some parentPos := hLd1
    have hUnl : vfsDirOps.unlinkAt parDh tmp false st2 =
        (.ok (), { st2 with tree := vfsTreeSet st2.tree (parentPos ++ [tmp.val]) none }) := by
      rw [vfsDirOps_unlinkAt_def, hLd2]; dsimp only; rw [hPar2]
      simp only [hWXF, Bool.false_eq_true, ↓reduceIte, hTmpFile2]
    dsimp only [st2] at hUnl
    rw [stateTBind_run, hUnl]
    refine ⟨rfl, fun q => ?_, by simp [hSt1]⟩
    change nodeAt (vfsTreeSet (vfsTreeSet st1.tree (parentPos ++ [tmp.val]) (some (.file bytes 0o644)))
      (parentPos ++ [tmp.val]) none) q = nodeAt st.tree q
    rw [nodeAt_vfsTreeSet_temp_roundtrip st1.tree parentPos tmp.val (.file bytes 0o644) hDirGet1 hTmpNone1, hSt1]

/-- `Internal.subtreeOpsM` satisfies `test_fs_subtree_atomicWriteBytes_maxSegmentAndTempCollisionAndCleanup`. -/
theorem proof_fs_subtree_atomicWriteBytes_maxSegmentAndTempCollisionAndCleanup :
    Core.AllPass (test_fs_subtree_atomicWriteBytes_maxSegmentAndTempCollisionAndCleanup Internal.subtreeOpsM) := by
  intro st dh pos bytes maxLeaf hLd _ _ hPar hTmp0 hTmp1 hNe hNotDir
  rcases hPar with ⟨pm, hParNd, hW, hX⟩
  have hStep := atomicWrite_collision_step vfsDirOps rfl rfl dh pos maxLeaf bytes st pm (.file ByteArray.empty 0o600)
    hLd hParNd hW hX hTmp0
  let stNext : VfsState := { st with nonce := st.nonce + 1 }
  have hOk := atomicWriteAtAuxM_ok_fresh_outside dh pos maxLeaf bytes 14 stNext pm
    hLd hParNd hW hX hTmp1 hNe.2 hNotDir
  change (let (r1, st1) := ((Internal.subtreeOpsM vfsDirOps dh).atomicWriteBytes { segments := [maxLeaf] } bytes).run st
    r1 = .ok () ∧ nodeAt st1.tree (pos ++ [maxLeaf.val]) = some (.file bytes 0o644) ∧
    nodeAt st1.tree (pos ++ [".t." ++ toString st.nonce]) = some (.file ByteArray.empty 0o600) ∧ _)
  dsimp only [Internal.subtreeOpsM, StateT.run]
  rw [show Internal.splitLastAux [maxLeaf] [] = some ([], maxLeaf) from rfl]
  dsimp only
  rw [walkDescendM_nil_eq, hStep]
  cases hRes1 : Internal.atomicWriteAtAuxM vfsDirOps dh maxLeaf bytes 15 stNext with
  | mk r1 st1 =>
    rw [hRes1] at hOk
    rcases hOk with ⟨rfl, hLeafNd, hOut1⟩
    have hNotPreTmp0 : ¬ (pos ++ [maxLeaf.val] <+: pos ++ [".t." ++ toString st.nonce]) := by
      intro hP
      rcases List.prefix_append_right_inj pos |>.mp hP with hSub
      rcases hSub with ⟨r, hr⟩
      cases r with
      | nil => simp only [List.append_nil, List.cons.injEq, and_true] at hr; exact hNe.1 hr
      | cons _ _ => have hL := congrArg List.length hr; simp at hL
    have hTmp0Pres : nodeAt st1.tree (pos ++ [".t." ++ toString st.nonce]) = some (.file ByteArray.empty 0o600) :=
      (hOut1 _ hNotPreTmp0).trans hTmp0
    refine ⟨rfl, hLeafNd, hTmp0Pres, ?_⟩
    intro dirLeaf _ hDirNd
    have hWXF : (pm / 128 % 2 == 0 || pm / 64 % 2 == 0) = false := by rw [hW, hX]; decide
    have hStepDir := atomicWrite_collision_step vfsDirOps rfl rfl dh pos dirLeaf bytes st pm (.file ByteArray.empty 0o600)
      hLd hParNd hW hX hTmp0
    let dirErr : FsError := { kind := .isADirectory, path := some dirLeaf.val, message := s!"is a directory: {dirLeaf.val}" }
    have hDirClean := atomicWriteAtAuxM_rename_err_cleanup vfsDirOps rfl rfl rfl dh pos dirLeaf bytes 14 stNext pm dirErr
      hLd hParNd hW hX hTmp1 (fun tmp st2 hTmpV hLd2 hPar2 hTree2 _ => by
        dsimp only [stNext] at hTmpV
        have hTmpNeDir : tmp.val ≠ dirLeaf.val := fun hEq => by
          rw [← hTmpV, hEq, hDirNd] at hTmp1
          cases hTmp1
        have hDiffP : pos ++ [tmp.val] ≠ pos ++ [dirLeaf.val] := fun hEq => by
          simp only [List.append_cancel_left_eq, List.cons.injEq, and_true] at hEq
          exact hTmpNeDir hEq
        have hBeqDiff : ((pos ++ [tmp.val]) == (pos ++ [dirLeaf.val])) = false := beq_false_of_ne hDiffP
        have hNotPref : (pos ++ [tmp.val]).isPrefixOf pos = false := by
          rw [Bool.eq_false_iff]; intro hP
          have hL := List.IsPrefix.length_le (List.isPrefixOf_iff_prefix.mp hP)
          simp at hL; omega
        have hDirGet : ∃ dm ch, vfsTreeGet st.tree pos = some (.dir dm ch) := ⟨pm, vfsTreeGet_dir_of_nodeAt hParNd⟩
        have hTmp2 : vfsTreeGet st2.tree (pos ++ [tmp.val]) = some (.file bytes 0o644) := by
          rw [hTree2]; exact vfsTreeGet_vfsTreeSet_eq st.tree pos tmp.val (some (.file bytes 0o644)) hDirGet
        have hNotPreTmpDir : ¬ (pos ++ [tmp.val] <+: pos ++ [dirLeaf.val]) := by
          intro hP
          rcases hP with ⟨r, hr⟩
          cases r with
          | nil => simp at hr; exact hTmpNeDir hr
          | cons _ _ => have hL := congrArg List.length hr; simp at hL
        have hDst2Dir : nodeAt st2.tree (pos ++ [dirLeaf.val]) = some (.dir 0o755) := by
          rw [hTree2, nodeAt_vfsTreeSet_outside st.tree pos tmp.val _ (pos ++ [dirLeaf.val]) hDirGet hNotPreTmpDir]
          exact hDirNd
        rw [vfsDirOps_renameAt_def, hLd2]; dsimp only; rw [hPar2]
        simp only [hWXF, Bool.false_eq_true, ↓reduceIte, hTmp2, hBeqDiff, hNotPref, hDst2Dir]
        rfl)
    dsimp only [Internal.subtreeOpsM, StateT.run]
    rw [show Internal.splitLastAux [dirLeaf] [] = some ([], dirLeaf) from rfl]
    dsimp only
    rw [walkDescendM_nil_eq, hStepDir]
    cases hResDir : Internal.atomicWriteAtAuxM vfsDirOps dh dirLeaf bytes 15 stNext with
    | mk rDir stDirFail =>
      rw [hResDir] at hDirClean
      rcases hDirClean with ⟨rfl, hNodesDir, _⟩
      refine ⟨⟨dirErr, rfl, rfl⟩, (hNodesDir _).trans hTmp1, (hNodesDir _).trans hDirNd, ?_⟩
      let failOps : RawDirOpsM (StateM VfsState) :=
        { vfsDirOps with
          renameAt := fun _ _ _ _ s => (.error { kind := .ioError, message := "injected rename failure" }, s) }
      let injErr : FsError := { kind := .ioError, message := "injected rename failure" }
      have hStepFail := atomicWrite_collision_step failOps rfl rfl dh pos maxLeaf bytes st pm (.file ByteArray.empty 0o600)
        hLd hParNd hW hX hTmp0
      have hFailClean := atomicWriteAtAuxM_rename_err_cleanup failOps rfl rfl rfl dh pos maxLeaf bytes 14 stNext pm injErr
        hLd hParNd hW hX hTmp1 (fun _ _ _ _ _ _ _ => rfl)
      rw [walkDescendM_nil_eq]
      erw [hStepFail]
      cases hResFail : Internal.atomicWriteAtAuxM failOps dh maxLeaf bytes 15 stNext with
      | mk rFail stFail =>
        rw [hResFail] at hFailClean
        rcases hFailClean with ⟨rfl, hNodesFail, hOpenFail⟩
        refine ⟨⟨injErr, rfl⟩, (hNodesFail _).trans hTmp0, (hNodesFail _).trans hTmp1, hOpenFail, ?_⟩
        intro stExh dhExh posExh hLdE _ hParE hCols
        rcases hParE with ⟨pmE, hParNdE, hWE, hXE⟩
        rcases atomicWriteAtAuxM_exhausted dhExh posExh maxLeaf bytes 16 stExh pmE (by decide)
            hLdE hParNdE hWE hXE (fun k hk => by rw [hCols k hk]; simp) with
          ⟨eExh, stExh', hExhEq, hKindE, hTreeE, hOpenE⟩
        rw [walkDescendM_nil_eq, hExhEq]
        exact ⟨⟨⟨eExh, rfl, hKindE⟩, nodes_eq_of_tree_eq' hTreeE, hOpenE⟩, trivial⟩

@[irreducible] private def exh16State : VfsState :=
  stateWithRootHandle
    (fun s => if (List.range 16).any (fun k => s == ".t." ++ toString k) then some (.file ByteArray.empty 0o600) else none)
    (["/"] ++ (List.range 16).map (fun k => "/.t." ++ toString k))

private theorem exh16State_lookup : lookupDir exh16State rootHandle = some [] := by
  unfold exh16State stateWithRootHandle rootHandle lookupDir; rfl

private theorem exh16State_openDirs : exh16State.openDirs = [(rootHandle.handleId, [])] := by
  unfold exh16State stateWithRootHandle; rfl

private theorem exh16State_nextDirId : exh16State.nextDirId = 2 := by
  unfold exh16State stateWithRootHandle; rfl

private theorem exh16State_root : nodeAt exh16State.tree [] = some (.dir 0o755) := by
  unfold exh16State stateWithRootHandle; rfl

private theorem exh16State_cols :
    ∀ k < 16, nodeAt exh16State.tree ([] ++ [".t." ++ toString (exh16State.nonce + k)]) = some (.file ByteArray.empty 0o600) := by
  intro k hk
  have hNon : exh16State.nonce = 0 := by unfold exh16State stateWithRootHandle; rfl
  rw [hNon, Nat.zero_add, List.nil_append]
  have hAny : (List.range 16).any (fun j => (".t." ++ toString k) == ".t." ++ toString j) = true :=
    List.any_eq_true.mpr ⟨k, List.mem_range.mpr hk, beq_self_eq_true _⟩
  unfold exh16State stateWithRootHandle nodeAt vfsTreeGet
  simp only [hAny, ↓reduceIte]
  rfl

/-- Witness check for `test_fs_subtree_atomicWriteBytes_maxSegmentAndTempCollisionAndCleanup`. -/
theorem reach_fs_subtree_atomicWriteBytes_maxSegmentAndTempCollisionAndCleanup :
    Core.CanReach (test_fs_subtree_atomicWriteBytes_maxSegmentAndTempCollisionAndCleanup Internal.subtreeOpsM) := by
  let maxLeaf : EntryName := ⟨str255, str255_valid⟩
  let st := stateWithRootHandle (fun
    | "d" => some (vfsEmptyDir 0o755)
    | ".t.0" => some (.file ByteArray.empty 0o600)
    | _ => none) ["/", "/d", "/.t.0"]
  have hInv : DirHandleInvariant st := fun _ _ hm => by
    simp [st, stateWithRootHandle] at hm; rcases hm with ⟨rfl, rfl⟩; decide
  have hPar : ∃ pm, nodeAt st.tree [] = some (.dir pm) ∧ (pm / 128) % 2 = 1 ∧ (pm / 64) % 2 = 1 :=
    ⟨0o755, rfl, by decide, by decide⟩
  have hTmp0 : nodeAt st.tree ([] ++ [".t." ++ toString st.nonce]) = some (.file ByteArray.empty 0o600) := by
    have h0 : ".t." ++ toString st.nonce = ".t.0" := by decide
    rw [h0]; rfl
  have hTmp1 : nodeAt st.tree ([] ++ [".t." ++ toString (st.nonce + 1)]) = none := by
    have h1 : ".t." ++ toString (st.nonce + 1) = ".t.1" := by decide
    rw [h1]; rfl
  have hNe : maxLeaf.val ≠ ".t." ++ toString st.nonce ∧ maxLeaf.val ≠ ".t." ++ toString (st.nonce + 1) := by
    refine ⟨fun h => ?_, fun h => ?_⟩
    · have hLen := congrArg String.utf8ByteSize h
      have hL1 : maxLeaf.val.utf8ByteSize = 255 := str255_utf8ByteSize
      have hL2 : (".t." ++ toString st.nonce).utf8ByteSize = 4 := by decide
      omega
    · have hLen := congrArg String.utf8ByteSize h
      have hL1 : maxLeaf.val.utf8ByteSize = 255 := str255_utf8ByteSize
      have hL2 : (".t." ++ toString (st.nonce + 1)).utf8ByteSize = 4 := by decide
      omega
  have hNotDir : (match nodeAt st.tree ([] ++ [maxLeaf.val]) with | some (.dir _) => False | _ => True) := by
    have hNd : maxLeaf.val ≠ "d" := fun h => by
      have hL := congrArg String.utf8ByteSize h
      have h1 : maxLeaf.val.utf8ByteSize = 255 := str255_utf8ByteSize
      have h2 : ("d" : String).utf8ByteSize = 1 := by decide
      omega
    have hNt : maxLeaf.val ≠ ".t.0" := fun h => hNe.1 (h.trans (by decide))
    simp only [st, stateWithRootHandle, List.nil_append, nodeAt, vfsTreeGet]
    split <;> first | contradiction | trivial
  have hAll1 := proof_fs_subtree_atomicWriteBytes_maxSegmentAndTempCollisionAndCleanup st rootHandle [] ByteArray.empty maxLeaf
    rfl hInv str255_utf8ByteSize hPar hTmp0 hTmp1 hNe hNotDir
  rcases hAll1 with ⟨a1, a2, a3, hDirFn⟩
  have hDirNe : EntryName.lit "d" ≠ maxLeaf := fun h => by
    have hVal : "d" = str255 := congrArg (·.val) h
    have hL := congrArg String.utf8ByteSize hVal
    have hL1 : ("d" : String).utf8ByteSize = 1 := by decide
    have hL2 : str255.utf8ByteSize = 255 := str255_utf8ByteSize
    omega
  have hDirNd : nodeAt st.tree ([] ++ [(EntryName.lit "d").val]) = some (.dir 0o755) := rfl
  have hAll2 := hDirFn (EntryName.lit "d") hDirNe hDirNd
  rcases hAll2 with ⟨b1, b2, b3, b4, b5, b6, b7, hExhFn⟩
  have hInvE : DirHandleInvariant exh16State := fun _ _ hm => by
    rw [exh16State_openDirs] at hm
    simp only [List.mem_singleton, Prod.mk.injEq] at hm
    rcases hm with ⟨rfl, rfl⟩
    refine ⟨by decide, ?_⟩
    rw [exh16State_nextDirId]; decide
  have hParE : ∃ pm, nodeAt exh16State.tree [] = some (.dir pm) ∧ (pm / 128) % 2 = 1 ∧ (pm / 64) % 2 = 1 :=
    ⟨0o755, exh16State_root, by decide, by decide⟩
  have hAll3 := hExhFn exh16State rootHandle [] exh16State_lookup hInvE hParE exh16State_cols
  refine ⟨st, rootHandle, [], ByteArray.empty, maxLeaf,
    rfl, hInv, str255_utf8ByteSize, hPar, hTmp0, hTmp1, hNe, hNotDir,
    a1, a2, a3, EntryName.lit "d", hDirNe, hDirNd, b1, b2, b3, b4, b5, b6, b7,
    exh16State, rootHandle, [], exh16State_lookup, hInvE, hParE, exh16State_cols, ?_⟩
  cases hRun : StateT.run ((Internal.subtreeOpsM vfsDirOps rootHandle).atomicWriteBytes { segments := [maxLeaf] } ByteArray.empty) exh16State with
  | mk rExh stExh' =>
    rw [hRun] at hAll3
    exact hAll3


/-- `Internal.subtreeOpsM` satisfies `test_fs_subtree_mkdir_parentsAndExistOkRules`. -/
theorem proof_fs_subtree_mkdir_parentsAndExistOkRules :
    Core.AllPass (test_fs_subtree_mkdir_parentsAndExistOkRules Internal.subtreeOpsM) := by
  intro st dh pos pDir cDir existingFile hLd hInv hPar hPMiss hExist
  rcases hPar with ⟨pm, hParNd, hR, hW, hX⟩
  rcases hExist with ⟨bs, fm, hExistNd⟩
  have hXF : (pm / 64 % 2 == 0) = false := by rw [hX]; decide
  have hWXF : (pm / 128 % 2 == 0 || pm / 64 % 2 == 0) = false := by rw [hW, hX]; decide
  dsimp only [Internal.subtreeOpsM, StateT.run, Bind.bind, StateT.bind]
  refine ⟨?_, ?_, trivial⟩
  · change
      (Internal.mkdirWalkM vfsDirOps true dh [pDir] (fun parDh => do
        match ← vfsDirOps.createDirAt parDh cDir with
        | .ok () => pure (.ok ())
        | .error e =>
          if false && (e.kind == .alreadyExists || e.kind == .permissionDenied) then
            match ← vfsDirOps.lstatAt parDh cDir with
            | .error _ => pure (.error e)
            | .ok info =>
              if info.kind == .dir then pure (.ok ())
              else if e.kind == .alreadyExists then pure (.error e)
              else pure (.error { kind := .alreadyExists, path := some cDir.val, message := s!"already exists: {cDir.val}" })
          else pure (.error e)) st).fst = .ok () ∧
      nodeAt (Internal.mkdirWalkM vfsDirOps true dh [pDir] (fun parDh => do
        match ← vfsDirOps.createDirAt parDh cDir with
        | .ok () => pure (.ok ())
        | .error e =>
          if false && (e.kind == .alreadyExists || e.kind == .permissionDenied) then
            match ← vfsDirOps.lstatAt parDh cDir with
            | .error _ => pure (.error e)
            | .ok info =>
              if info.kind == .dir then pure (.ok ())
              else if e.kind == .alreadyExists then pure (.error e)
              else pure (.error { kind := .alreadyExists, path := some cDir.val, message := s!"already exists: {cDir.val}" })
          else pure (.error e)) st).snd.tree (pos ++ [pDir.val]) = some (.dir 0o755) ∧
      nodeAt (Internal.mkdirWalkM vfsDirOps true dh [pDir] (fun parDh => do
        match ← vfsDirOps.createDirAt parDh cDir with
        | .ok () => pure (.ok ())
        | .error e =>
          if false && (e.kind == .alreadyExists || e.kind == .permissionDenied) then
            match ← vfsDirOps.lstatAt parDh cDir with
            | .error _ => pure (.error e)
            | .ok info =>
              if info.kind == .dir then pure (.ok ())
              else if e.kind == .alreadyExists then pure (.error e)
              else pure (.error { kind := .alreadyExists, path := some cDir.val, message := s!"already exists: {cDir.val}" })
          else pure (.error e)) st).snd.tree (pos ++ [pDir.val, cDir.val]) = some (.dir 0o755)
    rw [mkdirWalkM_cons]
    simp only [↓reduceIte, Bind.bind, StateT.bind]
    have hOpMiss : vfsDirOps.openDirAt dh pDir st =
        (.error { kind := .notFound, path := some pDir.val, message := s!"no such file or directory: {pDir.val}" }, st) := by
      rcases (⟨_, rfl⟩ : ∃ d : Nat, vfsDirOps.openDirAt dh pDir st = openDirAtTpl' st dh pDir d) with ⟨d, hEq⟩
      rw [hEq]; unfold openDirAtTpl'; rw [hLd]; dsimp only; rw [hParNd]
      simp only [hXF, Bool.false_eq_true, ↓reduceIte, hPMiss]
    let st1 : VfsState :=
      { st with
        tree := vfsTreeSet st.tree (pos ++ [pDir.val]) (some (vfsEmptyDir 0o755)),
        keys := pathOfSegs (pos ++ [pDir.val]) :: st.keys }
    have hCrPar : vfsDirOps.createDirAt dh pDir st = (.ok (), st1) := by
      rw [vfsDirOps_createDirAt_def, hLd]; dsimp only; rw [hParNd]
      simp only [hWXF, Bool.false_eq_true, ↓reduceIte, hPMiss]
      rfl
    have hDirGet : ∃ dm ch, vfsTreeGet st.tree pos = some (.dir dm ch) :=
      let ⟨ch, hG⟩ := vfsTreeGet_dir_of_nodeAt hParNd; ⟨pm, ch, hG⟩
    have hNotSelf1 : ¬ (pos ++ [pDir.val] <+: pos) := by
      intro hP; have hL := List.IsPrefix.length_le hP; simp at hL; omega
    have hPar1 : nodeAt st1.tree pos = some (.dir pm) := by
      change nodeAt (vfsTreeSet st.tree (pos ++ [pDir.val]) (some (vfsEmptyDir 0o755))) pos = some (.dir pm)
      rw [nodeAt_vfsTreeSet_outside st.tree pos pDir.val _ pos hDirGet hNotSelf1, hParNd]
    have hP1 : nodeAt st1.tree (pos ++ [pDir.val]) = some (.dir 0o755) := by
      unfold nodeAt
      rw [show st1.tree = vfsTreeSet st.tree (pos ++ [pDir.val]) (some (vfsEmptyDir 0o755)) from rfl,
        vfsTreeGet_vfsTreeSet_eq st.tree pos pDir.val (some (vfsEmptyDir 0o755)) hDirGet]
      rfl
    have hLd1 : lookupDir st1 dh = some pos := hLd
    rcases vfsDirOps_openDirAt_dir_ok st1 dh pDir pos pm 0o755 hLd1 hPar1 hX hP1 (by decide) with
      ⟨nextDh, st2, hOp2⟩
    rcases vfsDirOps_openDirAt_ok dh pDir st1 nextDh st2 hOp2 with
      ⟨hNextPos, _, hNextGt, pos', _, _, hLd', _, _, _, _, _, hSt2⟩
    rcases Option.some.inj (hLd1.symm.trans hLd') with rfl
    have hLd2 : lookupDir st2 nextDh = some (pos ++ [pDir.val]) := by
      rw [hSt2]; exact lookupDir_cons_self st1 nextDh.handleId (pos ++ [pDir.val]) nextDh.rootPath hNextPos
    have hDir2 : nodeAt st2.tree (pos ++ [pDir.val]) = some (.dir 0o755) := by rw [hSt2]; exact hP1
    have hChildMiss2 : nodeAt st2.tree ((pos ++ [pDir.val]) ++ [cDir.val]) = none := by
      rw [hSt2]
      change nodeAt (vfsTreeSet st.tree (pos ++ [pDir.val]) (some (vfsEmptyDir 0o755))) ((pos ++ [pDir.val]) ++ [cDir.val]) = none
      have hG1 : vfsTreeGet st1.tree (pos ++ [pDir.val]) = some (vfsEmptyDir 0o755) := by
        change vfsTreeGet (vfsTreeSet st.tree (pos ++ [pDir.val]) (some (vfsEmptyDir 0o755))) (pos ++ [pDir.val]) =
          some (vfsEmptyDir 0o755)
        exact vfsTreeGet_vfsTreeSet_eq st.tree pos pDir.val (some (vfsEmptyDir 0o755)) hDirGet
      rw [nodeAt_sub_of_vfsTreeGet hG1]
      rfl
    let st3 : VfsState :=
      { st2 with
        tree := vfsTreeSet st2.tree ((pos ++ [pDir.val]) ++ [cDir.val]) (some (vfsEmptyDir 0o755)),
        keys := pathOfSegs ((pos ++ [pDir.val]) ++ [cDir.val]) :: st2.keys }
    have hCrChild : vfsDirOps.createDirAt nextDh cDir st2 = (.ok (), st3) := by
      rw [vfsDirOps_createDirAt_def, hLd2]; dsimp only; rw [hDir2]
      simp only [show (0o755 / 128 % 2 == 0 || 0o755 / 64 % 2 == 0) = false from by decide,
        Bool.false_eq_true, ↓reduceIte, hChildMiss2]
      rfl
    have hClose3 : vfsDirOps.closeDir nextDh st3 = (.ok (), { st3 with openDirs := st.openDirs }) :=
      vfsDirOps_closeDir_fresh nextDh st3 (pos ++ [pDir.val]) hNextPos st.openDirs
        (by change st2.openDirs = _; rw [hSt2]) hNextGt
    rw [hOpMiss]
    simp only [show (FsErrorKind.notFound == FsErrorKind.notFound) = true from rfl, ↓reduceIte,
      Bind.bind, StateT.bind, hCrPar, hOp2, mkdirWalkM_nil, Bool.false_eq_true, bracketCloseDirM_run, hCrChild]
    dsimp only [Pure.pure, StateT.pure]
    rw [hClose3]
    have hDirGet2 : ∃ dm ch, vfsTreeGet st2.tree (pos ++ [pDir.val]) = some (.dir dm ch) :=
      let ⟨ch, hG⟩ := vfsTreeGet_dir_of_nodeAt hDir2; ⟨0o755, ch, hG⟩
    have hNotSelf2 : ¬ ((pos ++ [pDir.val]) ++ [cDir.val] <+: pos ++ [pDir.val]) := by
      intro hP; have hL := List.IsPrefix.length_le hP; simp only [List.length_append, List.length_singleton] at hL; omega
    refine ⟨rfl, ?_, ?_⟩
    · change nodeAt (vfsTreeSet st2.tree ((pos ++ [pDir.val]) ++ [cDir.val]) (some (vfsEmptyDir 0o755)))
        (pos ++ [pDir.val]) = some (.dir 0o755)
      rw [nodeAt_vfsTreeSet_outside st2.tree (pos ++ [pDir.val]) cDir.val _ (pos ++ [pDir.val]) hDirGet2 hNotSelf2, hDir2]
    · change nodeAt (vfsTreeSet st2.tree ((pos ++ [pDir.val]) ++ [cDir.val]) (some (vfsEmptyDir 0o755)))
        (pos ++ [pDir.val, cDir.val]) = some (.dir 0o755)
      unfold nodeAt
      rw [show pos ++ [pDir.val, cDir.val] = (pos ++ [pDir.val]) ++ [cDir.val] from by simp,
        vfsTreeGet_vfsTreeSet_eq st2.tree (pos ++ [pDir.val]) cDir.val (some (vfsEmptyDir 0o755)) hDirGet2]
      rfl
  · change
      (∃ e, (Internal.walkDescendM vfsDirOps dh [] (fun parDh => do
        match ← vfsDirOps.createDirAt parDh existingFile with
        | .ok () => pure (.ok ())
        | .error e =>
          if true && (e.kind == .alreadyExists || e.kind == .permissionDenied) then
            match ← vfsDirOps.lstatAt parDh existingFile with
            | .error _ => pure (.error e)
            | .ok info =>
              if info.kind == .dir then pure (.ok ())
              else if e.kind == .alreadyExists then pure (.error e)
              else pure (.error { kind := .alreadyExists, path := some existingFile.val, message := s!"already exists: {existingFile.val}" })
          else pure (.error e)) st).fst = .error e ∧ e.kind = .alreadyExists) ∧
      (Internal.walkDescendM vfsDirOps dh [] (fun parDh => do
        match ← vfsDirOps.createDirAt parDh existingFile with
        | .ok () => pure (.ok ())
        | .error e =>
          if true && (e.kind == .alreadyExists || e.kind == .permissionDenied) then
            match ← vfsDirOps.lstatAt parDh existingFile with
            | .error _ => pure (.error e)
            | .ok info =>
              if info.kind == .dir then pure (.ok ())
              else if e.kind == .alreadyExists then pure (.error e)
              else pure (.error { kind := .alreadyExists, path := some existingFile.val, message := s!"already exists: {existingFile.val}" })
          else pure (.error e)) st).snd.nodes = st.nodes
    rw [walkDescendM_nil_eq]
    dsimp only [Bind.bind, StateT.bind]
    have hCrEx : vfsDirOps.createDirAt dh existingFile st =
        (.error { kind := .alreadyExists, path := some existingFile.val, message := s!"already exists: {existingFile.val}" }, st) := by
      rw [vfsDirOps_createDirAt_def, hLd]; dsimp only; rw [hParNd]
      simp only [hWXF, Bool.false_eq_true, ↓reduceIte, hExistNd]
    have hLstEx : vfsDirOps.lstatAt dh existingFile st = (.ok (vfsToStat (.file bs fm)), st) := by
      rw [vfsDirOps_lstatAt_def, hLd]; dsimp only; rw [hParNd]
      simp only [hXF, Bool.false_eq_true, ↓reduceIte, hExistNd]
    rw [hCrEx]
    simp only [Bind.bind, StateT.bind, Bool.false_eq_true, ↓reduceIte, Bool.true_and,
      show (FsErrorKind.alreadyExists == FsErrorKind.alreadyExists) = true from rfl,
      Bool.true_or, hLstEx, vfsToStat, show (EntryKind.file == EntryKind.dir) = false from rfl,
      Pure.pure, StateT.pure]
    exact ⟨⟨_, rfl, rfl⟩, trivial⟩

/-- Witness check for `test_fs_subtree_mkdir_parentsAndExistOkRules`. -/
theorem reach_fs_subtree_mkdir_parentsAndExistOkRules :
    Core.CanReach (test_fs_subtree_mkdir_parentsAndExistOkRules Internal.subtreeOpsM) := by
  let st := stateWithRootHandle (fun s => if s == "f" then some (.file ByteArray.empty 0o644) else none) ["/", "/f"]
  have hInv : DirHandleInvariant st := fun _ _ hm => by
    simp [st, stateWithRootHandle] at hm; rcases hm with ⟨rfl, rfl⟩; decide
  have hPar : ∃ pm, nodeAt st.tree [] = some (.dir pm) ∧ (pm / 256) % 2 = 1 ∧ (pm / 128) % 2 = 1 ∧ (pm / 64) % 2 = 1 :=
    ⟨0o755, rfl, by decide, by decide, by decide⟩
  have hAll := proof_fs_subtree_mkdir_parentsAndExistOkRules st rootHandle [] (EntryName.lit "p") (EntryName.lit "c")
    (EntryName.lit "f") rfl hInv hPar rfl ⟨ByteArray.empty, 0o644, rfl⟩
  exact ⟨st, rootHandle, [], EntryName.lit "p", EntryName.lit "c", EntryName.lit "f",
    rfl, hInv, hPar, rfl, ⟨ByteArray.empty, 0o644, rfl⟩, hAll⟩

/-- `Internal.subtreeOpsM` satisfies `test_fs_subtree_mkdir_existOkPreservesExistingDir`. -/
theorem proof_fs_subtree_mkdir_existOkPreservesExistingDir :
    Core.AllPass (test_fs_subtree_mkdir_existOkPreservesExistingDir Internal.subtreeOpsM) := by
  intro st dh pos child pm cm b hLd hInv hPar hChild
  rcases hPar with ⟨hParNd, hX⟩
  have hXF : (pm / 64 % 2 == 0) = false := by rw [hX]; decide
  have hStep : (do
      match ← vfsDirOps.createDirAt dh child with
      | Except.ok () => pure (Except.ok ())
      | Except.error e =>
        if true && (e.kind == FsErrorKind.alreadyExists || e.kind == FsErrorKind.permissionDenied) then
          match ← vfsDirOps.lstatAt dh child with
          | Except.error _ => pure (Except.error e)
          | Except.ok info =>
            if info.kind == EntryKind.dir then pure (Except.ok ())
            else if e.kind == FsErrorKind.alreadyExists then pure (Except.error e)
            else pure (Except.error { kind := FsErrorKind.alreadyExists, path := some child.val, message := s!"already exists: {child.val}" })
        else pure (Except.error e)) st = (.ok (), st) := by
    dsimp only [Bind.bind, StateT.bind]
    have hLst : vfsDirOps.lstatAt dh child st = (.ok (vfsToStat (.dir cm)), st) := by
      rw [vfsDirOps_lstatAt_def, hLd]; dsimp only; rw [hParNd]
      simp only [hXF, Bool.false_eq_true, ↓reduceIte, hChild]
    rw [vfsDirOps_createDirAt_def, hLd]
    dsimp only
    rw [hParNd]
    by_cases hW0 : ((pm / 128) % 2 == 0 || (pm / 64) % 2 == 0) = true
    · simp only [hW0, ↓reduceIte, Bool.true_and,
        show (FsErrorKind.permissionDenied == FsErrorKind.alreadyExists ||
          FsErrorKind.permissionDenied == FsErrorKind.permissionDenied) = true from rfl]
      dsimp only [Bind.bind, StateT.bind]
      rw [hLst]
      simp only [vfsToStat, show (EntryKind.dir == EntryKind.dir) = true from rfl, ↓reduceIte,
        Pure.pure, StateT.pure]
    · have hW0F : ((pm / 128) % 2 == 0 || (pm / 64) % 2 == 0) = false := Bool.eq_false_iff.mpr hW0
      simp only [hW0F, Bool.false_eq_true, ↓reduceIte, hChild, Bool.true_and,
        show (FsErrorKind.alreadyExists == FsErrorKind.alreadyExists ||
          FsErrorKind.alreadyExists == FsErrorKind.permissionDenied) = true from rfl]
      dsimp only [Bind.bind, StateT.bind]
      rw [hLst]
      simp only [vfsToStat, show (EntryKind.dir == EntryKind.dir) = true from rfl, ↓reduceIte,
        Pure.pure, StateT.pure]
  have hRun : ((Internal.subtreeOpsM vfsDirOps dh).mkdir { segments := [child] } b true).run st = (.ok (), st) := by
    dsimp only [Internal.subtreeOpsM, StateT.run, Bind.bind, StateT.bind]
    rw [show Internal.splitLastAux [child] [] = some ([], child) from rfl]
    dsimp only
    cases b
    · simp only [Bool.false_eq_true, ↓reduceIte]
      rw [walkDescendM_nil_eq]
      exact hStep
    · simp only [↓reduceIte, mkdirWalkM_nil]
      exact hStep
  change (match StateT.run ((Internal.subtreeOpsM vfsDirOps dh).mkdir { segments := [child] } b true) st with
    | (rMkExist, stMkExist) =>
      (rMkExist = Except.ok () ∧ nodeAt stMkExist.tree (pos ++ [child.val]) = some (VfsNode.dir cm)) ∧ True)
  rw [hRun]
  exact ⟨⟨rfl, hChild⟩, trivial⟩

/-- Witness check for `test_fs_subtree_mkdir_existOkPreservesExistingDir`. -/
theorem reach_fs_subtree_mkdir_existOkPreservesExistingDir :
    Core.CanReach (test_fs_subtree_mkdir_existOkPreservesExistingDir Internal.subtreeOpsM) := by
  let st := stateWithRootHandle (fun s => if s == "d" then some (vfsEmptyDir 0o700) else none) ["/", "/d"]
  have hInv : DirHandleInvariant st := fun _ _ hm => by
    simp [st, stateWithRootHandle] at hm; rcases hm with ⟨rfl, rfl⟩; decide
  have hAll := proof_fs_subtree_mkdir_existOkPreservesExistingDir st rootHandle [] (EntryName.lit "d")
    0o755 0o700 false rfl hInv ⟨rfl, by decide⟩ rfl
  exact ⟨st, rootHandle, [], EntryName.lit "d", 0o755, 0o700, false, rfl, hInv, ⟨rfl, by decide⟩, rfl, hAll⟩

/-- `Internal.subtreeOpsM` satisfies `test_fs_subtree_unlink_missingOkAndKindRules`. -/
theorem proof_fs_subtree_unlink_missingOkAndKindRules :
    Core.AllPass (test_fs_subtree_unlink_missingOkAndKindRules Internal.subtreeOpsM) := by
  intro st dh pos missingLeaf fileLeaf dirLeaf hLd _ hPar hMiss hFile hDir
  rcases hPar with ⟨pm, hParNd, hW, hX⟩
  rcases hFile with ⟨bs, fm, hFileNd⟩
  rcases hDir with ⟨dm, hDirNd⟩
  have hWXF : (pm / 128 % 2 == 0 || pm / 64 % 2 == 0) = false := by rw [hW, hX]; decide
  have runUnlinkNil : ∀ (leaf : EntryName) (b : Bool) (r : Except FsError Unit) (st' : VfsState),
      vfsDirOps.unlinkAt dh leaf false st = (r, st') →
      ((Internal.subtreeOpsM vfsDirOps dh).unlink { segments := [leaf] } b).run st =
        (match r with
        | .ok () => (.ok (), st')
        | .error e => if (e.kind == .notFound && b) = true then (.ok (), st') else (.error e, st')) := by
    intro leaf b r st' hU
    change ((do
      match ← Internal.walkDescendM vfsDirOps dh [] fun parDh => vfsDirOps.unlinkAt parDh leaf false with
      | .ok () => pure (.ok ())
      | .error e => if e.kind == .notFound && b then pure (.ok ()) else pure (.error e)) : StateM VfsState (Except FsError Unit)) st = _
    rw [walkDescendM_nil_eq, stateM_bind_step hU]
    cases r with
    | ok _ => rfl
    | error e => dsimp only [Pure.pure, StateT.pure]; split <;> rfl
  have hUMiss : vfsDirOps.unlinkAt dh missingLeaf false st =
      (.error { kind := .notFound, path := some missingLeaf.val, message := s!"no such file or directory: {missingLeaf.val}" }, st) := by
    rw [vfsDirOps_unlinkAt_def, hLd]; dsimp only; rw [hParNd]
    simp only [hWXF, Bool.false_eq_true, ↓reduceIte, hMiss]
  have hUFile : vfsDirOps.unlinkAt dh fileLeaf false st =
      (.ok (), { st with tree := vfsTreeSet st.tree (pos ++ [fileLeaf.val]) none }) := by
    rw [vfsDirOps_unlinkAt_def, hLd]; dsimp only; rw [hParNd]
    simp only [hWXF, Bool.false_eq_true, ↓reduceIte, hFileNd]
  have hUDir : vfsDirOps.unlinkAt dh dirLeaf false st =
      (.error { kind := .isADirectory, path := some dirLeaf.val, message := s!"is a directory: {dirLeaf.val}" }, st) := by
    rw [vfsDirOps_unlinkAt_def, hLd]; dsimp only; rw [hParNd]
    simp only [hWXF, Bool.false_eq_true, ↓reduceIte, hDirNd, Bool.not_false]
  have hRunMissT := runUnlinkNil missingLeaf true _ _ hUMiss
  have hRunMissF := runUnlinkNil missingLeaf false _ _ hUMiss
  have hRunFile := runUnlinkNil fileLeaf false _ _ hUFile
  have hRunDir := runUnlinkNil dirLeaf false _ _ hUDir
  simp only [show (FsErrorKind.notFound == FsErrorKind.notFound) = true from rfl,
    Bool.and_true, Bool.and_false, Bool.false_eq_true, ↓reduceIte] at hRunMissT hRunMissF
  simp only [show (FsErrorKind.isADirectory == FsErrorKind.notFound) = false from rfl,
    Bool.false_and, Bool.false_eq_true, ↓reduceIte] at hRunDir
  dsimp only at hRunFile ⊢
  rw [hRunMissT, hRunMissF, hRunFile, hRunDir]
  refine ⟨⟨rfl, rfl⟩, ⟨⟨_, rfl, rfl⟩, rfl⟩, ?_, ⟨⟨_, rfl, rfl⟩, rfl⟩, trivial⟩
  have hDirGet : ∃ dm ch, vfsTreeGet st.tree pos = some (.dir dm ch) :=
    let ⟨ch, hG⟩ := vfsTreeGet_dir_of_nodeAt hParNd; ⟨pm, ch, hG⟩
  refine ⟨rfl, ?_, ?_⟩
  · unfold nodeAt; rw [vfsTreeGet_vfsTreeSet_eq st.tree pos fileLeaf.val none hDirGet]; rfl
  · intro p hNot
    change vfsTreeNodes (vfsTreeSet st.tree (pos ++ [fileLeaf.val]) none) p = vfsTreeNodes st.tree p
    unfold vfsTreeNodes
    split
    · exact nodeAt_vfsTreeSet_outside st.tree pos fileLeaf.val none (vfsSplitSegs p) hDirGet hNot
    · rfl

/-- Witness check for `test_fs_subtree_unlink_missingOkAndKindRules`. -/
theorem reach_fs_subtree_unlink_missingOkAndKindRules :
    Core.CanReach (test_fs_subtree_unlink_missingOkAndKindRules Internal.subtreeOpsM) := by
  let st := stateWithRootHandle (fun
    | "f" => some (.file ByteArray.empty 0o644)
    | "d" => some (vfsEmptyDir 0o755)
    | _ => none) ["/", "/f", "/d"]
  have hInv : DirHandleInvariant st := fun _ _ hm => by
    simp [st, stateWithRootHandle] at hm; rcases hm with ⟨rfl, rfl⟩; decide
  have hAll := proof_fs_subtree_unlink_missingOkAndKindRules st rootHandle [] (EntryName.lit "m")
    (EntryName.lit "f") (EntryName.lit "d") rfl hInv ⟨0o755, rfl, by decide, by decide⟩ rfl
    ⟨ByteArray.empty, 0o644, rfl⟩ ⟨0o755, rfl⟩
  exact ⟨st, rootHandle, [], EntryName.lit "m", EntryName.lit "f", EntryName.lit "d",
    rfl, hInv, ⟨0o755, rfl, by decide, by decide⟩, rfl, ⟨ByteArray.empty, 0o644, rfl⟩, ⟨0o755, rfl⟩, hAll⟩

/-- `Internal.subtreeOpsM` satisfies `test_fs_subtree_rmdir_emptyAndErrors`. -/
theorem proof_fs_subtree_rmdir_emptyAndErrors :
    Core.AllPass (test_fs_subtree_rmdir_emptyAndErrors Internal.subtreeOpsM) := by
  intro st dh pos emptyDir nonEmptyDir child missingLeaf fileLeaf hLd _ hKeys hValid hPar hEmpty hNonE hChild hMiss hFile
  rcases hPar with ⟨pm, hParNd, hW, hX⟩
  rcases hEmpty with ⟨em, hEmptyNd, hNoChild⟩
  rcases hNonE with ⟨nm, hNonENd⟩
  rcases hFile with ⟨bs, fm, hFileNd⟩
  have hWXF : (pm / 128 % 2 == 0 || pm / 64 % 2 == 0) = false := by rw [hW, hX]; decide
  have hEmptyChild : mDirHasLiveChild st (pos ++ [emptyDir.val]) = false := by
    apply mDirHasLiveChild_false_of_treeEmpty st (pos ++ [emptyDir.val])
    · intro s hs
      rcases List.mem_append.mp hs with hp | hc
      · exact hValid s hp
      · simp only [List.mem_singleton] at hc; subst hc; exact emptyDir.valid
    · intro rest hRest
      cases rest with
      | nil => exact absurd rfl hRest
      | cons r rs =>
        have hNoneR := hNoChild r
        cases rs with
        | nil => simpa [List.append_assoc] using hNoneR
        | cons r2 rs2 =>
          unfold nodeAt at hNoneR ⊢
          cases hG : vfsTreeGet st.tree (pos ++ [emptyDir.val, r]) with
          | none =>
            rw [show pos ++ [emptyDir.val] ++ r :: r2 :: rs2 = (pos ++ [emptyDir.val, r]) ++ (r2 :: rs2) from by simp,
              vfsTreeGet_append_none _ _ _ hG]
            rfl
          | some _ => simp [hG] at hNoneR
  have hNonEmptyChild : mDirHasLiveChild st (pos ++ [nonEmptyDir.val]) = true := by
    have hPosNEValid : ∀ s ∈ pos ++ [nonEmptyDir.val], validSeg s = true := by
      intro s hs
      rcases List.mem_append.mp hs with hp | hn
      · exact hValid s hp
      · simp only [List.mem_singleton] at hn; subst hn; exact nonEmptyDir.valid
    have hKeyC : pathOfSegs ((pos ++ [nonEmptyDir.val]) ++ [child.val]) ∈ st.keys := by
      apply hKeys
      simpa [List.append_assoc] using hChild
    have hLiveC : (nodeAt st.tree ((pos ++ [nonEmptyDir.val]) ++ [child.val])).isSome = true := by
      cases hN : nodeAt st.tree ((pos ++ [nonEmptyDir.val]) ++ [child.val]) with
      | none => exact absurd (by simpa [List.append_assoc] using hN) hChild
      | some _ => rfl
    exact mDirHasLiveChild_true_of_node st (pos ++ [nonEmptyDir.val]) child.val hPosNEValid child.valid hKeyC hLiveC
  dsimp only [Internal.subtreeOpsM, StateT.run, Bind.bind, StateT.bind]
  rw [show Internal.splitLastAux [emptyDir] [] = some ([], emptyDir) from rfl,
    show Internal.splitLastAux [nonEmptyDir] [] = some ([], nonEmptyDir) from rfl,
    show Internal.splitLastAux [missingLeaf] [] = some ([], missingLeaf) from rfl,
    show Internal.splitLastAux [fileLeaf] [] = some ([], fileLeaf) from rfl]
  dsimp only [Bind.bind, StateT.bind, Pure.pure, StateT.pure]
  rw [walkDescendM_nil_eq, walkDescendM_nil_eq, walkDescendM_nil_eq, walkDescendM_nil_eq]
  refine ⟨?_, ?_, ?_, ?_, trivial⟩
  · have hU : vfsDirOps.unlinkAt dh emptyDir true st =
        (.ok (), { st with tree := vfsTreeSet st.tree (pos ++ [emptyDir.val]) none }) := by
      rw [vfsDirOps_unlinkAt_def, hLd]; dsimp only; rw [hParNd]
      simp only [hWXF, Bool.false_eq_true, ↓reduceIte, hEmptyNd, Bool.not_true, hEmptyChild]
    simp only [hU]
    have hDirGet : ∃ dm ch, vfsTreeGet st.tree pos = some (.dir dm ch) :=
      let ⟨ch, hG⟩ := vfsTreeGet_dir_of_nodeAt hParNd; ⟨pm, ch, hG⟩
    refine ⟨trivial, ?_⟩
    unfold nodeAt; rw [vfsTreeGet_vfsTreeSet_eq st.tree pos emptyDir.val none hDirGet]; rfl
  · have hU : vfsDirOps.unlinkAt dh nonEmptyDir true st =
        (.error { kind := .notEmpty, path := some nonEmptyDir.val, message := s!"directory not empty: {nonEmptyDir.val}" }, st) := by
      rw [vfsDirOps_unlinkAt_def, hLd]; dsimp only; rw [hParNd]
      simp only [hWXF, Bool.false_eq_true, ↓reduceIte, hNonENd, Bool.not_true, hNonEmptyChild, ↓reduceIte]
    simp only [hU]
    exact ⟨⟨_, rfl, rfl⟩, trivial⟩
  · have hU : vfsDirOps.unlinkAt dh missingLeaf true st =
        (.error { kind := .notFound, path := some missingLeaf.val, message := s!"no such file or directory: {missingLeaf.val}" }, st) := by
      rw [vfsDirOps_unlinkAt_def, hLd]; dsimp only; rw [hParNd]
      simp only [hWXF, Bool.false_eq_true, ↓reduceIte, hMiss]
    simp only [hU]
    exact ⟨⟨_, rfl, rfl⟩, trivial⟩
  · have hU : vfsDirOps.unlinkAt dh fileLeaf true st =
        (.error { kind := .notADirectory, path := some fileLeaf.val, message := s!"not a directory: {fileLeaf.val}" }, st) := by
      rw [vfsDirOps_unlinkAt_def, hLd]; dsimp only; rw [hParNd]
      simp only [hWXF, Bool.false_eq_true, ↓reduceIte, hFileNd, ↓reduceIte]
    simp only [hU]
    exact ⟨⟨_, rfl, rfl⟩, trivial⟩

/-- Witness check for `test_fs_subtree_rmdir_emptyAndErrors`. -/
theorem reach_fs_subtree_rmdir_emptyAndErrors :
    Core.CanReach (test_fs_subtree_rmdir_emptyAndErrors Internal.subtreeOpsM) := by
  let st := stateWithRootHandle (fun
    | "e" => some (vfsEmptyDir 0o755)
    | "ne" => some (.dir 0o755 (fun s => if s == "c" then some (.file ByteArray.empty 0o644) else none))
    | "f" => some (.file ByteArray.empty 0o644)
    | _ => none) ["/", "/e", "/ne", "/ne/c", "/f"]
  have hInv : DirHandleInvariant st := fun _ _ hm => by
    simp [st, stateWithRootHandle] at hm; rcases hm with ⟨rfl, rfl⟩; decide
  have hKeys : VfsKeysComplete st := by
    intro segs hne
    rcases segs with _ | ⟨a, r1⟩
    · simp [pathOfSegs, st, stateWithRootHandle]
    · by_cases hae : a = "e"
      · subst hae; rcases r1 with _ | ⟨b, _⟩
        · simp [pathOfSegs, st, stateWithRootHandle]
        · exfalso; apply hne; simp [st, stateWithRootHandle, nodeAt, vfsTreeGet, vfsEmptyDir]
      · by_cases han : a = "ne"
        · subst han; rcases r1 with _ | ⟨b, r2⟩
          · simp [pathOfSegs, st, stateWithRootHandle]
          · by_cases hbc : b = "c"
            · subst hbc; rcases r2 with _ | ⟨c, _⟩
              · simp [pathOfSegs, st, stateWithRootHandle]
              · exfalso; apply hne; simp [st, stateWithRootHandle, nodeAt, vfsTreeGet]
            · exfalso; apply hne; simp [st, stateWithRootHandle, nodeAt, vfsTreeGet, hbc]
        · by_cases haf : a = "f"
          · subst haf; rcases r1 with _ | ⟨b, _⟩
            · simp [pathOfSegs, st, stateWithRootHandle]
            · exfalso; apply hne; simp [st, stateWithRootHandle, nodeAt, vfsTreeGet]
          · exfalso; apply hne; simp [st, stateWithRootHandle, nodeAt, vfsTreeGet] <;> split <;> contradiction
  have hAll := proof_fs_subtree_rmdir_emptyAndErrors st rootHandle [] (EntryName.lit "e") (EntryName.lit "ne")
    (EntryName.lit "c") (EntryName.lit "m") (EntryName.lit "f") rfl hInv hKeys (fun _ hm => by cases hm)
    ⟨0o755, rfl, by decide, by decide⟩ ⟨0o755, rfl, fun s => by simp [EntryName.lit, st, stateWithRootHandle, nodeAt, vfsTreeGet, vfsEmptyDir]⟩
    ⟨0o755, rfl⟩ (by decide) rfl ⟨ByteArray.empty, 0o644, rfl⟩
  exact ⟨st, rootHandle, [], EntryName.lit "e", EntryName.lit "ne", EntryName.lit "c", EntryName.lit "m",
    EntryName.lit "f", rfl, hInv, hKeys, (fun _ hm => by cases hm), ⟨0o755, rfl, by decide, by decide⟩,
    ⟨0o755, rfl, fun s => by simp [EntryName.lit, st, stateWithRootHandle, nodeAt, vfsTreeGet, vfsEmptyDir]⟩,
    ⟨0o755, rfl⟩, (by decide), rfl, ⟨ByteArray.empty, 0o644, rfl⟩, hAll⟩

/-- `Internal.subtreeOpsM` satisfies `test_fs_subtree_rmtree_ignoreMissingErrorsAndNoRollback`. -/
theorem proof_fs_subtree_rmtree_ignoreMissingErrorsAndNoRollback :
    Core.AllPass (test_fs_subtree_rmtree_ignoreMissingErrorsAndNoRollback Internal.subtreeOpsM) := by
  intro st dh pos missingLeaf fileLeaf partialDir c1 c2 hLd hInv hKeys hValid hLen hPar hMiss hFile hOrd hPart hC1 hC2 hOnly
  rcases hPar with ⟨pm, hParNd, hW, hX⟩
  rcases hFile with ⟨bs, fm, hFileNd⟩
  rcases hC1 with ⟨c1Bs, c1Fm, hC1Nd⟩
  have hXF : (pm / 64 % 2 == 0) = false := by rw [hX]; decide
  dsimp only [Internal.subtreeOpsM, StateT.run, Bind.bind, StateT.bind]
  rw [show Internal.splitLastAux [missingLeaf] [] = some ([], missingLeaf) from rfl,
    show Internal.splitLastAux [fileLeaf] [] = some ([], fileLeaf) from rfl,
    show Internal.splitLastAux [partialDir] [] = some ([], partialDir) from rfl]
  dsimp only [Bind.bind, StateT.bind, Pure.pure, StateT.pure]
  rw [walkDescendM_nil_eq, walkDescendM_nil_eq, walkDescendM_nil_eq]
  have hLMiss : vfsDirOps.lstatAt dh missingLeaf st =
      (.error { kind := .notFound, path := some missingLeaf.val, message := s!"no such file or directory: {missingLeaf.val}" }, st) := by
    rw [vfsDirOps_lstatAt_def, hLd]; dsimp only; rw [hParNd]
    simp only [hXF, Bool.false_eq_true, ↓reduceIte, hMiss]
  have hLFile : vfsDirOps.lstatAt dh fileLeaf st = (.ok (vfsToStat (.file bs fm)), st) := by
    rw [vfsDirOps_lstatAt_def, hLd]; dsimp only; rw [hParNd]
    simp only [hXF, Bool.false_eq_true, ↓reduceIte, hFileNd]
  have hLPart : vfsDirOps.lstatAt dh partialDir st = (.ok (vfsToStat (.dir 0o700)), st) := by
    rw [vfsDirOps_lstatAt_def, hLd]; dsimp only; rw [hParNd]
    simp only [hXF, Bool.false_eq_true, ↓reduceIte, hPart]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp only [hLMiss, show (FsErrorKind.notFound == FsErrorKind.notFound) = true from rfl,
      Bool.and_true, ↓reduceIte, Pure.pure, StateT.pure]
    exact ⟨trivial, trivial⟩
  · simp only [hLMiss, show (FsErrorKind.notFound == FsErrorKind.notFound) = true from rfl,
      Bool.and_false, Bool.false_eq_true, ↓reduceIte, Pure.pure, StateT.pure]
    exact ⟨⟨_, rfl, rfl⟩, trivial⟩
  · simp only [hLFile, vfsToStat, show (EntryKind.file != EntryKind.dir) = true from rfl,
      ↓reduceIte, Pure.pure, StateT.pure]
    exact ⟨⟨_, rfl, rfl⟩, trivial⟩
  · simp only [hLPart, vfsToStat, show (EntryKind.dir != EntryKind.dir) = false from rfl,
      Bool.false_eq_true, ↓reduceIte]
    have hPPosValid : ∀ s ∈ pos ++ [partialDir.val], validSeg s = true := fun s hs => by
      rcases List.mem_append.mp hs with hp | hp
      · exact hValid s hp
      · simp only [List.mem_singleton] at hp; subst hp; exact partialDir.valid
    have hWalkR := walkDescendM_ok [partialDir] dh pos st (fun dirDh => vfsDirOps.readDirAt dirDh) hLd hInv
      (fun k hk => by
        have hk0 : k = 0 := by simp at hk; omega
        subst hk0; exact ⟨pm, by simpa using hParNd, fun h => absurd h (Nat.not_lt_zero 0), hX⟩)
      (fun _ => ⟨0o700, by simpa using hPart, by decide⟩)
    rcases hWalkR.2 (by simp) with
      ⟨pDh1, stM1, hPosDh1, hLdM1, hTM1, hKM1, _, _, _, hInvM1, hLtM1, hOpenM1, hWalkR1⟩
    have hSortedEq : Internal.sortEntryNames (mVfsReadDirAtEntries stM1 (pos ++ [partialDir.val])) = [c1, c2] := by
      have hRawEq : mVfsReadDirAtEntries stM1 (pos ++ [partialDir.val]) = mVfsReadDirAtEntries st (pos ++ [partialDir.val]) := by
        unfold mVfsReadDirAtEntries; rw [hKM1, nodes_eq_of_tree_eq' hTM1]
      rw [hRawEq]
      refine sorted_pair_eq c1 c2 _ (mVfsReadDirAtEntries_nodup st (pos ++ [partialDir.val])) ?_ ?_ hOrd ?_
      · have hk1 : pathOfSegs ((pos ++ [partialDir.val]) ++ [c1.val]) ∈ st.keys := by
          apply hKeys; simp [List.append_assoc, hC1Nd]
        exact mVfsReadDirAtEntries_mem_of_key st (pos ++ [partialDir.val]) c1 hPPosValid hk1
          (by simp [List.append_assoc, hC1Nd])
      · have hk2 : pathOfSegs ((pos ++ [partialDir.val]) ++ [c2.val]) ∈ st.keys := by
          apply hKeys; simp [List.append_assoc, hC2]
        exact mVfsReadDirAtEntries_mem_of_key st (pos ++ [partialDir.val]) c2 hPPosValid hk2
          (by simp [List.append_assoc, hC2])
      · intro x hx
        have hLive := mVfsReadDirAtEntries_mem_sound st (pos ++ [partialDir.val]) hPPosValid x hx
        by_cases hx1 : x.val = c1.val
        · exact Or.inl (entryName_ext hx1)
        · by_cases hx2 : x.val = c2.val
          · exact Or.inr (entryName_ext hx2)
          · exact absurd (by simpa [List.append_assoc] using hOnly x.val hx1 hx2) hLive
    have hReadOk1 : vfsDirOps.readDirAt pDh1 stM1 =
        (.ok (mVfsReadDirAtEntries stM1 (pos ++ [partialDir.val])), stM1) := by
      rw [vfsDirOps_readDirAt_def, hLdM1]; dsimp only
      simp only [List.map_cons, List.map_nil]
      have hPartM1 : nodeAt stM1.tree (pos ++ [partialDir.val]) = some (.dir 0o700) := by
        rw [hTM1]; simpa using hPart
      rw [hPartM1]
      simp only [show (0o700 / 256 % 2 == 0) = false from by decide, Bool.false_eq_true, ↓reduceIte]
    let stC1 : VfsState := { stM1 with openDirs := st.openDirs }
    have hReadR : Internal.walkDescendM vfsDirOps dh [partialDir] (fun dirDh => vfsDirOps.readDirAt dirDh) st =
        (.ok (mVfsReadDirAtEntries stM1 (pos ++ [partialDir.val])), stC1) := by
      rw [hWalkR1, bracketCloseDirM_run, hReadOk1]
      dsimp only
      rw [vfsDirOps_closeDir_fresh pDh1 stM1 (pos ++ [partialDir.val]) hPosDh1 st.openDirs hOpenM1 hLtM1]
    have hInvC1 : DirHandleInvariant stC1 :=
      dirHandleInvariant_of_subset hInvM1 (fun p hp => by rw [hOpenM1]; exact List.mem_cons_of_mem _ hp) rfl
    have hLdC1 : lookupDir stC1 dh = some pos := by unfold lookupDir at hLd ⊢; exact hLd
    have hParC1 : nodeAt stC1.tree pos = some (.dir pm) := by change nodeAt stM1.tree pos = _; rw [hTM1]; exact hParNd
    have hPartC1 : nodeAt stC1.tree (pos ++ [partialDir.val]) = some (.dir 0o700) := by
      change nodeAt stM1.tree (pos ++ [partialDir.val]) = _; rw [hTM1]; exact hPart
    have hWalkPfx := walkDescendM_ok [partialDir] dh pos stC1
      (fun pDh => Internal.rmtreeNonDirPrefixM vfsDirOps pDh [c1, c2]) hLdC1 hInvC1
      (fun k hk => by
        have hk0 : k = 0 := by simp at hk; omega
        subst hk0; exact ⟨pm, by simpa using hParC1, fun h => absurd h (Nat.not_lt_zero 0), hX⟩)
      (fun _ => ⟨0o700, by simpa using hPartC1, by decide⟩)
    rcases hWalkPfx.2 (by simp) with
      ⟨pDh2, stM2, hPosDh2, hLdM2, hTM2, _, _, _, _, hInvM2, hLtM2, hOpenM2, hWalkPfxEq⟩
    have hPartM2 : nodeAt stM2.tree (pos ++ [partialDir.val]) = some (.dir 0o700) := by
      rw [hTM2]; exact hPartC1
    have hC1M2 : nodeAt stM2.tree ((pos ++ [partialDir.val]) ++ [c1.val]) = some (.file c1Bs c1Fm) := by
      rw [hTM2]; change nodeAt stM1.tree _ = _; rw [hTM1]; simpa [List.append_assoc] using hC1Nd
    have hC2M2 : nodeAt stM2.tree ((pos ++ [partialDir.val]) ++ [c2.val]) = some (.dir 0o000) := by
      rw [hTM2]; change nodeAt stM1.tree _ = _; rw [hTM1]; simpa [List.append_assoc] using hC2
    have hC1NeC2 : c1.val ≠ c2.val := by
      intro hEq
      rw [hEq] at hOrd
      have := (Std.LawfulOrderLT.lt_iff c2.val c2.val).mp hOrd
      exact this.2 this.1
    have hDirGetM2 : ∃ dm ch, vfsTreeGet stM2.tree (pos ++ [partialDir.val]) = some (.dir dm ch) :=
      let ⟨ch, hG⟩ := vfsTreeGet_dir_of_nodeAt hPartM2; ⟨0o700, ch, hG⟩
    let stM2' : VfsState :=
      { stM2 with tree := vfsTreeSet stM2.tree ((pos ++ [partialDir.val]) ++ [c1.val]) none }
    have hNotC2 : ¬ ((pos ++ [partialDir.val]) ++ [c1.val] <+: (pos ++ [partialDir.val]) ++ [c2.val]) := by
      intro hP
      rcases hP with ⟨r, hr⟩
      rw [List.append_assoc] at hr
      have hR := List.append_cancel_left hr
      cases r with
      | nil => simp only [List.append_nil, List.cons.injEq, and_true] at hR; exact hC1NeC2 hR
      | cons _ _ => have hL := congrArg List.length hR; simp at hL
    have hPfxRes : Internal.rmtreeNonDirPrefixM vfsDirOps pDh2 [c1, c2] stM2 = (.ok (some (c2, [])), stM2') := by
      rw [Internal.rmtreeNonDirPrefixM.eq_2]
      simp only [Bind.bind, StateT.bind]
      have hL1 : vfsDirOps.lstatAt pDh2 c1 stM2 = (.ok (vfsToStat (.file c1Bs c1Fm)), stM2) := by
        rw [vfsDirOps_lstatAt_def, hLdM2]; dsimp only
        simp only [List.map_cons, List.map_nil]
        rw [hPartM2]
        simp only [show (0o700 / 64 % 2 == 0) = false from by decide, Bool.false_eq_true, ↓reduceIte, hC1M2]
      have hU1 : vfsDirOps.unlinkAt pDh2 c1 false stM2 = (.ok (), stM2') := by
        rw [vfsDirOps_unlinkAt_def, hLdM2]; dsimp only
        simp only [List.map_cons, List.map_nil]
        rw [hPartM2]
        simp only [show (0o700 / 128 % 2 == 0 || 0o700 / 64 % 2 == 0) = false from by decide,
          Bool.false_eq_true, ↓reduceIte, hC1M2]
        rfl
      rw [hL1]
      simp only [vfsToStat, show (EntryKind.file == EntryKind.dir) = false from rfl, Bool.false_eq_true,
        ↓reduceIte]
      dsimp only [Bind.bind, StateT.bind]
      rw [hU1]
      dsimp only
      rw [Internal.rmtreeNonDirPrefixM.eq_2]
      simp only [Bind.bind, StateT.bind]
      have hL2 : vfsDirOps.lstatAt pDh2 c2 stM2' = (.ok (vfsToStat (.dir 0o000)), stM2') := by
        have hLdM2' : lookupDir stM2' pDh2 = some (pos ++ [partialDir.val]) := by
          change lookupDir stM2 pDh2 = _; simpa using hLdM2
        rw [vfsDirOps_lstatAt_def, hLdM2']; dsimp only
        have hNotSelfM2 : ¬ ((pos ++ [partialDir.val]) ++ [c1.val] <+: pos ++ [partialDir.val]) := by
          intro hP; have hL := List.IsPrefix.length_le hP; simp only [List.length_append, List.length_singleton] at hL; omega
        have hPM2' : nodeAt stM2'.tree (pos ++ [partialDir.val]) = some (.dir 0o700) := by
          change nodeAt (vfsTreeSet stM2.tree ((pos ++ [partialDir.val]) ++ [c1.val]) none) (pos ++ [partialDir.val]) = _
          rw [nodeAt_vfsTreeSet_outside stM2.tree (pos ++ [partialDir.val]) c1.val none (pos ++ [partialDir.val]) hDirGetM2 hNotSelfM2, hPartM2]
        have hC2M2' : nodeAt stM2'.tree ((pos ++ [partialDir.val]) ++ [c2.val]) = some (.dir 0o000) := by
          change nodeAt (vfsTreeSet stM2.tree ((pos ++ [partialDir.val]) ++ [c1.val]) none) ((pos ++ [partialDir.val]) ++ [c2.val]) = _
          rw [nodeAt_vfsTreeSet_outside stM2.tree (pos ++ [partialDir.val]) c1.val none ((pos ++ [partialDir.val]) ++ [c2.val]) hDirGetM2 hNotC2, hC2M2]
        rw [hPM2']
        simp only [show (0o700 / 64 % 2 == 0) = false from by decide, Bool.false_eq_true, ↓reduceIte, hC2M2']
      rw [hL2]
      simp only [vfsToStat, show (EntryKind.dir == EntryKind.dir) = true from rfl, ↓reduceIte, Pure.pure, StateT.pure]
    let stPfx2 : VfsState := { stM2' with openDirs := st.openDirs }
    have hPfxStep : Internal.walkDescendM vfsDirOps dh [partialDir] (fun pDh => Internal.rmtreeNonDirPrefixM vfsDirOps pDh [c1, c2]) stC1 =
        (.ok (some (c2, [])), stPfx2) := by
      rw [hWalkPfxEq, bracketCloseDirM_run, hPfxRes]
      dsimp only
      rw [vfsDirOps_closeDir_fresh pDh2 stM2' (pos ++ [partialDir.val]) hPosDh2 st.openDirs hOpenM2 hLtM2]
    have hInvPfx2 : DirHandleInvariant stPfx2 :=
      dirHandleInvariant_of_subset hInvM2 (fun p hp => by rw [hOpenM2]; exact List.mem_cons_of_mem _ hp) rfl
    have hNotSelfPfx2 : ¬ ((pos ++ [partialDir.val]) ++ [c1.val] <+: pos ++ [partialDir.val]) := by
      intro hP; have hL := List.IsPrefix.length_le hP; simp only [List.length_append, List.length_singleton] at hL; omega
    have hNotPosPfx2 : ¬ ((pos ++ [partialDir.val]) ++ [c1.val] <+: pos) := by
      intro hP; have hL := List.IsPrefix.length_le hP; simp only [List.length_append, List.length_singleton] at hL; omega
    have hParPfx2 : nodeAt stPfx2.tree pos = some (.dir pm) := by
      change nodeAt (vfsTreeSet stM2.tree ((pos ++ [partialDir.val]) ++ [c1.val]) none) pos = _
      rw [nodeAt_vfsTreeSet_outside stM2.tree (pos ++ [partialDir.val]) c1.val none pos hDirGetM2 hNotPosPfx2, hTM2, hParC1]
    have hPartPfx2 : nodeAt stPfx2.tree (pos ++ [partialDir.val]) = some (.dir 0o700) := by
      change nodeAt (vfsTreeSet stM2.tree ((pos ++ [partialDir.val]) ++ [c1.val]) none) (pos ++ [partialDir.val]) = _
      rw [nodeAt_vfsTreeSet_outside stM2.tree (pos ++ [partialDir.val]) c1.val none (pos ++ [partialDir.val]) hDirGetM2 hNotSelfPfx2, hPartM2]
    have hC2Pfx2 : nodeAt stPfx2.tree ((pos ++ [partialDir.val]) ++ [c2.val]) = some (.dir 0o000) := by
      change nodeAt (vfsTreeSet stM2.tree ((pos ++ [partialDir.val]) ++ [c1.val]) none) ((pos ++ [partialDir.val]) ++ [c2.val]) = _
      rw [nodeAt_vfsTreeSet_outside stM2.tree (pos ++ [partialDir.val]) c1.val none ((pos ++ [partialDir.val]) ++ [c2.val]) hDirGetM2 hNotC2, hC2M2]
    have hC2PermErr : ∃ e st', Internal.rmtreeDirAtM vfsDirOps dh [partialDir] c2 4095 stPfx2 = (.error e, st') ∧
        e.kind = .permissionDenied ∧ st'.tree = stPfx2.tree ∧ st'.openDirs = st.openDirs := by
      rw [show (4095 : Nat) = 4094 + 1 from rfl, Internal.rmtreeDirAtM.eq_2]
      simp only [Bind.bind, StateT.bind]
      have hLdPfx2 : lookupDir stPfx2 dh = some pos := hLdC1
      rcases vfsDirOps_openDirAt_dir_ok stPfx2 dh partialDir pos pm 0o700 hLdPfx2 hParPfx2 hX hPartPfx2 (by decide) with
        ⟨pDh3, stM3, hOp3⟩
      rcases vfsDirOps_openDirAt_ok dh partialDir stPfx2 pDh3 stM3 hOp3 with
        ⟨hPosDh3, _, hLtM3, pos3, _, _, hLd3', _, _, _, _, _, hSt3⟩
      rcases Option.some.inj (hLdPfx2.symm.trans hLd3') with rfl
      have hLdM3 : lookupDir stM3 pDh3 = some (pos ++ [partialDir.val]) := by
        rw [hSt3]; exact lookupDir_cons_self stPfx2 pDh3.handleId (pos ++ [partialDir.val]) pDh3.rootPath hPosDh3
      have hPartM3 : nodeAt stM3.tree (pos ++ [partialDir.val]) = some (.dir 0o700) := by rw [hSt3]; exact hPartPfx2
      have hC2M3 : nodeAt stM3.tree ((pos ++ [partialDir.val]) ++ [c2.val]) = some (.dir 0o000) := by rw [hSt3]; exact hC2Pfx2
      have hOpenC2Err : vfsDirOps.openDirAt pDh3 c2 stM3 =
          (.error { kind := .permissionDenied, path := some c2.val, message := s!"permission denied: {c2.val}" }, stM3) := by
        rcases (⟨_, rfl⟩ : ∃ d : Nat, vfsDirOps.openDirAt pDh3 c2 stM3 = openDirAtTpl' stM3 pDh3 c2 d) with ⟨d, hEq⟩
        rw [hEq]; unfold openDirAtTpl'; rw [hLdM3]; dsimp only; rw [hPartM3]
        simp only [show (0o700 / 64 % 2 == 0) = false from by decide, Bool.false_eq_true, ↓reduceIte,
          hC2M3, show (0o000 / 256 % 2 == 0) = true from by decide]
      have hClM3 : vfsDirOps.closeDir pDh3 stM3 = (.ok (), { stM3 with openDirs := st.openDirs }) := by
        apply vfsDirOps_closeDir_fresh pDh3 stM3 (pos ++ [partialDir.val]) hPosDh3 st.openDirs
        · rw [hSt3]
        · exact hLtM3
      have hWalkFail : Internal.walkDescendM vfsDirOps dh ([partialDir, c2]) (fun dirDh => vfsDirOps.readDirAt dirDh) stPfx2 =
          (.error { kind := .permissionDenied, path := some c2.val, message := s!"permission denied: {c2.val}" },
            { stM3 with openDirs := st.openDirs }) := by
        rw [Internal.walkDescendM, walkDescendAuxM_cons]
        simp only [↓reduceIte, Bind.bind, StateT.bind, hOp3]
        rw [walkDescendAuxM_cons]
        simp only [Bool.false_eq_true, ↓reduceIte, Bind.bind, StateT.bind, bracketCloseDirM_run, hOpenC2Err]
        rw [hClM3]
        rfl
      have hWalkFail' : Internal.walkDescendM vfsDirOps dh ([partialDir] ++ [c2]) (fun dirDh => vfsDirOps.readDirAt dirDh) stPfx2 =
          (.error { kind := .permissionDenied, path := some c2.val, message := s!"permission denied: {c2.val}" },
            { stM3 with openDirs := st.openDirs }) := hWalkFail
      refine ⟨{ kind := .permissionDenied, path := some c2.val, message := s!"permission denied: {c2.val}" },
          { stM3 with openDirs := st.openDirs }, ?_, rfl, ?_, rfl⟩
      · rw [hWalkFail']; rfl
      · change stM3.tree = stPfx2.tree; rw [hSt3]
    rcases hC2PermErr with ⟨e, stPartial, hC2Err, hKindP, hTreeP, hOpenP⟩
    have hDirRun : Internal.rmtreeDirAtM vfsDirOps dh [] partialDir 4096 st = (.error e, stPartial) := by
      have hProcErr : Internal.rmtreeProcessM vfsDirOps dh [partialDir]
          (fun subDir => Internal.rmtreeDirAtM vfsDirOps dh [partialDir] subDir 4095)
          [c1, c2].length [c1, c2] stC1 = (.error e, stPartial) := by
        rw [show ([c1, c2] : List EntryName).length = Nat.succ 1 from rfl, Internal.rmtreeProcessM.eq_3]
        · dsimp only [Bind.bind, StateT.bind]; rw [hPfxStep]; dsimp only [Bind.bind, StateT.bind]; rw [hC2Err]; rfl
        · exact List.cons_ne_nil c1 [c2]
      rw [show (4096 : Nat) = 4095 + 1 from rfl, Internal.rmtreeDirAtM.eq_2]
      dsimp only [Bind.bind, StateT.bind]
      simp only [List.nil_append]
      rw [hReadR]
      dsimp only
      rw [show Internal.sortEntryNames (mVfsReadDirAtEntries stM1 (pos ++ [partialDir.val])) = [c1, c2] from hSortedEq]
      dsimp only [Bind.bind, StateT.bind]
      rw [hProcErr]
      rfl
    rw [hDirRun]
    refine ⟨⟨e, rfl, hKindP⟩, ?_, hOpenP, ?_⟩
    · rw [hTreeP]
      change nodeAt (vfsTreeSet stM2.tree ((pos ++ [partialDir.val]) ++ [c1.val]) none) (pos ++ [partialDir.val, c1.val]) = none
      unfold nodeAt
      rw [show pos ++ [partialDir.val, c1.val] = (pos ++ [partialDir.val]) ++ [c1.val] from by simp,
        vfsTreeGet_vfsTreeSet_eq stM2.tree (pos ++ [partialDir.val]) c1.val none hDirGetM2]
      rfl
    · apply SameOutside_mono (b := (pos ++ [partialDir.val]) ++ [c1.val]) ⟨[c1.val], rfl⟩
      intro p hNot
      change vfsTreeNodes stPartial.tree p = st.nodes p
      rw [hTreeP]
      change vfsTreeNodes (vfsTreeSet stM2.tree ((pos ++ [partialDir.val]) ++ [c1.val]) none) p = st.nodes p
      have hEqSt : stM2.tree = st.tree := by rw [hTM2]; change stM1.tree = st.tree; exact hTM1
      rw [← nodes_eq_of_tree_eq' hEqSt]
      change vfsTreeNodes (vfsTreeSet stM2.tree ((pos ++ [partialDir.val]) ++ [c1.val]) none) p = vfsTreeNodes stM2.tree p
      unfold vfsTreeNodes
      split
      · exact nodeAt_vfsTreeSet_outside stM2.tree (pos ++ [partialDir.val]) c1.val none (vfsSplitSegs p) hDirGetM2 hNot
      · rfl
  · intro stDeep dhDeep posDeep deepDir hLdD hInvD hKeysD hValidD _ hParD hDeepD hTsub
    rcases hParD with ⟨pmD, hParNdD, hWD, hXD⟩
    have hXDF : (pmD / 64 % 2 == 0) = false := by rw [hXD]; decide
    have hLDeep : vfsDirOps.lstatAt dhDeep deepDir stDeep = (.ok (vfsToStat (.dir 0o700)), stDeep) := by
      rw [vfsDirOps_lstatAt_def, hLdD]; dsimp only; rw [hParNdD]
      simp only [hXDF, Bool.false_eq_true, ↓reduceIte, hDeepD]
    rcases vfsTreeGet_dir_of_nodeAt hDeepD with ⟨chD, hGetD⟩
    rcases hTsub (.dir 0o700 chD) (by simpa using hGetD) with ⟨hVSD, hPermD, hNotRD⟩
    have hPosDirD : ∃ pm₀, nodeAt stDeep.tree posDeep = some (.dir pm₀) ∧ (([] : List EntryName) = [] → pm₀ / 128 % 2 = 1) ∧ pm₀ / 64 % 2 = 1 :=
      ⟨pmD, hParNdD, fun _ => hWD, hXD⟩
    rcases rmtreeDirAtM_depth_err 4096 [] deepDir dhDeep posDeep stDeep (.dir 0o700 chD)
      hKeysD hLdD hInvD hValidD hPosDirD (fun _ _ hle => by simp only [List.length_nil] at hle; omega)
      (by simpa using hGetD) hVSD hPermD hNotRD with ⟨e, st', hErr, hKind, hOpen⟩
    have hRunDeep : ((Internal.subtreeOpsM vfsDirOps dhDeep).rmtree { segments := [deepDir] } false).run stDeep = (.error e, st') := by
      dsimp only [Internal.subtreeOpsM, StateT.run, Bind.bind, StateT.bind]
      rw [show Internal.splitLastAux [deepDir] [] = some ([], deepDir) from rfl]
      dsimp only
      rw [walkDescendM_nil_eq]
      dsimp only [Bind.bind, StateT.bind]
      rw [hLDeep]
      simp only [vfsToStat, show (EntryKind.dir != EntryKind.dir) = false from rfl, Bool.false_eq_true, ↓reduceIte, hErr]
    change (match ((Internal.subtreeOpsM vfsDirOps dhDeep).rmtree { segments := [deepDir] } false).run stDeep with
      | (rDeep, stDeep') => ((∃ e, rDeep = .error e ∧ e.kind = .ioError) ∧ stDeep'.openDirs = stDeep.openDirs) ∧ True)
    rw [hRunDeep]
    exact ⟨⟨⟨e, rfl, hKind⟩, hOpen⟩, trivial⟩


@[irreducible] private def rmtreeWitnessSt : VfsState :=
  stateWithRootHandle (fun
    | "f" => some (.file ByteArray.empty 0o644)
    | "p" => some (.dir 0o700 (fun
      | "a" => some (.file ByteArray.empty 0o644)
      | "b" => some (.dir 0o000 (fun _ => none))
      | _ => none))
    | _ => none) ["/", "/f", "/p", "/p/a", "/p/b"]

private theorem rmtreeWitnessSt_lookup : lookupDir rmtreeWitnessSt rootHandle = some [] := by
  unfold rmtreeWitnessSt stateWithRootHandle rootHandle lookupDir; rfl

private theorem rmtreeWitnessSt_root : nodeAt rmtreeWitnessSt.tree [] = some (.dir 0o755) := by
  unfold rmtreeWitnessSt stateWithRootHandle; rfl

private theorem rmtreeWitnessSt_f : nodeAt rmtreeWitnessSt.tree ([] ++ [(EntryName.lit "f").val]) = some (.file ByteArray.empty 0o644) := by
  unfold rmtreeWitnessSt stateWithRootHandle; rfl

private theorem rmtreeWitnessSt_p : nodeAt rmtreeWitnessSt.tree ([] ++ [(EntryName.lit "p").val]) = some (.dir 0o700) := by
  unfold rmtreeWitnessSt stateWithRootHandle; rfl

private theorem rmtreeWitnessSt_pa : nodeAt rmtreeWitnessSt.tree ([] ++ [(EntryName.lit "p").val, (EntryName.lit "a").val]) = some (.file ByteArray.empty 0o644) := by
  unfold rmtreeWitnessSt stateWithRootHandle; rfl

private theorem rmtreeWitnessSt_pb : nodeAt rmtreeWitnessSt.tree ([] ++ [(EntryName.lit "p").val, (EntryName.lit "b").val]) = some (.dir 0o000) := by
  unfold rmtreeWitnessSt stateWithRootHandle; rfl

private theorem rmtreeWitnessSt_m : nodeAt rmtreeWitnessSt.tree ([] ++ [(EntryName.lit "m").val]) = none := by
  unfold rmtreeWitnessSt stateWithRootHandle; rfl

/-- Witness check for `test_fs_subtree_rmtree_ignoreMissingErrorsAndNoRollback`. -/
theorem reach_fs_subtree_rmtree_ignoreMissingErrorsAndNoRollback :
    Core.CanReach (test_fs_subtree_rmtree_ignoreMissingErrorsAndNoRollback Internal.subtreeOpsM) := by
  let st := rmtreeWitnessSt
  have hInv : DirHandleInvariant st := fun _ _ hm => by
    unfold st rmtreeWitnessSt at hm; simp [stateWithRootHandle] at hm; rcases hm with ⟨rfl, rfl⟩
    unfold st rmtreeWitnessSt; simp [stateWithRootHandle]
  have hKeys : VfsKeysComplete st := by
    unfold st rmtreeWitnessSt
    intro segs hne
    rcases segs with _ | ⟨a, r1⟩
    · simp [pathOfSegs, stateWithRootHandle]
    · by_cases haf : a = "f"
      · subst haf; rcases r1 with _ | ⟨b, _⟩
        · simp [pathOfSegs, stateWithRootHandle]
        · exfalso; apply hne; simp [stateWithRootHandle, nodeAt, vfsTreeGet]
      · by_cases hap : a = "p"
        · subst hap; rcases r1 with _ | ⟨b, r2⟩
          · simp [pathOfSegs, stateWithRootHandle]
          · by_cases hba : b = "a"
            · subst hba; rcases r2 with _ | ⟨c, _⟩
              · simp [pathOfSegs, stateWithRootHandle]
              · exfalso; apply hne; simp [stateWithRootHandle, nodeAt, vfsTreeGet]
            · by_cases hbb : b = "b"
              · subst hbb; rcases r2 with _ | ⟨c, _⟩
                · simp [pathOfSegs, stateWithRootHandle]
                · exfalso; apply hne; simp [stateWithRootHandle, nodeAt, vfsTreeGet]
              · exfalso; apply hne; simp [stateWithRootHandle, nodeAt, vfsTreeGet]
        · exfalso; apply hne; simp [stateWithRootHandle, nodeAt, vfsTreeGet]
  have hOnly : ∀ s, s ≠ (EntryName.lit "a").val → s ≠ (EntryName.lit "b").val →
      nodeAt st.tree ([] ++ [(EntryName.lit "p").val, s]) = none := fun s hsa hsb => by
    unfold st rmtreeWitnessSt
    simp only [EntryName.lit, stateWithRootHandle, nodeAt, vfsTreeGet, List.nil_append]
    have hna : s ≠ "a" := hsa
    have hnb : s ≠ "b" := hsb
    split
    · rfl
    · next _ h =>
      split at h <;> simp_all
  have hAll1 := proof_fs_subtree_rmtree_ignoreMissingErrorsAndNoRollback st rootHandle [] (EntryName.lit "m")
    (EntryName.lit "f") (EntryName.lit "p") (EntryName.lit "a") (EntryName.lit "b")
    rmtreeWitnessSt_lookup hInv hKeys (fun _ hm => by cases hm) (by decide) ⟨0o755, rmtreeWitnessSt_root, by decide, by decide⟩ rmtreeWitnessSt_m
    ⟨ByteArray.empty, 0o644, rmtreeWitnessSt_f⟩ (by decide) rmtreeWitnessSt_p ⟨ByteArray.empty, 0o644, rmtreeWitnessSt_pa⟩ rmtreeWitnessSt_pb
    hOnly
  rcases hAll1 with ⟨a1, a2, a3, a4, hDeepFn⟩
  let stDeep := deepSubdirState 0o700 4096
  have hInvD : DirHandleInvariant stDeep := by
    intro id p hm
    rw [deepSubdirState_openDirs] at hm
    simp only [List.mem_singleton, Prod.mk.injEq] at hm
    rcases hm with ⟨rfl, rfl⟩
    refine ⟨by decide, ?_⟩
    rw [deepSubdirState_nextDirId]; decide
  have hKeysD : VfsKeysComplete stDeep := deepSubdirKeys_complete 0o700 4096
  have hTsub : ∀ tsub, vfsTreeGet stDeep.tree ([] ++ [(EntryName.lit "d").val]) = some tsub →
      VfsTreeValidSegs tsub ∧ vfsTreePermRemovable' tsub ∧ ¬ VfsTreeRemovable 4096 tsub := by
    intro tsub hGet
    rw [deepSubdirState_tree] at hGet
    simp only [List.nil_append, EntryName.lit, vfsTreeGet, beq_self_eq_true, ↓reduceIte, Option.some.injEq] at hGet
    subst hGet
    exact ⟨deepSubdirTree_validSegs 0o700 4096, deepSubdirTree_permRemovable 4096, deepSubdirTree_not_removable 4096 4096 (Nat.le_refl _)⟩
  have hAll2 := hDeepFn stDeep rootHandle [] (EntryName.lit "d") (deepSubdirState_lookup 0o700 4096) hInvD hKeysD
    (fun _ hm => by cases hm) (by decide) ⟨0o755, deepSubdirState_rootNode 0o700 4096, by decide, by decide⟩
    (deepSubdirState_childDir 0o700 4096) hTsub
  refine ⟨st, rootHandle, [], EntryName.lit "m", EntryName.lit "f", EntryName.lit "p", EntryName.lit "a", EntryName.lit "b",
    rmtreeWitnessSt_lookup, hInv, hKeys, (fun _ hm => by cases hm), (by decide), ⟨0o755, rmtreeWitnessSt_root, by decide, by decide⟩, rmtreeWitnessSt_m,
    ⟨ByteArray.empty, 0o644, rmtreeWitnessSt_f⟩, (by decide), rmtreeWitnessSt_p, ⟨ByteArray.empty, 0o644, rmtreeWitnessSt_pa⟩, rmtreeWitnessSt_pb,
    hOnly, a1, a2, a3, a4, stDeep, rootHandle, [], EntryName.lit "d", deepSubdirState_lookup 0o700 4096, hInvD, hKeysD,
    (fun _ hm => by cases hm), (by decide), ⟨0o755, deepSubdirState_rootNode 0o700 4096, by decide, by decide⟩,
    deepSubdirState_childDir 0o700 4096, hTsub, ?_⟩
  cases hRun : StateT.run ((Internal.subtreeOpsM vfsDirOps rootHandle).rmtree { segments := [EntryName.lit "d"] } false) stDeep with
  | mk rDeep stDeep' =>
    rw [hRun] at hAll2
    exact hAll2

/-- `Internal.subtreeOpsM` satisfies `test_fs_subtree_symlink_createsAndValidatesTarget`. -/
theorem proof_fs_subtree_symlink_createsAndValidatesTarget :
    Core.AllPass (test_fs_subtree_symlink_createsAndValidatesTarget Internal.subtreeOpsM) := by
  intro st dh pos leaf badTarget goodTarget hLd _ hBad hGood hPar hMiss
  rcases hPar with ⟨pm, hParNd, hW, hX⟩
  have hWXF : (pm / 128 % 2 == 0 || pm / 64 % 2 == 0) = false := by rw [hW, hX]; decide
  have hBadCond : (badTarget.isEmpty || decide (Char.ofNat 0 ∈ badTarget.toList)) = true := by
    rcases hBad with rfl | hNul
    · decide
    · simp [hNul]
  have hNe : goodTarget.isEmpty = false := by
    cases hg : goodTarget.isEmpty with
    | false => rfl
    | true => exact absurd (String.isEmpty_iff.mp hg) hGood.1
  have hGoodCond : (goodTarget.isEmpty || decide (Char.ofNat 0 ∈ goodTarget.toList)) = false := by
    simp [hNe, hGood.2]
  have hGoodContains : (goodTarget.isEmpty || goodTarget.toList.contains (Char.ofNat 0)) = false := by
    simp [hNe, hGood.2]
  have hBadRun : ((Internal.subtreeOpsM vfsDirOps dh).symlink badTarget { segments := [leaf] }).run st =
      (.error { kind := .invalidInput, path := some badTarget, message := "invalid symlink target" }, st) := by
    dsimp only [Internal.subtreeOpsM, StateT.run]
    rw [show Internal.splitLastAux [leaf] [] = some ([], leaf) from rfl]
    simp only [hBadCond, ↓reduceIte, Pure.pure, StateT.pure]
  have hGoodRun : ((Internal.subtreeOpsM vfsDirOps dh).symlink goodTarget { segments := [leaf] }).run st =
      (.ok (), { st with
        tree := vfsTreeSet st.tree (pos ++ [leaf.val]) (some (.symlink goodTarget 0o777)),
        keys := pathOfSegs (pos ++ [leaf.val]) :: st.keys }) := by
    dsimp only [Internal.subtreeOpsM, StateT.run]
    rw [show Internal.splitLastAux [leaf] [] = some ([], leaf) from rfl]
    simp only [hGoodCond, Bool.false_eq_true, ↓reduceIte]
    rw [walkDescendM_nil_eq]
    rw [vfsDirOps_symlinkAt_def, hLd]; dsimp only; rw [hParNd]
    simp only [hGoodContains, hWXF, Bool.false_eq_true, ↓reduceIte, hMiss]
  refine ⟨?_, ?_, trivial⟩
  · change (∃ e, (((Internal.subtreeOpsM vfsDirOps dh).symlink badTarget { segments := [leaf] }).run st).1 = .error e ∧
        e.kind = .invalidInput) ∧
      (((Internal.subtreeOpsM vfsDirOps dh).symlink badTarget { segments := [leaf] }).run st).2.nodes = st.nodes
    rw [hBadRun]
    exact ⟨⟨_, rfl, rfl⟩, rfl⟩
  · change (((Internal.subtreeOpsM vfsDirOps dh).symlink goodTarget { segments := [leaf] }).run st).1 = .ok () ∧
      nodeAt (((Internal.subtreeOpsM vfsDirOps dh).symlink goodTarget { segments := [leaf] }).run st).2.tree (pos ++ [leaf.val]) =
        some (.symlink goodTarget 0o777)
    rw [hGoodRun]
    have hDirGet : ∃ dm ch, vfsTreeGet st.tree pos = some (.dir dm ch) :=
      let ⟨ch, hG⟩ := vfsTreeGet_dir_of_nodeAt hParNd; ⟨pm, ch, hG⟩
    refine ⟨rfl, ?_⟩
    unfold nodeAt; rw [vfsTreeGet_vfsTreeSet_eq st.tree pos leaf.val (some (.symlink goodTarget 0o777)) hDirGet]; rfl

/-- Witness check for `test_fs_subtree_symlink_createsAndValidatesTarget`. -/
theorem reach_fs_subtree_symlink_createsAndValidatesTarget :
    Core.CanReach (test_fs_subtree_symlink_createsAndValidatesTarget Internal.subtreeOpsM) := by
  let st := stateWithRootHandle (fun _ => none)
  have hInv : DirHandleInvariant st := fun _ _ hm => by
    simp [st, stateWithRootHandle] at hm; rcases hm with ⟨rfl, rfl⟩; decide
  have hAll := proof_fs_subtree_symlink_createsAndValidatesTarget st rootHandle [] (EntryName.lit "s") "" "t"
    rfl hInv (Or.inl rfl) ⟨by decide, by decide⟩ ⟨0o755, rfl, by decide, by decide⟩ rfl
  exact ⟨st, rootHandle, [], EntryName.lit "s", "", "t",
    rfl, hInv, (Or.inl rfl), ⟨by decide, by decide⟩, ⟨0o755, rfl, by decide, by decide⟩, rfl, hAll⟩

private theorem vfsTreeGet_snoc : ∀ (t : VfsTree) (pos : List String) (s : String) (dm : Nat)
    (ch : String → Option VfsTree),
    vfsTreeGet t pos = some (.dir dm ch) →
    vfsTreeGet t (pos ++ [s]) = ch s := by
  intro t pos s dm ch hGet
  induction pos generalizing t with
  | nil =>
    simp only [List.nil_append]
    simp only [vfsTreeGet] at hGet
    cases hGet
    cases hcs : ch s <;> simp [vfsTreeGet, hcs]
  | cons a rest ih =>
    simp only [List.cons_append]
    cases t with
    | file _ _ => simp [vfsTreeGet] at hGet
    | symlink _ _ => simp [vfsTreeGet] at hGet
    | dir _ tch =>
      simp only [vfsTreeGet] at hGet ⊢
      cases hC : tch a with
      | none => simp [hC] at hGet
      | some sub =>
        simp only [hC] at hGet
        exact ih sub hGet

private theorem foldr_walkEntrySorted : ∀ (xs : List WalkEntry),
    (∀ e ∈ xs, walkEntrySorted' e) →
    xs.foldr (fun e acc => walkEntrySorted' e ∧ acc) True := by
  intro xs h
  induction xs with
  | nil => exact trivial
  | cons a rest ih =>
    exact ⟨h a List.mem_cons_self, ih (fun e he => h e (List.mem_cons_of_mem _ he))⟩

/-- `Internal.subtreeOpsM` satisfies `test_fs_subtree_walkAndListDir_sortedValidAndSymlinkSafe`. -/
theorem proof_fs_subtree_walkAndListDir_sortedValidAndSymlinkSafe :
    Core.AllPass (test_fs_subtree_walkAndListDir_sortedValidAndSymlinkSafe Internal.subtreeOpsM) := by
  intro st dh pos child symName dirTarget hLd hInv hKeys hValid _ hWalk _ hPar hSym hDir hFile
  rcases hPar with ⟨pm, hParNd, hR, hX⟩
  have hRF : (pm / 256 % 2 == 0) = false := by rw [hR]; decide
  rcases vfsTreeGet_dir_of_nodeAt hParNd with ⟨ch, hGetPos⟩
  have hWalkRoot : VfsTreeWalkable 4096 (.dir pm ch) := hWalk (.dir pm ch) hGetPos
  let sorted := Internal.sortEntryNames (mVfsReadDirAtEntries st pos)
  have hPerm := List.mergeSort_perm (mVfsReadDirAtEntries st pos).toList (fun a b : EntryName => decide (a.val ≤ b.val))
  have hSymMem : symName ∈ sorted :=
    hPerm.mem_iff.mpr (mVfsReadDirAtEntries_mem_complete st pos hKeys hValid symName (by simp [hSym]))
  have hDirMem : dirTarget ∈ sorted :=
    hPerm.mem_iff.mpr (mVfsReadDirAtEntries_mem_complete st pos hKeys hValid dirTarget (by simp [hDir]))
  have hStrict : List.Pairwise (fun a b => a.val < b.val) sorted :=
    list_mergeSort_entryName_strict (mVfsReadDirAtEntries_nodup st pos)
  have hReadOk : vfsDirOps.readDirAt dh st = (.ok (mVfsReadDirAtEntries st pos), st) := by
    rw [vfsDirOps_readDirAt_def, hLd]; dsimp only; rw [hParNd]
    simp only [hRF, Bool.false_eq_true, ↓reduceIte]
  have hListRun : ((Internal.subtreeOpsM vfsDirOps dh).listDir .root).run st = (.ok sorted.toArray, st) := by
    dsimp only [Internal.subtreeOpsM, StateT.run, RelPath.root]
    rw [walkDescendM_nil_eq]
    dsimp only [Bind.bind, StateT.bind]
    rw [hReadOk]
    rfl
  dsimp only [Internal.subtreeOpsM, StateT.run, RelPath.root]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, trivial⟩
  · change ∃ names, (((Internal.subtreeOpsM vfsDirOps dh).listDir .root).run st).1 = .ok names ∧
        symName ∈ names.toList ∧ dirTarget ∈ names.toList ∧ List.Pairwise (fun a b => a.val < b.val) names.toList
    rw [hListRun]
    exact ⟨sorted.toArray, rfl, by simpa using hSymMem, by simpa using hDirMem, by simpa using hStrict⟩
  · change (((Internal.subtreeOpsM vfsDirOps dh).listDir .root).run st).2.nodes = st.nodes ∧
        (((Internal.subtreeOpsM vfsDirOps dh).listDir .root).run st).2.openDirs = st.openDirs
    rw [hListRun]
    exact ⟨rfl, rfl⟩
  · rcases walkRecM_ok 4095 [] "." #[] dh pos st pm ch hKeys hLd hInv hValid
        ⟨pm, hParNd, hX⟩ (fun k hk hle => by simp at hle; omega) (by simpa using hGetPos) hWalkRoot with
      ⟨tail, stW, hWalkEq, _, _, _, _, _, _, _, ⟨rest, hTailEq⟩, hSortedW, hRootsW⟩
    have hWalkShow : Internal.walkRecM vfsDirOps dh [] "." #[] 4096 st = (.ok (#[] ++ tail.toArray), stW) := hWalkEq
    rw [hWalkShow]
    let dirs := sorted.filter (isDirAt st (pos ++ ([] : List EntryName).map (·.val)))
    let files := (sorted.filter (fun n => !(isDirAt st (pos ++ ([] : List EntryName).map (·.val)) n))).map (·.val)
    let headEntry : WalkEntry := { root := ".", dirs := (dirs.map (·.val)).toArray, files := files.toArray }
    have hListEq : (#[] ++ tail.toArray).toList = tail := by simp
    refine ⟨#[] ++ tail.toArray, rfl, ?_, ?_, ?_, ?_⟩
    · rw [hListEq, hTailEq]; rfl
    · rw [List.any_eq_true]
      refine ⟨headEntry, ?_, ?_⟩
      · rw [hListEq, hTailEq]; dsimp only [headEntry, dirs, files, sorted]; simp only [List.map_nil, List.append_nil]; exact List.mem_cons_self
      · have hIsSymD : isDirAt st (pos ++ ([] : List EntryName).map (·.val)) symName = false := by
          simp [isDirAt, hSym]
        have hIsSymPos : isDirAt st pos symName = false := by simp [isDirAt, hSym]
        have hIsDirD : isDirAt st (pos ++ ([] : List EntryName).map (·.val)) dirTarget = true := by
          simp [isDirAt, hDir]
        have hSymInF : symName.val ∈ files := List.mem_map.mpr ⟨symName, List.mem_filter.mpr ⟨hSymMem, by simp [hIsSymPos]⟩, rfl⟩
        have hSymNotD : ¬ (symName.val ∈ dirs.map (·.val)) := by
          intro hm
          rcases List.mem_map.mp hm with ⟨x, hx, hVal⟩
          have hEq := entryName_ext hVal
          subst hEq
          have hD := (List.mem_filter.mp hx).2
          simp [hIsSymPos] at hD
        have hDirInD : dirTarget.val ∈ dirs.map (·.val) :=
          List.mem_map.mpr ⟨dirTarget, List.mem_filter.mpr ⟨hDirMem, hIsDirD⟩, rfl⟩
        simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true', decide_eq_false_iff_not, headEntry]
        exact ⟨⟨⟨rfl, hSymInF⟩, hSymNotD⟩, by simpa using hDirInD⟩
    · rw [Bool.not_eq_true']
      cases hAny : (#[] ++ tail.toArray).toList.any (fun e => e.root == symName.val) with
      | false => rfl
      | true =>
        rcases List.any_eq_true.mp hAny with ⟨e, he, hEqSym⟩
        rw [hListEq] at he
        have hRootSym : e.root = symName.val := beq_iff_eq.mp hEqSym
        have hv := symName.valid
        rcases hRootsW e he with hDot | ⟨s, hs, hSubR⟩
        · have hSymDot : symName.val = "." := hRootSym.symm.trans hDot
          rw [hSymDot] at hv
          exact absurd hv (by decide)
        · have hIsDS : isDirAt st (pos ++ ([] : List EntryName).map (·.val)) s = true := (List.mem_filter.mp hs).2
          have hSNeSym : s.val ≠ symName.val := by
            intro hSV
            have hEq := entryName_ext hSV
            subst hEq
            simp [isDirAt, hSym] at hIsDS
          have hLbl : (if ("." == ".") then s.val else "." ++ "/" ++ s.val) = s.val := rfl
          rw [hLbl] at hSubR
          rcases hSubR with hEqS | ⟨suf, hEqSlash⟩
          · exact False.elim (hSNeSym (hEqS.symm.trans hRootSym))
          · have hSl : '/' ∈ symName.val.toList := by
              rw [← hRootSym, hEqSlash]
              simp [String.toList_append]
            have hNoSl : '/' ∉ symName.val.toList := by
              have hv' := hv
              simp [validSeg] at hv'
              exact hv'.1.1.1.2
            exact False.elim (hNoSl hSl)
    · rw [hListEq]
      exact foldr_walkEntrySorted tail hSortedW
  · rcases walkRecM_ok 4095 [] "." #[] dh pos st pm ch hKeys hLd hInv hValid
        ⟨pm, hParNd, hX⟩ (fun k hk hle => by simp at hle; omega) (by simpa using hGetPos) hWalkRoot with
      ⟨tail, stW, hWalkEq, hTreeW, _, _, _, _, hOpenW, _, _, _, _⟩
    have hWalkShow : Internal.walkRecM vfsDirOps dh [] "." #[] 4096 st = (.ok (#[] ++ tail.toArray), stW) := hWalkEq
    rw [hWalkShow]
    exact ⟨nodes_eq_of_tree_eq' hTreeW, hOpenW⟩
  · rcases vfsTreeGet_dir_of_nodeAt hDir with ⟨chSub, hGetSub⟩
    rw [VfsTreeWalkable.eq_4] at hWalkRoot
    have hChSub : ch dirTarget.val = some (.dir 0o755 chSub) :=
      (vfsTreeGet_snoc st.tree pos dirTarget.val pm ch hGetPos).symm.trans hGetSub
    have hW4095 : VfsTreeWalkable 4095 (.dir 0o755 chSub) := hWalkRoot.2.2 dirTarget.val (.dir 0o755 chSub) hChSub
    have hW4096 : VfsTreeWalkable 4096 (.dir 0o755 chSub) :=
      vfsTreeWalkable_mono 4095 4096 (.dir 0o755 chSub) (by omega) hW4095
    have hAnc2 : ∀ k, 0 < k → k ≤ ([dirTarget] : List EntryName).length →
        ∃ dk, nodeAt st.tree (pos ++ (([dirTarget] : List EntryName).take k).map (·.val)) = some (.dir dk) ∧
          dk / 256 % 2 = 1 ∧ dk / 64 % 2 = 1 := by
      intro k hk hle
      have hk1 : k = 1 := by simp at hle; omega
      subst hk1
      exact ⟨0o755, by simpa [List.take] using hDir, by decide, by decide⟩
    rcases walkRecM_ok 4095 [dirTarget] "." #[] dh pos st 0o755 chSub hKeys hLd hInv hValid
        ⟨pm, hParNd, hX⟩ hAnc2 (by simpa using hGetSub) hW4096 with
      ⟨tail2, stW2, hWalkEq2, _, _, _, _, _, _, _, ⟨rest2, hTailEq2⟩, hSortedW2, _⟩
    have hWalkShow2 : Internal.walkRecM vfsDirOps dh [dirTarget] "." #[] 4096 st = (.ok (#[] ++ tail2.toArray), stW2) := hWalkEq2
    rw [hWalkShow2]
    let subPos := pos ++ [dirTarget.val]
    have hSubValid : ∀ s ∈ subPos, validSeg s = true := by
      intro s hs
      rcases List.mem_append.mp hs with hp | hr
      · exact hValid s hp
      · simp at hr; subst hr; exact dirTarget.valid
    have hPerm2 := List.mergeSort_perm (mVfsReadDirAtEntries st subPos).toList (fun a b : EntryName => decide (a.val ≤ b.val))
    have hChildMem : child ∈ Internal.sortEntryNames (mVfsReadDirAtEntries st subPos) :=
      hPerm2.mem_iff.mpr (mVfsReadDirAtEntries_mem_complete st subPos hKeys hSubValid child (by simp [subPos, List.append_assoc, hFile]))
    let sorted2 := Internal.sortEntryNames (mVfsReadDirAtEntries st (pos ++ ([dirTarget] : List EntryName).map (·.val)))
    let dirs2 := sorted2.filter (isDirAt st (pos ++ ([dirTarget] : List EntryName).map (·.val)))
    let files2 := (sorted2.filter (fun n => !(isDirAt st (pos ++ ([dirTarget] : List EntryName).map (·.val)) n))).map (·.val)
    let headEntry2 : WalkEntry := { root := ".", dirs := (dirs2.map (·.val)).toArray, files := files2.toArray }
    have hListEq2 : (#[] ++ tail2.toArray).toList = tail2 := by simp
    refine ⟨#[] ++ tail2.toArray, rfl, ?_, ?_, ?_⟩
    · rw [hListEq2, hTailEq2]; rfl
    · rw [List.any_eq_true]
      refine ⟨headEntry2, ?_, ?_⟩
      · rw [hListEq2, hTailEq2]; dsimp only [headEntry2, dirs2, files2, sorted2]; exact List.mem_cons_self
      · have hNotD : isDirAt st subPos child = false := by simp [isDirAt, subPos, List.append_assoc, hFile]
        have hChildInF : child.val ∈ files2 :=
          List.mem_map.mpr ⟨child, List.mem_filter.mpr ⟨hChildMem, by simp [subPos, hNotD]⟩, rfl⟩
        simp only [Bool.and_eq_true, decide_eq_true_eq, headEntry2]
        exact ⟨rfl, by simpa using hChildInF⟩
    · rw [hListEq2]
      exact foldr_walkEntrySorted tail2 hSortedW2
  · rcases vfsTreeGet_dir_of_nodeAt hDir with ⟨chSub, hGetSub⟩
    rw [VfsTreeWalkable.eq_4] at hWalkRoot
    have hChSub : ch dirTarget.val = some (.dir 0o755 chSub) :=
      (vfsTreeGet_snoc st.tree pos dirTarget.val pm ch hGetPos).symm.trans hGetSub
    have hW4095 : VfsTreeWalkable 4095 (.dir 0o755 chSub) := hWalkRoot.2.2 dirTarget.val (.dir 0o755 chSub) hChSub
    have hW4096 : VfsTreeWalkable 4096 (.dir 0o755 chSub) :=
      vfsTreeWalkable_mono 4095 4096 (.dir 0o755 chSub) (by omega) hW4095
    have hAnc2 : ∀ k, 0 < k → k ≤ ([dirTarget] : List EntryName).length →
        ∃ dk, nodeAt st.tree (pos ++ (([dirTarget] : List EntryName).take k).map (·.val)) = some (.dir dk) ∧
          dk / 256 % 2 = 1 ∧ dk / 64 % 2 = 1 := by
      intro k hk hle
      have hk1 : k = 1 := by simp at hle; omega
      subst hk1
      exact ⟨0o755, by simpa [List.take] using hDir, by decide, by decide⟩
    rcases walkRecM_ok 4095 [dirTarget] "." #[] dh pos st 0o755 chSub hKeys hLd hInv hValid
        ⟨pm, hParNd, hX⟩ hAnc2 (by simpa using hGetSub) hW4096 with
      ⟨tail2, stW2, hWalkEq2, hTreeW2, _, _, _, _, hOpenW2, _, _, _, _⟩
    have hWalkShow2 : Internal.walkRecM vfsDirOps dh [dirTarget] "." #[] 4096 st = (.ok (#[] ++ tail2.toArray), stW2) := hWalkEq2
    rw [hWalkShow2]
    exact ⟨nodes_eq_of_tree_eq' hTreeW2, hOpenW2⟩
  · have hAncF : ∀ k ≤ ([dirTarget] : List EntryName).length,
        ∃ dm, nodeAt st.tree (pos ++ (([dirTarget] : List EntryName).take k).map (·.val)) = some (.dir dm) ∧
          (0 < k → dm / 256 % 2 = 1) ∧ dm / 64 % 2 = 1 := by
      intro k hk
      cases k with
      | zero => exact ⟨pm, by simpa using hParNd, fun h => absurd h (Nat.not_lt_zero _), hX⟩
      | succ k' =>
        have hk0 : k' = 0 := by simp at hk; omega
        subst hk0
        exact ⟨0o755, by simpa [List.take] using hDir, fun _ => by decide, by decide⟩
    rcases walkDescendM_nonDir_err dh pos [dirTarget] child ByteArray.empty 0o644 st
        (fun dirDh => do
          match ← vfsDirOps.readDirAt dirDh with
          | .error e => pure (.error e)
          | .ok rawNames => Internal.classifyChildrenM vfsDirOps dirDh (Internal.sortEntryNames rawNames) [] [])
        hLd hInv hAncF (by simpa [List.append_assoc] using hFile) with
      ⟨e, stF, hDescErr, hKind, hNodesF, hOpenF⟩
    have hDescErr' : Internal.walkDescendM vfsDirOps dh [dirTarget, child]
        (fun dirDh => do
          match ← vfsDirOps.readDirAt dirDh with
          | .error e => pure (.error e)
          | .ok rawNames => Internal.classifyChildrenM vfsDirOps dirDh (Internal.sortEntryNames rawNames) [] []) st =
        (.error e, stF) := hDescErr
    rw [show (4096 : Nat) = 4095 + 1 from rfl, Internal.walkRecM.eq_2]
    dsimp only [Bind.bind, StateT.bind]
    erw [hDescErr']
    dsimp only [Pure.pure, StateT.pure]
    exact ⟨⟨e, rfl, hKind⟩, hNodesF, hOpenF⟩

/-- Witness check for `test_fs_subtree_walkAndListDir_sortedValidAndSymlinkSafe`. -/
theorem reach_fs_subtree_walkAndListDir_sortedValidAndSymlinkSafe :
    Core.CanReach (test_fs_subtree_walkAndListDir_sortedValidAndSymlinkSafe Internal.subtreeOpsM) := by
  let st := stateWithRootHandle (fun
    | "s" => some (.symlink "d" 0o777)
    | "d" => some (.dir 0o755 (fun s => if s == "c" then some (.file ByteArray.empty 0o644) else none))
    | _ => none) ["/", "/s", "/d", "/d/c"]
  have hInv : DirHandleInvariant st := fun _ _ hm => by
    simp [st, stateWithRootHandle] at hm; rcases hm with ⟨rfl, rfl⟩; decide
  have hKeys : VfsKeysComplete st := by
    intro segs hne
    rcases segs with _ | ⟨a, r1⟩
    · simp [pathOfSegs, st, stateWithRootHandle]
    · by_cases ha : a = "s"
      · subst ha
        rcases r1 with _ | ⟨b, r2⟩
        · simp [pathOfSegs, st, stateWithRootHandle]
        · exfalso; apply hne; simp [st, stateWithRootHandle, nodeAt, vfsTreeGet]
      · by_cases had : a = "d"
        · subst had
          rcases r1 with _ | ⟨b, r2⟩
          · simp [pathOfSegs, st, stateWithRootHandle]
          · by_cases hb : b = "c"
            · subst hb
              rcases r2 with _ | ⟨c, r3⟩
              · simp [pathOfSegs, st, stateWithRootHandle]
              · exfalso; apply hne; simp [st, stateWithRootHandle, nodeAt, vfsTreeGet]
            · exfalso; apply hne; simp [st, stateWithRootHandle, nodeAt, vfsTreeGet, hb]
        · exfalso; apply hne; simp [st, stateWithRootHandle, nodeAt, vfsTreeGet]
  have hWalkable : ∀ tsub, vfsTreeGet st.tree [] = some tsub → VfsTreeWalkable 4096 tsub := by
    intro tsub hget
    simp [st, stateWithRootHandle, vfsTreeGet] at hget
    subst hget
    rw [VfsTreeWalkable.eq_4]
    refine ⟨by decide, by decide, ?_⟩
    intro name sub hch
    by_cases hn1 : name = "s"
    · subst hn1; simp at hch; subst hch; rw [VfsTreeWalkable.eq_2]; trivial
    · by_cases hn2 : name = "d"
      · subst hn2; simp at hch; subst hch
        rw [VfsTreeWalkable.eq_4]
        refine ⟨by decide, by decide, ?_⟩
        intro n2 sub2 hch2
        by_cases hn3 : n2 = "c"
        · subst hn3; simp at hch2; subst hch2; rw [VfsTreeWalkable.eq_1]; trivial
        · simp [hn3] at hch2
      · simp at hch
  have hAll := proof_fs_subtree_walkAndListDir_sortedValidAndSymlinkSafe st rootHandle []
    (EntryName.lit "c") (EntryName.lit "s") (EntryName.lit "d")
    rfl hInv hKeys (fun _ hm => by cases hm) (by decide) hWalkable (by decide)
    ⟨0o755, rfl, by decide, by decide⟩ rfl rfl rfl
  exact ⟨st, rootHandle, [], EntryName.lit "c", EntryName.lit "s", EntryName.lit "d",
    rfl, hInv, hKeys, (fun _ hm => by cases hm), (by decide), hWalkable, (by decide),
    ⟨0o755, rfl, by decide, by decide⟩, rfl, rfl, rfl, hAll⟩

/-- `Internal.subtreeOpsM` satisfies `test_fs_subtree_walk_errorsAndDepth`. -/
theorem proof_fs_subtree_walk_errorsAndDepth :
    Core.AllPass (test_fs_subtree_walk_errorsAndDepth Internal.subtreeOpsM) := by
  intro st dh pos unrd hLd _ _ _ _ hPar hUnrd
  rcases hPar with ⟨pm, hParNd, _, hX⟩
  dsimp only [Internal.subtreeOpsM, StateT.run]
  rcases walkRecM_single_perm_err dh pos unrd 0o111 pm st hLd hParNd hX hUnrd (by decide) with
    ⟨e, st', hErr, hKind, hNodes, hOpen⟩
  refine ⟨?_, ?_⟩
  · rw [hErr]
    exact ⟨⟨e, rfl, hKind⟩, hNodes, hOpen⟩
  · intro stDeep dhDeep posDeep deep hLdD hInvD hKeysD hValidD _ hParD hDeepD hTsub
    rcases hParD with ⟨pmD, hParNdD, _, hXD⟩
    rcases vfsTreeGet_dir_of_nodeAt hDeepD with ⟨chD, hGetD⟩
    rcases hTsub (.dir 0o555 chD) (by simpa using hGetD) with ⟨hVSD, hPermD, hNotWD⟩
    have hPosDirD : ∃ pm₀, nodeAt stDeep.tree posDeep = some (.dir pm₀) ∧ pm₀ / 64 % 2 = 1 := ⟨pmD, hParNdD, hXD⟩
    have hAncD : ∀ k, 0 < k → k ≤ ([deep] : List EntryName).length →
        ∃ dk, nodeAt stDeep.tree (posDeep ++ (([deep] : List EntryName).take k).map (·.val)) = some (.dir dk) ∧
          dk / 256 % 2 = 1 ∧ dk / 64 % 2 = 1 := fun k hkPos hkLe => by
      have hk1 : k = 1 := by simp at hkLe; omega
      subst hk1
      exact ⟨0o555, by simpa using hDeepD, by decide, by decide⟩
    rcases walkRecM_depth_err 4096 [deep] "." #[] dhDeep posDeep stDeep (.dir 0o555 chD)
      hKeysD hLdD hInvD hValidD hPosDirD hAncD (by simpa using hGetD) hVSD hPermD hNotWD with
      ⟨eD, stD', hErrD, hKindD, hNodesD, hOpenD⟩
    rw [hErrD]
    exact ⟨⟨⟨eD, rfl, hKindD⟩, hNodesD, hOpenD⟩, trivial⟩

/-- Witness check for `test_fs_subtree_walk_errorsAndDepth`. -/
theorem reach_fs_subtree_walk_errorsAndDepth :
    Core.CanReach (test_fs_subtree_walk_errorsAndDepth Internal.subtreeOpsM) := by
  let st := stateWithRootHandle (fun s => if s == "u" then some (vfsEmptyDir 0o111) else none) ["/", "/u"]
  have hInv : DirHandleInvariant st := fun _ _ hm => by
    simp [st, stateWithRootHandle] at hm; rcases hm with ⟨rfl, rfl⟩; decide
  have hKeys : VfsKeysComplete st := by
    intro segs hne
    rcases segs with _ | ⟨a, r1⟩
    · simp [pathOfSegs, st, stateWithRootHandle]
    · by_cases hau : a = "u"
      · subst hau; rcases r1 with _ | ⟨b, _⟩
        · simp [pathOfSegs, st, stateWithRootHandle]
        · exfalso; apply hne; simp [st, stateWithRootHandle, nodeAt, vfsTreeGet, vfsEmptyDir]
      · exfalso; apply hne; simp [st, stateWithRootHandle, nodeAt, vfsTreeGet, hau]
  have hAll1 := proof_fs_subtree_walk_errorsAndDepth st rootHandle [] (EntryName.lit "u")
    rfl hInv hKeys (fun _ hm => by cases hm) (by decide) ⟨0o755, rfl, by decide, by decide⟩ rfl
  rcases hAll1 with ⟨a1, hDeepFn⟩
  let stDeep := deepSubdirState 0o555 4096
  have hInvD : DirHandleInvariant stDeep := by
    intro id p hm
    rw [deepSubdirState_openDirs] at hm
    simp only [List.mem_singleton, Prod.mk.injEq] at hm
    rcases hm with ⟨rfl, rfl⟩
    refine ⟨by decide, ?_⟩
    rw [deepSubdirState_nextDirId]; decide
  have hKeysD : VfsKeysComplete stDeep := deepSubdirKeys_complete 0o555 4096
  have hTsub : ∀ tsub, vfsTreeGet stDeep.tree ([] ++ [(EntryName.lit "d").val]) = some tsub →
      VfsTreeValidSegs tsub ∧ vfsTreePermWalkable' tsub ∧ ¬ VfsTreeWalkable 4096 tsub := by
    intro tsub hGet
    rw [deepSubdirState_tree] at hGet
    simp only [List.nil_append, EntryName.lit, vfsTreeGet, beq_self_eq_true, ↓reduceIte, Option.some.injEq] at hGet
    subst hGet
    exact ⟨deepSubdirTree_validSegs 0o555 4096, deepSubdirTree_permWalkable 4096, deepSubdirTree_not_walkable 4096 4096 (Nat.le_refl _)⟩
  have hAll2 := hDeepFn stDeep rootHandle [] (EntryName.lit "d") (deepSubdirState_lookup 0o555 4096) hInvD hKeysD
    (fun _ hm => by cases hm) (by decide) ⟨0o755, deepSubdirState_rootNode 0o555 4096, by decide, by decide⟩
    (deepSubdirState_childDir 0o555 4096) hTsub
  refine ⟨st, rootHandle, [], EntryName.lit "u", rfl, hInv, hKeys, (fun _ hm => by cases hm), (by decide),
    ⟨0o755, rfl, by decide, by decide⟩, rfl, a1, stDeep, rootHandle, [], EntryName.lit "d",
    deepSubdirState_lookup 0o555 4096, hInvD, hKeysD, (fun _ hm => by cases hm), (by decide),
    ⟨0o755, deepSubdirState_rootNode 0o555 4096, by decide, by decide⟩,
    deepSubdirState_childDir 0o555 4096, hTsub, ?_⟩
  cases hRun : StateT.run ((Internal.subtreeOpsM vfsDirOps rootHandle).walk { segments := [EntryName.lit "d"] }) stDeep with
  | mk rD stD' =>
    rw [hRun] at hAll2
    exact hAll2

private theorem stateBind_run {α β : Type} (x : StateM VfsState α) (f : α → StateM VfsState β) (s : VfsState) :
    (x >>= f) s = f (x s).1 (x s).2 := by
  change (match x s with | (a, s') => f a s') = f (x s).1 (x s).2
  cases x s; rfl

/-- `Internal.subtreeOpsM` satisfies `test_fs_subtree_withFileLock_releasesOnErrorAndTryLockWouldBlock`. -/
theorem proof_fs_subtree_withFileLock_releasesOnErrorAndTryLockWouldBlock :
    Core.AllPass (test_fs_subtree_withFileLock_releasesOnErrorAndTryLockWouldBlock Internal.subtreeOpsM) := by
  intro st dh pos leaf lockMode hLd _ hPar hFile hNoConf
  rcases hPar with ⟨pm, hParNd, hX⟩
  rcases hFile with ⟨fm, hFileNd⟩
  have hNoConfF : hasLockConflict st.locks (pathOfSegs (pos ++ [leaf.val])) lockMode = false := by
    cases hb : hasLockConflict st.locks (pathOfSegs (pos ++ [leaf.val])) lockMode with
    | false => rfl
    | true => simp [hb] at hNoConf
  have hXF : (pm / 64 % 2 == 0) = false := by rw [hX]; decide
  have hAcqOk : ∀ (nb : Bool), ∃ (lh : LockHandle) (st1 : VfsState),
      vfsDirOps.acquireLockAt dh leaf lockMode false nb st = (.ok lh, st1) ∧
        0 < lh.handleId ∧ (∀ l ∈ st.locks, l.1 < lh.handleId) ∧
        st1 = { st with locks := (lh.handleId, lh.path, lockMode) :: st.locks, nextLockId := lh.handleId } := by
    intro nb
    rcases vfsDirOps_acquireLockAt_tpl st dh leaf lockMode false nb with ⟨d, hEq⟩
    have hD := hEq
    unfold acquireLockAtTpl at hD
    rw [hLd] at hD; dsimp only at hD; rw [hParNd] at hD
    simp only [hXF, Bool.false_eq_true, ↓reduceIte, hFileNd, hNoConfF] at hD
    let id := max d st.nextLockId + 1
    let lh : LockHandle := { handleId := id, path := pathOfSegs (pos ++ [leaf.val]), mode := lockMode }
    let st1 : VfsState := { st with locks := (id, lh.path, lockMode) :: st.locks, nextLockId := id }
    rcases vfsDirOps_acquireLockAt_ok dh leaf lockMode false nb st lh st1 hD with ⟨hPos, _, hLt, _⟩
    exact ⟨lh, st1, hD, hPos, hLt, rfl⟩
  have hWflRun : ∃ stOut,
      ((Internal.subtreeOpsM vfsDirOps dh).withFileLock { segments := [leaf] } lockMode false
        (pure (.error { kind := .ioError, message := "callback aborted" } : Except FsError Unit))).run st =
        (.error { kind := .ioError, message := "callback aborted" }, stOut) ∧
      stOut.locks = st.locks ∧ stOut.openDirs = st.openDirs := by
    rcases hAcqOk false with ⟨lh, st1, hAcq, hPosLh, hLtLh, hSt1⟩
    have hRel : vfsDirOps.releaseLock lh st1 = (.ok (), { st1 with locks := st.locks }) := by
      rw [vfsDirOps_releaseLock_def, hSt1]
      have hNZ : (lh.handleId == 0) = false := beq_false_of_ne (Nat.ne_of_gt hPosLh)
      have hFilt : ((lh.handleId, lh.path, lockMode) :: st.locks).filter
          (fun l => l.1 != lh.handleId) = st.locks := by
        rw [List.filter_cons, bne_self_eq_false]
        simp only [Bool.false_eq_true, ↓reduceIte]
        rw [List.filter_eq_self]
        intro p hp
        simp only [bne_iff_ne, ne_eq]
        exact Nat.ne_of_lt (hLtLh p hp)
      simp only [hNZ, Bool.false_eq_true, ↓reduceIte, List.any_cons, beq_self_eq_true, Bool.true_or, hFilt]
    refine ⟨{ st1 with locks := st.locks }, ?_, by rw [hSt1], by rw [hSt1]⟩
    dsimp only [Internal.subtreeOpsM, StateT.run]
    rw [show Internal.splitLastAux [leaf] [] = some ([], leaf) from rfl]
    dsimp only
    rw [walkDescendM_nil_eq, stateBind_run, hAcq]
    dsimp only [Internal.bracketDirLockM, Bind.bind, StateT.bind, Pure.pure, StateT.pure, tryFinally']
    rw [hRel]
  have hTryOkRun : ∃ stOut,
      ((Internal.subtreeOpsM vfsDirOps dh).tryWithFileLock { segments := [leaf] } lockMode false
        (pure (.ok (42 : Nat)))).run st = (.ok (some (42 : Nat)), stOut) ∧
      stOut.locks = st.locks ∧ stOut.openDirs = st.openDirs := by
    rcases hAcqOk true with ⟨lh, st1, hAcq, hPosLh, hLtLh, hSt1⟩
    have hRel : vfsDirOps.releaseLock lh st1 = (.ok (), { st1 with locks := st.locks }) := by
      rw [vfsDirOps_releaseLock_def, hSt1]
      have hNZ : (lh.handleId == 0) = false := beq_false_of_ne (Nat.ne_of_gt hPosLh)
      have hFilt : ((lh.handleId, lh.path, lockMode) :: st.locks).filter
          (fun l => l.1 != lh.handleId) = st.locks := by
        rw [List.filter_cons, bne_self_eq_false]
        simp only [Bool.false_eq_true, ↓reduceIte]
        rw [List.filter_eq_self]
        intro p hp
        simp only [bne_iff_ne, ne_eq]
        exact Nat.ne_of_lt (hLtLh p hp)
      simp only [hNZ, Bool.false_eq_true, ↓reduceIte, List.any_cons, beq_self_eq_true, Bool.true_or, hFilt]
    refine ⟨{ st1 with locks := st.locks }, ?_, by rw [hSt1], by rw [hSt1]⟩
    dsimp only [Internal.subtreeOpsM, StateT.run]
    rw [show Internal.splitLastAux [leaf] [] = some ([], leaf) from rfl]
    dsimp only
    rw [walkDescendM_nil_eq, stateBind_run, hAcq]
    dsimp only [Internal.bracketDirLockM, Bind.bind, StateT.bind, Pure.pure, StateT.pure, tryFinally']
    rw [hRel]
    rfl
  refine ⟨?_, ?_, ?_, trivial⟩
  · rcases hWflRun with ⟨stOut, hEq, hL, hO⟩
    change (match ((Internal.subtreeOpsM vfsDirOps dh).withFileLock { segments := [leaf] } lockMode false
          (pure (.error { kind := .ioError, message := "callback aborted" } : Except FsError Unit))).run st with
      | (r, s) => r = .error { kind := .ioError, message := "callback aborted" } ∧ s.locks = st.locks ∧ s.openDirs = st.openDirs)
    rw [hEq]; exact ⟨rfl, hL, hO⟩
  · rcases hTryOkRun with ⟨stOut, hEq, hL, hO⟩
    change (match ((Internal.subtreeOpsM vfsDirOps dh).tryWithFileLock { segments := [leaf] } lockMode false
          (pure (.ok (42 : Nat)))).run st with
      | (r, s) => r = .ok (some (42 : Nat)) ∧ s.locks = st.locks ∧ s.openDirs = st.openDirs)
    rw [hEq]; exact ⟨rfl, hL, hO⟩
  · let contendedSt : VfsState :=
      { st with locks := (st.nextLockId, pathOfSegs (pos ++ [leaf.val]), .exclusive) :: st.locks, nextLockId := st.nextLockId + 1 }
    have hCont : hasLockConflict contendedSt.locks (pathOfSegs (pos ++ [leaf.val])) lockMode = true := by
      unfold hasLockConflict
      simp only [contendedSt, List.any_cons, beq_self_eq_true, Bool.true_and, Bool.or_eq_true]
      exact Or.inl (by cases lockMode <;> decide)
    have hAcqErr : vfsDirOps.acquireLockAt dh leaf lockMode false true contendedSt =
        (.error { kind := .wouldBlock, path := some leaf.val, message := "resource temporarily unavailable" }, contendedSt) := by
      rcases vfsDirOps_acquireLockAt_tpl contendedSt dh leaf lockMode false true with ⟨d, hEq⟩
      rw [hEq]; unfold acquireLockAtTpl
      have hLdC : lookupDir contendedSt dh = some pos := hLd
      have hParC : nodeAt contendedSt.tree pos = some (.dir pm) := hParNd
      have hFileC : nodeAt contendedSt.tree (pos ++ [leaf.val]) = some (.file ByteArray.empty fm) := hFileNd
      rw [hLdC]; dsimp only; rw [hParC]; simp only [hXF, Bool.false_eq_true, ↓reduceIte, hFileC, hCont, ↓reduceIte]
    have hTryRun : ((Internal.subtreeOpsM vfsDirOps dh).tryWithFileLock { segments := [leaf] } lockMode false
          (pure (.error { kind := .ioError, message := "callback aborted" } : Except FsError Unit))).run contendedSt =
        (.ok none, contendedSt) := by
      dsimp only [Internal.subtreeOpsM, StateT.run]
      rw [show Internal.splitLastAux [leaf] [] = some ([], leaf) from rfl]
      dsimp only
      rw [walkDescendM_nil_eq, stateBind_run, hAcqErr]
      simp only [show (FsErrorKind.wouldBlock == FsErrorKind.wouldBlock) = true from rfl, ↓reduceIte]
      rfl
    change (match ((Internal.subtreeOpsM vfsDirOps dh).tryWithFileLock { segments := [leaf] } lockMode false
          (pure (.error { kind := .ioError, message := "callback aborted" } : Except FsError Unit))).run contendedSt with
      | (rTry, stTry) => rTry = .ok none ∧ stTry.locks = contendedSt.locks ∧ stTry.openDirs = contendedSt.openDirs)
    rw [hTryRun]
    exact ⟨rfl, rfl, rfl⟩

/-- Witness check for `test_fs_subtree_withFileLock_releasesOnErrorAndTryLockWouldBlock`. -/
theorem reach_fs_subtree_withFileLock_releasesOnErrorAndTryLockWouldBlock :
    Core.CanReach (test_fs_subtree_withFileLock_releasesOnErrorAndTryLockWouldBlock Internal.subtreeOpsM) := by
  let st := stateWithRootHandle (fun s => if s == "f" then some (.file ByteArray.empty 0o644) else none) ["/", "/f"]
  have hInv : DirHandleInvariant st := fun _ _ hm => by
    simp [st, stateWithRootHandle] at hm; rcases hm with ⟨rfl, rfl⟩; decide
  have hAll := proof_fs_subtree_withFileLock_releasesOnErrorAndTryLockWouldBlock st rootHandle []
    (EntryName.lit "f") .exclusive rfl hInv ⟨0o755, rfl, by decide⟩ ⟨0o644, rfl⟩ (by decide)
  exact ⟨st, rootHandle, [], EntryName.lit "f", .exclusive, rfl, hInv, ⟨0o755, rfl, by decide⟩,
    ⟨0o644, rfl⟩, (by decide), hAll⟩

/-- `Internal.subtreeOpsM` satisfies `test_fs_subtree_closedHandle_refusesAllOps`. -/
theorem proof_fs_subtree_closedHandle_refusesAllOps :
    Core.AllPass (test_fs_subtree_closedHandle_refusesAllOps Internal.subtreeOpsM) := by
  intro st dh child bytes lockMode b1 b2 hClosed
  have hFstat : vfsDirOps.fstatDir dh st = (.error (mInvalidDirHandleErr dh), st) := by
    rw [vfsDirOps_fstatDir_def, hClosed]
  have hRead : vfsDirOps.readRegularAt dh child st = (.error (mInvalidDirHandleErr dh), st) := by
    rw [vfsDirOps_readRegularAt_def, hClosed]
  have hReadDir : vfsDirOps.readDirAt dh st = (.error (mInvalidDirHandleErr dh), st) := by
    rw [vfsDirOps_readDirAt_def, hClosed]
  have hLstat : vfsDirOps.lstatAt dh child st = (.error (mInvalidDirHandleErr dh), st) := by
    rw [vfsDirOps_lstatAt_def, hClosed]
  have hUnlinkF : vfsDirOps.unlinkAt dh child false st = (.error (mInvalidDirHandleErr dh), st) := by
    rw [vfsDirOps_unlinkAt_def, hClosed]
  have hUnlinkT : vfsDirOps.unlinkAt dh child true st = (.error (mInvalidDirHandleErr dh), st) := by
    rw [vfsDirOps_unlinkAt_def, hClosed]
  have hSym : vfsDirOps.symlinkAt "t" dh child st = (.error (mInvalidDirHandleErr dh), st) := by
    rw [vfsDirOps_symlinkAt_def, hClosed]
    simp only [show ("t".isEmpty || "t".toList.contains (Char.ofNat 0)) = false from by decide,
      Bool.false_eq_true, ↓reduceIte]
  have hAcqF : vfsDirOps.acquireLockAt dh child lockMode b1 false st = (.error (mInvalidDirHandleErr dh), st) :=
    vfsDirOps_acquireLockAt_none st dh child lockMode b1 false hClosed
  have hAcqT : vfsDirOps.acquireLockAt dh child lockMode b1 true st = (.error (mInvalidDirHandleErr dh), st) :=
    vfsDirOps_acquireLockAt_none st dh child lockMode b1 true hClosed
  have hWalkErr : ∃ e st', Internal.walkRecM vfsDirOps dh [] "." #[] 4096 st = (.error e, st') ∧
      e.kind = .invalidInput ∧ st'.nodes = st.nodes := by
    rw [show (4096 : Nat) = Nat.succ 4095 from rfl, Internal.walkRecM.eq_2]
    dsimp only [Bind.bind, StateT.bind]
    rw [walkDescendM_nil_eq]
    dsimp only [Bind.bind, StateT.bind]
    rw [hReadDir]
    exact ⟨mInvalidDirHandleErr dh, st, rfl, rfl, rfl⟩
  rcases hWalkErr with ⟨ew, stw, hWalkRes, hKindW, hNodesW⟩
  have hAwClosed : ∃ st1, Internal.atomicWriteAtAuxM vfsDirOps dh child bytes 16 st =
      (.error (mInvalidDirHandleErr dh), st1) ∧ st1.nodes = st.nodes := by
    rw [show (16 : Nat) = 15 + 1 from rfl, Internal.atomicWriteAtAuxM.eq_2]
    cases hFr : vfsDirOps.freshTempName st with
    | mk tmp st1 =>
      have hFrDef := vfsDirOps_freshTempName_def st
      rw [hFr] at hFrDef
      dsimp only at hFrDef
      rcases hFrDef with ⟨_, hSt1⟩
      have hClosed1 : lookupDir st1 dh = none := by rw [hSt1]; exact hClosed
      have hCf1 : vfsDirOps.createFileAt dh tmp bytes st1 = (.error (mInvalidDirHandleErr dh), st1) := by
        rw [vfsDirOps_createFileAt_def, hClosed1]
      refine ⟨st1, ?_, nodes_eq_of_tree_eq' (by rw [hSt1])⟩
      rw [stateBind_run, hFr]
      dsimp only
      rw [stateBind_run, hCf1]
      rfl
  have hSymCond : ("t".isEmpty || decide (Char.ofNat 0 ∈ "t".toList)) = false := by decide
  have hSymClosed :
      (if ("t".isEmpty || decide (Char.ofNat 0 ∈ "t".toList)) = true then
        pure (.error { kind := .invalidInput, path := some "t", message := "invalid symlink target" })
       else vfsDirOps.symlinkAt "t" dh child) st =
        (.error (mInvalidDirHandleErr dh), st) := by
    simp only [hSymCond, Bool.false_eq_true, ↓reduceIte, hSym]
  rcases hAwClosed with ⟨stAw, hAwEq, hAwNodes⟩
  dsimp only [Internal.subtreeOpsM, StateT.run]
  rw [show Internal.splitLastAux RelPath.root.segments [] = none from rfl,
    show Internal.splitLastAux [child] [] = some ([], child) from rfl,
    show RelPath.root.segments = [] from rfl]
  simp only [walkDescendM_nil_eq]
  rw [hAwEq, hSymClosed, hWalkRes]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, trivial⟩
  · simp only [hFstat]; exact ⟨⟨_, rfl, rfl⟩, trivial⟩
  · simp only [hRead]; exact ⟨⟨_, rfl, rfl⟩, trivial⟩
  · exact ⟨⟨_, rfl, rfl⟩, hAwNodes⟩
  · simp only [hFstat]; exact ⟨⟨_, rfl, rfl⟩, rfl⟩
  · simp only [hUnlinkF]
    cases b1 <;> simp [show (FsErrorKind.invalidInput == FsErrorKind.notFound) = false from rfl, Pure.pure, StateT.pure]
  · simp only [hUnlinkT]; exact ⟨⟨_, rfl, rfl⟩, trivial⟩
  · simp only [hLstat]
    cases b1 <;> simp [show (FsErrorKind.invalidInput == FsErrorKind.notFound) = false from rfl, Pure.pure, StateT.pure]
  · exact ⟨⟨_, rfl, rfl⟩, rfl⟩
  · try rw [walkDescendAuxM_nil]
    simp only [hReadDir]; exact ⟨⟨_, rfl, rfl⟩, rfl⟩
  · exact ⟨⟨ew, rfl, hKindW⟩, hNodesW⟩
  · simp only [hAcqF]; exact ⟨⟨_, rfl, rfl⟩, rfl, rfl⟩
  · simp only [hAcqT]
    simp only [show (FsErrorKind.invalidInput == FsErrorKind.wouldBlock) = false from rfl, Bool.false_eq_true, ↓reduceIte,
      Pure.pure, StateT.pure]
    exact ⟨⟨_, rfl, rfl⟩, trivial, trivial⟩

/-- Witness check for `test_fs_subtree_closedHandle_refusesAllOps`. -/
theorem reach_fs_subtree_closedHandle_refusesAllOps :
    Core.CanReach (test_fs_subtree_closedHandle_refusesAllOps Internal.subtreeOpsM) := by
  let dh0 : DirHandle := { handleId := 0, rootPath := "/" }
  have hAll := proof_fs_subtree_closedHandle_refusesAllOps emptyVfsState dh0 (EntryName.lit "c")
    ByteArray.empty .exclusive false false rfl
  exact ⟨emptyVfsState, dh0, EntryName.lit "c", ByteArray.empty, .exclusive, false, false, rfl, hAll⟩

end LeanSwe.Fs.Proofs