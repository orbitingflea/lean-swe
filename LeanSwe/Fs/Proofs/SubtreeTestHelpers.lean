import LeanSwe.Fs.Proofs.SubtreeModelSpecs

namespace LeanSwe.Fs.Proofs

open Core LeanSwe.Fs LeanSwe.Fs.Raw LeanSwe.Fs.Model

/-- Empty VFS state rooted at `"/"` with no open handles. -/
def emptyVfsState : VfsState :=
  { tree := vfsEmptyDir 0o755
    keys := ["/"]
    cwd := "/"
    nonce := 0
    locks := []
    nextLockId := 1
    openDirs := []
    nextDirId := 1 }

/-- Default open root directory handle `{ handleId := 1, rootPath := "/" }`. -/
def rootHandle : DirHandle :=
  { handleId := 1, rootPath := "/" }

/-- VFS state rooted at `"/"` with `rootHandle` open and custom root children. -/
def stateWithRootHandle (rootChildren : String → Option VfsTree) (keys : List String := ["/"]) : VfsState :=
  { tree := .dir 0o755 rootChildren
    keys := keys
    cwd := "/"
    nonce := 0
    locks := []
    nextLockId := 1
    openDirs := [(1, [])]
    nextDirId := 2 }

/-- Fixed 51-byte `'a'` string for constructing 255-byte valid entry names. -/
def s51 : String :=
  "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"

/-- Fixed 255-byte `'a'` string for max-segment tests. -/
def str255 : String :=
  s51 ++ s51 ++ s51 ++ s51 ++ s51

/-- Proof that `str255` is a valid path segment. -/
theorem str255_valid : validSeg str255 = true := by
  have h1 : s51 ≠ "" := by decide
  have h2 : '/' ∉ s51.toList := by decide
  have h3 : Char.ofNat 0 ∉ s51.toList := by decide
  have hl : s51.toList.length = 51 := by decide
  have hneDot : s51.toList ++ (s51.toList ++ (s51.toList ++ (s51.toList ++ s51.toList))) ≠ ['.'] := by
    intro he; have hc := congrArg List.length he; simp [hl] at hc
  have hneDotDot : s51.toList ++ (s51.toList ++ (s51.toList ++ (s51.toList ++ s51.toList))) ≠ ['.', '.'] := by
    intro he; have hc := congrArg List.length he; simp [hl] at hc
  simpa [validSeg, str255, String.toList_append, List.append_assoc] using
    ⟨⟨⟨⟨h1, h2⟩, h3⟩, hneDot⟩, hneDotDot⟩

/-- Proof that `str255.utf8ByteSize = 255`. -/
theorem str255_utf8ByteSize : str255.utf8ByteSize = 255 := by
  have h51 : s51.utf8ByteSize = 51 := by decide
  simp [str255, String.utf8ByteSize_append, h51]

/-- Max-length 255-byte `EntryName`. -/
def maxName255 : EntryName :=
  { val := str255, valid := str255_valid }

/-- Stub `SubtreeM` used in non-vacuity checks. -/
def stubSubtreeTest : SubtreeM (StateM VfsState) :=
  { lstat := fun _ => pure (.error { kind := .notFound, message := "stub" })
    readRegular := fun _ => pure (.error { kind := .notFound, message := "stub" })
    atomicWriteBytes := fun _ _ => pure (.error { kind := .notFound, message := "stub" })
    mkdir := fun _ _ _ => pure (.error { kind := .notFound, message := "stub" })
    unlink := fun _ _ => pure (.error { kind := .notFound, message := "stub" })
    rmdir := fun _ => pure (.error { kind := .notFound, message := "stub" })
    rmtree := fun _ _ => pure (.error { kind := .notFound, message := "stub" })
    symlink := fun _ _ => pure (.error { kind := .notFound, message := "stub" })
    listDir := fun _ => pure (.error { kind := .notFound, message := "stub" })
    walk := fun _ => pure (.error { kind := .notFound, message := "stub" })
    withFileLock := fun _ _ _ _ => pure (.error { kind := .notFound, message := "stub" })
    tryWithFileLock := fun _ _ _ _ => pure (.error { kind := .notFound, message := "stub" }) }

/-- Sortedness predicate matching `SpecTests.walkEntrySorted`. -/
def walkEntrySorted' (e : WalkEntry) : Prop :=
  List.Pairwise (fun a b => a < b) e.dirs.toList ∧ List.Pairwise (fun a b => a < b) e.files.toList

/-- Walkable permission predicate matching `SpecTests.vfsTreePermWalkable`. -/
def vfsTreePermWalkable' (t : VfsTree) : Prop :=
  ∀ (segs : List String) (m : Nat), nodeAt t segs = some (.dir m) →
    (m / 256) % 2 = 1 ∧ (m / 64) % 2 = 1

/-- Removable permission predicate matching `SpecTests.vfsTreePermRemovable`. -/
def vfsTreePermRemovable' (t : VfsTree) : Prop :=
  ∀ (segs : List String) (m : Nat), nodeAt t segs = some (.dir m) →
    (m / 256) % 2 = 1 ∧ (m / 128) % 2 = 1 ∧ (m / 64) % 2 = 1

/-- Two `VfsState` values with equal `tree` have identical `nodes` maps. -/
theorem nodes_eq_of_tree_eq' {s1 s2 : VfsState} (h : s1.tree = s2.tree) : s1.nodes = s2.nodes := by
  funext p
  simp [VfsState.nodes, h]

/-- `openDir` template parameterized by base max directory id. -/
noncomputable def openDirTpl (st : VfsState) (root : String) (d : Nat) :
    Except FsError DirHandle × VfsState :=
  if !isValidRawPath root then
    (.error { kind := .invalidInput, path := some root, message := s!"invalid path: {root}" }, st)
  else
    let abs := vfsAbsNorm st.cwd root
    match vfsResolveSegs st.nodes "/" (vfsSplitSegs abs) true 1024 with
    | .error e => (.error e, st)
    | .ok (canon, .dir mode) =>
      if (mode / 256) % 2 == 0 then
        (.error { kind := .permissionDenied, path := some root, message := s!"permission denied: {root}" }, st)
      else
        let id := max d st.nextDirId + 1
        (.ok { handleId := id, rootPath := root },
          { st with openDirs := (id, vfsSplitSegs canon) :: st.openDirs, nextDirId := id + 1 })
    | .ok (_, _) =>
      (.error { kind := .notADirectory, path := some root, message := s!"not a directory: {root}" }, st)

/-- Existential template equivalence for `vfsDirOps.openDir`. -/
theorem vfsDirOps_openDir_tpl (st : VfsState) (root : String) :
    ∃ d : Nat, vfsDirOps.openDir root st = openDirTpl st root d := ⟨_, rfl⟩

/-- `acquireLockAt` template parameterized by base max lock id. -/
noncomputable def acquireLockAtTpl (st : VfsState) (dh : DirHandle) (name : EntryName)
    (mode : LockMode) (createIfMissing : Bool) (d : Nat) :
    Except FsError LockHandle × VfsState :=
  match lookupDir st dh with
  | none => (.error (mInvalidDirHandleErr dh), st)
  | some pos =>
    match nodeAt st.tree pos with
    | none => (.error { kind := .notFound, path := some dh.rootPath, message := "directory no longer exists" }, st)
    | some (.dir parMode) =>
      if (parMode / 64) % 2 == 0 then
        (.error { kind := .permissionDenied, path := some name.val, message := s!"permission denied: {name.val}" }, st)
      else
        let childPos := pos ++ [name.val]
        let childCanon := pathOfSegs childPos
        match nodeAt st.tree childPos with
        | some (.file _ _) =>
          if hasLockConflict st.locks childCanon mode then
            (.error { kind := .wouldBlock, path := some name.val, message := "resource temporarily unavailable" }, st)
          else
            let id := max d st.nextLockId + 1
            (.ok { handleId := id, path := childCanon, mode := mode },
              { st with locks := (id, childCanon, mode) :: st.locks, nextLockId := id })
        | some (.dir _) =>
          (.error { kind := .isADirectory, path := some name.val, message := s!"is a directory: {name.val}" }, st)
        | some (.symlink _ _) =>
          (.error { kind := .invalidInput, path := some name.val, message := s!"symlink rejected for lock: {name.val}" }, st)
        | none =>
          if !createIfMissing then
            (.error { kind := .notFound, path := some name.val, message := s!"no such file or directory: {name.val}" }, st)
          else if (parMode / 128) % 2 == 0 then
            (.error { kind := .permissionDenied, path := some name.val, message := s!"permission denied: {name.val}" }, st)
          else if hasLockConflict st.locks childCanon mode then
            (.error { kind := .wouldBlock, path := some name.val, message := "resource temporarily unavailable" }, st)
          else
            let id := max d st.nextLockId + 1
            (.ok { handleId := id, path := childCanon, mode := mode },
              { st with
                tree := vfsTreeSet st.tree childPos (some (.file ByteArray.empty 0o644))
                keys := childCanon :: st.keys
                locks := (id, childCanon, mode) :: st.locks
                nextLockId := id })
    | some _ => (.error { kind := .notADirectory, path := some dh.rootPath, message := s!"not a directory: {dh.rootPath}" }, st)

/-- Existential template equivalence for `vfsDirOps.acquireLockAt`. -/
theorem vfsDirOps_acquireLockAt_tpl (st : VfsState) (dh : DirHandle) (name : EntryName)
    (mode : LockMode) (createIfMissing nonBlocking : Bool) :
    ∃ d : Nat, vfsDirOps.acquireLockAt dh name mode createIfMissing nonBlocking st =
      acquireLockAtTpl st dh name mode createIfMissing d := ⟨_, rfl⟩

/-- If every open entry of `st2` comes from `st1` and `nextDirId` matches, `DirHandleInvariant` transfers. -/
theorem dirHandleInvariant_of_subset {st1 st2 : VfsState} (hInv : DirHandleInvariant st1)
    (hSub : ∀ p ∈ st2.openDirs, p ∈ st1.openDirs) (hNext : st2.nextDirId = st1.nextDirId) :
    DirHandleInvariant st2 :=
  fun id p hm => let h := hInv id p (hSub (id, p) hm); ⟨h.1, hNext ▸ h.2⟩

private theorem str_lt_irrefl {s : String} (h : s < s) : False :=
  let hIff := (Std.LawfulOrderLT.lt_iff s s).mp h
  hIff.2 hIff.1

private theorem str_lt_asymm {a b : String} (h1 : a < b) (h2 : b < a) : False :=
  let ha := (Std.LawfulOrderLT.lt_iff a b).mp h1
  let hb := (Std.LawfulOrderLT.lt_iff b a).mp h2
  hb.2 ha.1

/-- Sorting a duplicate-free list whose every element is `a` or `b` with `a.val < b.val` yields `[a, b]`. -/
theorem sorted_pair_eq (a b : EntryName) (xs : List EntryName) (hNodup : xs.Nodup)
    (ha : a ∈ xs) (hb : b ∈ xs) (hab : a.val < b.val) (hOnly : ∀ x ∈ xs, x = a ∨ x = b) :
    Internal.sortEntryNames xs.toArray = [a, b] := by
  have hPerm := List.mergeSort_perm xs (fun x y : EntryName => decide (x.val ≤ y.val))
  have hStrict := list_mergeSort_entryName_strict hNodup
  have hNd : (xs.mergeSort (fun x y : EntryName => decide (x.val ≤ y.val))).Nodup := hPerm.nodup_iff.mpr hNodup
  have haM := hPerm.mem_iff.mpr ha
  have hbM := hPerm.mem_iff.mpr hb
  have hOnlyM : ∀ x ∈ xs.mergeSort (fun x y : EntryName => decide (x.val ≤ y.val)), x = a ∨ x = b :=
    fun x hx => hOnly x (hPerm.mem_iff.mp hx)
  change xs.mergeSort (fun x y : EntryName => decide (x.val ≤ y.val)) = [a, b]
  cases hS : xs.mergeSort (fun x y : EntryName => decide (x.val ≤ y.val)) with
  | nil => rw [hS] at haM; cases haM
  | cons x rest =>
    cases rest with
    | nil =>
      rw [hS] at haM hbM
      rcases List.mem_singleton.mp haM with rfl
      rcases List.mem_singleton.mp hbM with hEq
      rw [hEq] at hab
      exact False.elim (str_lt_irrefl hab)
    | cons y rest2 =>
      cases rest2 with
      | nil =>
        rw [hS, List.pairwise_cons] at hStrict
        have hXY : x.val < y.val := hStrict.1 y List.mem_cons_self
        have hOx := hOnlyM x (by rw [hS]; exact List.mem_cons_self)
        have hOy := hOnlyM y (by rw [hS]; exact List.mem_cons_of_mem _ List.mem_cons_self)
        rcases hOx with rfl | rfl <;> rcases hOy with rfl | rfl
        · exact False.elim (str_lt_irrefl hXY)
        · rfl
        · exact False.elim (str_lt_asymm hab hXY)
        · exact False.elim (str_lt_irrefl hXY)
      | cons z _ =>
        rw [hS] at hOnlyM hNd
        have hOx := hOnlyM x List.mem_cons_self
        have hOy := hOnlyM y (List.mem_cons_of_mem _ List.mem_cons_self)
        have hOz := hOnlyM z (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))
        rw [List.nodup_cons] at hNd
        have hNdY := (List.nodup_cons.mp hNd.2)
        rcases hOx with rfl | rfl <;> rcases hOy with rfl | rfl <;> rcases hOz with rfl | rfl
        · exact absurd List.mem_cons_self hNd.1
        · exact absurd List.mem_cons_self hNd.1
        · exact absurd (List.mem_cons_of_mem _ List.mem_cons_self) hNd.1
        · exact absurd List.mem_cons_self hNdY.1
        · exact absurd List.mem_cons_self hNdY.1
        · exact absurd (List.mem_cons_of_mem _ List.mem_cons_self) hNd.1
        · exact absurd List.mem_cons_self hNd.1
        · exact absurd List.mem_cons_self hNd.1

/-- When all ancestor segments already exist as readable/executable directories, `mkdirWalkM` matches `walkDescendAuxM`. -/
theorem mkdirWalkM_eq_walkDescendAuxM :
    ∀ (segs : List EntryName) (isRoot : Bool) (cur : DirHandle) (pos : List String)
      (act : DirHandle → StateM VfsState (Except FsError Unit)) (st : VfsState),
      lookupDir st cur = some pos →
      (∀ k < segs.length, ∃ dm, nodeAt st.tree (pos ++ (segs.take k).map (·.val)) = some (.dir dm) ∧
        (0 < k → dm / 256 % 2 = 1) ∧ dm / 64 % 2 = 1) →
      (segs ≠ [] → ∃ dm, nodeAt st.tree (pos ++ segs.map (·.val)) = some (.dir dm) ∧
        dm / 256 % 2 = 1) →
      Internal.mkdirWalkM vfsDirOps isRoot cur segs act st =
        Internal.walkDescendAuxM vfsDirOps isRoot cur segs act st := by
  intro segs
  induction segs with
  | nil =>
    intro isRoot cur pos act st _ _ _
    rw [mkdirWalkM_nil, walkDescendAuxM_nil]
  | cons s rest ih =>
    intro isRoot cur pos act st hLd hAnc hLeaf
    rcases hAnc 0 (Nat.zero_lt_succ _) with ⟨parM, hPar, _, hParX⟩
    simp only [List.take_zero, List.map_nil, List.append_nil] at hPar
    have hChild : ∃ dm, nodeAt st.tree (pos ++ [s.val]) = some (.dir dm) ∧ dm / 256 % 2 = 1 := by
      cases rest with
      | nil =>
        rcases hLeaf (List.cons_ne_nil _ _) with ⟨dm, hD, hDR⟩
        exact ⟨dm, by simpa using hD, hDR⟩
      | cons r rs =>
        rcases hAnc 1 (by simp) with ⟨dm, hD, hDR, _⟩
        exact ⟨dm, by simpa [List.take] using hD, hDR (by omega)⟩
    rcases hChild with ⟨dm, hChildNd, hChildR⟩
    rcases vfsDirOps_openDirAt_dir_ok st cur s pos parM dm hLd hPar hParX hChildNd hChildR with
      ⟨nextDh, st1, hOpenOk⟩
    rcases vfsDirOps_openDirAt_ok cur s st nextDh st1 hOpenOk with
      ⟨hNextPos, _, hNextGt, pos', _, _, hLd', _, _, _, _, _, hSt1⟩
    rcases Option.some.inj (hLd.symm.trans hLd') with rfl
    have hNextNeCur : nextDh.handleId ≠ cur.handleId := by
      unfold lookupDir at hLd
      cases hZ : (cur.handleId == 0) with
      | true => simp [hZ] at hLd
      | false =>
        simp only [hZ, Bool.false_eq_true, ↓reduceIte, Option.map_eq_some_iff] at hLd
        rcases hLd with ⟨p, hFind, _⟩
        have hEqId : p.1 = cur.handleId := by simpa using List.find?_some hFind
        have hLt := hNextGt p (List.mem_of_find?_eq_some hFind)
        omega
    rw [mkdirWalkM_cons, walkDescendAuxM_cons]
    have hRecAux : ∀ (stM : VfsState),
        stM.tree = st.tree → lookupDir stM nextDh = some (pos ++ [s.val]) →
        Internal.mkdirWalkM vfsDirOps false nextDh rest act stM =
          Internal.walkDescendAuxM vfsDirOps false nextDh rest act stM := by
      intro stM hTreeM hLdM
      refine ih false nextDh (pos ++ [s.val]) act stM hLdM ?_ ?_
      · intro k hk
        rcases hAnc (k + 1) (Nat.succ_lt_succ hk) with ⟨dk, hDk, hDkR, hDkX⟩
        refine ⟨dk, ?_, fun _ => hDkR (Nat.zero_lt_succ k), hDkX⟩
        rw [hTreeM]
        simpa [List.take, List.append_assoc] using hDk
      · intro _
        rcases hLeaf (List.cons_ne_nil _ _) with ⟨dl, hDl, hDlR⟩
        refine ⟨dl, ?_, hDlR⟩
        rw [hTreeM]
        simpa [List.append_assoc] using hDl
    cases isRoot with
    | true =>
      simp only [↓reduceIte, Bind.bind, StateT.bind, hOpenOk]
      have hLd1 : lookupDir st1 nextDh = some (pos ++ [s.val]) := by
        rw [hSt1]
        exact lookupDir_cons_self st nextDh.handleId (pos ++ [s.val]) nextDh.rootPath hNextPos
      exact hRecAux st1 (by rw [hSt1]) hLd1
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte, Bind.bind, StateT.bind]
      rw [bracketCloseDirM_run, bracketCloseDirM_run]
      simp only [Bind.bind, StateT.bind, Pure.pure, hOpenOk]
      rw [show (StateT.pure (Except.ok nextDh) st1 : Id (Except FsError DirHandle × VfsState)) = (Except.ok nextDh, st1) from rfl]
      cases hCl : vfsDirOps.closeDir cur st1 with
      | mk rCl stCl =>
        have hClTree : stCl.tree = st.tree := by
          rw [vfsDirOps_closeDir_def] at hCl
          split at hCl
          · cases hCl; rw [hSt1]
          · split at hCl
            · cases hCl; rw [hSt1]
            · cases hCl; rw [hSt1]
        have hLdCl : lookupDir stCl nextDh = some (pos ++ [s.val]) := by
          rw [vfsDirOps_closeDir_def] at hCl
          split at hCl
          · cases hCl; rw [hSt1]; exact lookupDir_cons_self st nextDh.handleId (pos ++ [s.val]) nextDh.rootPath hNextPos
          · split at hCl
            · cases hCl
              rw [lookupDir_erase_ne st1 cur nextDh hNextNeCur, hSt1]
              exact lookupDir_cons_self st nextDh.handleId (pos ++ [s.val]) nextDh.rootPath hNextPos
            · cases hCl; rw [hSt1]; exact lookupDir_cons_self st nextDh.handleId (pos ++ [s.val]) nextDh.rootPath hNextPos
        dsimp only
        exact hRecAux stCl hClTree hLdCl

/-- When all `attempts` candidate temp names collide (`≠ none`), `atomicWriteAtAuxM` fails `.alreadyExists` without mutating `tree` or `openDirs`. -/
theorem atomicWriteAtAuxM_exhausted (parDh : DirHandle) (parentPos : List String)
    (leaf : EntryName) (bytes : ByteArray) :
    ∀ (attempts : Nat) (st : VfsState) (pm : Nat),
      0 < attempts →
      lookupDir st parDh = some parentPos →
      nodeAt st.tree parentPos = some (.dir pm) →
      pm / 128 % 2 = 1 →
      pm / 64 % 2 = 1 →
      (∀ k < attempts, nodeAt st.tree (parentPos ++ [".t." ++ toString (st.nonce + k)]) ≠ none) →
      ∃ e st', Internal.atomicWriteAtAuxM vfsDirOps parDh leaf bytes attempts st = (.error e, st') ∧
        e.kind = .alreadyExists ∧ st'.tree = st.tree ∧ st'.openDirs = st.openDirs := by
  intro attempts
  induction attempts with
  | zero => intro _ _ h; omega
  | succ n ih =>
    intro st pm _ hLd hPar hW hX hAll
    rw [atomicWriteAtAuxM_succ]
    simp only [Bind.bind, StateT.bind, Pure.pure]
    rcases vfsDirOps_freshTempName_def st with ⟨hTmpVal, hTmpSt⟩
    cases hTmpRes : vfsDirOps.freshTempName st with
    | mk tmp st1 =>
      rw [hTmpRes] at hTmpVal hTmpSt
      dsimp only at hTmpVal hTmpSt ⊢
      have hTmpNe : nodeAt st1.tree (parentPos ++ [tmp.val]) ≠ none := by
        rw [hTmpSt, hTmpVal]
        simpa using hAll 0 (Nat.zero_lt_succ n)
      have hLd1 : lookupDir st1 parDh = some parentPos := by rw [hTmpSt]; exact hLd
      have hPar1 : nodeAt st1.tree parentPos = some (.dir pm) := by rw [hTmpSt]; exact hPar
      have hWXF : (pm / 128 % 2 == 0 || pm / 64 % 2 == 0) = false := by simp [hW, hX]
      cases hExNode : nodeAt st1.tree (parentPos ++ [tmp.val]) with
      | none => exact absurd hExNode hTmpNe
      | some nd =>
        have hCreate : vfsDirOps.createFileAt parDh tmp bytes st1 =
            (.error { kind := .alreadyExists, path := some tmp.val, message := s!"already exists: {tmp.val}" }, st1) := by
          rw [vfsDirOps_createFileAt_def, hLd1]
          dsimp only
          rw [hPar1]
          simp only [hWXF, Bool.false_eq_true, ↓reduceIte, hExNode]
        rw [hCreate]
        dsimp only
        cases n with
        | zero =>
          simp only [show (FsErrorKind.alreadyExists == FsErrorKind.alreadyExists) = true from rfl,
            show decide (0 > 0) = false from rfl, Bool.and_false, Bool.false_eq_true, ↓reduceIte]
          exact ⟨_, st1, rfl, rfl, by rw [hTmpSt], by rw [hTmpSt]⟩
        | succ m =>
          simp only [show (FsErrorKind.alreadyExists == FsErrorKind.alreadyExists) = true from rfl,
            show decide (m.succ > 0) = true from rfl, Bool.and_true, ↓reduceIte]
          have hAllNext : ∀ k < m + 1, nodeAt st1.tree (parentPos ++ [".t." ++ toString (st1.nonce + k)]) ≠ none := by
            intro k hk
            rw [hTmpSt]
            dsimp only
            rw [show st.nonce + 1 + k = st.nonce + (k + 1) from by omega]
            exact hAll (k + 1) (Nat.succ_lt_succ hk)
          rcases ih st1 pm (Nat.zero_lt_succ m) hLd1 hPar1 hW hX hAllNext with ⟨e, st', hRec, hKind, hTree, hOpen⟩
          exact ⟨e, st', hRec, hKind, hTree.trans (by rw [hTmpSt]), hOpen.trans (by rw [hTmpSt])⟩

/-- Directory predicate used when classifying sorted directory entries. -/
def isDirAt (st : VfsState) (dirPos : List String) (n : EntryName) : Bool :=
  match nodeAt st.tree (dirPos ++ [n.val]) with
  | some (.dir _) => true
  | _ => false

/-- `classifyChildrenM` splits `items` cleanly into directories and non-directories without mutating state. -/
theorem classifyChildrenM_ok (dirDh : DirHandle) (dirPos : List String) (st : VfsState) (pm : Nat)
    (hLd : lookupDir st dirDh = some dirPos)
    (hDir : nodeAt st.tree dirPos = some (.dir pm))
    (hX : pm / 64 % 2 = 1) :
    ∀ (items dirsAcc : List EntryName) (filesAcc : List String),
      (∀ n ∈ items, nodeAt st.tree (dirPos ++ [n.val]) ≠ none) →
      Internal.classifyChildrenM vfsDirOps dirDh items dirsAcc filesAcc st =
        (.ok (dirsAcc.reverse ++ items.filter (isDirAt st dirPos),
              filesAcc.reverse ++ (items.filter (fun n => !(isDirAt st dirPos n))).map (·.val)), st) := by
  intro items
  induction items with
  | nil =>
    intro dirsAcc filesAcc _
    rw [Internal.classifyChildrenM.eq_1]
    simp only [List.filter_nil, List.map_nil, List.append_nil]
    rfl
  | cons n rest ih =>
    intro dirsAcc filesAcc hLive
    have hNLive := hLive n List.mem_cons_self
    have hXF : (pm / 64 % 2 == 0) = false := by rw [hX]; decide
    cases hNd : nodeAt st.tree (dirPos ++ [n.val]) with
    | none => exact absurd hNd hNLive
    | some nd =>
      have hLstat : vfsDirOps.lstatAt dirDh n st = (.ok (vfsToStat nd), st) := by
        rw [vfsDirOps_lstatAt_def, hLd]
        dsimp only
        rw [hDir]
        simp only [hXF, Bool.false_eq_true, ↓reduceIte, hNd]
      change (do
          let r ← vfsDirOps.lstatAt dirDh n
          match r with
          | Except.error e => pure (Except.error e)
          | Except.ok info =>
            if info.kind == EntryKind.dir then
              Internal.classifyChildrenM vfsDirOps dirDh rest (n :: dirsAcc) filesAcc
            else
              Internal.classifyChildrenM vfsDirOps dirDh rest dirsAcc (n.val :: filesAcc)) st = _
      simp only [Bind.bind, StateT.bind, hLstat]
      cases nd with
      | dir dm =>
        have hIsD : isDirAt st dirPos n = true := by simp [isDirAt, hNd]
        simp only [vfsToStat, show (EntryKind.dir == EntryKind.dir) = true from rfl, ↓reduceIte]
        rw [ih (n :: dirsAcc) filesAcc (fun m hm => hLive m (List.mem_cons_of_mem _ hm))]
        simp only [List.filter_cons, hIsD, ↓reduceIte, Bool.not_true, Bool.false_eq_true,
          List.reverse_cons, List.append_assoc, List.singleton_append]
      | file _ _ =>
        have hNotD : isDirAt st dirPos n = false := by simp [isDirAt, hNd]
        simp only [vfsToStat, show (EntryKind.file == EntryKind.dir) = false from rfl, Bool.false_eq_true, ↓reduceIte]
        rw [ih dirsAcc (n.val :: filesAcc) (fun m hm => hLive m (List.mem_cons_of_mem _ hm))]
        simp only [List.filter_cons, hNotD, Bool.false_eq_true, ↓reduceIte, Bool.not_false,
          List.map_cons, List.reverse_cons, List.append_assoc, List.singleton_append]
      | symlink _ _ =>
        have hNotD : isDirAt st dirPos n = false := by simp [isDirAt, hNd]
        simp only [vfsToStat, show (EntryKind.symlink == EntryKind.dir) = false from rfl, Bool.false_eq_true, ↓reduceIte]
        rw [ih dirsAcc (n.val :: filesAcc) (fun m hm => hLive m (List.mem_cons_of_mem _ hm))]
        simp only [List.filter_cons, hNotD, Bool.false_eq_true, ↓reduceIte, Bool.not_false,
          List.map_cons, List.reverse_cons, List.append_assoc, List.singleton_append]

private theorem pairwise_filter_val {α : Type} {f : α → String} (p : α → Bool)
    (xs : List α) (hp : List.Pairwise (fun a b => f a < f b) xs) :
    List.Pairwise (fun a b => f a < f b) (xs.filter p) := by
  induction xs with
  | nil => exact List.Pairwise.nil
  | cons a rest ih =>
    rw [List.pairwise_cons] at hp
    simp only [List.filter_cons]
    cases p a
    · exact ih hp.2
    · refine List.pairwise_cons.mpr ⟨fun b hb => hp.1 b (List.mem_filter.mp hb).1, ih hp.2⟩

private theorem stateM_bind_eq {α β : Type} {m : StateM VfsState α} {k : α → StateM VfsState β}
    {s : VfsState} {a : α} {s' : VfsState} (hm : m s = (a, s')) :
    (m >>= k) s = k a s' := by
  simp only [Bind.bind, StateT.bind, hm]

private theorem entryName_ext {a b : EntryName} (h : a.val = b.val) : a = b := by
  cases a; cases b; simp at h; subst h; rfl

private theorem pairwise_map_val (xs : List EntryName)
    (hp : List.Pairwise (fun a b => a.val < b.val) xs) :
    List.Pairwise (fun a b => a < b) (xs.map (·.val)) := by
  induction xs with
  | nil => exact List.Pairwise.nil
  | cons a rest ih =>
    rw [List.pairwise_cons] at hp
    refine List.pairwise_cons.mpr ⟨fun b hb => ?_, ih hp.2⟩
    rcases List.mem_map.mp hb with ⟨x, hx, rfl⟩
    exact hp.1 x hx

/-- `VfsTreeWalkable` implies every directory along any walkable subtree has read+exec bits (`0o5`). -/
theorem walkable_dir_perms : ∀ (fuel : Nat) (t : VfsTree), VfsTreeWalkable fuel t →
    ∀ dm ch, t = .dir dm ch → dm / 256 % 2 = 1 ∧ dm / 64 % 2 = 1 := by
  intro fuel t hW dm ch rfl
  cases fuel with
  | zero => rw [VfsTreeWalkable.eq_3] at hW; exact False.elim hW
  | succ f => rw [VfsTreeWalkable.eq_4] at hW; exact ⟨hW.1, hW.2.1⟩

/-- `VfsTreeWalkable` is monotone in its recursion fuel bound. -/
theorem vfsTreeWalkable_mono : ∀ (fuel fuel' : Nat) (t : VfsTree),
    fuel ≤ fuel' → VfsTreeWalkable fuel t → VfsTreeWalkable fuel' t := by
  intro fuel
  induction fuel with
  | zero =>
    intro fuel' t _ hW
    cases t with
    | file d m => rw [VfsTreeWalkable.eq_1]; trivial
    | symlink tgt m => rw [VfsTreeWalkable.eq_2]; trivial
    | dir m ch => rw [VfsTreeWalkable.eq_3] at hW; exact False.elim hW
  | succ f ih =>
    intro fuel' t hLe hW
    cases fuel' with
    | zero => omega
    | succ f' =>
      cases t with
      | file d m => rw [VfsTreeWalkable.eq_1]; trivial
      | symlink tgt m => rw [VfsTreeWalkable.eq_2]; trivial
      | dir m ch =>
        rw [VfsTreeWalkable.eq_4] at hW ⊢
        exact ⟨hW.1, hW.2.1, fun nm sub hs => ih f' sub (Nat.le_of_succ_le_succ hLe) (hW.2.2 nm sub hs)⟩

private theorem walkRecM_step_ok (fuel : Nat)
    (ih : ∀ (relSegs : List EntryName) (relLabel : String) (acc : Array WalkEntry) (rootDh : DirHandle)
      (pos : List String) (st : VfsState) (dm : Nat) (ch : String → Option VfsTree),
      VfsKeysComplete st → lookupDir st rootDh = some pos → DirHandleInvariant st →
      (∀ s ∈ pos, validSeg s = true) →
      (∃ pm₀, nodeAt st.tree pos = some (.dir pm₀) ∧ pm₀ / 64 % 2 = 1) →
      (∀ k, 0 < k → k ≤ relSegs.length → ∃ dk, nodeAt st.tree (pos ++ (relSegs.take k).map (·.val)) = some (.dir dk) ∧
        dk / 256 % 2 = 1 ∧ dk / 64 % 2 = 1) →
      vfsTreeGet st.tree (pos ++ relSegs.map (·.val)) = some (.dir dm ch) →
      VfsTreeWalkable (fuel + 1) (.dir dm ch) →
      ∃ tail st', Internal.walkRecM vfsDirOps rootDh relSegs relLabel acc (fuel + 1) st =
          (.ok (acc ++ tail.toArray), st') ∧
        st'.tree = st.tree ∧ st'.keys = st.keys ∧ st'.cwd = st.cwd ∧ st'.nonce = st.nonce ∧
        st'.locks = st.locks ∧ st'.openDirs = st.openDirs ∧ DirHandleInvariant st' ∧
        (let sorted := Internal.sortEntryNames (mVfsReadDirAtEntries st (pos ++ relSegs.map (·.val)))
         let dirs := sorted.filter (isDirAt st (pos ++ relSegs.map (·.val)))
         let files := (sorted.filter (fun n => !(isDirAt st (pos ++ relSegs.map (·.val)) n))).map (·.val)
         ∃ rest, tail = { root := relLabel, dirs := (dirs.map (·.val)).toArray, files := files.toArray } :: rest) ∧
        (∀ e ∈ tail, walkEntrySorted' e) ∧
        (∀ e ∈ tail, e.root = relLabel ∨ ∃ s, s ∈ (Internal.sortEntryNames (mVfsReadDirAtEntries st (pos ++ relSegs.map (·.val)))).filter (isDirAt st (pos ++ relSegs.map (·.val))) ∧
          (let lbl := if relLabel == "." then s.val else relLabel ++ "/" ++ s.val
           e.root = lbl ∨ ∃ suf, e.root = lbl ++ "/" ++ suf)))
    (relSegs : List EntryName) (relLabel : String) (acc : Array WalkEntry) (rootDh : DirHandle)
    (pos : List String) (st : VfsState) (dm : Nat) (ch : String → Option VfsTree)
    (hKeys : VfsKeysComplete st) (hLd : lookupDir st rootDh = some pos) (hInv : DirHandleInvariant st)
    (hPosValid : ∀ s ∈ pos, validSeg s = true)
    (hPosDir : ∃ pm₀, nodeAt st.tree pos = some (.dir pm₀) ∧ pm₀ / 64 % 2 = 1)
    (hAnc : ∀ k, 0 < k → k ≤ relSegs.length → ∃ dk, nodeAt st.tree (pos ++ (relSegs.take k).map (·.val)) = some (.dir dk) ∧
      dk / 256 % 2 = 1 ∧ dk / 64 % 2 = 1)
    (hGet : vfsTreeGet st.tree (pos ++ relSegs.map (·.val)) = some (.dir dm ch))
    (hWalk : VfsTreeWalkable (fuel + 2) (.dir dm ch)) :
    ∃ tail st', Internal.walkRecM vfsDirOps rootDh relSegs relLabel acc (fuel + 2) st =
        (.ok (acc ++ tail.toArray), st') ∧
      st'.tree = st.tree ∧ st'.keys = st.keys ∧ st'.cwd = st.cwd ∧ st'.nonce = st.nonce ∧
      st'.locks = st.locks ∧ st'.openDirs = st.openDirs ∧ DirHandleInvariant st' ∧
      (let sorted := Internal.sortEntryNames (mVfsReadDirAtEntries st (pos ++ relSegs.map (·.val)))
       let dirs := sorted.filter (isDirAt st (pos ++ relSegs.map (·.val)))
       let files := (sorted.filter (fun n => !(isDirAt st (pos ++ relSegs.map (·.val)) n))).map (·.val)
       ∃ rest, tail = { root := relLabel, dirs := (dirs.map (·.val)).toArray, files := files.toArray } :: rest) ∧
      (∀ e ∈ tail, walkEntrySorted' e) ∧
      (∀ e ∈ tail, e.root = relLabel ∨ ∃ s, s ∈ (Internal.sortEntryNames (mVfsReadDirAtEntries st (pos ++ relSegs.map (·.val)))).filter (isDirAt st (pos ++ relSegs.map (·.val))) ∧
        (let lbl := if relLabel == "." then s.val else relLabel ++ "/" ++ s.val
         e.root = lbl ∨ ∃ suf, e.root = lbl ++ "/" ++ suf)) := by
  let dirPos := pos ++ relSegs.map (·.val)
  have hDirValid : ∀ s ∈ dirPos, validSeg s = true := by
    intro s hs
    rcases List.mem_append.mp hs with hp | hr
    · exact hPosValid s hp
    · simp only [List.mem_map] at hr
      rcases hr with ⟨e, _, rfl⟩
      exact e.valid
  rw [VfsTreeWalkable.eq_4] at hWalk
  rcases hWalk with ⟨hDmR, hDmX, hSubWalk⟩
  have hDirNd : nodeAt st.tree dirPos = some (.dir dm) := by
    simp only [dirPos, nodeAt, hGet, vfsTreeTopNode, Option.map_some]
  let readFn : DirHandle → StateM VfsState (Except FsError (List EntryName × List String)) :=
    fun dirDh => do
      let rRead ← vfsDirOps.readDirAt dirDh
      match rRead with
      | Except.error e => pure (Except.error e)
      | Except.ok rawNames => Internal.classifyChildrenM vfsDirOps dirDh (Internal.sortEntryNames rawNames) [] []
  have hWalkRead := walkDescendM_ok relSegs rootDh pos st readFn
    hLd hInv
    (fun k hk => by
      by_cases hk0 : k = 0
      · subst hk0
        rcases hPosDir with ⟨pm₀, hP0, hP0X⟩
        exact ⟨pm₀, by simpa using hP0, fun h => absurd h (Nat.not_lt_zero 0), hP0X⟩
      · rcases hAnc k (Nat.pos_of_ne_zero hk0) (Nat.le_of_lt hk) with ⟨dk, hDk, hDkR, hDkX⟩
        exact ⟨dk, hDk, fun _ => hDkR, hDkX⟩)
    (fun _ => ⟨dm, hDirNd, hDmR⟩)
  let sorted := Internal.sortEntryNames (mVfsReadDirAtEntries st dirPos)
  let dirs := sorted.filter (isDirAt st dirPos)
  let files := (sorted.filter (fun n => !(isDirAt st dirPos n))).map (·.val)
  let entry : WalkEntry := { root := relLabel, dirs := (dirs.map (·.val)).toArray, files := files.toArray }
  have hSortedLive : ∀ n ∈ sorted, nodeAt st.tree (dirPos ++ [n.val]) ≠ none := by
    intro n hn
    have hMemRaw : n ∈ (mVfsReadDirAtEntries st dirPos).toList := by
      have hPerm := List.mergeSort_perm (mVfsReadDirAtEntries st dirPos).toList (fun a b => decide (a.val ≤ b.val))
      exact hPerm.mem_iff.mp hn
    exact mVfsReadDirAtEntries_mem_sound st dirPos hDirValid n hMemRaw
  have hSortedStrict : List.Pairwise (fun a b => a.val < b.val) sorted :=
    list_mergeSort_entryName_strict (mVfsReadDirAtEntries_nodup st dirPos)
  have hEntrySorted : walkEntrySorted' entry := by
    refine ⟨?_, ?_⟩
    · simp only [entry]
      exact pairwise_map_val dirs (pairwise_filter_val (isDirAt st dirPos) sorted hSortedStrict)
    · simp only [entry]
      exact pairwise_map_val (sorted.filter (fun n => !(isDirAt st dirPos n)))
        (pairwise_filter_val (fun n => !(isDirAt st dirPos n)) sorted hSortedStrict)
  have hReadStage : ∀ (dhUse : DirHandle) (stUse : VfsState),
      lookupDir stUse dhUse = some dirPos → stUse.tree = st.tree → stUse.keys = st.keys →
      readFn dhUse stUse = (.ok (dirs, files), stUse) := by
    intro dhUse stUse hLdUse hTreeUse hKeysUse
    have hDirUse : nodeAt stUse.tree dirPos = some (.dir dm) := by rw [hTreeUse]; exact hDirNd
    have hDmRF : (dm / 256 % 2 == 0) = false := by rw [hDmR]; decide
    have hReadOk : vfsDirOps.readDirAt dhUse stUse = (.ok (mVfsReadDirAtEntries stUse dirPos), stUse) := by
      rw [vfsDirOps_readDirAt_def, hLdUse]
      dsimp only
      rw [hDirUse]
      simp only [hDmRF, Bool.false_eq_true, ↓reduceIte]
    have hEntriesEq : mVfsReadDirAtEntries stUse dirPos = mVfsReadDirAtEntries st dirPos := by
      unfold mVfsReadDirAtEntries
      rw [hKeysUse, nodes_eq_of_tree_eq' hTreeUse]
    rw [hEntriesEq] at hReadOk
    have hIsDirEq : isDirAt stUse dirPos = isDirAt st dirPos := by
      funext n
      simp [isDirAt, hTreeUse]
    dsimp only [readFn]
    simp only [Bind.bind, StateT.bind, hReadOk]
    rw [classifyChildrenM_ok dhUse dirPos stUse dm hLdUse hDirUse hDmX sorted [] []
      (fun n hn => by rw [hTreeUse]; exact hSortedLive n hn), hIsDirEq]
    rfl
  have hAfterRead : ∃ stR,
      Internal.walkDescendM vfsDirOps rootDh relSegs readFn st = (.ok (dirs, files), stR) ∧
      stR.tree = st.tree ∧ stR.keys = st.keys ∧ stR.cwd = st.cwd ∧ stR.nonce = st.nonce ∧
      stR.locks = st.locks ∧ stR.openDirs = st.openDirs ∧ DirHandleInvariant stR ∧ lookupDir stR rootDh = some pos := by
    by_cases hRelNil : relSegs = []
    · subst hRelNil
      have hRS := hReadStage rootDh st (by simpa [dirPos] using hLd) rfl rfl
      refine ⟨st, ?_, rfl, rfl, rfl, rfl, rfl, rfl, hInv, hLd⟩
      rw [hWalkRead.1 rfl]
      exact hRS
    · rcases hWalkRead.2 hRelNil with
        ⟨dirDh, stMid, hPosDh, hLdMid, hTreeMid, hKeysMid, hCwdMid, hNonceMid, hLocksMid,
          hInvMid, hLtMid, hOpenMid, hWalkEq⟩
      have hRS := hReadStage dirDh stMid hLdMid hTreeMid hKeysMid
      have hCl := vfsDirOps_closeDir_fresh dirDh stMid dirPos hPosDh st.openDirs hOpenMid hLtMid
      refine ⟨{ stMid with openDirs := st.openDirs }, ?_, hTreeMid, hKeysMid, hCwdMid, hNonceMid,
        hLocksMid, rfl, ?_, ?_⟩
      · rw [hWalkEq, bracketCloseDirM_run, hRS]
        dsimp only
        rw [hCl]
      · exact dirHandleInvariant_of_subset hInvMid (fun p hp => by rw [hOpenMid]; exact List.mem_cons_of_mem _ hp) rfl
      · unfold lookupDir at hLd ⊢; exact hLd
  rcases hAfterRead with ⟨stR, hReadRes, hTreeR, hKeysR, hCwdR, hNonceR, hLocksR, hOpenR, hInvR, hLdR⟩
  have hChLoop : ∀ (ds : List EntryName) (curAcc : Array WalkEntry) (stC : VfsState),
      (∀ d ∈ ds, d ∈ dirs) →
      VfsKeysComplete stC → lookupDir stC rootDh = some pos → DirHandleInvariant stC →
      stC.tree = st.tree → stC.keys = st.keys → stC.cwd = st.cwd → stC.nonce = st.nonce →
      stC.locks = st.locks → stC.openDirs = st.openDirs →
      ∃ (chTail : List WalkEntry) (stF : VfsState),
        Internal.walkChildrenM vfsDirOps rootDh relSegs relLabel (fuel + 1) curAcc ds stC =
          (.ok (curAcc ++ chTail.toArray), stF) ∧
        stF.tree = st.tree ∧ stF.keys = st.keys ∧ stF.cwd = st.cwd ∧ stF.nonce = st.nonce ∧
        stF.locks = st.locks ∧ stF.openDirs = st.openDirs ∧ DirHandleInvariant stF ∧
        (∀ e ∈ chTail, walkEntrySorted' e) ∧
        (∀ e ∈ chTail, ∃ s ∈ ds,
          (let lbl := if relLabel == "." then s.val else relLabel ++ "/" ++ s.val
           e.root = lbl ∨ ∃ suf, e.root = lbl ++ "/" ++ suf)) := by
    intro ds
    induction ds with
    | nil =>
      intro curAcc stC _ _ _ hInvC hTC hKC hCC hNC hLC hOC
      rw [Internal.walkChildrenM.eq_1]
      refine ⟨[], stC, ?_, hTC, hKC, hCC, hNC, hLC, hOC, hInvC, ?_, ?_⟩
      · simp [Pure.pure, StateT.pure]
      · intro _ h; cases h
      · intro _ h; cases h
    | cons d rest ihDs =>
      intro curAcc stC hSubDirs hKCC hLdC hInvC hTC hKC hCC hNC hLC hOC
      have hdInDirs : d ∈ dirs := hSubDirs d List.mem_cons_self
      have hdFilt := List.mem_filter.mp hdInDirs
      have hIsD : isDirAt st dirPos d = true := hdFilt.2
      have hdDir : ∃ dmD chD, ch d.val = some (.dir dmD chD) ∧
          nodeAt st.tree (dirPos ++ [d.val]) = some (.dir dmD) := by
        have hNdEx : ∃ dmD, nodeAt st.tree (dirPos ++ [d.val]) = some (.dir dmD) := by
          unfold isDirAt at hIsD
          cases hNd : nodeAt st.tree (dirPos ++ [d.val]) with
          | none => simp [hNd] at hIsD
          | some nd =>
            cases nd with
            | file _ _ | symlink _ _ => simp [hNd] at hIsD
            | dir dmD => exact ⟨dmD, rfl⟩
        rcases hNdEx with ⟨dmD, hNd⟩
        have hNdSub := hNd
        rw [nodeAt_sub_of_vfsTreeGet hGet] at hNdSub
        have hChEx : ∃ chD, ch d.val = some (.dir dmD chD) := by
          cases hChD : ch d.val with
          | none => simp [nodeAt, vfsTreeGet, hChD] at hNdSub
          | some subD =>
            cases subD with
            | file _ _ | symlink _ _ => simp [nodeAt, vfsTreeGet, hChD, vfsTreeTopNode] at hNdSub
            | dir dmD' chD =>
              simp [nodeAt, vfsTreeGet, hChD, vfsTreeTopNode] at hNdSub
              cases hNdSub
              exact ⟨chD, rfl⟩
        rcases hChEx with ⟨chD, hChD⟩
        exact ⟨dmD, chD, hChD, hNd⟩
      rcases hdDir with ⟨dmD, chD, hChD, hNdD⟩
      have hWalkD : VfsTreeWalkable (fuel + 1) (.dir dmD chD) := hSubWalk d.val (.dir dmD chD) hChD
      have hGetDC : vfsTreeGet stC.tree (pos ++ (relSegs ++ [d]).map (·.val)) = some (.dir dmD chD) := by
        rw [hTC, List.map_append, List.map_singleton, ← List.append_assoc]
        change vfsTreeGet st.tree (dirPos ++ [d.val]) = some (.dir dmD chD)
        rw [vfsTreeGet_sub_of_vfsTreeGet hGet]
        simp [vfsTreeGet, hChD]
      have hPosDirC : ∃ pm₀, nodeAt stC.tree pos = some (.dir pm₀) ∧ pm₀ / 64 % 2 = 1 := by
        rcases hPosDir with ⟨pm₀, hP0, hP0X⟩
        exact ⟨pm₀, by rw [hTC]; exact hP0, hP0X⟩
      have hAncC : ∀ k, 0 < k → k ≤ (relSegs ++ [d]).length →
          ∃ dk, nodeAt stC.tree (pos ++ ((relSegs ++ [d]).take k).map (·.val)) = some (.dir dk) ∧
            dk / 256 % 2 = 1 ∧ dk / 64 % 2 = 1 := by
        intro k hkPos hkLe
        rw [List.length_append, List.length_singleton] at hkLe
        by_cases hkIn : k ≤ relSegs.length
        · rcases hAnc k hkPos hkIn with ⟨dk, hDk, hR, hX⟩
          refine ⟨dk, ?_, hR, hX⟩
          rw [hTC, List.take_append_of_le_length hkIn]
          exact hDk
        · have hkEq : k = relSegs.length + 1 := by omega
          subst hkEq
          rw [List.take_of_length_le (by simp)]
          rw [List.map_append, List.map_singleton, ← List.append_assoc, hTC]
          have hPermsD := walkable_dir_perms (fuel + 1) (.dir dmD chD) hWalkD dmD chD rfl
          exact ⟨dmD, hNdD, hPermsD.1, hPermsD.2⟩
      let childLabel := if relLabel == "." then d.val else relLabel ++ "/" ++ d.val
      rcases ih (relSegs ++ [d]) childLabel curAcc rootDh pos stC dmD chD
        hKCC hLdC hInvC hPosValid hPosDirC hAncC hGetDC hWalkD with
        ⟨dTail, stD, hWalkDRes, hTD, hKD, hCD, hND, hLD, hOD, hInvD, _, hDSorted, hDRoots⟩
      have hLdD : lookupDir stD rootDh = some pos := by
        unfold lookupDir at hLd ⊢
        rw [hOD, hOC]
        exact hLd
      have hKCD : VfsKeysComplete stD := by
        intro segs hNe
        rw [hKD, hKC]
        apply hKeys segs
        rw [← hTC, ← hTD]
        exact hNe
      rcases ihDs (curAcc ++ dTail.toArray) stD
        (fun x hx => hSubDirs x (List.mem_cons_of_mem _ hx))
        hKCD hLdD hInvD (hTD.trans hTC) (hKD.trans hKC) (hCD.trans hCC) (hND.trans hNC)
        (hLD.trans hLC) (hOD.trans hOC) with
        ⟨rTail, stF, hChRest, hTF, hKF, hCF, hNF, hLF, hOF, hInvF, hRSorted, hRRoots⟩
      refine ⟨dTail ++ rTail, stF, ?_, hTF, hKF, hCF, hNF, hLF, hOF, hInvF, ?_, ?_⟩
      · rw [Internal.walkChildrenM.eq_2]
        refine (stateM_bind_eq hWalkDRes).trans ?_
        dsimp only
        rw [hChRest]
        exact congrArg (fun a => (Except.ok a, stF)) (Array.toList_inj.mp (by simp))
      · intro e he
        rcases List.mem_append.mp he with hd | hr
        · exact hDSorted e hd
        · exact hRSorted e hr
      · intro e he
        rcases List.mem_append.mp he with hd | hr
        · refine ⟨d, List.mem_cons_self, ?_⟩
          rcases hDRoots e hd with hEq0 | ⟨s, _, hRest0⟩
          · exact Or.inl hEq0
          · by_cases hCEq : (childLabel == ".") = true
            · exfalso
              by_cases hr0 : (relLabel == ".") = true
              · simp [childLabel, hr0] at hCEq
                have hDV := d.valid
                unfold validSeg at hDV
                simp only [Bool.and_eq_true, Bool.not_eq_true'] at hDV
                have hB : (d.val.toList != ['.']) = false := by simp [congrArg String.toList hCEq]
                rw [hB] at hDV
                exact Bool.false_ne_true hDV.1.2
              · simp [childLabel, Bool.eq_false_iff.mpr hr0] at hCEq
                have hSlash : '/' ∈ (relLabel ++ "/" ++ d.val).toList := by simp
                rw [hCEq] at hSlash
                cases (by decide : ¬ '/' ∈ ".".toList) hSlash
            · have hCF : (childLabel == ".") = false := Bool.eq_false_iff.mpr hCEq
              dsimp only at hRest0
              simp only [hCF, Bool.false_eq_true, ↓reduceIte] at hRest0
              rcases hRest0 with hEqS | ⟨suf, hEqS⟩
              · right; exact ⟨s.val, by rw [hEqS]⟩
              · right; exact ⟨s.val ++ "/" ++ suf, by rw [hEqS]; dsimp only [childLabel]; simp [String.append_assoc]⟩
        · rcases hRRoots e hr with ⟨s, hs, hR⟩
          exact ⟨s, List.mem_cons_of_mem _ hs, hR⟩
  have hKCR : VfsKeysComplete stR := by
    intro segs hNe
    rw [hKeysR]
    apply hKeys segs
    rw [← hTreeR]
    exact hNe
  rcases hChLoop dirs (acc.push entry) stR (fun _ h => h) hKCR hLdR hInvR hTreeR hKeysR hCwdR hNonceR hLocksR hOpenR with
    ⟨chTail, stF, hWalkCh, hTF, hKF, hCF, hNF, hLF, hOF, hInvF, hChSorted, hChRoots⟩
  refine ⟨entry :: chTail, stF, ?_, hTF, hKF, hCF, hNF, hLF, hOF, hInvF, ?_, ?_, ?_⟩
  · rw [Internal.walkRecM.eq_2]
    refine (stateM_bind_eq hReadRes).trans ?_
    dsimp only
    rw [hWalkCh]
    exact congrArg (fun a => (Except.ok a, stF)) (Array.toList_inj.mp (by simp))
  · exact ⟨chTail, rfl⟩
  · intro e he
    rcases List.mem_cons.mp he with rfl | hT
    · exact hEntrySorted
    · exact hChSorted e hT
  · intro e he
    rcases List.mem_cons.mp he with rfl | hT
    · exact Or.inl rfl
    · right
      exact hChRoots e hT

/-- Top-level correctness theorem for `Internal.walkRecM` on `VfsTreeWalkable (fuel + 1)` subtrees. -/
theorem walkRecM_ok : ∀ (fuel : Nat) (relSegs : List EntryName) (relLabel : String)
    (acc : Array WalkEntry) (rootDh : DirHandle) (pos : List String) (st : VfsState)
    (dm : Nat) (ch : String → Option VfsTree),
    VfsKeysComplete st → lookupDir st rootDh = some pos → DirHandleInvariant st →
    (∀ s ∈ pos, validSeg s = true) →
    (∃ pm₀, nodeAt st.tree pos = some (.dir pm₀) ∧ pm₀ / 64 % 2 = 1) →
    (∀ k, 0 < k → k ≤ relSegs.length → ∃ dk, nodeAt st.tree (pos ++ (relSegs.take k).map (·.val)) = some (.dir dk) ∧
      dk / 256 % 2 = 1 ∧ dk / 64 % 2 = 1) →
    vfsTreeGet st.tree (pos ++ relSegs.map (·.val)) = some (.dir dm ch) →
    VfsTreeWalkable (fuel + 1) (.dir dm ch) →
    ∃ tail st', Internal.walkRecM vfsDirOps rootDh relSegs relLabel acc (fuel + 1) st =
        (.ok (acc ++ tail.toArray), st') ∧
      st'.tree = st.tree ∧ st'.keys = st.keys ∧ st'.cwd = st.cwd ∧ st'.nonce = st.nonce ∧
      st'.locks = st.locks ∧ st'.openDirs = st.openDirs ∧ DirHandleInvariant st' ∧
      (let sorted := Internal.sortEntryNames (mVfsReadDirAtEntries st (pos ++ relSegs.map (·.val)))
       let dirs := sorted.filter (isDirAt st (pos ++ relSegs.map (·.val)))
       let files := (sorted.filter (fun n => !(isDirAt st (pos ++ relSegs.map (·.val)) n))).map (·.val)
       ∃ rest, tail = { root := relLabel, dirs := (dirs.map (·.val)).toArray, files := files.toArray } :: rest) ∧
      (∀ e ∈ tail, walkEntrySorted' e) ∧
      (∀ e ∈ tail, e.root = relLabel ∨ ∃ s, s ∈ (Internal.sortEntryNames (mVfsReadDirAtEntries st (pos ++ relSegs.map (·.val)))).filter (isDirAt st (pos ++ relSegs.map (·.val))) ∧
        (let lbl := if relLabel == "." then s.val else relLabel ++ "/" ++ s.val
         e.root = lbl ∨ ∃ suf, e.root = lbl ++ "/" ++ suf)) := by
  intro fuel
  induction fuel with
  | zero =>
    intro relSegs relLabel acc rootDh pos st dm ch hKeys hLd hInv hPosValid hPosDir hAnc hGet hWalk
    let dirPos := pos ++ relSegs.map (·.val)
    have hDirValid : ∀ s ∈ dirPos, validSeg s = true := by
      intro s hs
      rcases List.mem_append.mp hs with hp | hr
      · exact hPosValid s hp
      · simp only [List.mem_map] at hr; rcases hr with ⟨e, _, rfl⟩; exact e.valid
    rw [VfsTreeWalkable.eq_4] at hWalk
    rcases hWalk with ⟨hDmR, hDmX, hSubWalk⟩
    have hNoDirs : ∀ s sub, ch s = some sub → ∀ d m, sub ≠ .dir d m := by
      intro s sub hCh d m rfl
      have hW0 := hSubWalk s (.dir d m) hCh
      rw [VfsTreeWalkable.eq_3] at hW0
      exact hW0
    have hDirNd : nodeAt st.tree dirPos = some (.dir dm) := by
      simp only [dirPos, nodeAt, hGet, vfsTreeTopNode, Option.map_some]
    let sorted := Internal.sortEntryNames (mVfsReadDirAtEntries st dirPos)
    have hDirsNil : sorted.filter (isDirAt st dirPos) = [] := by
      rw [List.filter_eq_nil_iff]
      intro n hn
      simp only [Bool.not_eq_true]
      unfold isDirAt
      cases hNd : nodeAt st.tree (dirPos ++ [n.val]) with
      | none => rfl
      | some nd =>
        cases nd with
        | file _ _ | symlink _ _ => rfl
        | dir d =>
          exfalso
          rw [nodeAt_sub_of_vfsTreeGet hGet] at hNd
          cases hCh : ch n.val with
          | none => simp [nodeAt, vfsTreeGet, hCh] at hNd
          | some sub =>
            cases sub with
            | file _ _ | symlink _ _ => simp [nodeAt, vfsTreeGet, hCh, vfsTreeTopNode] at hNd
            | dir dmD chD => exact hNoDirs n.val (.dir dmD chD) hCh dmD chD rfl
    have hSortedLive : ∀ n ∈ sorted, nodeAt st.tree (dirPos ++ [n.val]) ≠ none := by
      intro n hn
      have hPerm := List.mergeSort_perm (mVfsReadDirAtEntries st dirPos).toList (fun a b => decide (a.val ≤ b.val))
      exact mVfsReadDirAtEntries_mem_sound st dirPos hDirValid n (hPerm.mem_iff.mp hn)
    have hSortedStrict : List.Pairwise (fun a b => a.val < b.val) sorted :=
      list_mergeSort_entryName_strict (mVfsReadDirAtEntries_nodup st dirPos)
    let files := (sorted.filter (fun n => !(isDirAt st dirPos n))).map (·.val)
    let entry : WalkEntry := { root := relLabel, dirs := #[], files := files.toArray }
    have hEntrySorted : walkEntrySorted' entry := by
      refine ⟨by simp [entry], ?_⟩
      simp only [entry]
      exact pairwise_map_val (sorted.filter (fun n => !(isDirAt st dirPos n)))
        (pairwise_filter_val (fun n => !(isDirAt st dirPos n)) sorted hSortedStrict)
    let readFn : DirHandle → StateM VfsState (Except FsError (List EntryName × List String)) :=
      fun dirDh => do
        let rRead ← vfsDirOps.readDirAt dirDh
        match rRead with
        | Except.error e => pure (Except.error e)
        | Except.ok rawNames => Internal.classifyChildrenM vfsDirOps dirDh (Internal.sortEntryNames rawNames) [] []
    have hReadStage : ∀ (dhUse : DirHandle) (stUse : VfsState),
        lookupDir stUse dhUse = some dirPos → stUse.tree = st.tree → stUse.keys = st.keys →
        readFn dhUse stUse = (.ok ([], files), stUse) := by
      intro dhUse stUse hLdUse hTreeUse hKeysUse
      have hDirUse : nodeAt stUse.tree dirPos = some (.dir dm) := by rw [hTreeUse]; exact hDirNd
      have hDmRF : (dm / 256 % 2 == 0) = false := by rw [hDmR]; decide
      have hReadOk : vfsDirOps.readDirAt dhUse stUse = (.ok (mVfsReadDirAtEntries stUse dirPos), stUse) := by
        rw [vfsDirOps_readDirAt_def, hLdUse]
        dsimp only
        rw [hDirUse]
        simp only [hDmRF, Bool.false_eq_true, ↓reduceIte]
      have hEntriesEq : mVfsReadDirAtEntries stUse dirPos = mVfsReadDirAtEntries st dirPos := by
        unfold mVfsReadDirAtEntries
        rw [hKeysUse, nodes_eq_of_tree_eq' hTreeUse]
      rw [hEntriesEq] at hReadOk
      have hIsDirEq : isDirAt stUse dirPos = isDirAt st dirPos := by
        funext n
        simp [isDirAt, hTreeUse]
      dsimp only [readFn]
      simp only [Bind.bind, StateT.bind, hReadOk]
      rw [classifyChildrenM_ok dhUse dirPos stUse dm hLdUse hDirUse hDmX sorted [] []
        (fun n hn => by rw [hTreeUse]; exact hSortedLive n hn), hIsDirEq, hDirsNil]
      rfl
    have hWalkRead := walkDescendM_ok relSegs rootDh pos st readFn
      hLd hInv
      (fun k hk => by
        by_cases hk0 : k = 0
        · subst hk0
          rcases hPosDir with ⟨pm₀, hP0, hP0X⟩
          exact ⟨pm₀, by simpa using hP0, fun h => absurd h (Nat.not_lt_zero 0), hP0X⟩
        · rcases hAnc k (Nat.pos_of_ne_zero hk0) (Nat.le_of_lt hk) with ⟨dk, hDk, hDkR, hDkX⟩
          exact ⟨dk, hDk, fun _ => hDkR, hDkX⟩)
      (fun _ => ⟨dm, hDirNd, hDmR⟩)
    by_cases hRelNil : relSegs = []
    · subst hRelNil
      have hRead := hReadStage rootDh st (by simpa [dirPos] using hLd) rfl rfl
      rw [← hWalkRead.1 rfl] at hRead
      refine ⟨[entry], st, ?_, rfl, rfl, rfl, rfl, rfl, rfl, hInv, ?_, ?_, ?_⟩
      · rw [Internal.walkRecM.eq_2]
        refine (stateM_bind_eq hRead).trans ?_
        dsimp only
        rw [Internal.walkChildrenM.eq_1]
        simp only [Pure.pure, StateT.pure]
        exact congrArg (fun a => (Except.ok a, st)) (Array.toList_inj.mp (by simp [Array.toList_push, entry]))
      · refine ⟨[], ?_⟩
        have hD0 : List.filter (isDirAt st (pos ++ ([] : List EntryName).map (·.val)))
            (Internal.sortEntryNames (mVfsReadDirAtEntries st (pos ++ ([] : List EntryName).map (·.val)))) = [] := hDirsNil
        rw [hD0]
        rfl
      · intro e he; rcases List.mem_singleton.mp he with rfl; exact hEntrySorted
      · intro e he; rcases List.mem_singleton.mp he with rfl; exact Or.inl rfl
    · rcases hWalkRead.2 hRelNil with
        ⟨dirDh, stMid, hPosDh, hLdMid, hTreeMid, hKeysMid, hCwdMid, hNonceMid, hLocksMid,
          hInvMid, hLtMid, hOpenMid, hWalkEq⟩
      have hRead : Internal.walkDescendM vfsDirOps rootDh relSegs readFn st =
          (.ok ([], files), { stMid with openDirs := st.openDirs }) := by
        rw [hWalkEq, bracketCloseDirM_run, hReadStage dirDh stMid hLdMid hTreeMid hKeysMid]
        dsimp only
        rw [vfsDirOps_closeDir_fresh dirDh stMid dirPos hPosDh st.openDirs hOpenMid hLtMid]
      have hInvF : DirHandleInvariant { stMid with openDirs := st.openDirs } :=
        dirHandleInvariant_of_subset hInvMid (fun p hp => by rw [hOpenMid]; exact List.mem_cons_of_mem _ hp) rfl
      refine ⟨[entry], { stMid with openDirs := st.openDirs }, ?_, hTreeMid, hKeysMid, hCwdMid, hNonceMid,
        hLocksMid, rfl, hInvF, ?_, ?_, ?_⟩
      · rw [Internal.walkRecM.eq_2]
        refine (stateM_bind_eq hRead).trans ?_
        dsimp only
        rw [Internal.walkChildrenM.eq_1]
        simp only [Pure.pure, StateT.pure]
        exact congrArg (fun a => (Except.ok a, _)) (Array.toList_inj.mp (by simp [Array.toList_push, entry]))
      · refine ⟨[], ?_⟩
        have hD0 : List.filter (isDirAt st (pos ++ relSegs.map (·.val)))
            (Internal.sortEntryNames (mVfsReadDirAtEntries st (pos ++ relSegs.map (·.val)))) = [] := hDirsNil
        rw [hD0]
        rfl
      · intro e he; rcases List.mem_singleton.mp he with rfl; exact hEntrySorted
      · intro e he; rcases List.mem_singleton.mp he with rfl; exact Or.inl rfl
  | succ f ih =>
    exact walkRecM_step_ok f ih

/-- Descending into a non-directory leaf via `walkDescendM` fails `.notADirectory` while preserving `nodes` and `openDirs`. -/
theorem walkDescendM_nonDir_err {α : Type} (dh : DirHandle) (pos : List String)
    (pre : List EntryName) (leaf : EntryName) (bs : ByteArray) (fm : Nat) (st : VfsState)
    (act : DirHandle → StateM VfsState (Except FsError α))
    (hLd : lookupDir st dh = some pos) (hInv : DirHandleInvariant st)
    (hAnc : ∀ k ≤ pre.length, ∃ dm, nodeAt st.tree (pos ++ (pre.take k).map (·.val)) = some (.dir dm) ∧
      (0 < k → dm / 256 % 2 = 1) ∧ dm / 64 % 2 = 1)
    (hFile : nodeAt st.tree (pos ++ pre.map (·.val) ++ [leaf.val]) = some (.file bs fm)) :
    ∃ e st', Internal.walkDescendM vfsDirOps dh (pre ++ [leaf]) act st = (.error e, st') ∧
      e.kind = .notADirectory ∧ st'.nodes = st.nodes ∧ st'.openDirs = st.openDirs := by
  have hAux : ∀ (segs : List EntryName) (isRoot : Bool) (curDh : DirHandle) (curPos : List String)
      (origOpen : List (Nat × List String)) (stC : VfsState),
      lookupDir stC curDh = some curPos →
      DirHandleInvariant stC →
      (if isRoot then stC.openDirs = origOpen
       else 0 < curDh.handleId ∧ stC.openDirs = (curDh.handleId, curPos) :: origOpen ∧
         ∀ p ∈ origOpen, p.1 < curDh.handleId) →
      (∀ k ≤ segs.length, ∃ dm, nodeAt stC.tree (curPos ++ (segs.take k).map (·.val)) = some (.dir dm) ∧
        (0 < k → dm / 256 % 2 = 1) ∧ dm / 64 % 2 = 1) →
      nodeAt stC.tree (curPos ++ segs.map (·.val) ++ [leaf.val]) = some (.file bs fm) →
      ∃ e st', Internal.walkDescendAuxM vfsDirOps isRoot curDh (segs ++ [leaf]) act stC = (.error e, st') ∧
        e.kind = .notADirectory ∧ st'.nodes = stC.nodes ∧ st'.openDirs = origOpen := by
    intro segs
    induction segs with
    | nil =>
      intro isRoot curDh curPos origOpen stC hLdC _ hOpenC hAncC hFileC
      rcases hAncC 0 (Nat.le_refl 0) with ⟨parM, hParC, _, hParXC⟩
      simp only [List.take_zero, List.map_nil, List.append_nil] at hParC
      simp only [List.nil_append, walkDescendAuxM_cons]
      have hErrOpen : ∃ e, vfsDirOps.openDirAt curDh leaf stC = (.error e, stC) ∧ e.kind = .notADirectory := by
        cases hOpen : vfsDirOps.openDirAt curDh leaf stC with
        | mk r s =>
          have hSpec : ∃ d : Nat, vfsDirOps.openDirAt curDh leaf stC =
              match lookupDir stC curDh with
              | none => (.error (mInvalidDirHandleErr curDh), stC)
              | some p =>
                match nodeAt stC.tree p with
                | none => (.error { kind := .notFound, path := some curDh.rootPath, message := "directory no longer exists" }, stC)
                | some (.dir pm) =>
                  if (pm / 64) % 2 == 0 then (.error { kind := .permissionDenied, path := some leaf.val, message := s!"permission denied: {leaf.val}" }, stC)
                  else match nodeAt stC.tree (p ++ [leaf.val]) with
                    | none => (.error { kind := .notFound, path := some leaf.val, message := s!"no such file or directory: {leaf.val}" }, stC)
                    | some (.symlink _ _) => (.error { kind := .invalidInput, path := some leaf.val, message := s!"symlink refused in subtree traversal: {leaf.val}" }, stC)
                    | some (.dir m) =>
                      if (m / 256) % 2 == 0 then (.error { kind := .permissionDenied, path := some leaf.val, message := s!"permission denied: {leaf.val}" }, stC)
                      else (.ok { handleId := max d stC.nextDirId + 1, rootPath := pathOfSegs (p ++ [leaf.val]) },
                        { stC with openDirs := (max d stC.nextDirId + 1, p ++ [leaf.val]) :: stC.openDirs, nextDirId := max d stC.nextDirId + 2 })
                    | some _ => (.error { kind := .notADirectory, path := some leaf.val, message := s!"not a directory: {leaf.val}" }, stC)
                | some _ => (.error { kind := .notADirectory, path := some curDh.rootPath, message := s!"not a directory: {curDh.rootPath}" }, stC) := ⟨_, rfl⟩
          rcases hSpec with ⟨d, hEq⟩
          rw [hEq, hLdC] at hOpen
          dsimp only at hOpen
          rw [hParC] at hOpen
          have hParXCF : (parM / 64 % 2 == 0) = false := by rw [hParXC]; decide
          simp only [hParXCF, Bool.false_eq_true, ↓reduceIte, List.map_nil, List.append_nil] at hFileC hOpen
          rw [hFileC] at hOpen
          cases hOpen
          exact ⟨_, rfl, rfl⟩
      rcases hErrOpen with ⟨e, hOpenErr, hKind⟩
      cases isRoot with
      | true =>
        simp only [↓reduceIte] at hOpenC ⊢
        simp only [Bind.bind, StateT.bind, hOpenErr]
        exact ⟨e, stC, rfl, hKind, rfl, hOpenC⟩
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte] at hOpenC ⊢
        rcases hOpenC with ⟨hCurPos, hCurOpen, hCurLt⟩
        simp only [Bind.bind, StateT.bind]
        rw [bracketCloseDirM_run, hOpenErr]
        dsimp only
        rw [vfsDirOps_closeDir_fresh curDh stC curPos hCurPos origOpen hCurOpen hCurLt]
        exact ⟨e, { stC with openDirs := origOpen }, rfl, hKind, rfl, rfl⟩
    | cons a rest ih =>
      intro isRoot curDh curPos origOpen stC hLdC hInvC hOpenC hAncC hFileC
      rcases hAncC 0 (Nat.zero_le _) with ⟨parM, hParC, _, hParXC⟩
      simp only [List.take_zero, List.map_nil, List.append_nil] at hParC
      rcases hAncC 1 (by simp) with ⟨nextM, hNextC, hNextR, _⟩
      simp only [List.take, List.map_cons, List.map_nil] at hNextC
      rcases vfsDirOps_openDirAt_dir_ok stC curDh a curPos parM nextM hLdC hParC hParXC hNextC (hNextR (by omega)) with
        ⟨nextDh, st1, hOpenOk⟩
      rcases vfsDirOps_openDirAt_ok curDh a stC nextDh st1 hOpenOk with
        ⟨hNextPos, _, hNextGt, pos', _, _, hLd', _, _, _, _, _, hSt1⟩
      rcases Option.some.inj (hLdC.symm.trans hLd') with rfl
      simp only [List.cons_append, walkDescendAuxM_cons]
      have hStepRec : ∀ (stM : VfsState) (baseOpen : List (Nat × List String)),
          stM.tree = stC.tree →
          DirHandleInvariant stM →
          lookupDir stM nextDh = some (curPos ++ [a.val]) →
          stM.openDirs = (nextDh.handleId, curPos ++ [a.val]) :: baseOpen →
          (∀ p ∈ baseOpen, p.1 < nextDh.handleId) →
          ∃ e st', Internal.walkDescendAuxM vfsDirOps false nextDh (rest ++ [leaf]) act stM = (.error e, st') ∧
            e.kind = .notADirectory ∧ st'.nodes = stC.nodes ∧ st'.openDirs = baseOpen := by
        intro stM baseOpen hTreeM hInvM hLdM hOpenM hLtM
        rcases ih false nextDh (curPos ++ [a.val]) baseOpen stM hLdM hInvM
          ⟨hNextPos, hOpenM, hLtM⟩
          (fun k hk => by
            rcases hAncC (k + 1) (Nat.succ_le_succ hk) with ⟨dk, hDk, hDkR, hDkX⟩
            refine ⟨dk, ?_, fun _ => hDkR (Nat.zero_lt_succ k), hDkX⟩
            rw [hTreeM]
            simpa [List.take, List.append_assoc] using hDk)
          (by rw [hTreeM]; simpa [List.append_assoc] using hFileC) with
          ⟨e, st', hRec, hKind, hNodes, hOpen'⟩
        exact ⟨e, st', hRec, hKind, hNodes.trans (nodes_eq_of_tree_eq' hTreeM), hOpen'⟩
      have hNextInv1 : DirHandleInvariant st1 := by
        intro id p hm
        rw [hSt1] at hm
        simp only [List.mem_cons, Prod.mk.injEq] at hm
        rcases hm with ⟨rfl, rfl⟩ | hOld
        · rw [hSt1]; dsimp only; exact ⟨hNextPos, Nat.lt_succ_self _⟩
        · have hOldInv := hInvC id p hOld
          rw [hSt1]; dsimp only; exact ⟨hOldInv.1, Nat.lt_trans hOldInv.2 (by omega)⟩
      cases isRoot with
      | true =>
        simp only [↓reduceIte] at hOpenC ⊢
        simp only [Bind.bind, StateT.bind, hOpenOk]
        have hLd1 : lookupDir st1 nextDh = some (curPos ++ [a.val]) := by
          rw [hSt1]
          exact lookupDir_cons_self stC nextDh.handleId (curPos ++ [a.val]) nextDh.rootPath hNextPos
        have hOpen1 : st1.openDirs = (nextDh.handleId, curPos ++ [a.val]) :: origOpen := by
          rw [hSt1, hOpenC]
        exact hStepRec st1 origOpen (by rw [hSt1]) hNextInv1 hLd1 hOpen1 (fun p hp => hNextGt p (hOpenC ▸ hp))
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte] at hOpenC ⊢
        rcases hOpenC with ⟨hCurPos, hCurOpen, hCurLt⟩
        simp only [Bind.bind, StateT.bind]
        rw [bracketCloseDirM_run, hOpenOk]
        dsimp only
        have hNextNeCur : nextDh.handleId ≠ curDh.handleId := by
          have hIn : (curDh.handleId, curPos) ∈ stC.openDirs := by rw [hCurOpen]; exact List.mem_cons_self
          have hLt := hNextGt (curDh.handleId, curPos) hIn
          omega
        have hOpen1 : st1.openDirs = (nextDh.handleId, curPos ++ [a.val]) :: (curDh.handleId, curPos) :: origOpen := by
          rw [hSt1, hCurOpen]
        have hClose1 : vfsDirOps.closeDir curDh st1 = (.ok (),
            { st1 with openDirs := (nextDh.handleId, curPos ++ [a.val]) :: origOpen }) := by
          rw [vfsDirOps_closeDir_def]
          have hCurNZ : (curDh.handleId == 0) = false := beq_false_of_ne (Nat.ne_of_gt hCurPos)
          have hFlt1 : (nextDh.handleId != curDh.handleId) = true := bne_iff_ne.mpr hNextNeCur
          have hFlt2 : (curDh.handleId != curDh.handleId) = false := bne_self_eq_false _
          simp only [hCurNZ, Bool.false_eq_true, ↓reduceIte, hOpen1, List.any_cons, beq_self_eq_true, Bool.true_or, Bool.or_true,
            List.filter_cons, hFlt1, hFlt2, Bool.false_eq_true]
          have hFiltTail : origOpen.filter (fun x => x.1 != curDh.handleId) = origOpen := by
            rw [List.filter_eq_self]
            intro ⟨id, p⟩ hMem
            simp only [bne_iff_ne, ne_eq]
            have hLtO := hCurLt (id, p) hMem
            omega
          rw [hFiltTail]
        rw [hClose1]
        dsimp only
        let stCl : VfsState := { st1 with openDirs := (nextDh.handleId, curPos ++ [a.val]) :: origOpen }
        have hInvCl : DirHandleInvariant stCl :=
          dirHandleInvariant_of_subset hNextInv1 (fun p hp => by
            dsimp only [stCl] at hp
            rw [hOpen1]
            simp only [List.mem_cons] at hp ⊢
            rcases hp with rfl | hOld
            · exact Or.inl rfl
            · exact Or.inr (Or.inr hOld)) rfl
        have hLdCl : lookupDir stCl nextDh = some (curPos ++ [a.val]) :=
          lookupDir_cons_self { st1 with openDirs := origOpen } nextDh.handleId (curPos ++ [a.val]) nextDh.rootPath hNextPos
        exact hStepRec stCl origOpen (by dsimp only [stCl]; rw [hSt1]) hInvCl hLdCl rfl (fun p hp => hNextGt p (by rw [hCurOpen]; exact List.mem_cons_of_mem _ hp))
  exact hAux pre true dh pos st.openDirs st hLd hInv rfl hAnc hFile

/-- Walking a directory whose permissions fail readable (`0o400`) returns `.permissionDenied`. -/
theorem walkRecM_single_perm_err (dh : DirHandle) (pos : List String) (unrd : EntryName)
    (m pm : Nat) (st : VfsState)
    (hLd : lookupDir st dh = some pos)
    (hPar : nodeAt st.tree pos = some (.dir pm)) (hX : pm / 64 % 2 = 1)
    (hUnrd : nodeAt st.tree (pos ++ [unrd.val]) = some (.dir m)) (hNoR : m / 256 % 2 = 0) :
    ∃ e st', Internal.walkRecM vfsDirOps dh [unrd] "." #[] 4096 st = (.error e, st') ∧
      e.kind = .permissionDenied ∧ st'.nodes = st.nodes ∧ st'.openDirs = st.openDirs := by
  let readFn : DirHandle → StateT VfsState Id (Except FsError (List EntryName × List String)) := fun dirDh => do
    let rRead ← vfsDirOps.readDirAt dirDh
    match rRead with
    | .error e => pure (.error e)
    | .ok rawNames => Internal.classifyChildrenM vfsDirOps dirDh (Internal.sortEntryNames rawNames) [] []
  have hReadErr : ∃ e st', Internal.walkDescendAuxM vfsDirOps true dh [unrd] readFn st = (.error e, st') ∧
      e.kind = .permissionDenied ∧ st'.nodes = st.nodes ∧ st'.openDirs = st.openDirs := by
    rw [walkDescendAuxM_cons]
    simp only [↓reduceIte, Bind.bind, StateT.bind]
    have hSpec : ∃ d : Nat, vfsDirOps.openDirAt dh unrd st =
        match lookupDir st dh with
        | none => (.error (mInvalidDirHandleErr dh), st)
        | some p =>
          match nodeAt st.tree p with
          | none => (.error { kind := .notFound, path := some dh.rootPath, message := "directory no longer exists" }, st)
          | some (.dir parM) =>
            if (parM / 64) % 2 == 0 then (.error { kind := .permissionDenied, path := some unrd.val, message := s!"permission denied: {unrd.val}" }, st)
            else match nodeAt st.tree (p ++ [unrd.val]) with
              | none => (.error { kind := .notFound, path := some unrd.val, message := s!"no such file or directory: {unrd.val}" }, st)
              | some (.symlink _ _) => (.error { kind := .invalidInput, path := some unrd.val, message := s!"symlink refused in subtree traversal: {unrd.val}" }, st)
              | some (.dir dm) =>
                if (dm / 256) % 2 == 0 then (.error { kind := .permissionDenied, path := some unrd.val, message := s!"permission denied: {unrd.val}" }, st)
                else (.ok { handleId := max d st.nextDirId + 1, rootPath := pathOfSegs (p ++ [unrd.val]) },
                  { st with openDirs := (max d st.nextDirId + 1, p ++ [unrd.val]) :: st.openDirs, nextDirId := max d st.nextDirId + 2 })
              | some _ => (.error { kind := .notADirectory, path := some unrd.val, message := s!"not a directory: {unrd.val}" }, st)
          | some _ => (.error { kind := .notADirectory, path := some dh.rootPath, message := s!"not a directory: {dh.rootPath}" }, st) := ⟨_, rfl⟩
    rcases hSpec with ⟨d, hEq⟩
    rw [hEq, hLd]
    dsimp only
    rw [hPar]
    have hXF : (pm / 64 % 2 == 0) = false := by rw [hX]; decide
    have hRT : (m / 256 % 2 == 0) = true := by simp [hNoR]
    simp only [hXF, Bool.false_eq_true, ↓reduceIte, hUnrd, hRT]
    exact ⟨_, st, rfl, rfl, rfl, rfl⟩
  rcases hReadErr with ⟨e, st', hRead, hKind, hNodes, hOpen⟩
  refine ⟨e, st', ?_, hKind, hNodes, hOpen⟩
  rw [show (4096 : Nat) = Nat.succ 4095 from rfl, Internal.walkRecM.eq_2]
  exact (stateM_bind_eq (m := Internal.walkDescendM vfsDirOps dh [unrd] readFn) hRead).trans
    (by simp [Pure.pure, StateT.pure])

/-- `walkRecM` fails `.ioError` whenever the target subtree exceeds remaining `fuel` while satisfying `VfsTreeValidSegs` and `vfsTreePermWalkable'`. -/
theorem walkRecM_depth_err : ∀ (fuel : Nat) (relSegs : List EntryName) (relLabel : String)
    (acc : Array WalkEntry) (rootDh : DirHandle) (pos : List String) (st : VfsState)
    (tsub : VfsTree),
    VfsKeysComplete st → lookupDir st rootDh = some pos → DirHandleInvariant st →
    (∀ s ∈ pos, validSeg s = true) →
    (∃ pm₀, nodeAt st.tree pos = some (.dir pm₀) ∧ pm₀ / 64 % 2 = 1) →
    (∀ k, 0 < k → k ≤ relSegs.length → ∃ dk, nodeAt st.tree (pos ++ (relSegs.take k).map (·.val)) = some (.dir dk) ∧
      dk / 256 % 2 = 1 ∧ dk / 64 % 2 = 1) →
    vfsTreeGet st.tree (pos ++ relSegs.map (·.val)) = some tsub →
    VfsTreeValidSegs tsub → vfsTreePermWalkable' tsub → ¬ VfsTreeWalkable fuel tsub →
    ∃ e st', Internal.walkRecM vfsDirOps rootDh relSegs relLabel acc fuel st = (.error e, st') ∧
      e.kind = .ioError ∧ st'.nodes = st.nodes ∧ st'.openDirs = st.openDirs := by
  intro fuel
  induction fuel with
  | zero =>
    intro relSegs relLabel acc rootDh pos st _ _ _ _ _ _ _ _ _ _ _
    rw [Internal.walkRecM.eq_1]
    exact ⟨_, st, rfl, rfl, rfl, rfl⟩
  | succ f ih =>
    intro relSegs relLabel acc rootDh pos st tsub hKeys hLd hInv hPosValid hPosDir hAnc hGet hVS hPerm hNotW
    cases tsub with
    | file d m => rw [VfsTreeWalkable.eq_1] at hNotW; exact absurd trivial hNotW
    | symlink tgt m => rw [VfsTreeWalkable.eq_2] at hNotW; exact absurd trivial hNotW
    | dir dm ch =>
      have hPerm0 := hPerm [] dm (by simp [nodeAt, vfsTreeGet, vfsTreeTopNode])
      have hDmR : dm / 256 % 2 = 1 := hPerm0.1
      have hDmX : dm / 64 % 2 = 1 := hPerm0.2
      rw [VfsTreeWalkable.eq_4] at hNotW
      have hBadExists : ∃ name sub, ch name = some sub ∧ ¬ VfsTreeWalkable f sub :=
        Classical.byContradiction fun hAll => hNotW ⟨hDmR, hDmX, fun nm sb hs =>
          Classical.byContradiction fun hNot => hAll ⟨nm, sb, hs, hNot⟩⟩
      rcases hBadExists with ⟨badName, badSub, hBadCh, hBadNotW⟩
      have hBadValid : validSeg badName = true := hVS [badName] (by simp [nodeAt, vfsTreeGet, hBadCh]) badName List.mem_cons_self
      let badEnt : EntryName := ⟨badName, hBadValid⟩
      let dirPos := pos ++ relSegs.map (·.val)
      have hDirValid : ∀ s ∈ dirPos, validSeg s = true := by
        intro s hs
        rcases List.mem_append.mp hs with hp | hr
        · exact hPosValid s hp
        · simp only [List.mem_map] at hr; rcases hr with ⟨e, _, rfl⟩; exact e.valid
      have hDirNd : nodeAt st.tree dirPos = some (.dir dm) := by
        simp only [dirPos, nodeAt, hGet, vfsTreeTopNode, Option.map_some]
      let sorted := Internal.sortEntryNames (mVfsReadDirAtEntries st dirPos)
      let dirs := sorted.filter (isDirAt st dirPos)
      let files := (sorted.filter (fun n => !(isDirAt st dirPos n))).map (·.val)
      have hBadLive : nodeAt st.tree (dirPos ++ [badEnt.val]) ≠ none := by
        dsimp only [dirPos, badEnt]
        rw [nodeAt_sub_of_vfsTreeGet hGet]
        simp [nodeAt, vfsTreeGet, hBadCh]
      have hBadInRaw : badEnt ∈ (mVfsReadDirAtEntries st dirPos).toList := by
        have hBadKey : pathOfSegs (dirPos ++ [badEnt.val]) ∈ st.keys := hKeys _ hBadLive
        exact mVfsReadDirAtEntries_mem_of_key st dirPos badEnt hDirValid hBadKey hBadLive
      have hBadInSorted : badEnt ∈ sorted :=
        (List.mergeSort_perm (mVfsReadDirAtEntries st dirPos).toList (fun a b => decide (a.val ≤ b.val))).mem_iff.mpr hBadInRaw
      have hBadDir : ∃ badDm badCh, badSub = .dir badDm badCh := by
        cases badSub with
        | file _ _ => rw [VfsTreeWalkable.eq_1] at hBadNotW; exact absurd trivial hBadNotW
        | symlink _ _ => rw [VfsTreeWalkable.eq_2] at hBadNotW; exact absurd trivial hBadNotW
        | dir m c => exact ⟨m, c, rfl⟩
      rcases hBadDir with ⟨badDm, badCh, hBadEq⟩
      have hBadInDirs : badEnt ∈ dirs := by
        refine List.mem_filter.mpr ⟨hBadInSorted, ?_⟩
        unfold isDirAt
        dsimp only [dirPos, badEnt]
        rw [nodeAt_sub_of_vfsTreeGet hGet]
        simp [nodeAt, vfsTreeGet, hBadCh, hBadEq, vfsTreeTopNode]
      have hSortedLive : ∀ n ∈ sorted, nodeAt st.tree (dirPos ++ [n.val]) ≠ none := by
        intro n hn
        have hPermS := List.mergeSort_perm (mVfsReadDirAtEntries st dirPos).toList (fun a b => decide (a.val ≤ b.val))
        exact mVfsReadDirAtEntries_mem_sound st dirPos hDirValid n (hPermS.mem_iff.mp hn)
      let readFn : DirHandle → StateT VfsState Id (Except FsError (List EntryName × List String)) := fun dirDh => do
        let rRead ← vfsDirOps.readDirAt dirDh
        match rRead with
        | .error e => pure (.error e)
        | .ok rawNames => Internal.classifyChildrenM vfsDirOps dirDh (Internal.sortEntryNames rawNames) [] []
      have hWalkRead := walkDescendM_ok relSegs rootDh pos st readFn
        hLd hInv
        (fun k hk => by
          by_cases hk0 : k = 0
          · subst hk0
            rcases hPosDir with ⟨pm₀, hP0, hP0X⟩
            exact ⟨pm₀, by simpa using hP0, fun h => absurd h (Nat.not_lt_zero 0), hP0X⟩
          · rcases hAnc k (Nat.pos_of_ne_zero hk0) (Nat.le_of_lt hk) with ⟨dk, hDk, hDkR, hDkX⟩
            exact ⟨dk, hDk, fun _ => hDkR, hDkX⟩)
        (fun _ => ⟨dm, hDirNd, hDmR⟩)
      have hReadStage : ∀ (dhUse : DirHandle) (stUse : VfsState),
          lookupDir stUse dhUse = some dirPos → stUse.tree = st.tree → stUse.keys = st.keys →
          readFn dhUse stUse = (.ok (dirs, files), stUse) := by
        intro dhUse stUse hLdUse hTreeUse hKeysUse
        have hDirUse : nodeAt stUse.tree dirPos = some (.dir dm) := by rw [hTreeUse]; exact hDirNd
        have hDmRF : (dm / 256 % 2 == 0) = false := by rw [hDmR]; decide
        have hReadOk : vfsDirOps.readDirAt dhUse stUse = (.ok (mVfsReadDirAtEntries stUse dirPos), stUse) := by
          rw [vfsDirOps_readDirAt_def, hLdUse]
          dsimp only
          rw [hDirUse]
          simp only [hDmRF, Bool.false_eq_true, ↓reduceIte]
        have hEntriesEq : mVfsReadDirAtEntries stUse dirPos = mVfsReadDirAtEntries st dirPos := by
          unfold mVfsReadDirAtEntries
          rw [hKeysUse, nodes_eq_of_tree_eq' hTreeUse]
        rw [hEntriesEq] at hReadOk
        have hIsDirEq : isDirAt stUse dirPos = isDirAt st dirPos := by
          funext n
          simp [isDirAt, hTreeUse]
        dsimp only [readFn]
        simp only [Bind.bind, StateT.bind, hReadOk]
        rw [classifyChildrenM_ok dhUse dirPos stUse dm hLdUse hDirUse hDmX sorted [] []
          (fun n hn => by rw [hTreeUse]; exact hSortedLive n hn), hIsDirEq]
        rfl
      have hAfterRead : ∃ stR,
          Internal.walkDescendM vfsDirOps rootDh relSegs readFn st = (.ok (dirs, files), stR) ∧
          stR.tree = st.tree ∧ stR.keys = st.keys ∧ stR.cwd = st.cwd ∧ stR.nonce = st.nonce ∧
          stR.locks = st.locks ∧ stR.openDirs = st.openDirs ∧ DirHandleInvariant stR ∧ lookupDir stR rootDh = some pos := by
        by_cases hRelNil : relSegs = []
        · subst hRelNil
          refine ⟨st, ?_, rfl, rfl, rfl, rfl, rfl, rfl, hInv, hLd⟩
          rw [hWalkRead.1 rfl]
          exact hReadStage rootDh st (by simpa [dirPos] using hLd) rfl rfl
        · rcases hWalkRead.2 hRelNil with
            ⟨dirDh, stMid, hPosDh, hLdMid, hTreeMid, hKeysMid, hCwdMid, hNonceMid, hLocksMid,
              hInvMid, hLtMid, hOpenMid, hWalkEq⟩
          have hRS := hReadStage dirDh stMid hLdMid hTreeMid hKeysMid
          have hCl := vfsDirOps_closeDir_fresh dirDh stMid dirPos hPosDh st.openDirs hOpenMid hLtMid
          refine ⟨{ stMid with openDirs := st.openDirs }, ?_, hTreeMid, hKeysMid, hCwdMid, hNonceMid,
            hLocksMid, rfl, ?_, ?_⟩
          · rw [hWalkEq, bracketCloseDirM_run, hRS]
            dsimp only
            rw [hCl]
          · exact dirHandleInvariant_of_subset hInvMid (fun p hp => by rw [hOpenMid]; exact List.mem_cons_of_mem _ hp) rfl
          · unfold lookupDir at hLd ⊢; exact hLd
      rcases hAfterRead with ⟨stR, hReadRes, hTreeR, hKeysR, hCwdR, hNonceR, hLocksR, hOpenR, hInvR, hLdR⟩
      have hChErr : ∀ (ds : List EntryName) (curAcc : Array WalkEntry) (stC : VfsState),
          (∀ d ∈ ds, d ∈ dirs) →
          badEnt ∈ ds →
          VfsKeysComplete stC → lookupDir stC rootDh = some pos → DirHandleInvariant stC →
          stC.tree = st.tree → stC.keys = st.keys → stC.cwd = st.cwd → stC.nonce = st.nonce →
          stC.locks = st.locks → stC.openDirs = st.openDirs →
          ∃ e st', Internal.walkChildrenM vfsDirOps rootDh relSegs relLabel f curAcc ds stC = (.error e, st') ∧
            e.kind = .ioError ∧ st'.nodes = st.nodes ∧ st'.openDirs = st.openDirs := by
        intro ds
        induction ds with
        | nil => intro _ _ _ hMem; cases hMem
        | cons d rest ihDs =>
          intro curAcc stC hSubD hBadMem hKCC hLdC hInvC hTC hKC hCC hNC hLC hOC
          have hdFilt := List.mem_filter.mp (hSubD d List.mem_cons_self)
          have hIsD : isDirAt st dirPos d = true := hdFilt.2
          have hdSub : ∃ dmD chD, ch d.val = some (.dir dmD chD) ∧
              nodeAt st.tree (dirPos ++ [d.val]) = some (.dir dmD) := by
            have hNdEx : ∃ dmD, nodeAt st.tree (dirPos ++ [d.val]) = some (.dir dmD) := by
              unfold isDirAt at hIsD
              cases hNd : nodeAt st.tree (dirPos ++ [d.val]) with
              | none => simp [hNd] at hIsD
              | some nd =>
                cases nd with
                | file _ _ | symlink _ _ => simp [hNd] at hIsD
                | dir dmD => exact ⟨dmD, rfl⟩
            rcases hNdEx with ⟨dmD, hNd⟩
            have hNdSub := hNd
            rw [nodeAt_sub_of_vfsTreeGet hGet] at hNdSub
            have hChEx : ∃ chD, ch d.val = some (.dir dmD chD) := by
              cases hChD : ch d.val with
              | none => simp [nodeAt, vfsTreeGet, hChD] at hNdSub
              | some s =>
                cases s with
                | file _ _ | symlink _ _ => simp [nodeAt, vfsTreeGet, hChD, vfsTreeTopNode] at hNdSub
                | dir dmD' chD =>
                  simp [nodeAt, vfsTreeGet, hChD, vfsTreeTopNode] at hNdSub
                  cases hNdSub
                  exact ⟨chD, rfl⟩
            rcases hChEx with ⟨chD, hChD⟩
            exact ⟨dmD, chD, hChD, hNd⟩
          rcases hdSub with ⟨dmD, chD, hChD, hNdD⟩
          have hGetDC : vfsTreeGet stC.tree (pos ++ (relSegs ++ [d]).map (·.val)) = some (.dir dmD chD) := by
            rw [hTC, List.map_append, List.map_singleton, ← List.append_assoc]
            change vfsTreeGet st.tree (dirPos ++ [d.val]) = some (.dir dmD chD)
            rw [vfsTreeGet_sub_of_vfsTreeGet hGet]
            simp [vfsTreeGet, hChD]
          have hPosDirC : ∃ pm₀, nodeAt stC.tree pos = some (.dir pm₀) ∧ pm₀ / 64 % 2 = 1 := by
            rcases hPosDir with ⟨pm₀, hP0, hP0X⟩
            exact ⟨pm₀, by rw [hTC]; exact hP0, hP0X⟩
          have hVSD : VfsTreeValidSegs (.dir dmD chD) := by
            intro segs hNe s hs
            apply hVS (d.val :: segs) _ s (List.mem_cons_of_mem d.val hs)
            intro hN0
            apply hNe
            simpa [nodeAt, vfsTreeGet, hChD] using hN0
          have hPermD : vfsTreePermWalkable' (.dir dmD chD) := by
            intro segs m hm
            apply hPerm (d.val :: segs) m
            simpa [nodeAt, vfsTreeGet, hChD] using hm
          have hPermD0 := hPermD [] dmD (by simp [nodeAt, vfsTreeGet, vfsTreeTopNode])
          have hAncC : ∀ k, 0 < k → k ≤ (relSegs ++ [d]).length →
              ∃ dk, nodeAt stC.tree (pos ++ ((relSegs ++ [d]).take k).map (·.val)) = some (.dir dk) ∧
                dk / 256 % 2 = 1 ∧ dk / 64 % 2 = 1 := by
            intro k hkPos hkLe
            rw [List.length_append, List.length_singleton] at hkLe
            by_cases hkIn : k ≤ relSegs.length
            · rcases hAnc k hkPos hkIn with ⟨dk, hDk, hR, hX⟩
              refine ⟨dk, ?_, hR, hX⟩
              rw [hTC, List.take_append_of_le_length hkIn]
              exact hDk
            · have hkEq : k = relSegs.length + 1 := by omega
              subst hkEq
              rw [List.take_of_length_le (by simp)]
              rw [List.map_append, List.map_singleton, ← List.append_assoc, hTC]
              exact ⟨dmD, hNdD, hPermD0.1, hPermD0.2⟩
          rw [Internal.walkChildrenM.eq_2]
          simp only [Bind.bind, StateT.bind]
          let childLabel := if relLabel == "." then d.val else relLabel ++ "/" ++ d.val
          by_cases hWD : VfsTreeWalkable f (.dir dmD chD)
          · cases f with
            | zero => rw [VfsTreeWalkable.eq_3] at hWD; exact False.elim hWD
            | succ f' =>
              have hBadNeD : badEnt ≠ d := by
                intro hEq
                have hEqV : d.val = badName := congrArg EntryName.val hEq.symm
                rw [hEqV, hBadCh, hBadEq] at hChD
                cases hChD
                rw [hBadEq] at hBadNotW
                exact hBadNotW hWD
              have hBadInRest : badEnt ∈ rest := by
                rcases List.mem_cons.mp hBadMem with rfl | hR
                · exact absurd rfl hBadNeD
                · exact hR
              rcases walkRecM_ok f' (relSegs ++ [d]) childLabel curAcc rootDh pos stC dmD chD
                hKCC hLdC hInvC hPosValid hPosDirC hAncC hGetDC hWD with
                ⟨dTail, stD, hWalkD, hTD, hKD, hCD, hND, hLD, hOD, hInvD, _⟩
              have hLdD : lookupDir stD rootDh = some pos := by unfold lookupDir at hLd ⊢; rw [hOD, hOC]; exact hLd
              have hKCD : VfsKeysComplete stD := by
                intro segs hNe
                rw [hKD, hKC]
                apply hKeys segs
                rw [← hTC, ← hTD]
                exact hNe
              rw [hWalkD]
              dsimp only
              exact ihDs (curAcc ++ dTail.toArray) stD
                (fun x hx => hSubD x (List.mem_cons_of_mem _ hx)) hBadInRest
                hKCD hLdD hInvD (hTD.trans hTC) (hKD.trans hKC) (hCD.trans hCC) (hND.trans hNC)
                (hLD.trans hLC) (hOD.trans hOC)
          · rcases ih (relSegs ++ [d]) childLabel curAcc rootDh pos stC (.dir dmD chD)
              hKCC hLdC hInvC hPosValid hPosDirC hAncC hGetDC hVSD hPermD hWD with
              ⟨e, st', hErrD, hKindD, hNodesD, hOpenD⟩
            rw [hErrD]
            exact ⟨e, st', rfl, hKindD, hNodesD.trans (nodes_eq_of_tree_eq' hTC), hOpenD.trans hOC⟩
      let entry : WalkEntry := { root := relLabel, dirs := (dirs.map (·.val)).toArray, files := files.toArray }
      rcases hChErr dirs (acc.push entry) stR (fun _ h => h) hBadInDirs
        (by intro segs hNe; rw [hKeysR]; apply hKeys segs; rw [← hTreeR]; exact hNe)
        hLdR hInvR hTreeR hKeysR hCwdR hNonceR hLocksR hOpenR with ⟨e, st', hChRes, hKind, hNodes, hOpen⟩
      refine ⟨e, st', ?_, hKind, hNodes, hOpen⟩
      rw [Internal.walkRecM.eq_2]
      refine (stateM_bind_eq hReadRes).trans ?_
      dsimp only
      exact hChRes

/-- `rmtreeNonDirPrefixM` preserves any live directory `d ∈ items` and every node in its subtree, returning `.ok (some (subDir, rest))`. -/
theorem rmtreeNonDirPrefixM_preserves_dir (dirDh : DirHandle) (dirPos : List String) :
    ∀ (items : List EntryName) (st : VfsState) (cm : Nat) (ch : String → Option VfsTree)
      (d : EntryName) (dm : Nat),
      d ∈ items →
      lookupDir st dirDh = some dirPos →
      vfsTreeGet st.tree dirPos = some (.dir cm ch) →
      cm / 128 % 2 = 1 → cm / 64 % 2 = 1 →
      nodeAt st.tree (dirPos ++ [d.val]) = some (.dir dm) →
      ∃ subDir rest st', Internal.rmtreeNonDirPrefixM vfsDirOps dirDh items st = (.ok (some (subDir, rest)), st') ∧
        (d = subDir ∨ d ∈ rest) ∧
        (∃ dmSub, nodeAt st'.tree (dirPos ++ [subDir.val]) = some (.dir dmSub)) ∧
        nodeAt st'.tree (dirPos ++ [d.val]) = some (.dir dm) ∧
        (∀ q, nodeAt st'.tree ((dirPos ++ [d.val]) ++ q) = nodeAt st.tree ((dirPos ++ [d.val]) ++ q)) ∧
        (∃ ch', vfsTreeGet st'.tree dirPos = some (.dir cm ch')) ∧
        SameOutside dirPos st st' ∧
        TreeShrunk st'.tree st.tree ∧
        st'.keys = st.keys ∧ st'.openDirs = st.openDirs ∧ st'.locks = st.locks ∧ st'.nextDirId = st.nextDirId ∧
        (VfsKeysComplete st → VfsKeysComplete st') := by
  intro items
  induction items with
  | nil => intro _ _ _ _ _ hMem; cases hMem
  | cons c cs ih =>
    intro st cm ch d dm hMem hLd hGet hW hX hDirD
    have hDirNd : nodeAt st.tree dirPos = some (.dir cm) := by
      simp [nodeAt, hGet, vfsTreeTopNode]
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
      have hcNeD : c ≠ d := by
        intro rfl
        rw [hChild] at hDirD
        cases hDirD
      have hdInCs : d ∈ cs := by
        rcases List.mem_cons.mp hMem with rfl | hR
        · exact absurd rfl hcNeD
        · exact hR
      dsimp only
      simp only [show (FsErrorKind.notFound == FsErrorKind.notFound) = true from rfl, ↓reduceIte]
      exact ih st cm ch d dm hdInCs hLd hGet hW hX hDirD
    | some nd =>
      cases nd with
      | dir dmC =>
        simp only [vfsToStat, show (EntryKind.dir == EntryKind.dir) = true from rfl, ↓reduceIte]
        exact ⟨c, cs, st, rfl, List.mem_cons.mp hMem, ⟨dmC, hChild⟩, hDirD, fun _ => rfl, ⟨ch, hGet⟩,
          SameOutside_refl dirPos st, treeShrunk_refl st.tree, rfl, rfl, rfl, rfl, id⟩
      | file _ _ | symlink _ _ =>
        have hcNeD : c ≠ d := by
          intro rfl
          rw [hChild] at hDirD
          cases hDirD
        have hdInCs : d ∈ cs := by
          rcases List.mem_cons.mp hMem with rfl | hR
          · exact absurd rfl hcNeD
          · exact hR
        have hcValNeD : c.val ≠ d.val := fun heq => hcNeD (by cases c; cases d; simp at heq; subst heq; rfl)
        dsimp only
        simp only [vfsToStat, show (EntryKind.file == EntryKind.dir) = false from rfl,
          show (EntryKind.symlink == EntryKind.dir) = false from rfl, Bool.false_eq_true, ↓reduceIte,
          Bind.bind, StateT.bind]
        rw [vfsDirOps_unlinkAt_def, hLd]
        dsimp only
        rw [hDirNd]
        simp only [hWF, Bool.false_eq_true, ↓reduceIte, hChild]
        let st1 : VfsState :=
          { tree := vfsTreeSet st.tree (dirPos ++ [c.val]) none, keys := st.keys, cwd := st.cwd,
            nonce := st.nonce, locks := st.locks, nextLockId := st.nextLockId,
            openDirs := st.openDirs, nextDirId := st.nextDirId }
        have hNotSelf : ¬ (dirPos ++ [c.val] <+: dirPos) := by
          intro hP; have hL := List.IsPrefix.length_le hP; simp at hL; omega
        have hNotSub : ∀ q, ¬ (dirPos ++ [c.val] <+: (dirPos ++ [d.val]) ++ q) := by
          intro q hP
          rcases hP with ⟨r, hr⟩
          rw [List.append_assoc, List.append_assoc] at hr
          have hRest := List.append_cancel_left hr
          exact hcValNeD (List.cons.inj hRest).1
        have hDirNd1 : nodeAt st1.tree dirPos = some (.dir cm) := by
          change nodeAt (vfsTreeSet st.tree (dirPos ++ [c.val]) none) dirPos = some (.dir cm)
          rw [nodeAt_vfsTreeSet_outside st.tree dirPos c.val none dirPos ⟨cm, ch, hGet⟩ hNotSelf, hDirNd]
        rcases vfsTreeGet_dir_of_nodeAt hDirNd1 with ⟨ch1, hGet1⟩
        have hSubEq1 : ∀ q, nodeAt st1.tree ((dirPos ++ [d.val]) ++ q) = nodeAt st.tree ((dirPos ++ [d.val]) ++ q) := by
          intro q
          change nodeAt (vfsTreeSet st.tree (dirPos ++ [c.val]) none) ((dirPos ++ [d.val]) ++ q) = _
          exact nodeAt_vfsTreeSet_outside st.tree dirPos c.val none ((dirPos ++ [d.val]) ++ q) ⟨cm, ch, hGet⟩ (hNotSub q)
        have hDirD1 : nodeAt st1.tree (dirPos ++ [d.val]) = some (.dir dm) := by
          have hEq := hSubEq1 []
          simp only [List.append_nil] at hEq
          exact hEq.trans hDirD
        have hSame01 : SameOutside dirPos st st1 := by
          apply SameOutside_mono ⟨[c.val], rfl⟩
          intro p hNot
          change vfsTreeNodes (vfsTreeSet st.tree (dirPos ++ [c.val]) none) p = vfsTreeNodes st.tree p
          unfold vfsTreeNodes
          split
          · exact nodeAt_vfsTreeSet_outside st.tree dirPos c.val none (vfsSplitSegs p) ⟨cm, ch, hGet⟩ hNot
          · rfl
        have hShrunk01 : TreeShrunk st1.tree st.tree := treeShrunk_set_none st.tree dirPos c.val ⟨cm, ch, hGet⟩
        rcases ih st1 cm ch1 d dm hdInCs hLd hGet1 hW hX hDirD1 with
          ⟨subDir, rest, st', hRec, hDMem, hSubDirNd, hD', hSubEq', hCh', hSame1, hShrunk1, hKeys1, hOpen1, hLocks1, hNid1, hKC1⟩
        exact ⟨subDir, rest, st', hRec, hDMem, hSubDirNd, hD', fun q => (hSubEq' q).trans (hSubEq1 q), hCh',
          SameOutside_trans hSame01 hSame1, treeShrunk_trans hShrunk1 hShrunk01, hKeys1, hOpen1, hLocks1, hNid1,
          fun hK => hKC1 (vfsKeysComplete_treeShrunk st st1 hK rfl hShrunk01)⟩

/-- `rmtreeDirAtM` fails `.ioError` whenever the target subtree exceeds remaining `fuel` while satisfying `VfsTreeValidSegs` and `vfsTreePermRemovable'`. -/
theorem rmtreeDirAtM_depth_err : ∀ (fuel : Nat) (parSegs : List EntryName) (leaf : EntryName)
    (rootDh : DirHandle) (pos : List String) (st : VfsState) (tsub : VfsTree),
    VfsKeysComplete st → lookupDir st rootDh = some pos → DirHandleInvariant st →
    (∀ s ∈ pos, validSeg s = true) →
    (∃ pm₀, nodeAt st.tree pos = some (.dir pm₀) ∧ (parSegs = [] → pm₀ / 128 % 2 = 1) ∧ pm₀ / 64 % 2 = 1) →
    (∀ k, 0 < k → k ≤ parSegs.length →
      ∃ dm, nodeAt st.tree (pos ++ (parSegs.take k).map (·.val)) = some (.dir dm) ∧
        dm / 256 % 2 = 1 ∧ dm / 128 % 2 = 1 ∧ dm / 64 % 2 = 1) →
    vfsTreeGet st.tree (pos ++ (parSegs ++ [leaf]).map (·.val)) = some tsub →
    VfsTreeValidSegs tsub → vfsTreePermRemovable' tsub → ¬ VfsTreeRemovable fuel tsub →
    ∃ e st', Internal.rmtreeDirAtM vfsDirOps rootDh parSegs leaf fuel st = (.error e, st') ∧
      e.kind = .ioError ∧ st'.openDirs = st.openDirs := by
  intro fuel
  induction fuel with
  | zero =>
    intro parSegs leaf rootDh pos st _ _ _ _ _ _ _ _ _ _ _
    rw [Internal.rmtreeDirAtM.eq_1]
    exact ⟨_, st, rfl, rfl, rfl⟩
  | succ f ih =>
    intro parSegs leaf rootDh pos st tsub hKeys hLd hInv hPosValid hPosDir hMidAnc hGet hVS hPerm hNotR
    cases tsub with
    | file d m => rw [VfsTreeRemovable.eq_1] at hNotR; exact absurd trivial hNotR
    | symlink tgt m => rw [VfsTreeRemovable.eq_2] at hNotR; exact absurd trivial hNotR
    | dir cm ch =>
      have hPerm0 := hPerm [] cm (by simp [nodeAt, vfsTreeGet, vfsTreeTopNode])
      have hCmR : cm / 256 % 2 = 1 := hPerm0.1
      have hCmW : cm / 128 % 2 = 1 := hPerm0.2.1
      have hCmX : cm / 64 % 2 = 1 := hPerm0.2.2
      rw [VfsTreeRemovable.eq_4] at hNotR
      have hBadExists : ∃ name sub, ch name = some sub ∧ ¬ VfsTreeRemovable f sub :=
        Classical.byContradiction fun hAll => hNotR ⟨hCmR, hCmW, hCmX, fun nm sb hs =>
          Classical.byContradiction fun hNot => hAll ⟨nm, sb, hs, hNot⟩⟩
      rcases hBadExists with ⟨badName, badSub, hBadCh, hBadNotR⟩
      have hBadValid : validSeg badName = true := hVS [badName] (by simp [nodeAt, vfsTreeGet, hBadCh]) badName List.mem_cons_self
      let badEnt : EntryName := ⟨badName, hBadValid⟩
      have hBadDir : ∃ badDm badCh, badSub = .dir badDm badCh := by
        cases badSub with
        | file _ _ => rw [VfsTreeRemovable.eq_1] at hBadNotR; exact absurd trivial hBadNotR
        | symlink _ _ => rw [VfsTreeRemovable.eq_2] at hBadNotR; exact absurd trivial hBadNotR
        | dir m c => exact ⟨m, c, rfl⟩
      rcases hBadDir with ⟨badDm, badCh, hBadEq⟩
      let dirSegs := parSegs ++ [leaf]
      let dirPos := pos ++ dirSegs.map (·.val)
      have hDirValid : ∀ s ∈ dirPos, validSeg s = true := by
        intro s hs
        rcases List.mem_append.mp hs with hp | hd
        · exact hPosValid s hp
        · simp only [List.mem_map] at hd; rcases hd with ⟨e, _, rfl⟩; exact e.valid
      have hDirNd : nodeAt st.tree dirPos = some (.dir cm) := by
        simp only [dirPos, dirSegs, nodeAt, hGet, vfsTreeTopNode, Option.map_some]
      let sorted := Internal.sortEntryNames (mVfsReadDirAtEntries st dirPos)
      have hBadLive : nodeAt st.tree (dirPos ++ [badEnt.val]) ≠ none := by
        dsimp only [dirPos, dirSegs, badEnt]
        rw [nodeAt_sub_of_vfsTreeGet hGet]
        simp [nodeAt, vfsTreeGet, hBadCh]
      have hBadInSorted : badEnt ∈ sorted := by
        have hBadKey : pathOfSegs (dirPos ++ [badEnt.val]) ∈ st.keys := hKeys _ hBadLive
        have hRaw := mVfsReadDirAtEntries_mem_of_key st dirPos badEnt hDirValid hBadKey hBadLive
        exact (List.mergeSort_perm (mVfsReadDirAtEntries st dirPos).toList (fun a b => decide (a.val ≤ b.val))).mem_iff.mpr hRaw
      have hWalkRead := walkDescendM_ok dirSegs rootDh pos st
        (fun dirDh => vfsDirOps.readDirAt dirDh) hLd hInv
        (fun k hk => by
          by_cases hk0 : k = 0
          · subst hk0
            rcases hPosDir with ⟨pm₀, hP0, _, hP0X⟩
            exact ⟨pm₀, by simpa using hP0, fun h => absurd h (Nat.not_lt_zero 0), hP0X⟩
          · rcases hMidAnc k (Nat.pos_of_ne_zero hk0) (by
              simp only [dirSegs, List.length_append, List.length_singleton] at hk; omega) with
              ⟨dk, hDk, hDkR, _, hDkX⟩
            refine ⟨dk, ?_, fun _ => hDkR, hDkX⟩
            rw [show dirSegs.take k = parSegs.take k from List.take_append_of_le_length (by
              simp only [dirSegs, List.length_append, List.length_singleton] at hk; omega)]
            exact hDk)
        (fun _ => ⟨cm, hDirNd, hCmR⟩)
      have hCmRF : (cm / 256 % 2 == 0) = false := by rw [hCmR]; decide
      have hAfterRead : ∃ stClose,
          Internal.walkDescendM vfsDirOps rootDh dirSegs (fun dirDh => vfsDirOps.readDirAt dirDh) st =
            (.ok (mVfsReadDirAtEntries st dirPos), stClose) ∧
          stClose.tree = st.tree ∧ stClose.keys = st.keys ∧ stClose.openDirs = st.openDirs ∧
          DirHandleInvariant stClose ∧ lookupDir stClose rootDh = some pos := by
        rcases hWalkRead.2 (by simp [dirSegs]) with
          ⟨dirDh, stMid, hPosDh, hLdMid, hTreeMid, hKeysMid, _, _, _, hInvMid, hLtMid, hOpenMid, hWalkEq⟩
        have hDirNdMid : nodeAt stMid.tree dirPos = some (.dir cm) := by rw [hTreeMid]; exact hDirNd
        have hReadOk : vfsDirOps.readDirAt dirDh stMid = (.ok (mVfsReadDirAtEntries st dirPos), stMid) := by
          rw [vfsDirOps_readDirAt_def, hLdMid]
          dsimp only
          rw [hDirNdMid]
          simp only [hCmRF, Bool.false_eq_true, ↓reduceIte]
          congr 2
          unfold mVfsReadDirAtEntries
          rw [hKeysMid, nodes_eq_of_tree_eq' hTreeMid]
        have hCl := vfsDirOps_closeDir_fresh dirDh stMid dirPos hPosDh st.openDirs hOpenMid hLtMid
        refine ⟨{ stMid with openDirs := st.openDirs }, ?_, hTreeMid, hKeysMid, rfl, ?_, ?_⟩
        · rw [hWalkEq, bracketCloseDirM_run, hReadOk]
          dsimp only
          rw [hCl]
        · exact dirHandleInvariant_of_subset hInvMid (fun p hp => by rw [hOpenMid]; exact List.mem_cons_of_mem _ hp) rfl
        · unfold lookupDir at hLd ⊢; exact hLd
      rcases hAfterRead with ⟨stClose, hReadDone, hTreeClose, hKeysClose, hOpenClose, hInvClose, hLdClose⟩
      have hProcErr : ∀ (n : Nat) (items : List EntryName) (stP : VfsState) (chP : String → Option VfsTree),
          items.length ≤ n →
          badEnt ∈ items →
          nodeAt stP.tree (dirPos ++ [badEnt.val]) = some (.dir badDm) →
          (∀ q, nodeAt stP.tree ((dirPos ++ [badEnt.val]) ++ q) = nodeAt badSub q) →
          VfsKeysComplete stP → lookupDir stP rootDh = some pos → DirHandleInvariant stP →
          (∃ pm₀, nodeAt stP.tree pos = some (.dir pm₀) ∧ pm₀ / 64 % 2 = 1) →
          (∀ k, 0 < k → k ≤ dirSegs.length →
            ∃ dk, nodeAt stP.tree (pos ++ (dirSegs.take k).map (·.val)) = some (.dir dk) ∧
              dk / 256 % 2 = 1 ∧ dk / 128 % 2 = 1 ∧ dk / 64 % 2 = 1) →
          vfsTreeGet stP.tree dirPos = some (.dir cm chP) →
          VfsTreeValidSegs (.dir cm chP) →
          vfsTreePermRemovable' (.dir cm chP) →
          ∃ e st', Internal.rmtreeProcessM vfsDirOps rootDh dirSegs
              (fun subDir => Internal.rmtreeDirAtM vfsDirOps rootDh dirSegs subDir f) n items stP = (.error e, st') ∧
            e.kind = .ioError ∧ st'.openDirs = stP.openDirs := by
        intro n
        induction n with
        | zero => intro items _ _ hLen hBad; cases items <;> simp at hLen hBad
        | succ n' ihN =>
          intro items stP chP hLen hBadIn hBadNd hBadNodes hKCP hLdP hInvP hPosDirP hAncP hGetP hVSP hPermP
          rcases items with _ | ⟨hd, tl⟩
          · cases hBadIn
          · rw [Internal.rmtreeProcessM.eq_3]
            simp only [Bind.bind, StateT.bind]
            have hWalkPfx := walkDescendM_ok dirSegs rootDh pos stP
              (fun dirDh => Internal.rmtreeNonDirPrefixM vfsDirOps dirDh (hd :: tl))
              hLdP hInvP
              (fun k hk => by
                by_cases hk0 : k = 0
                · subst hk0
                  rcases hPosDirP with ⟨pm₀, hP0, hP0X⟩
                  exact ⟨pm₀, by simpa using hP0, fun h => absurd h (Nat.not_lt_zero 0), hP0X⟩
                · rcases hAncP k (Nat.pos_of_ne_zero hk0) (Nat.le_of_lt hk) with ⟨dk, hDk, hR, _, hX⟩
                  exact ⟨dk, hDk, fun _ => hR, hX⟩)
              (fun _ => ⟨cm, by
                change nodeAt stP.tree dirPos = some (.dir cm)
                unfold nodeAt
                rw [hGetP]
                rfl, hCmR⟩)
            rcases hWalkPfx.2 (by simp [dirSegs]) with
              ⟨dirDh, stMid, hPosDh, hLdMid, hTreeMid, hKeysMid, _, _, _, hInvMid, hLtMid, hOpenMid, hWalkEq⟩
            have hGetMid : vfsTreeGet stMid.tree dirPos = some (.dir cm chP) := by rw [hTreeMid]; exact hGetP
            have hBadNdMid : nodeAt stMid.tree (dirPos ++ [badEnt.val]) = some (.dir badDm) := by rw [hTreeMid]; exact hBadNd
            rcases rmtreeNonDirPrefixM_preserves_dir dirDh dirPos (hd :: tl) stMid cm chP badEnt badDm
              hBadIn hLdMid hGetMid hCmW hCmX hBadNdMid with
              ⟨subDir, rest, stPfx, hPfxEq, hBadWhere, ⟨dmSub, hSubNdPfx⟩, hBadNdPfx, hBadSubEqPfx,
                ⟨chPfx, hGetPfx⟩, hSamePfx, hShrunkPfx, hKeysPfx, hOpenPfx, _, hNidPfx, hKCPfx⟩
            have hCl := vfsDirOps_closeDir_fresh dirDh stPfx dirPos hPosDh stP.openDirs (hOpenPfx.trans hOpenMid) hLtMid
            have hRestLen : rest.length ≤ n' := by
              have hPfxOk := rmtreeNonDirPrefixM_ok dirDh dirPos (hd :: tl) stMid cm chP hLdMid hGetMid hCmW hCmX
              rw [hPfxEq] at hPfxOk
              omega
            let stCl : VfsState := { stPfx with openDirs := stP.openDirs }
            have hInvCl : DirHandleInvariant stCl :=
              dirHandleInvariant_of_subset hInvMid (fun p hp => by rw [hOpenMid]; exact List.mem_cons_of_mem _ hp) hNidPfx
            have hLdCl : lookupDir stCl rootDh = some pos := by unfold lookupDir at hLdP ⊢; exact hLdP
            have hKCCl : VfsKeysComplete stCl := by
              have hKCMid : VfsKeysComplete stMid := fun segs hN => by rw [hKeysMid]; apply hKCP segs; rw [← hTreeMid]; exact hN
              exact hKCPfx hKCMid
            have hSameCl : SameOutside dirPos stP stCl := by
              intro p hNot
              change stPfx.nodes p = stP.nodes p
              rw [hSamePfx p hNot, nodes_eq_of_tree_eq' hTreeMid]
            have hShrunkCl : TreeShrunk stCl.tree stP.tree := by
              change TreeShrunk stPfx.tree stP.tree
              rw [← hTreeMid]
              exact hShrunkPfx
            have hShrunkDirCl : TreeShrunk (.dir cm chPfx) (.dir cm chP) := by
              intro q
              have h := hShrunkCl (dirPos ++ q)
              rw [nodeAt_sub_of_vfsTreeGet (show vfsTreeGet stCl.tree dirPos = some (.dir cm chPfx) from hGetPfx),
                nodeAt_sub_of_vfsTreeGet hGetP] at h
              exact h
            have hVSCl : VfsTreeValidSegs (.dir cm chPfx) := vfsTreeValidSegs_treeShrunk hVSP hShrunkDirCl
            have hPermCl : vfsTreePermRemovable' (.dir cm chPfx) := by
              intro segs m hm
              apply hPermP segs m
              rcases hShrunkDirCl segs with hN | hEq
              · rw [hm] at hN; cases hN
              · rw [← hEq]; exact hm
            have hSubTreeCl : ∃ subTree, vfsTreeGet stCl.tree (pos ++ (dirSegs ++ [subDir]).map (·.val)) = some subTree ∧
                VfsTreeValidSegs subTree ∧ vfsTreePermRemovable' subTree := by
              have hGetSub : vfsTreeGet stCl.tree (dirPos ++ [subDir.val]) = vfsTreeGet (.dir cm chPfx) [subDir.val] :=
                vfsTreeGet_sub_of_vfsTreeGet hGetPfx
              cases hCS : chPfx subDir.val with
              | none =>
                rw [nodeAt_sub_of_vfsTreeGet (show vfsTreeGet stCl.tree dirPos = some (.dir cm chPfx) from hGetPfx)] at hSubNdPfx
                simp [nodeAt, vfsTreeGet, hCS] at hSubNdPfx
              | some subTree =>
                refine ⟨subTree, ?_, ?_, ?_⟩
                · rw [List.map_append, List.map_singleton, ← List.append_assoc]
                  change vfsTreeGet stCl.tree (dirPos ++ [subDir.val]) = some subTree
                  rw [hGetSub]
                  simp [vfsTreeGet, hCS]
                · intro segs hNe s hs
                  exact hVSCl (subDir.val :: segs) (by simpa [nodeAt, vfsTreeGet, hCS] using hNe) s (List.mem_cons_of_mem _ hs)
                · intro segs m hm
                  exact hPermCl (subDir.val :: segs) m (by simpa [nodeAt, vfsTreeGet, hCS] using hm)
            rcases hSubTreeCl with ⟨subTree, hGetSubTree, hVSSub, hPermSub⟩
            have hNotPrefPos : ¬ (dirPos <+: pos) := by
              intro hP
              have hLenP := List.IsPrefix.length_le hP
              simp only [dirPos, dirSegs, List.length_append, List.length_map, List.length_singleton] at hLenP
              omega
            have hPosDirCl : ∃ pm₀, nodeAt stCl.tree pos = some (.dir pm₀) ∧ pm₀ / 64 % 2 = 1 := by
              rcases hPosDirP with ⟨pm₀, hP0, hP0X⟩
              exact ⟨pm₀, SameOutside_nodeAt_eq hSameCl hNotPrefPos hPosValid |>.trans hP0, hP0X⟩
            have hAncCl : ∀ k, 0 < k → k ≤ dirSegs.length →
                ∃ dk, nodeAt stCl.tree (pos ++ (dirSegs.take k).map (·.val)) = some (.dir dk) ∧
                  dk / 256 % 2 = 1 ∧ dk / 128 % 2 = 1 ∧ dk / 64 % 2 = 1 := by
              intro k hkPos hkLe
              by_cases hkEq : k = dirSegs.length
              · subst hkEq
                rw [List.take_length]
                exact ⟨cm, by
                  change nodeAt stPfx.tree dirPos = some (.dir cm)
                  unfold nodeAt
                  rw [hGetPfx]
                  rfl, hCmR, hCmW, hCmX⟩
              · rcases hAncP k hkPos hkLe with ⟨dk, hDk, hR, hW, hX⟩
                have hSubV : ∀ s ∈ pos ++ (dirSegs.take k).map (·.val), validSeg s = true := by
                  intro s hs
                  rcases List.mem_append.mp hs with hp | ht
                  · exact hPosValid s hp
                  · simp only [List.mem_map] at ht; rcases ht with ⟨e, _, rfl⟩; exact e.valid
                have hNotPK : ¬ (dirPos <+: pos ++ (dirSegs.take k).map (·.val)) := by
                  intro hP
                  have hLenP := List.IsPrefix.length_le hP
                  simp only [dirPos, List.length_append, List.length_map, List.length_take] at hLenP
                  omega
                exact ⟨dk, SameOutside_nodeAt_eq hSameCl hNotPK hSubV |>.trans hDk, hR, hW, hX⟩
            have hBadNodesCl : ∀ q, nodeAt stCl.tree ((dirPos ++ [badEnt.val]) ++ q) = nodeAt badSub q := by
              intro q
              change nodeAt stPfx.tree ((dirPos ++ [badEnt.val]) ++ q) = nodeAt badSub q
              rw [hBadSubEqPfx q, hTreeMid]
              exact hBadNodes q
            rw [hWalkEq, bracketCloseDirM_run, hPfxEq]
            dsimp only
            rw [hCl]
            dsimp only
            by_cases hRemSub : VfsTreeRemovable f subTree
            · have hSubNotBad : subDir ≠ badEnt := by
                intro hEq
                subst hEq
                have hBadDirTree : TreeShrunk badSub subTree := by
                  intro q
                  right
                  have hG : vfsTreeGet stCl.tree (dirPos ++ [badEnt.val]) = some subTree := by
                    simpa [dirPos, List.append_assoc] using hGetSubTree
                  exact (hBadNodesCl q).symm.trans (nodeAt_sub_of_vfsTreeGet hG)
                exact hBadNotR (vfsTreeRemovable_treeShrunk f hBadDirTree hRemSub)
              have hBadInRest : badEnt ∈ rest := by
                rcases hBadWhere with rfl | hR
                · exact absurd rfl hSubNotBad
                · exact hR
              have hSubNdCl : nodeAt stCl.tree (dirPos ++ [subDir.val]) = some (vfsTreeTopNode subTree) := by
                have hCS0 := hGetSubTree
                rw [List.map_append, List.map_singleton, ← List.append_assoc] at hCS0
                unfold nodeAt
                rw [show dirPos ++ [subDir.val] = pos ++ dirSegs.map (·.val) ++ [subDir.val] from rfl, hCS0]
                rfl
              cases hF : f with
              | zero =>
                cases subTree with
                | file _ _ | symlink _ _ =>
                  rw [hSubNdPfx] at hSubNdCl
                  cases hSubNdCl
                | dir cmSub chSub =>
                  rw [hF, VfsTreeRemovable.eq_3] at hRemSub
                  exact False.elim hRemSub
              | succ f' =>
                rcases hPosDirCl with ⟨pm₀, hP0, hP0X⟩
                have hSubDirOk := rmtreeDirAtM_ok rootDh pos f' dirSegs subDir stCl
                  hKCCl hLdCl hInvCl hPosValid
                  ⟨pm₀, hP0, fun h => absurd h (by simp [dirSegs]), hP0X⟩
                  hAncCl
                cases subTree with
                | file _ _ | symlink _ _ =>
                  rw [hSubNdPfx] at hSubNdCl
                  cases hSubNdCl
                | dir cmSub chSub =>
                  have hRemF' : VfsTreeRemovable (f' + 1) (.dir cmSub chSub) := hF ▸ hRemSub
                  have hOk := hSubDirOk ⟨cmSub, chSub, hGetSubTree, hVSSub, hRemF'⟩
                  rw [← hF] at hOk
                  cases hSubRes : Internal.rmtreeDirAtM vfsDirOps rootDh dirSegs subDir f stCl with
                  | mk rSub stSub =>
                    rw [hSubRes] at hOk
                    cases rSub with
                    | error e => exact False.elim hOk
                    | ok u =>
                      cases u
                      rcases hOk with ⟨_, hSameSub, hShrunkSub, hInvSub, hOpenSub, _, _, hKCSub⟩
                      have hLdSub : lookupDir stSub rootDh = some pos := by unfold lookupDir at hLdCl ⊢; rw [hOpenSub]; exact hLdCl
                      have hNotPrefSubBad : ∀ q, ¬ (pos ++ (dirSegs ++ [subDir]).map (·.val) <+: (dirPos ++ [badEnt.val]) ++ q) := by
                        intro q hP
                        rw [List.map_append, List.map_singleton, ← List.append_assoc] at hP
                        change dirPos ++ [subDir.val] <+: (dirPos ++ [badEnt.val]) ++ q at hP
                        rcases hP with ⟨r, hr⟩
                        dsimp only [dirPos] at hr
                        simp only [List.append_assoc] at hr
                        have hRest := List.append_cancel_left (List.append_cancel_left hr)
                        simp only [List.singleton_append, List.cons.injEq] at hRest
                        exact hSubNotBad (entryName_ext hRest.1)
                      have hSubValidQ : ∀ q, (∀ s ∈ q, validSeg s = true) → ∀ s ∈ (dirPos ++ [badEnt.val]) ++ q, validSeg s = true := by
                        intro q hq s hs
                        rcases List.mem_append.mp hs with hdb | hqq
                        · rcases List.mem_append.mp hdb with hd | hb
                          · exact hDirValid s hd
                          · simp only [List.mem_singleton] at hb; subst hb; exact badEnt.valid
                        · exact hq s hqq
                      have hBadNdSub : nodeAt stSub.tree (dirPos ++ [badEnt.val]) = some (.dir badDm) := by
                        have hEq := SameOutside_nodeAt_eq hSameSub (hNotPrefSubBad []) (hSubValidQ [] (fun _ h => nomatch h))
                        simp only [List.append_nil] at hEq
                        exact hEq.trans hBadNdPfx
                      have hBadNodesSub : ∀ q, nodeAt stSub.tree ((dirPos ++ [badEnt.val]) ++ q) = nodeAt badSub q := by
                        intro q
                        by_cases hValidQ : ∀ s ∈ q, validSeg s = true
                        · rw [SameOutside_nodeAt_eq hSameSub (hNotPrefSubBad q) (hSubValidQ q hValidQ), hBadNodesCl q]
                        · have hInvalidN : nodeAt badSub q = none := by
                            cases hN : nodeAt badSub q with
                            | none => rfl
                            | some _ =>
                              exfalso
                              apply hValidQ
                              intro s hs
                              exact hVS (badName :: q) (by
                                intro hZ
                                rw [nodeAt, vfsTreeGet, hBadCh] at hZ
                                dsimp only at hZ
                                change nodeAt badSub q = none at hZ
                                rw [hN] at hZ
                                cases hZ) s (List.mem_cons_of_mem _ hs)
                          have hSubN : nodeAt stSub.tree ((dirPos ++ [badEnt.val]) ++ q) = none := by
                            rcases hShrunkSub ((dirPos ++ [badEnt.val]) ++ q) with hN | hEq
                            · exact hN
                            · rw [hEq, hBadNodesCl q]; exact hInvalidN
                          rw [hSubN, hInvalidN]
                      have hPosDirSub : ∃ pm₀, nodeAt stSub.tree pos = some (.dir pm₀) ∧ pm₀ / 64 % 2 = 1 := by
                        have hNP : ¬ (pos ++ (dirSegs ++ [subDir]).map (·.val) <+: pos) := by
                          intro hP; have hL := List.IsPrefix.length_le hP; simp at hL; omega
                        exact ⟨pm₀, SameOutside_nodeAt_eq hSameSub hNP hPosValid |>.trans hP0, hP0X⟩
                      have hAncSub : ∀ k, 0 < k → k ≤ dirSegs.length →
                          ∃ dk, nodeAt stSub.tree (pos ++ (dirSegs.take k).map (·.val)) = some (.dir dk) ∧
                            dk / 256 % 2 = 1 ∧ dk / 128 % 2 = 1 ∧ dk / 64 % 2 = 1 := by
                        intro k hkPos hkLe
                        rcases hAncCl k hkPos hkLe with ⟨dk, hDk, hR, hW, hX⟩
                        have hSubV : ∀ s ∈ pos ++ (dirSegs.take k).map (·.val), validSeg s = true := by
                          intro s hs; rcases List.mem_append.mp hs with hp | ht
                          · exact hPosValid s hp
                          · simp only [List.mem_map] at ht; rcases ht with ⟨e, _, rfl⟩; exact e.valid
                        have hNP : ¬ (pos ++ (dirSegs ++ [subDir]).map (·.val) <+: pos ++ (dirSegs.take k).map (·.val)) := by
                          intro hP; have hL := List.IsPrefix.length_le hP
                          simp only [List.length_append, List.length_map, List.length_singleton, List.length_take] at hL; omega
                        exact ⟨dk, SameOutside_nodeAt_eq hSameSub hNP hSubV |>.trans hDk, hR, hW, hX⟩
                      have hDirNdSub : nodeAt stSub.tree dirPos = some (.dir cm) := by
                        have hNP : ¬ (pos ++ (dirSegs ++ [subDir]).map (·.val) <+: dirPos) := by
                          intro hP; have hL := List.IsPrefix.length_le hP; simp [dirPos] at hL; omega
                        rw [SameOutside_nodeAt_eq hSameSub hNP hDirValid]
                        change nodeAt stPfx.tree dirPos = some (.dir cm)
                        simp [nodeAt, hGetPfx, vfsTreeTopNode]
                      rcases vfsTreeGet_dir_of_nodeAt hDirNdSub with ⟨chSub, hGetSub⟩
                      have hShrunkDirSub : TreeShrunk (.dir cm chSub) (.dir cm chPfx) := by
                        intro q
                        have h := hShrunkSub (dirPos ++ q)
                        rw [nodeAt_sub_of_vfsTreeGet hGetSub,
                          nodeAt_sub_of_vfsTreeGet (show vfsTreeGet stCl.tree dirPos = some (.dir cm chPfx) from hGetPfx)] at h
                        exact h
                      have hVSSub' : VfsTreeValidSegs (.dir cm chSub) := vfsTreeValidSegs_treeShrunk hVSCl hShrunkDirSub
                      have hPermSub' : vfsTreePermRemovable' (.dir cm chSub) := by
                        intro segs m hm
                        apply hPermCl segs m
                        rcases hShrunkDirSub segs with hN | hEq
                        · rw [hm] at hN; cases hN
                        · rw [← hEq]; exact hm
                      rcases ihN rest stSub chSub hRestLen hBadInRest hBadNdSub hBadNodesSub hKCSub hLdSub hInvSub
                        hPosDirSub hAncSub hGetSub hVSSub' hPermSub' with ⟨e, st', hRec, hKind, hOpen'⟩
                      refine ⟨e, st', ?_, hKind, hOpen'.trans hOpenSub⟩
                      rw [hF] at hSubRes hRec
                      exact (stateM_bind_eq hSubRes).trans (by dsimp only; exact hRec)
            · have hPosDirCl' : ∃ pm₀, nodeAt stCl.tree pos = some (.dir pm₀) ∧
                  (dirSegs = [] → pm₀ / 128 % 2 = 1) ∧ pm₀ / 64 % 2 = 1 := by
                rcases hPosDirCl with ⟨pm₀, hP0, hP0X⟩
                exact ⟨pm₀, hP0, fun h => absurd h (by simp [dirSegs]), hP0X⟩
              rcases ih dirSegs subDir rootDh pos stCl subTree hKCCl hLdCl hInvCl hPosValid hPosDirCl' hAncCl
                hGetSubTree hVSSub hPermSub hRemSub with ⟨e, st', hErr, hKind, hOpen'⟩
              exact ⟨e, st', (stateM_bind_eq hErr).trans (by simp [Pure.pure, StateT.pure]), hKind, hOpen'⟩
            intro h; cases h
      have hMidAncClose : ∀ k, 0 < k → k ≤ dirSegs.length →
          ∃ dk, nodeAt stClose.tree (pos ++ (dirSegs.take k).map (·.val)) = some (.dir dk) ∧
            dk / 256 % 2 = 1 ∧ dk / 128 % 2 = 1 ∧ dk / 64 % 2 = 1 := by
        intro k hkPos hkLe
        rw [hTreeClose]
        by_cases hkEq : k = dirSegs.length
        · subst hkEq
          rw [List.take_length]
          exact ⟨cm, hDirNd, hCmR, hCmW, hCmX⟩
        · have hkLt : k ≤ parSegs.length := by
            simp only [dirSegs, List.length_append, List.length_singleton] at hkLe hkEq
            omega
          rw [show (dirSegs).take k = parSegs.take k from List.take_append_of_le_length hkLt]
          exact hMidAnc k hkPos hkLt
      have hKCClose : VfsKeysComplete stClose := by
        intro segs hNe
        rw [hKeysClose]
        apply hKeys segs
        rw [← hTreeClose]
        exact hNe
      have hPosDirClose : ∃ pm₀, nodeAt stClose.tree pos = some (.dir pm₀) ∧ pm₀ / 64 % 2 = 1 := by
        rcases hPosDir with ⟨pm₀, hP0, _, hP0X⟩
        exact ⟨pm₀, by rw [hTreeClose]; exact hP0, hP0X⟩
      have hBadNdClose : nodeAt stClose.tree (dirPos ++ [badEnt.val]) = some (.dir badDm) := by
        dsimp only [dirPos, dirSegs, badEnt]
        rw [hTreeClose, nodeAt_sub_of_vfsTreeGet hGet]
        simp [nodeAt, vfsTreeGet, hBadCh, hBadEq, vfsTreeTopNode]
      have hBadNodesClose : ∀ q, nodeAt stClose.tree ((dirPos ++ [badEnt.val]) ++ q) = nodeAt badSub q := by
        intro q
        dsimp only [dirPos, dirSegs, badEnt]
        rw [hTreeClose, List.append_assoc, show [badName] ++ q = badName :: q from rfl,
          nodeAt_sub_of_vfsTreeGet hGet]
        simp [nodeAt, vfsTreeGet, hBadCh]
      have hGetClose : vfsTreeGet stClose.tree dirPos = some (.dir cm ch) := by rw [hTreeClose]; exact hGet
      rcases hProcErr sorted.length sorted stClose ch (Nat.le_refl _) hBadInSorted hBadNdClose hBadNodesClose
        hKCClose hLdClose hInvClose hPosDirClose hMidAncClose hGetClose hVS hPerm with
        ⟨e, st', hProcRes, hKind, hOpen'⟩
      refine ⟨e, st', ?_, hKind, hOpen'.trans hOpenClose⟩
      rw [Internal.rmtreeDirAtM.eq_2]
      refine (stateM_bind_eq (m := Internal.walkDescendM vfsDirOps rootDh dirSegs (fun dirDh => vfsDirOps.readDirAt dirDh)) hReadDone).trans ?_
      dsimp only
      exact (stateM_bind_eq hProcRes).trans (by simp [Pure.pure, StateT.pure])

end LeanSwe.Fs.Proofs