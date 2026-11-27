import LeanSweProofs.Fs.Model
import LeanSwe.Fs.Impl
import LeanSweProofs.Fs.SpecTests

namespace LeanSwe.Fs.Proofs

open LeanSwe.Fs
open LeanSwe.Fs.Model

/-- Mirror of `Model.maxDirId` for induction over `openDirs`. -/
@[reducible] def mMaxDirId : List (Nat × List String) → Nat
  | [] => 0
  | (i, _) :: rest => max i (mMaxDirId rest)

/-- Mirror of `Model.freshDirId`. -/
@[reducible] def mFreshDirId (st : VfsState) : Nat :=
  max (mMaxDirId st.openDirs) st.nextDirId + 1

/-- Mirror of `Model.invalidDirHandleErr`. -/
@[reducible] def mInvalidDirHandleErr (dh : DirHandle) : FsError :=
  { kind := .invalidInput, path := some dh.rootPath, message := s!"invalid or closed directory handle: {dh.handleId}" }

/-- Mirror of `Model.maxLockId`. -/
@[reducible] def mMaxLockId : List (Nat × String × LockMode) → Nat
  | [] => 0
  | (i, _, _) :: rest => max i (mMaxLockId rest)

/-- Mirror of `Model.dirHasLiveChild`. -/
@[reducible] def mDirHasLiveChild (st : VfsState) (dirPos : List String) : Bool :=
  let dirCanon := pathOfSegs dirPos
  let prefixChars := (if dirCanon == "/" then "/" else dirCanon ++ "/").toList
  st.keys.any fun k =>
    (st.nodes k).isSome && k != dirCanon && prefixChars.isPrefixOf k.toList

/-- Mirror of `Model.vfsReadDirAtEntries`. -/
@[reducible] def mVfsReadDirAtEntries (st : VfsState) (pos : List String) : Array EntryName :=
  let dirCanon := pathOfSegs pos
  let prefixChars := (if dirCanon == "/" then "/" else dirCanon ++ "/").toList
  let entries := st.keys.eraseDups.filterMap fun k =>
    if (st.nodes k).isSome then
      if k != dirCanon && prefixChars.isPrefixOf k.toList then
        let restChars := k.toList.drop prefixChars.length
        let restStr := String.ofList restChars
        if h : validSeg restStr = true then
          some { val := restStr, valid := h }
        else
          none
      else none
    else none
  entries.toArray

/-- Mirror of `Model.remapKeysAfterRename`. -/
@[reducible] def mRemapKeysAfterRename (keys : List String) (srcPos dstPos : List String) : List String :=
  let srcPrefix := srcPos
  keys.map fun k =>
    let kSegs := vfsSplitSegs k
    if srcPrefix.isPrefixOf kSegs then
      pathOfSegs (dstPos ++ kSegs.drop srcPrefix.length)
    else
      k

private def probeSafeNameN (len : Nat) : EntryName :=
  let s := String.ofList (List.replicate (len + 3) 'a')
  if h : validSeg s = true then { val := s, valid := h } else EntryName.lit "aaa"

private def probeLockStateN (len : Nat) (xs : List (Nat × String × LockMode)) (nxt : Nat) : VfsState :=
  let nm := probeSafeNameN len
  { tree := vfsTreeSet (vfsEmptyDir 0o755) [nm.val] (some (.file ByteArray.empty 0o644))
    keys := ["/", "/" ++ nm.val]
    cwd := "/"
    nonce := 0
    locks := xs
    nextLockId := nxt
    openDirs := [(1, [])]
    nextDirId := 2 }

private def probeLockIdN (len : Nat) (xs : List (Nat × String × LockMode)) (nxt : Nat) : Nat :=
  match (vfsDirOps.acquireLockAt { handleId := 1, rootPath := "/" } (probeSafeNameN len) .exclusive false true (probeLockStateN len xs nxt)).1 with
  | .ok lh => lh.handleId
  | .error _ => 0

private theorem validSeg_replicate_a (n : Nat) (hn : n ≥ 3) :
    validSeg (String.ofList (List.replicate n 'a')) = true := by
  have h1 : (!(List.replicate n 'a').isEmpty) = true := by
    cases n with
    | zero => omega
    | succ k => simp
  have h2 : (!(List.replicate n 'a').contains '/') = true := by
    simp only [Bool.not_eq_true']
    refine Bool.eq_false_iff.mpr ?_
    intro hm
    have := List.mem_replicate.mp (List.contains_iff_mem.mp hm)
    exact absurd this.2 (by decide)
  have h3 : (!(List.replicate n 'a').contains (Char.ofNat 0)) = true := by
    simp only [Bool.not_eq_true']
    refine Bool.eq_false_iff.mpr ?_
    intro hm
    have := List.mem_replicate.mp (List.contains_iff_mem.mp hm)
    exact absurd this.2 (by decide)
  have h4 : (List.replicate n 'a' != ['.']) = true := by
    rcases n with _ | _ | _ | k <;> simp_all [List.replicate]
  have h5 : (List.replicate n 'a' != ['.', '.']) = true := by
    rcases n with _ | _ | _ | k <;> simp_all [List.replicate]
  unfold validSeg
  simp only [String.toList_ofList, h1, h2, h3, h4, h5]
  rfl

private theorem foldl_max_le (l : List Nat) (acc : Nat) : ∀ x ∈ l, x ≤ l.foldl Nat.max acc := by
  intro x hx
  induction l generalizing acc with
  | nil => cases hx
  | cons hd tl ih =>
    rcases List.mem_cons.mp hx with rfl | htl
    · have hMono : ∀ (k : List Nat) (a : Nat), a ≤ k.foldl Nat.max a := by
        intro k
        induction k with
        | nil => intro a; exact Nat.le_refl a
        | cons h2 t2 ih2 => intro a; exact Nat.le_trans (Nat.le_max_left a h2) (ih2 (max a h2))
      exact Nat.le_trans (Nat.le_max_right acc x) (hMono tl (max acc x))
    · exact ih (max acc hd) htl

@[reducible] private def acquireLockAtTemplate (st : VfsState) (dh : DirHandle) (name : EntryName)
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

private theorem hasLockConflict_probeSafeNameN (len : Nat) (xs : List (Nat × String × LockMode))
    (hBound : ∀ x ∈ xs, x.2.1.toList.length ≤ len) (mode : LockMode) :
    hasLockConflict xs (pathOfSegs [(probeSafeNameN len).val]) mode = false := by
  have hv : validSeg (String.ofList (List.replicate (len + 3) 'a')) = true :=
    validSeg_replicate_a _ (by omega)
  have hVal : (probeSafeNameN len).val = String.ofList (List.replicate (len + 3) 'a') := by
    unfold probeSafeNameN
    dsimp only
    split
    · rfl
    · next hNot => exact absurd hv hNot
  rw [hVal]
  unfold hasLockConflict
  refine List.any_eq_false.mpr ?_
  intro ⟨id, p, m⟩ hpMem
  simp only [Bool.not_eq_true]
  by_cases hEq : (p == pathOfSegs [String.ofList (List.replicate (len + 3) 'a')]) = true
  · exfalso
    have hStr : p = "/" ++ String.ofList (List.replicate (len + 3) 'a') := by
      have := beq_iff_eq.mp hEq
      simpa [pathOfSegs] using this
    have hLen : p.toList.length = len + 4 := by
      rw [hStr, String.toList_append, String.toList_ofList]
      simp [List.length_replicate]
    have hLe : p.toList.length ≤ len := hBound (id, p, m) hpMem
    omega
  · simp [Bool.eq_false_iff.mpr hEq]

private theorem probeLockIdN_eval (len : Nat) (xs : List (Nat × String × LockMode)) (nxt : Nat)
    (hBound : ∀ x ∈ xs, x.2.1.toList.length ≤ len) :
    ∃ d : Nat, probeLockIdN len xs nxt = max d nxt + 1 := by
  have hConf := hasLockConflict_probeSafeNameN len xs hBound .exclusive
  have hLd : lookupDir (probeLockStateN len xs nxt) { handleId := 1, rootPath := "/" } = some [] := by
    simp [probeLockStateN, lookupDir]
  have hN1 : nodeAt (probeLockStateN len xs nxt).tree [] = some (.dir 0o755) := rfl
  have hN2 : nodeAt (probeLockStateN len xs nxt).tree [(probeSafeNameN len).val] =
      some (.file ByteArray.empty 0o644) := by
    simp [probeLockStateN, nodeAt, vfsTreeGet, vfsTreeSet, vfsEmptyDir, vfsTreeTopNode]
  have hAcq : ∃ d : Nat,
      (vfsDirOps.acquireLockAt { handleId := 1, rootPath := "/" } (probeSafeNameN len) .exclusive false true
        (probeLockStateN len xs nxt)).1 =
      (acquireLockAtTemplate (probeLockStateN len xs nxt) { handleId := 1, rootPath := "/" }
        (probeSafeNameN len) .exclusive false d).1 := ⟨_, rfl⟩
  rcases hAcq with ⟨d, hEq⟩
  refine ⟨d, ?_⟩
  unfold probeLockIdN
  rw [hEq]
  dsimp only [acquireLockAtTemplate]
  rw [hLd]
  dsimp only
  rw [hN1]
  dsimp only
  simp only [List.nil_append]
  rw [hN2]
  simp [probeLockStateN, hConf]

private theorem probeLockIdN_cons (len : Nat) (i : Nat) (p : String) (m : LockMode)
    (xs : List (Nat × String × LockMode)) (nxt : Nat)
    (hBound : ∀ x ∈ (i, p, m) :: xs, x.2.1.toList.length ≤ len) :
    probeLockIdN len ((i, p, m) :: xs) nxt = max (i + 1) (probeLockIdN len xs nxt) := by
  have h1 := hasLockConflict_probeSafeNameN len ((i, p, m) :: xs) hBound .exclusive
  have h2 := hasLockConflict_probeSafeNameN len xs (fun x hx => hBound x (List.mem_cons_of_mem _ hx)) .exclusive
  have hL1 : lookupDir (probeLockStateN len ((i, p, m) :: xs) nxt) { handleId := 1, rootPath := "/" } = some [] := by
    simp [probeLockStateN, lookupDir]
  have hL2 : lookupDir (probeLockStateN len xs nxt) { handleId := 1, rootPath := "/" } = some [] := by
    simp [probeLockStateN, lookupDir]
  have hN1a : nodeAt (probeLockStateN len ((i, p, m) :: xs) nxt).tree [] = some (.dir 0o755) := rfl
  have hN1b : nodeAt (probeLockStateN len xs nxt).tree [] = some (.dir 0o755) := rfl
  have hN2a : nodeAt (probeLockStateN len ((i, p, m) :: xs) nxt).tree [(probeSafeNameN len).val] =
      some (.file ByteArray.empty 0o644) := by
    simp [probeLockStateN, nodeAt, vfsTreeGet, vfsTreeSet, vfsEmptyDir, vfsTreeTopNode]
  have hN2b : nodeAt (probeLockStateN len xs nxt).tree [(probeSafeNameN len).val] =
      some (.file ByteArray.empty 0o644) := by
    simp [probeLockStateN, nodeAt, vfsTreeGet, vfsTreeSet, vfsEmptyDir, vfsTreeTopNode]
  have hPair : ∃ d : Nat,
      (vfsDirOps.acquireLockAt { handleId := 1, rootPath := "/" } (probeSafeNameN len) .exclusive false true
        (probeLockStateN len ((i, p, m) :: xs) nxt)).1 =
      (acquireLockAtTemplate (probeLockStateN len ((i, p, m) :: xs) nxt) { handleId := 1, rootPath := "/" }
        (probeSafeNameN len) .exclusive false (max i d)).1 ∧
      (vfsDirOps.acquireLockAt { handleId := 1, rootPath := "/" } (probeSafeNameN len) .exclusive false true
        (probeLockStateN len xs nxt)).1 =
      (acquireLockAtTemplate (probeLockStateN len xs nxt) { handleId := 1, rootPath := "/" }
        (probeSafeNameN len) .exclusive false d).1 := ⟨_, rfl, rfl⟩
  rcases hPair with ⟨d, hP1, hP2⟩
  unfold probeLockIdN
  rw [hP1, hP2]
  dsimp only [acquireLockAtTemplate]
  rw [hL1, hL2]
  dsimp only
  rw [hN1a, hN1b]
  dsimp only
  simp only [List.nil_append]
  rw [hN2a, hN2b]
  simp [probeLockStateN, h1, h2]

private theorem probeLockIdN_bounds (len : Nat) (xs : List (Nat × String × LockMode)) (nxt : Nat)
    (hBound : ∀ x ∈ xs, x.2.1.toList.length ≤ len) :
    0 < probeLockIdN len xs nxt ∧ nxt < probeLockIdN len xs nxt ∧ ∀ x ∈ xs, x.1 < probeLockIdN len xs nxt := by
  induction xs with
  | nil =>
    rcases probeLockIdN_eval len [] nxt (fun _ h => nomatch h) with ⟨d, hd⟩
    rw [hd]
    exact ⟨by omega, by omega, fun _ h => nomatch h⟩
  | cons hd tl ih =>
    rcases hd with ⟨i, p, m⟩
    rw [probeLockIdN_cons len i p m tl nxt hBound]
    rcases ih (fun x hx => hBound x (List.mem_cons_of_mem _ hx)) with ⟨h0, h1, hAll⟩
    refine ⟨by omega, by omega, ?_⟩
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hTl
    · omega
    · exact Nat.lt_of_lt_of_le (hAll x hTl) (Nat.le_max_right _ _)

private def probeAtState (xs : List (Nat × List String)) (nxt : Nat) : VfsState :=
  { tree := .dir 0o755 (fun _ => some (.dir 0o755 (fun _ => none)))
    keys := []
    cwd := "/"
    nonce := 0
    locks := []
    nextLockId := 0
    openDirs := xs
    nextDirId := nxt }

private def probeAtId (xs : List (Nat × List String)) (nxt : Nat) : Nat :=
  match (vfsDirOps.openDirAt { handleId := 1, rootPath := "/" } (EntryName.lit "a") (probeAtState ((1, []) :: xs) nxt)).1 with
  | .ok dh => dh.handleId
  | .error _ => 0

private theorem probeAtId_nil (nxt : Nat) :
    probeAtId [] nxt = max 1 nxt + 1 :=
  rfl

private theorem probeAtId_cons (i : Nat) (p : List String) (xs : List (Nat × List String)) (nxt : Nat) :
    probeAtId ((i, p) :: xs) nxt = max (i + 1) (probeAtId xs nxt) := by
  have hEx : ∃ d : Nat,
      probeAtId ((i, p) :: xs) nxt = max (max 1 (max i d)) nxt + 1 ∧
      probeAtId xs nxt = max (max 1 d) nxt + 1 := ⟨_, rfl, rfl⟩
  rcases hEx with ⟨d, h1, h2⟩
  rw [h1, h2]
  omega

private theorem probeAtId_bounds (xs : List (Nat × List String)) (nxt : Nat) :
    0 < probeAtId xs nxt ∧ nxt < probeAtId xs nxt ∧ ∀ p ∈ xs, p.1 < probeAtId xs nxt := by
  induction xs with
  | nil => rw [probeAtId_nil]; refine ⟨by omega, by omega, fun _ h => nomatch h⟩
  | cons hd tl ih =>
    rcases hd with ⟨i, pos⟩
    rw [probeAtId_cons]
    refine ⟨by omega, by omega, ?_⟩
    intro p hp
    rcases List.mem_cons.mp hp with rfl | hTl
    · omega
    · exact Nat.lt_of_lt_of_le (ih.2.2 p hTl) (Nat.le_max_right _ _)

private def mkDeepDirTree : Nat → VfsTree
  | 0 => .dir 0o755 (fun _ => some (.dir 0o755 (fun _ => none)))
  | k + 1 => .dir 0o755 (fun _ => some (mkDeepDirTree k))

private theorem nodeAt_mkDeepDirTree :
    ∀ pos : List String,
      nodeAt (mkDeepDirTree pos.length) pos = some (.dir 0o755) ∧
      nodeAt (mkDeepDirTree pos.length) (pos ++ ["a"]) = some (.dir 0o755)
  | [] => ⟨rfl, rfl⟩
  | _ :: rest => nodeAt_mkDeepDirTree rest

private def probeExactDirId (xs : List (Nat × List String)) (nxt : Nat) : Nat :=
  match xs.find? (fun p => p.1 != 0) with
  | none => nxt + 1
  | some (i, pos) =>
    match (vfsDirOps.openDirAt { handleId := i, rootPath := "/" } (EntryName.lit "a")
        { tree := mkDeepDirTree pos.length, keys := [], cwd := "/", nonce := 0,
          locks := [], nextLockId := 0, openDirs := xs, nextDirId := nxt }).1 with
    | .ok dh => dh.handleId
    | .error _ => 0

private theorem find?_nonZero_lookup {xs : List (Nat × List String)} {i : Nat} {pos : List String}
    (hFind : xs.find? (fun p => p.1 != 0) = some (i, pos)) :
    i ≠ 0 ∧ (xs.find? (fun p => p.1 == i)) = some (i, pos) := by
  induction xs with
  | nil => simp at hFind
  | cons hd tl ih =>
    rcases hd with ⟨j, jp⟩
    simp only [List.find?_cons] at hFind
    by_cases hj : (j != 0) = true
    · have hNe : j ≠ 0 := by simpa using hj
      simp only [hj] at hFind
      cases hFind
      refine ⟨hNe, ?_⟩
      simp
    · simp only [Bool.not_eq_true] at hj
      simp only [hj] at hFind
      have hJ0 : j = 0 := by simpa using hj
      rcases ih hFind with ⟨hiNe, hRest⟩
      refine ⟨hiNe, ?_⟩
      have hBeq : (j == i) = false := beq_false_of_ne (by omega)
      simp [hBeq, hRest]

private theorem vfsTreeSet_cons_ne_nil (t : VfsTree) (b : String) (rest : List String)
    (hNe : rest ≠ []) (v : Option VfsTree) :
    vfsTreeSet t (b :: rest) v =
      match t with
      | .dir m ch =>
        .dir m (fun s =>
          if s == b then
            match ch b with
            | some sub => some (vfsTreeSet sub rest v)
            | none => none
          else ch s)
      | _ => t := by
  cases rest with
  | nil => exact absurd rfl hNe
  | cons _ _ => rfl

/-- Updating `(base ++ [leaf])` in `t` (when `base` resolves to a directory) leaves `nodeAt t q` untouched for every `q` not having `base ++ [leaf]` as a prefix. -/
theorem nodeAt_vfsTreeSet_outside (t : VfsTree) (base : List String) (leaf : String)
    (v : Option VfsTree) (q : List String)
    (hDir : ∃ dm ch, vfsTreeGet t base = some (.dir dm ch))
    (hNot : ¬ (base ++ [leaf]) <+: q) :
    nodeAt (vfsTreeSet t (base ++ [leaf]) v) q = nodeAt t q := by
  induction base generalizing t q with
  | nil =>
    rcases hDir with ⟨dm, ch, hGet⟩
    cases t with
    | file _ _ | symlink _ _ => simp [vfsTreeGet] at hGet
    | dir m f =>
      simp only [vfsTreeGet] at hGet
      cases hGet
      simp only [List.nil_append, vfsTreeSet]
      cases q with
      | nil => rfl
      | cons s qs =>
        by_cases hs : s = leaf
        · subst hs
          exact absurd ⟨qs, rfl⟩ hNot
        · simp [nodeAt, vfsTreeGet, beq_false_of_ne hs]
  | cons b bs ih =>
    rcases hDir with ⟨dm, ch, hGet⟩
    cases t with
    | file _ _ | symlink _ _ => simp [vfsTreeGet] at hGet
    | dir m f =>
      simp only [vfsTreeGet] at hGet
      cases hf : f b with
      | none => simp [hf] at hGet
      | some sub =>
        simp only [hf] at hGet
        have hNe : bs ++ [leaf] ≠ [] := List.append_ne_nil_of_right_ne_nil bs (List.cons_ne_nil leaf [])
        rw [List.cons_append, vfsTreeSet_cons_ne_nil _ b (bs ++ [leaf]) hNe v]
        cases q with
        | nil => rfl
        | cons s qs =>
          by_cases hs : s = b
          · subst hs
            have hSubNot : ¬ (bs ++ [leaf]) <+: qs := by
              intro ⟨r, hr⟩
              exact hNot ⟨r, by rw [List.cons_append, List.cons_append, hr]⟩
            simp only [nodeAt, vfsTreeGet, beq_self_eq_true, ↓reduceIte, hf]
            exact ih sub qs ⟨dm, ch, hGet⟩ hSubNot
          · simp [nodeAt, vfsTreeGet, beq_false_of_ne hs]

/-- Reading `(base ++ [leaf])` after setting it on a live parent directory yields `v`. -/
theorem vfsTreeGet_vfsTreeSet_eq (t : VfsTree) (base : List String) (leaf : String)
    (v : Option VfsTree) (hDir : ∃ dm ch, vfsTreeGet t base = some (.dir dm ch)) :
    vfsTreeGet (vfsTreeSet t (base ++ [leaf]) v) (base ++ [leaf]) = v := by
  induction base generalizing t with
  | nil =>
    rcases hDir with ⟨dm, ch, hGet⟩
    cases t with
    | file _ _ | symlink _ _ => simp [vfsTreeGet] at hGet
    | dir m f => cases v <;> simp [vfsTreeSet, vfsTreeGet]
  | cons b bs ih =>
    rcases hDir with ⟨dm, ch, hGet⟩
    cases t with
    | file _ _ | symlink _ _ => simp [vfsTreeGet] at hGet
    | dir m f =>
      simp only [vfsTreeGet] at hGet
      cases hf : f b with
      | none => simp [hf] at hGet
      | some sub =>
        simp only [hf] at hGet
        have hNe : bs ++ [leaf] ≠ [] := List.append_ne_nil_of_right_ne_nil bs (List.cons_ne_nil leaf [])
        rw [List.cons_append, vfsTreeSet_cons_ne_nil _ b (bs ++ [leaf]) hNe v]
        simp only [vfsTreeGet, beq_self_eq_true, ↓reduceIte, hf]
        exact ih sub ⟨dm, ch, hGet⟩

/-- Reading `(base ++ [leaf] ++ rest)` after setting `(base ++ [leaf])` to `v` binds through `v`. -/
theorem vfsTreeGet_vfsTreeSet_desc (t : VfsTree) (base : List String) (leaf : String)
    (v : Option VfsTree) (rest : List String)
    (hDir : ∃ dm ch, vfsTreeGet t base = some (.dir dm ch)) :
    vfsTreeGet (vfsTreeSet t (base ++ [leaf]) v) (base ++ [leaf] ++ rest) =
      v.bind (fun sub => vfsTreeGet sub rest) := by
  induction base generalizing t with
  | nil =>
    rcases hDir with ⟨dm, ch, hGet⟩
    cases t with
    | file _ _ | symlink _ _ => simp [vfsTreeGet] at hGet
    | dir m f =>
      simp only [List.nil_append, List.singleton_append, vfsTreeSet, vfsTreeGet, beq_self_eq_true, ↓reduceIte]
      cases v <;> rfl
  | cons b bs ih =>
    rcases hDir with ⟨dm, ch, hGet⟩
    cases t with
    | file _ _ | symlink _ _ => simp [vfsTreeGet] at hGet
    | dir m f =>
      simp only [vfsTreeGet] at hGet
      cases hf : f b with
      | none => simp [hf] at hGet
      | some sub =>
        simp only [hf] at hGet
        have hNe : bs ++ [leaf] ≠ [] := List.append_ne_nil_of_right_ne_nil bs (List.cons_ne_nil leaf [])
        rw [List.cons_append, vfsTreeSet_cons_ne_nil _ b (bs ++ [leaf]) hNe v]
        simp only [List.cons_append, vfsTreeGet, beq_self_eq_true, ↓reduceIte, hf]
        exact ih sub ⟨dm, ch, hGet⟩

/-- Reflexivity of `SameOutside`. -/
theorem SameOutside_refl (root : List String) (st : VfsState) : SameOutside root st st :=
  fun _ _ => rfl

/-- Transitivity of `SameOutside`. -/
theorem SameOutside_trans {root : List String} {s1 s2 s3 : VfsState}
    (h12 : SameOutside root s1 s2) (h23 : SameOutside root s2 s3) : SameOutside root s1 s3 :=
  fun p hp => (h23 p hp).trans (h12 p hp)

/-- Monotonicity of `SameOutside` when widening the allowed mutation prefix. -/
theorem SameOutside_mono {a b : List String} {s1 s2 : VfsState}
    (hPre : a <+: b) (hOut : SameOutside b s1 s2) : SameOutside a s1 s2 :=
  fun p hp => hOut p fun hb => hp (List.IsPrefix.trans hPre hb)

/-- Deriving `SameOutside pos` from a `vfsTreeSet` at `base ++ [leaf]` under `pos <+: base`. -/
theorem SameOutside_of_vfsTreeSet {st st' : VfsState} {pos base : List String} {leaf : String}
    {v : Option VfsTree} (hPre : pos <+: base)
    (hDir : ∃ dm ch, vfsTreeGet st.tree base = some (.dir dm ch))
    (hTree : st'.tree = vfsTreeSet st.tree (base ++ [leaf]) v) :
    SameOutside pos st st' := by
  intro p hp
  have hNot : ¬ (base ++ [leaf]) <+: vfsSplitSegs p := by
    intro hSub
    exact hp (List.IsPrefix.trans hPre (List.IsPrefix.trans (List.prefix_append base [leaf]) hSub))
  unfold VfsState.nodes vfsTreeNodes
  rw [hTree]
  split
  · exact nodeAt_vfsTreeSet_outside st.tree base leaf v (vfsSplitSegs p) hDir hNot
  · rfl

/-- Extracting `(dm, ch)` witnessing a directory in `vfsTreeGet` from `nodeAt st.tree base = some (.dir m)`. -/
theorem vfsTreeGet_dir_of_nodeAt {t : VfsTree} {segs : List String} {m : Nat}
    (h : nodeAt t segs = some (.dir m)) :
    ∃ ch, vfsTreeGet t segs = some (.dir m ch) := by
  unfold nodeAt at h
  cases hg : vfsTreeGet t segs with
  | none => simp [hg] at h
  | some sub =>
    cases sub with
    | file _ _ | symlink _ _ => simp [hg, vfsTreeTopNode] at h
    | dir m' ch =>
      simp only [hg, vfsTreeTopNode, Option.map_some, Option.some.injEq] at h
      cases h
      exact ⟨ch, rfl⟩
@[reducible] private def openDirTemplate (st : VfsState) (root : String) (d : Nat) :
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
        ({ handleId := id, rootPath := root },
          { st with openDirs := (id, vfsSplitSegs canon) :: st.openDirs, nextDirId := id + 1 })
        |> fun (dh, st') => (.ok dh, st')
    | .ok (_, _) =>
      (.error { kind := .notADirectory, path := some root, message := s!"not a directory: {root}" }, st)

@[reducible] private def openDirAtTemplate (st : VfsState) (dh : DirHandle) (name : EntryName) (d : Nat) :
    Except FsError DirHandle × VfsState :=
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
        match nodeAt st.tree childPos with
        | none => (.error { kind := .notFound, path := some name.val, message := s!"no such file or directory: {name.val}" }, st)
        | some (.symlink _ _) =>
          (.error { kind := .invalidInput, path := some name.val, message := s!"symlink refused in subtree traversal: {name.val}" }, st)
        | some (.dir mode) =>
          if (mode / 256) % 2 == 0 then
            (.error { kind := .permissionDenied, path := some name.val, message := s!"permission denied: {name.val}" }, st)
          else
            let id := max d st.nextDirId + 1
            (.ok { handleId := id, rootPath := pathOfSegs childPos },
              { st with openDirs := (id, childPos) :: st.openDirs, nextDirId := id + 1 })
        | some _ =>
          (.error { kind := .notADirectory, path := some name.val, message := s!"not a directory: {name.val}" }, st)
    | some _ =>
      (.error { kind := .notADirectory, path := some dh.rootPath, message := s!"not a directory: {dh.rootPath}" }, st)

private theorem probeExactDirId_ge2 (xs : List (Nat × List String)) :
    (∃ q ∈ xs, q.1 ≠ 0) → 2 ≤ probeExactDirId xs 0 := by
  intro hNz
  induction xs with
  | nil => rcases hNz with ⟨_, h, _⟩; cases h
  | cons hd tl ih =>
    rcases hd with ⟨j, jp⟩
    by_cases hj : j = 0
    · subst hj
      have hNzTl : ∃ q ∈ tl, q.1 ≠ 0 := by
        rcases hNz with ⟨q, hMem, hNe⟩
        rcases List.mem_cons.mp hMem with rfl | hT
        · exact absurd rfl hNe
        · exact ⟨q, hT, hNe⟩
      have ih2 := ih hNzTl
      have hSome : ∃ pair, tl.find? (fun p => p.1 != 0) = some pair := by
        rcases hNzTl with ⟨q, hM, hN⟩
        cases hF : tl.find? (fun p => p.1 != 0) with
        | some p => exact ⟨p, rfl⟩
        | none => have := List.find?_eq_none.mp hF q hM; simp [hN] at this
      rcases hSome with ⟨⟨i, pos⟩, hFind⟩
      rcases find?_nonZero_lookup hFind with ⟨hiNe, hLookup⟩
      have hFindCons : ((0, jp) :: tl).find? (fun p => p.1 != 0) = some (i, pos) := by
        simp [hFind]
      have hLd1 : lookupDir
          { tree := mkDeepDirTree pos.length, keys := [], cwd := "/", nonce := 0,
            locks := [], nextLockId := 0, openDirs := (0, jp) :: tl, nextDirId := 0 }
          { handleId := i, rootPath := "/" } = some pos := by
        unfold lookupDir
        simp [beq_false_of_ne hiNe, beq_false_of_ne (by omega : 0 ≠ i), hLookup]
      have hLd2 : lookupDir
          { tree := mkDeepDirTree pos.length, keys := [], cwd := "/", nonce := 0,
            locks := [], nextLockId := 0, openDirs := tl, nextDirId := 0 }
          { handleId := i, rootPath := "/" } = some pos := by
        unfold lookupDir
        simp [beq_false_of_ne hiNe, hLookup]
      rcases nodeAt_mkDeepDirTree pos with ⟨hN1, hN2⟩
      have hBoth : ∃ d : Nat,
          vfsDirOps.openDirAt { handleId := i, rootPath := "/" } (EntryName.lit "a")
            { tree := mkDeepDirTree pos.length, keys := [], cwd := "/", nonce := 0,
              locks := [], nextLockId := 0, openDirs := (0, jp) :: tl, nextDirId := 0 } =
            openDirAtTemplate
              { tree := mkDeepDirTree pos.length, keys := [], cwd := "/", nonce := 0,
                locks := [], nextLockId := 0, openDirs := (0, jp) :: tl, nextDirId := 0 }
              { handleId := i, rootPath := "/" } (EntryName.lit "a") (max 0 d) ∧
          vfsDirOps.openDirAt { handleId := i, rootPath := "/" } (EntryName.lit "a")
            { tree := mkDeepDirTree pos.length, keys := [], cwd := "/", nonce := 0,
              locks := [], nextLockId := 0, openDirs := tl, nextDirId := 0 } =
            openDirAtTemplate
              { tree := mkDeepDirTree pos.length, keys := [], cwd := "/", nonce := 0,
                locks := [], nextLockId := 0, openDirs := tl, nextDirId := 0 }
              { handleId := i, rootPath := "/" } (EntryName.lit "a") d := ⟨_, rfl, rfl⟩
      rcases hBoth with ⟨d, hB1, hB2⟩
      unfold probeExactDirId at ih2 ⊢
      rw [hFindCons]
      rw [hFind] at ih2
      dsimp only at ih2 ⊢
      rw [hB1]
      rw [hB2] at ih2
      dsimp only [openDirAtTemplate] at ih2 ⊢
      rw [hLd1]
      rw [hLd2] at ih2
      dsimp only at ih2 ⊢
      rw [hN1] at ih2 ⊢
      dsimp only at ih2 ⊢
      simp only [show (EntryName.lit "a").val = "a" from rfl, hN2,
        show (0o755 / 64 % 2 == 0) = false from rfl, Bool.false_eq_true, ↓reduceIte] at ih2 ⊢
      omega
    · have hjNe : (j != 0) = true := by simpa using hj
      have hFindCons : ((j, jp) :: tl).find? (fun p => p.1 != 0) = some (j, jp) := by
        simp [hjNe]
      have hLd : lookupDir
          { tree := mkDeepDirTree jp.length, keys := [], cwd := "/", nonce := 0,
            locks := [], nextLockId := 0, openDirs := (j, jp) :: tl, nextDirId := 0 }
          { handleId := j, rootPath := "/" } = some jp := by
        unfold lookupDir
        simp [beq_false_of_ne hj]
      rcases nodeAt_mkDeepDirTree jp with ⟨hN1, hN2⟩
      have hEx : ∃ d : Nat,
          vfsDirOps.openDirAt { handleId := j, rootPath := "/" } (EntryName.lit "a")
            { tree := mkDeepDirTree jp.length, keys := [], cwd := "/", nonce := 0,
              locks := [], nextLockId := 0, openDirs := (j, jp) :: tl, nextDirId := 0 } =
            openDirAtTemplate
              { tree := mkDeepDirTree jp.length, keys := [], cwd := "/", nonce := 0,
                locks := [], nextLockId := 0, openDirs := (j, jp) :: tl, nextDirId := 0 }
              { handleId := j, rootPath := "/" } (EntryName.lit "a") (max j d) := ⟨_, rfl⟩
      rcases hEx with ⟨d, hOp⟩
      unfold probeExactDirId
      rw [hFindCons]
      dsimp only
      rw [hOp]
      dsimp only [openDirAtTemplate]
      rw [hLd]
      dsimp only
      rw [hN1]
      dsimp only
      simp only [show (EntryName.lit "a").val = "a" from rfl, hN2,
        show (0o755 / 64 % 2 == 0) = false from rfl, Bool.false_eq_true, ↓reduceIte]
      omega

private theorem openDirAt_maxDirId_ge_one (xs : List (Nat × List String)) (d : Nat)
    (hNz : ∃ q ∈ xs, q.1 ≠ 0)
    (i : Nat) (pos : List String)
    (hFind : xs.find? (fun p => p.1 != 0) = some (i, pos))
    (hOp : vfsDirOps.openDirAt { handleId := i, rootPath := "/" } (EntryName.lit "a")
        { tree := mkDeepDirTree pos.length, keys := [], cwd := "/", nonce := 0,
          locks := [], nextLockId := 0, openDirs := xs, nextDirId := 0 } =
      openDirAtTemplate
        { tree := mkDeepDirTree pos.length, keys := [], cwd := "/", nonce := 0,
          locks := [], nextLockId := 0, openDirs := xs, nextDirId := 0 }
        { handleId := i, rootPath := "/" } (EntryName.lit "a") d) :
    1 ≤ d := by
  have hGe2 := probeExactDirId_ge2 xs hNz
  rcases find?_nonZero_lookup hFind with ⟨hiNe, hLookup⟩
  have hLd : lookupDir
      { tree := mkDeepDirTree pos.length, keys := [], cwd := "/", nonce := 0,
        locks := [], nextLockId := 0, openDirs := xs, nextDirId := 0 }
      { handleId := i, rootPath := "/" } = some pos := by
    unfold lookupDir
    simp [beq_false_of_ne hiNe, hLookup]
  rcases nodeAt_mkDeepDirTree pos with ⟨hN1, hN2⟩
  unfold probeExactDirId at hGe2
  rw [hFind] at hGe2
  dsimp only at hGe2
  rw [hOp] at hGe2
  dsimp only [openDirAtTemplate] at hGe2
  rw [hLd] at hGe2
  dsimp only at hGe2
  rw [hN1] at hGe2
  dsimp only at hGe2
  simp only [show (EntryName.lit "a").val = "a" from rfl, hN2,
    show (0o755 / 64 % 2 == 0) = false from rfl, Bool.false_eq_true, ↓reduceIte] at hGe2
  omega

private theorem dirId_lt_of_open_and_probe {xs : List (Nat × List String)} {nxt d : Nat}
    (hPa : probeAtId xs 0 = max (max 1 d) 0 + 1)
    (hExact : ∀ (i : Nat) (pos : List String),
      xs.find? (fun p => p.1 != 0) = some (i, pos) →
      vfsDirOps.openDirAt { handleId := i, rootPath := "/" } (EntryName.lit "a")
          { tree := mkDeepDirTree pos.length, keys := [], cwd := "/", nonce := 0,
            locks := [], nextLockId := 0, openDirs := xs, nextDirId := 0 } =
        openDirAtTemplate
          { tree := mkDeepDirTree pos.length, keys := [], cwd := "/", nonce := 0,
            locks := [], nextLockId := 0, openDirs := xs, nextDirId := 0 }
          { handleId := i, rootPath := "/" } (EntryName.lit "a") d) :
    ∀ p ∈ xs, p.1 < max d nxt + 1 := by
  intro p hpMem
  by_cases hp0 : p.1 = 0
  · omega
  · have hNz : ∃ q ∈ xs, q.1 ≠ 0 := ⟨p, hpMem, hp0⟩
    have hSome : ∃ pair, xs.find? (fun q => q.1 != 0) = some pair := by
      cases hF : xs.find? (fun q => q.1 != 0) with
      | some q => exact ⟨q, rfl⟩
      | none => have := List.find?_eq_none.mp hF p hpMem; simp [hp0] at this
    rcases hSome with ⟨⟨i, pos⟩, hFind⟩
    have hGe1 := openDirAt_maxDirId_ge_one xs d hNz i pos hFind (hExact i pos hFind)
    have hBounds := (probeAtId_bounds xs 0).2.2 p hpMem
    rw [hPa] at hBounds
    omega

/-- When `vfsDirOps.openDir` succeeds, the returned `DirHandle` has a fresh positive ID exceeding `st.nextDirId` and every ID in `st.openDirs`. -/
theorem vfsDirOps_openDir_ok (root : String) (st : VfsState) (dh : DirHandle) (st' : VfsState)
    (hOk : vfsDirOps.openDir root st = (.ok dh, st')) :
    0 < dh.handleId ∧ st.nextDirId < dh.handleId ∧ (∀ p ∈ st.openDirs, p.1 < dh.handleId) ∧
    ∃ pos, st' = { st with openDirs := (dh.handleId, pos) :: st.openDirs, nextDirId := dh.handleId + 1 } := by
  have hPair : ∃ d : Nat, vfsDirOps.openDir root st = openDirTemplate st root d ∧
      probeAtId st.openDirs 0 = max (max 1 d) 0 + 1 ∧
      ∀ (i : Nat) (pos : List String),
        st.openDirs.find? (fun p => p.1 != 0) = some (i, pos) →
        vfsDirOps.openDirAt { handleId := i, rootPath := "/" } (EntryName.lit "a")
            { tree := mkDeepDirTree pos.length, keys := [], cwd := "/", nonce := 0,
              locks := [], nextLockId := 0, openDirs := st.openDirs, nextDirId := 0 } =
          openDirAtTemplate
            { tree := mkDeepDirTree pos.length, keys := [], cwd := "/", nonce := 0,
              locks := [], nextLockId := 0, openDirs := st.openDirs, nextDirId := 0 }
            { handleId := i, rootPath := "/" } (EntryName.lit "a") d :=
    ⟨_, rfl, rfl, fun _ _ _ => rfl⟩
  rcases hPair with ⟨d, hOp, hPa, hExact⟩
  rw [hOp] at hOk
  dsimp only [openDirTemplate] at hOk
  split at hOk
  · cases hOk
  · split at hOk
    · cases hOk
    · split at hOk
      · cases hOk
      · cases hOk
        refine ⟨by dsimp only; omega, by dsimp only; omega, ?_, _, rfl⟩
        exact dirId_lt_of_open_and_probe hPa hExact
    · cases hOk

/-- When `vfsDirOps.openDirAt` succeeds, the returned `DirHandle` has a fresh positive ID exceeding `st.nextDirId` and every ID in `st.openDirs`. -/
theorem vfsDirOps_openDirAt_ok (dh : DirHandle) (name : EntryName) (st : VfsState)
    (childDh : DirHandle) (st' : VfsState)
    (hOk : vfsDirOps.openDirAt dh name st = (.ok childDh, st')) :
    0 < childDh.handleId ∧ st.nextDirId < childDh.handleId ∧ (∀ p ∈ st.openDirs, p.1 < childDh.handleId) ∧
    ∃ pos parMode mode,
      lookupDir st dh = some pos ∧
      nodeAt st.tree pos = some (.dir parMode) ∧
      (parMode / 64) % 2 ≠ 0 ∧
      nodeAt st.tree (pos ++ [name.val]) = some (.dir mode) ∧
      (mode / 256) % 2 ≠ 0 ∧
      childDh.rootPath = pathOfSegs (pos ++ [name.val]) ∧
      st' = { st with openDirs := (childDh.handleId, pos ++ [name.val]) :: st.openDirs, nextDirId := childDh.handleId + 1 } := by
  have hPair : ∃ d : Nat, vfsDirOps.openDirAt dh name st = openDirAtTemplate st dh name d ∧
      probeAtId st.openDirs 0 = max (max 1 d) 0 + 1 ∧
      ∀ (i : Nat) (pos : List String),
        st.openDirs.find? (fun p => p.1 != 0) = some (i, pos) →
        vfsDirOps.openDirAt { handleId := i, rootPath := "/" } (EntryName.lit "a")
            { tree := mkDeepDirTree pos.length, keys := [], cwd := "/", nonce := 0,
              locks := [], nextLockId := 0, openDirs := st.openDirs, nextDirId := 0 } =
          openDirAtTemplate
            { tree := mkDeepDirTree pos.length, keys := [], cwd := "/", nonce := 0,
              locks := [], nextLockId := 0, openDirs := st.openDirs, nextDirId := 0 }
            { handleId := i, rootPath := "/" } (EntryName.lit "a") d :=
    ⟨_, rfl, rfl, fun _ _ _ => rfl⟩
  rcases hPair with ⟨d, hOp, hPa, hExact⟩
  rw [hOp] at hOk
  dsimp only [openDirAtTemplate] at hOk
  cases hLd : lookupDir st dh with
  | none => simp only [hLd] at hOk; cases hOk
  | some pos =>
    simp only [hLd] at hOk
    cases hP : nodeAt st.tree pos with
    | none => simp only [hP] at hOk; cases hOk
    | some node =>
      cases node with
      | file _ _ | symlink _ _ => simp only [hP] at hOk; cases hOk
      | dir parMode =>
        simp only [hP] at hOk
        by_cases hPm : (parMode / 64 % 2 == 0) = true
        · simp only [hPm, ↓reduceIte] at hOk; cases hOk
        · simp only [hPm, Bool.false_eq_true, ↓reduceIte] at hOk
          cases hC : nodeAt st.tree (pos ++ [name.val]) with
          | none => simp only [hC] at hOk; cases hOk
          | some cnode =>
            cases cnode with
            | file _ _ | symlink _ _ => simp only [hC] at hOk; cases hOk
            | dir mode =>
              simp only [hC] at hOk
              by_cases hm : (mode / 256 % 2 == 0) = true
              · simp only [hm, ↓reduceIte] at hOk; cases hOk
              · simp only [hm, Bool.false_eq_true, ↓reduceIte] at hOk
                cases hOk
                have hPmNe : (parMode / 64) % 2 ≠ 0 := by simpa using hPm
                have hMNe : (mode / 256) % 2 ≠ 0 := by simpa using hm
                refine ⟨by dsimp only; omega, by dsimp only; omega, ?_, pos, parMode, mode, rfl, hP, hPmNe, hC, hMNe, rfl, rfl⟩
                exact dirId_lt_of_open_and_probe hPa hExact

/-- When `vfsDirOps.openDirAt` fails, `st` is completely unchanged. -/
theorem vfsDirOps_openDirAt_err (dh : DirHandle) (name : EntryName) (st : VfsState)
    (e : FsError) (st' : VfsState)
    (hErr : vfsDirOps.openDirAt dh name st = (.error e, st')) :
    st' = st := by
  have hEx : ∃ d : Nat, vfsDirOps.openDirAt dh name st = openDirAtTemplate st dh name d := ⟨_, rfl⟩
  rcases hEx with ⟨d, hOp⟩
  rw [hOp] at hErr
  dsimp only [openDirAtTemplate] at hErr
  split at hErr
  · cases hErr; rfl
  · split at hErr
    · cases hErr; rfl
    · split at hErr
      · cases hErr; rfl
      · split at hErr
        · cases hErr; rfl
        · cases hErr; rfl
        · split at hErr
          · cases hErr; rfl
          · cases hErr
        · cases hErr; rfl
    · cases hErr; rfl

/-- When `vfsDirOps.acquireLockAt` fails with `lookupDir st dh = none`, it returns `.invalidInput` without modifying `st`. -/
theorem vfsDirOps_acquireLockAt_none (st : VfsState) (dh : DirHandle) (name : EntryName)
    (mode : LockMode) (createIfMissing nonBlocking : Bool)
    (hNone : lookupDir st dh = none) :
    vfsDirOps.acquireLockAt dh name mode createIfMissing nonBlocking st =
      (.error (mInvalidDirHandleErr dh), st) := by
  have hEx : ∃ d : Nat,
      vfsDirOps.acquireLockAt dh name mode createIfMissing nonBlocking st =
        acquireLockAtTemplate st dh name mode createIfMissing d := ⟨_, rfl⟩
  rcases hEx with ⟨d, hOp⟩
  rw [hOp]
  simp [acquireLockAtTemplate, hNone]

/-- When `vfsDirOps.acquireLockAt` succeeds, the returned `LockHandle` has a fresh positive ID exceeding every ID in `st.locks`. -/
theorem vfsDirOps_acquireLockAt_ok (dh : DirHandle) (name : EntryName) (mode : LockMode)
    (createIfMissing nonBlocking : Bool) (st : VfsState) (lh : LockHandle) (st' : VfsState)
    (hOk : vfsDirOps.acquireLockAt dh name mode createIfMissing nonBlocking st = (.ok lh, st')) :
    0 < lh.handleId ∧ st.nextLockId < lh.handleId ∧ (∀ l ∈ st.locks, l.1 < lh.handleId) ∧
    ∃ pos, lookupDir st dh = some pos ∧
      (∀ p : String, ¬ (pos ++ [name.val]) <+: vfsSplitSegs p → st'.nodes p = st.nodes p) ∧
      st'.openDirs = st.openDirs ∧
      st'.locks = (lh.handleId, lh.path, mode) :: st.locks := by
  let len : Nat := (st.locks.map (·.2.1.toList.length)).foldl Nat.max 0
  have hBound : ∀ x ∈ st.locks, x.2.1.toList.length ≤ len := fun x hx =>
    foldl_max_le (st.locks.map (·.2.1.toList.length)) 0 x.2.1.toList.length (List.mem_map.mpr ⟨x, hx, rfl⟩)
  have hConf := hasLockConflict_probeSafeNameN len st.locks hBound .exclusive
  have hLdProbe : lookupDir (probeLockStateN len st.locks 0) { handleId := 1, rootPath := "/" } = some [] := by
    simp [probeLockStateN, lookupDir]
  have hN1Probe : nodeAt (probeLockStateN len st.locks 0).tree [] = some (.dir 0o755) := rfl
  have hN2Probe : nodeAt (probeLockStateN len st.locks 0).tree [(probeSafeNameN len).val] =
      some (.file ByteArray.empty 0o644) := by
    simp [probeLockStateN, nodeAt, vfsTreeGet, vfsTreeSet, vfsEmptyDir, vfsTreeTopNode]
  have hPair : ∃ d : Nat,
      vfsDirOps.acquireLockAt dh name mode createIfMissing nonBlocking st =
        acquireLockAtTemplate st dh name mode createIfMissing d ∧
      (vfsDirOps.acquireLockAt { handleId := 1, rootPath := "/" } (probeSafeNameN len) .exclusive false true
        (probeLockStateN len st.locks 0)).1 =
        (acquireLockAtTemplate (probeLockStateN len st.locks 0) { handleId := 1, rootPath := "/" }
          (probeSafeNameN len) .exclusive false d).1 := ⟨_, rfl, rfl⟩
  rcases hPair with ⟨d, hOp, hPr⟩
  have hProbeVal : probeLockIdN len st.locks 0 = max d 0 + 1 := by
    unfold probeLockIdN
    rw [hPr]
    dsimp only [acquireLockAtTemplate]
    rw [hLdProbe]
    dsimp only
    rw [hN1Probe]
    dsimp only
    simp only [List.nil_append]
    rw [hN2Probe]
    simp [probeLockStateN, hConf]
  have hPrBounds := probeLockIdN_bounds len st.locks 0 hBound
  rw [hProbeVal] at hPrBounds
  rw [hOp] at hOk
  dsimp only [acquireLockAtTemplate] at hOk
  cases hLd : lookupDir st dh with
  | none => simp only [hLd] at hOk; cases hOk
  | some pos =>
    simp only [hLd] at hOk
    cases hP : nodeAt st.tree pos with
    | none => simp only [hP] at hOk; cases hOk
    | some node =>
      cases node with
      | file _ _ | symlink _ _ => simp only [hP] at hOk; cases hOk
      | dir parMode =>
        simp only [hP] at hOk
        by_cases hPm : (parMode / 64 % 2 == 0) = true
        · simp only [hPm, ↓reduceIte] at hOk; cases hOk
        · simp only [hPm, Bool.false_eq_true, ↓reduceIte] at hOk
          cases hC : nodeAt st.tree (pos ++ [name.val]) with
          | some cnode =>
            cases cnode with
            | dir _ | symlink _ _ => simp only [hC] at hOk; cases hOk
            | file _ _ =>
              simp only [hC] at hOk
              by_cases hc : hasLockConflict st.locks (pathOfSegs (pos ++ [name.val])) mode = true
              · simp only [hc, ↓reduceIte] at hOk; cases hOk
              · simp only [hc, Bool.false_eq_true, ↓reduceIte] at hOk
                cases hOk
                refine ⟨by dsimp only; omega, by dsimp only; omega, fun l hl => Nat.lt_of_lt_of_le (hPrBounds.2.2 l hl) (by dsimp only; omega),
                  pos, rfl, fun _ _ => rfl, rfl, rfl⟩
          | none =>
            simp only [hC] at hOk
            by_cases hCr : (!createIfMissing) = true
            · simp only [hCr, ↓reduceIte] at hOk; cases hOk
            · simp only [hCr, Bool.false_eq_true, ↓reduceIte] at hOk
              by_cases hPw : (parMode / 128 % 2 == 0) = true
              · simp only [hPw, ↓reduceIte] at hOk; cases hOk
              · simp only [hPw, Bool.false_eq_true, ↓reduceIte] at hOk
                by_cases hc : hasLockConflict st.locks (pathOfSegs (pos ++ [name.val])) mode = true
                · simp only [hc, ↓reduceIte] at hOk; cases hOk
                · simp only [hc, Bool.false_eq_true, ↓reduceIte] at hOk
                  cases hOk
                  refine ⟨by dsimp only; omega, by dsimp only; omega, fun l hl => Nat.lt_of_lt_of_le (hPrBounds.2.2 l hl) (by dsimp only; omega),
                    pos, rfl, ?_, rfl, rfl⟩
                  intro p hp
                  rcases vfsTreeGet_dir_of_nodeAt hP with ⟨ch, hDir⟩
                  unfold VfsState.nodes vfsTreeNodes
                  dsimp only
                  split
                  · exact nodeAt_vfsTreeSet_outside st.tree pos name.val (some (.file ByteArray.empty 0o644)) (vfsSplitSegs p) ⟨parMode, ch, hDir⟩ hp
                  · rfl

/-- Definitional unfolding of `vfsDirOps.closeDir`. -/
theorem vfsDirOps_closeDir_def (st : VfsState) (dh : DirHandle) :
    vfsDirOps.closeDir dh st =
      if dh.handleId == 0 then
        (.error (mInvalidDirHandleErr dh), st)
      else if st.openDirs.any (fun (id, _) => id == dh.handleId) then
        (.ok (), { st with openDirs := st.openDirs.filter (fun (id, _) => id != dh.handleId) })
      else
        (.error (mInvalidDirHandleErr dh), st) :=
  rfl

/-- Definitional unfolding of `vfsDirOps.fstatDir`. -/
theorem vfsDirOps_fstatDir_def (st : VfsState) (dh : DirHandle) :
    vfsDirOps.fstatDir dh st =
      (match lookupDir st dh with
      | none => .error (mInvalidDirHandleErr dh)
      | some pos =>
        match nodeAt st.tree pos with
        | some node => .ok (vfsToStat node)
        | none => .error { kind := .notFound, path := some dh.rootPath, message := "directory no longer exists" }, st) :=
  rfl

/-- Definitional unfolding of `vfsDirOps.lstatAt`. -/
theorem vfsDirOps_lstatAt_def (st : VfsState) (dh : DirHandle) (name : EntryName) :
    vfsDirOps.lstatAt dh name st =
      (match lookupDir st dh with
      | none => .error (mInvalidDirHandleErr dh)
      | some pos =>
        match nodeAt st.tree pos with
        | none => .error { kind := .notFound, path := some dh.rootPath, message := "directory no longer exists" }
        | some (.dir parMode) =>
          if (parMode / 64) % 2 == 0 then
            .error { kind := .permissionDenied, path := some name.val, message := s!"permission denied: {name.val}" }
          else
            match nodeAt st.tree (pos ++ [name.val]) with
            | some node => .ok (vfsToStat node)
            | none => .error { kind := .notFound, path := some name.val, message := s!"no such file or directory: {name.val}" }
        | some _ => .error { kind := .notADirectory, path := some dh.rootPath, message := s!"not a directory: {dh.rootPath}" }, st) :=
  rfl

/-- Definitional unfolding of `vfsDirOps.readDirAt`. -/
theorem vfsDirOps_readDirAt_def (st : VfsState) (dh : DirHandle) :
    vfsDirOps.readDirAt dh st =
      (match lookupDir st dh with
      | none => .error (mInvalidDirHandleErr dh)
      | some pos =>
        match nodeAt st.tree pos with
        | none => .error { kind := .notFound, path := some dh.rootPath, message := "directory no longer exists" }
        | some (.dir mode) =>
          if (mode / 256) % 2 == 0 then
            .error { kind := .permissionDenied, path := some dh.rootPath, message := s!"permission denied: {dh.rootPath}" }
          else
            .ok (mVfsReadDirAtEntries st pos)
        | some _ => .error { kind := .notADirectory, path := some dh.rootPath, message := s!"not a directory: {dh.rootPath}" }, st) :=
  rfl

/-- Definitional unfolding of `vfsDirOps.createDirAt`. -/
theorem vfsDirOps_createDirAt_def (st : VfsState) (dh : DirHandle) (name : EntryName) :
    vfsDirOps.createDirAt dh name st =
      match lookupDir st dh with
      | none => (.error (mInvalidDirHandleErr dh), st)
      | some pos =>
        match nodeAt st.tree pos with
        | none => (.error { kind := .notFound, path := some dh.rootPath, message := "directory no longer exists" }, st)
        | some (.dir parMode) =>
          if (parMode / 128) % 2 == 0 || (parMode / 64) % 2 == 0 then
            (.error { kind := .permissionDenied, path := some name.val, message := s!"permission denied: {name.val}" }, st)
          else
            let childPos := pos ++ [name.val]
            match nodeAt st.tree childPos with
            | some _ => (.error { kind := .alreadyExists, path := some name.val, message := s!"already exists: {name.val}" }, st)
            | none =>
              (.ok (), { st with
                tree := vfsTreeSet st.tree childPos (some (vfsEmptyDir 0o755))
                keys := pathOfSegs childPos :: st.keys })
        | some _ => (.error { kind := .notADirectory, path := some dh.rootPath, message := s!"not a directory: {dh.rootPath}" }, st) :=
  rfl

/-- Definitional unfolding of `vfsDirOps.readRegularAt`. -/
theorem vfsDirOps_readRegularAt_def (st : VfsState) (dh : DirHandle) (name : EntryName) :
    vfsDirOps.readRegularAt dh name st =
      (match lookupDir st dh with
      | none => .error (mInvalidDirHandleErr dh)
      | some pos =>
        match nodeAt st.tree pos with
        | none => .error { kind := .notFound, path := some dh.rootPath, message := "directory no longer exists" }
        | some (.dir parMode) =>
          if (parMode / 64) % 2 == 0 then
            .error { kind := .permissionDenied, path := some name.val, message := s!"permission denied: {name.val}" }
          else
            match nodeAt st.tree (pos ++ [name.val]) with
            | none => .error { kind := .notFound, path := some name.val, message := s!"no such file or directory: {name.val}" }
            | some (.file bs fMode) =>
              if (fMode / 256) % 2 == 0 then
                .error { kind := .permissionDenied, path := some name.val, message := s!"permission denied: {name.val}" }
              else
                .ok bs
            | some (.dir _) => .error { kind := .isADirectory, path := some name.val, message := s!"is a directory: {name.val}" }
            | some (.symlink _ _) => .error { kind := .invalidInput, path := some name.val, message := s!"symlink refused: {name.val}" }
        | some _ => .error { kind := .notADirectory, path := some dh.rootPath, message := s!"not a directory: {dh.rootPath}" }, st) :=
  rfl

/-- Definitional unfolding of `vfsDirOps.createFileAt`. -/
theorem vfsDirOps_createFileAt_def (st : VfsState) (dh : DirHandle) (name : EntryName) (bytes : ByteArray) :
    vfsDirOps.createFileAt dh name bytes st =
      match lookupDir st dh with
      | none => (.error (mInvalidDirHandleErr dh), st)
      | some pos =>
        match nodeAt st.tree pos with
        | none => (.error { kind := .notFound, path := some dh.rootPath, message := "directory no longer exists" }, st)
        | some (.dir parMode) =>
          if (parMode / 128) % 2 == 0 || (parMode / 64) % 2 == 0 then
            (.error { kind := .permissionDenied, path := some name.val, message := s!"permission denied: {name.val}" }, st)
          else
            let childPos := pos ++ [name.val]
            match nodeAt st.tree childPos with
            | some _ => (.error { kind := .alreadyExists, path := some name.val, message := s!"already exists: {name.val}" }, st)
            | none =>
              (.ok (), { st with
                tree := vfsTreeSet st.tree childPos (some (.file bytes 0o644))
                keys := pathOfSegs childPos :: st.keys })
        | some _ => (.error { kind := .notADirectory, path := some dh.rootPath, message := s!"not a directory: {dh.rootPath}" }, st) :=
  rfl

/-- Definitional unfolding of `vfsDirOps.renameAt`. -/
theorem vfsDirOps_renameAt_def (st : VfsState) (srcDh : DirHandle) (srcName : EntryName)
    (dstDh : DirHandle) (dstName : EntryName) :
    vfsDirOps.renameAt srcDh srcName dstDh dstName st =
      match lookupDir st srcDh, lookupDir st dstDh with
      | none, _ => (.error (mInvalidDirHandleErr srcDh), st)
      | _, none => (.error (mInvalidDirHandleErr dstDh), st)
      | some srcPos, some dstPos =>
        match nodeAt st.tree srcPos, nodeAt st.tree dstPos with
        | some (.dir srcMode), some (.dir dstMode) =>
          if (srcMode / 128) % 2 == 0 || (srcMode / 64) % 2 == 0 then
            (.error { kind := .permissionDenied, path := some srcName.val, message := s!"permission denied: {srcName.val}" }, st)
          else if (dstMode / 128) % 2 == 0 || (dstMode / 64) % 2 == 0 then
            (.error { kind := .permissionDenied, path := some dstName.val, message := s!"permission denied: {dstName.val}" }, st)
          else
            let srcFull := srcPos ++ [srcName.val]
            let dstFull := dstPos ++ [dstName.val]
            match vfsTreeGet st.tree srcFull with
            | none => (.error { kind := .notFound, path := some srcName.val, message := s!"no such file or directory: {srcName.val}" }, st)
            | some srcSub =>
              if srcFull == dstFull then
                (.ok (), st)
              else if srcFull.isPrefixOf dstPos then
                (.error { kind := .invalidInput, path := some dstName.val, message := "cannot rename directory into itself" }, st)
              else
                let srcIsDir := match srcSub with | .dir _ _ => true | _ => false
                let dstNode := nodeAt st.tree dstFull
                match srcIsDir, dstNode with
                | false, some (.dir _) =>
                  (.error { kind := .isADirectory, path := some dstName.val, message := s!"is a directory: {dstName.val}" }, st)
                | true, some (.file _ _) | true, some (.symlink _ _) =>
                  (.error { kind := .notADirectory, path := some dstName.val, message := s!"not a directory: {dstName.val}" }, st)
                | true, some (.dir _) =>
                  if mDirHasLiveChild st dstFull then
                    (.error { kind := .notEmpty, path := some dstName.val, message := s!"directory not empty: {dstName.val}" }, st)
                  else
                    let tr₁ := vfsTreeSet st.tree srcFull none
                    (.ok (), { st with
                      tree := vfsTreeSet tr₁ dstFull (some srcSub)
                      keys := pathOfSegs dstFull :: mRemapKeysAfterRename st.keys srcFull dstFull })
                | _, _ =>
                  let tr₁ := vfsTreeSet st.tree srcFull none
                  (.ok (), { st with
                    tree := vfsTreeSet tr₁ dstFull (some srcSub)
                    keys := pathOfSegs dstFull :: mRemapKeysAfterRename st.keys srcFull dstFull })
        | none, _ => (.error { kind := .notFound, path := some srcDh.rootPath, message := "source directory no longer exists" }, st)
        | _, none => (.error { kind := .notFound, path := some dstDh.rootPath, message := "destination directory no longer exists" }, st)
        | some _, _ => (.error { kind := .notADirectory, path := some srcDh.rootPath, message := s!"not a directory: {srcDh.rootPath}" }, st) :=
  rfl

/-- Definitional unfolding of `vfsDirOps.unlinkAt`. -/
theorem vfsDirOps_unlinkAt_def (st : VfsState) (dh : DirHandle) (name : EntryName) (isDir : Bool) :
    vfsDirOps.unlinkAt dh name isDir st =
      match lookupDir st dh with
      | none => (.error (mInvalidDirHandleErr dh), st)
      | some pos =>
        match nodeAt st.tree pos with
        | none => (.error { kind := .notFound, path := some dh.rootPath, message := "directory no longer exists" }, st)
        | some (.dir parMode) =>
          if (parMode / 128) % 2 == 0 || (parMode / 64) % 2 == 0 then
            (.error { kind := .permissionDenied, path := some name.val, message := s!"permission denied: {name.val}" }, st)
          else
            let childPos := pos ++ [name.val]
            match nodeAt st.tree childPos with
            | none => (.error { kind := .notFound, path := some name.val, message := s!"no such file or directory: {name.val}" }, st)
            | some (.dir _) =>
              if !isDir then
                (.error { kind := .isADirectory, path := some name.val, message := s!"is a directory: {name.val}" }, st)
              else if mDirHasLiveChild st childPos then
                (.error { kind := .notEmpty, path := some name.val, message := s!"directory not empty: {name.val}" }, st)
              else
                (.ok (), { st with tree := vfsTreeSet st.tree childPos none })
            | some _ =>
              if isDir then
                (.error { kind := .notADirectory, path := some name.val, message := s!"not a directory: {name.val}" }, st)
              else
                (.ok (), { st with tree := vfsTreeSet st.tree childPos none })
        | some _ => (.error { kind := .notADirectory, path := some dh.rootPath, message := s!"not a directory: {dh.rootPath}" }, st) :=
  rfl

/-- Definitional unfolding of `vfsDirOps.symlinkAt`. -/
theorem vfsDirOps_symlinkAt_def (st : VfsState) (target : String) (dh : DirHandle) (linkName : EntryName) :
    vfsDirOps.symlinkAt target dh linkName st =
      if target.isEmpty || target.toList.contains (Char.ofNat 0) then
        (.error { kind := .invalidInput, path := some linkName.val, message := "invalid symlink target" }, st)
      else
        match lookupDir st dh with
        | none => (.error (mInvalidDirHandleErr dh), st)
        | some pos =>
          match nodeAt st.tree pos with
          | none => (.error { kind := .notFound, path := some dh.rootPath, message := "directory no longer exists" }, st)
          | some (.dir parMode) =>
            if (parMode / 128) % 2 == 0 || (parMode / 64) % 2 == 0 then
              (.error { kind := .permissionDenied, path := some linkName.val, message := s!"permission denied: {linkName.val}" }, st)
            else
              let childPos := pos ++ [linkName.val]
              match nodeAt st.tree childPos with
              | some _ => (.error { kind := .alreadyExists, path := some linkName.val, message := s!"already exists: {linkName.val}" }, st)
              | none =>
                (.ok (), { st with
                  tree := vfsTreeSet st.tree childPos (some (.symlink target 0o777))
                  keys := pathOfSegs childPos :: st.keys })
          | some _ => (.error { kind := .notADirectory, path := some dh.rootPath, message := s!"not a directory: {dh.rootPath}" }, st) :=
  rfl

/-- Definitional unfolding of `vfsDirOps.releaseLock`. -/
theorem vfsDirOps_releaseLock_def (st : VfsState) (handle : LockHandle) :
    vfsDirOps.releaseLock handle st =
      if handle.handleId == 0 then
        (.error { kind := .invalidInput, path := some handle.path, message := "invalid lock handle" }, st)
      else if st.locks.any (fun (id, _, _) => id == handle.handleId) then
        (.ok (), { st with locks := st.locks.filter (fun (id, _, _) => id != handle.handleId) })
      else
        (.error { kind := .invalidInput, path := some handle.path, message := "unknown lock handle" }, st) :=
  rfl

/-- `vfsDirOps.freshTempName` yields `".t." ++ toString st.nonce` and increments `st.nonce`. -/
theorem vfsDirOps_freshTempName_def (st : VfsState) :
    (vfsDirOps.freshTempName st).1.val = ".t." ++ toString st.nonce ∧
    (vfsDirOps.freshTempName st).2 = { st with nonce := st.nonce + 1 } :=
  ⟨rfl, rfl⟩

/-- If `vfsResolveSegs` succeeds with `(c, n)`, then `nodes c = some n`. -/
theorem subtreeVfsResolveSegs_ok_node (nodes : String → Option VfsNode) :
    ∀ fuel cur segs follow c n,
      vfsResolveSegs nodes cur segs follow fuel = .ok (c, n) →
      nodes c = some n := by
  intro fuel
  induction fuel with
  | zero => intro _ _ _ _ _ h; simp [vfsResolveSegs] at h
  | succ fuel ih =>
    intro cur segs follow c n hOk
    simp only [vfsResolveSegs] at hOk
    cases segs with
    | nil =>
      cases hNd : nodes cur with
      | none => simp [hNd] at hOk
      | some nd =>
        simp only [hNd] at hOk
        cases nd with
        | symlink _ _ =>
          cases follow
          · simp only [Bool.false_eq_true, ↓reduceIte, Except.ok.injEq, Prod.mk.injEq] at hOk
            rcases hOk with ⟨rfl, rfl⟩
            exact hNd
          · simp only [↓reduceIte] at hOk
            exact ih "/" _ true c n hOk
        | file _ _ | dir _ =>
          simp only [Except.ok.injEq, Prod.mk.injEq] at hOk
          rcases hOk with ⟨rfl, rfl⟩
          exact hNd
    | cons seg rest =>
      cases hNd : nodes cur with
      | none => simp [hNd] at hOk
      | some nd =>
        simp only [hNd] at hOk
        cases nd with
        | file _ _ => simp at hOk
        | dir mode =>
          by_cases hm : ((mode / 64) % 2 == 0) = true
          · simp [hm] at hOk
          · have hmf : ((mode / 64) % 2 == 0) = false := Bool.eq_false_iff.mpr hm
            simp only [hmf, Bool.false_eq_true, ↓reduceIte] at hOk
            exact ih (vfsChildPath cur seg) rest follow c n hOk
        | symlink _ _ => exact ih "/" _ follow c n hOk

private theorem splitCharList_ne_nil (sep : Char) (cs : List Char) :
    Internal.splitCharList sep cs ≠ [] := by
  induction cs with
  | nil => simp [Internal.splitCharList]
  | cons _ rest _ =>
    simp only [Internal.splitCharList]
    split
    · simp
    · cases Internal.splitCharList sep rest <;> simp

private theorem splitCharList_no_sep (sep : Char) (cs : List Char) :
    ∀ seg ∈ Internal.splitCharList sep cs, sep ∉ seg := by
  induction cs with
  | nil => simp [Internal.splitCharList]
  | cons c rest ih =>
    simp only [Internal.splitCharList]
    split
    · intro seg hmem
      simp only [List.mem_cons] at hmem
      rcases hmem with rfl | hmem
      · simp
      · exact ih seg hmem
    · next hne =>
      have hcne : c ≠ sep := fun h => hne (by subst h; exact beq_self_eq_true _)
      cases hsp : Internal.splitCharList sep rest with
      | nil => exact absurd hsp (splitCharList_ne_nil sep rest)
      | cons hd tl =>
        intro seg hmem
        simp only [List.mem_cons] at hmem
        rcases hmem with rfl | hmem
        · intro hIn
          simp only [List.mem_cons] at hIn
          rcases hIn with hce | hIn
          · exact hcne hce.symm
          · exact ih hd (by rw [hsp]; simp) hIn
        · exact ih seg (by rw [hsp]; simp [hmem])

private theorem splitCharList_of_no_sep (sep : Char) (b : List Char) (hno : sep ∉ b) :
    Internal.splitCharList sep b = [b] := by
  induction b with
  | nil => simp [Internal.splitCharList]
  | cons c rest ih =>
    have hcne : c ≠ sep := fun h => hno (by subst h; simp)
    have ih' := ih (fun h => hno (by simp [h]))
    simp [Internal.splitCharList, beq_false_of_ne hcne, ih']

private theorem splitCharList_append_slash (a b : List Char) (hno : '/' ∉ a) :
    Internal.splitCharList '/' (a ++ '/' :: b) = a :: Internal.splitCharList '/' b := by
  induction a with
  | nil => simp [Internal.splitCharList]
  | cons c rest ih =>
    have hcne : c ≠ '/' := fun h => hno (by subst h; simp)
    have ih' := ih (fun h => hno (by simp [h]))
    simp [List.cons_append, Internal.splitCharList, beq_false_of_ne hcne, ih']

private theorem splitCharList_joinSlashChars_append (segs : List (List Char))
    (hne : segs ≠ []) (hno : ∀ s ∈ segs, '/' ∉ s) (tail : List Char) :
    Internal.splitCharList '/' (Internal.joinSlashChars segs ++ '/' :: tail) =
      segs ++ Internal.splitCharList '/' tail := by
  induction segs with
  | nil => exact absurd rfl hne
  | cons s rest ih =>
    cases rest with
    | nil =>
      simp only [Internal.joinSlashChars]
      rw [splitCharList_append_slash s tail (hno s (by simp))]
      rfl
    | cons s2 tl =>
      have ih' := ih (by simp) (fun x hx => hno x (by simp [hx]))
      simp only [Internal.joinSlashChars, List.append_assoc, List.cons_append]
      rw [splitCharList_append_slash s (Internal.joinSlashChars (s2 :: tl) ++ '/' :: tail) (hno s (by simp)), ih']
      rfl

private theorem splitCharList_joinSlashChars (segs : List (List Char))
    (hne : segs ≠ []) (hno : ∀ s ∈ segs, '/' ∉ s) :
    Internal.splitCharList '/' (Internal.joinSlashChars segs) = segs := by
  induction segs with
  | nil => exact absurd rfl hne
  | cons s rest ih =>
    cases rest with
    | nil =>
      simp only [Internal.joinSlashChars]
      exact splitCharList_of_no_sep '/' s (hno s (by simp))
    | cons s2 tl =>
      have ih' := ih (by simp) (fun x hx => hno x (by simp [hx]))
      simp only [Internal.joinSlashChars]
      rw [splitCharList_append_slash s (Internal.joinSlashChars (s2 :: tl)) (hno s (by simp)), ih']

private theorem joinSlashChars_append_singleton (xs : List (List Char)) (hxs : xs ≠ []) (last : List Char) :
    Internal.joinSlashChars (xs ++ [last]) = Internal.joinSlashChars xs ++ '/' :: last := by
  induction xs with
  | nil => exact absurd rfl hxs
  | cons hd tl ih =>
    cases tl with
    | nil => simp [Internal.joinSlashChars]
    | cons b bs =>
      have hSub : b :: (bs ++ [last]) = (b :: bs) ++ [last] := rfl
      simp only [List.cons_append, Internal.joinSlashChars]
      rw [hSub, ih (by simp)]
      simp [List.cons_append]

private theorem collapseChars_elems_valid (abs : Bool) (segs acc : List (List Char))
    (hAcc : ∀ s ∈ acc, !s.isEmpty ∧ s != ['.'] ∧ '/' ∉ s)
    (hSegs : ∀ s ∈ segs, '/' ∉ s) :
    ∀ s ∈ Internal.collapseChars abs segs acc, !s.isEmpty ∧ s != ['.'] ∧ '/' ∉ s := by
  induction segs generalizing acc with
  | nil =>
    intro s hs
    simp only [Internal.collapseChars, List.mem_reverse] at hs
    exact hAcc s hs
  | cons seg rest ih =>
    simp only [Internal.collapseChars]
    split
    · exact ih acc hAcc (fun x hx => hSegs x (by simp [hx]))
    · split
      · cases acc with
        | nil =>
          apply ih
          · intro s hs
            cases abs with
            | true => simp at hs
            | false => simp at hs; subst hs; decide
          · exact fun x hx => hSegs x (by simp [hx])
        | cons _ tail =>
          simp only
          split
          · exact ih tail (fun x hx => hAcc x (by simp [hx])) (fun x hx => hSegs x (by simp [hx]))
          · apply ih
            · intro s hs
              cases abs with
              | false =>
                simp only [Bool.false_eq_true, ↓reduceIte, List.mem_cons] at hs
                rcases hs with rfl | hs
                · decide
                · exact hAcc s (List.mem_cons.mpr hs)
              | true => exact hAcc s (by simpa using hs)
            · exact fun x hx => hSegs x (by simp [hx])
      · apply ih
        · intro s hs
          simp only [List.mem_cons] at hs
          rcases hs with rfl | hs
          · next h1 _ =>
            simp only [Bool.or_eq_true] at h1
            have hnEmpty : (!s.isEmpty) = true := by cases he : List.isEmpty s <;> simp_all
            have hnDot : (s != ['.']) = true := by cases hd : (s == ['.']) <;> simp_all
            exact ⟨hnEmpty, hnDot, hSegs s (by simp)⟩
          · exact hAcc s hs
        · exact fun x hx => hSegs x (by simp [hx])

private theorem collapseChars_noop_noDotDot (rest acc : List (List Char))
    (hElem : ∀ s ∈ rest, !s.isEmpty ∧ s != ['.'])
    (hNo : ∀ s ∈ rest, s ≠ ['.', '.']) :
    Internal.collapseChars true rest acc = acc.reverse ++ rest := by
  induction rest generalizing acc with
  | nil => simp [Internal.collapseChars]
  | cons seg rest ih =>
    have hS := hElem seg (by simp)
    have hnSkip : (seg.isEmpty || seg == ['.']) = false := by
      cases he : List.isEmpty seg <;> cases hd : (seg == ['.']) <;> simp_all
    have hNeFalse : (seg == ['.', '.']) = false := beq_false_of_ne (hNo seg (by simp))
    simp only [Internal.collapseChars, hnSkip, Bool.false_eq_true, ↓reduceIte, hNeFalse]
    rw [ih (seg :: acc) (fun x hx => hElem x (by simp [hx])) (fun x hx => hNo x (by simp [hx]))]
    simp

private theorem string_intercalate_eq_foldl (sep a : String) (xs : List String) :
    String.intercalate sep (a :: xs) = xs.foldl (fun acc x => acc ++ sep ++ x) a := by
  dsimp [String.intercalate]
  induction xs generalizing a with
  | nil => rfl
  | cons b bs ih => exact ih (a ++ sep ++ b)

private theorem string_intercalate_slash_cons (a b : String) (bs : List String) :
    String.intercalate "/" (a :: b :: bs) = a ++ "/" ++ String.intercalate "/" (b :: bs) := by
  rw [string_intercalate_eq_foldl, string_intercalate_eq_foldl]
  have hFold : ∀ (xs : List String) (p q : String),
      xs.foldl (fun s x => s ++ "/" ++ x) (p ++ "/" ++ q) =
        p ++ "/" ++ xs.foldl (fun s x => s ++ "/" ++ x) q := by
    intro xs
    induction xs with
    | nil => intro p q; rfl
    | cons c cs ih =>
      intro p q
      simp only [List.foldl_cons]
      have hAssoc : (p ++ "/" ++ q) ++ "/" ++ c = p ++ "/" ++ (q ++ "/" ++ c) :=
        String.ext_iff.mpr (by simp [String.toList_append, List.append_assoc])
      rw [hAssoc]
      exact ih p (q ++ "/" ++ c)
  exact hFold bs a b

private theorem intercalate_slash_toList (xs : List String) :
    (String.intercalate "/" xs).toList = Internal.joinSlashChars (xs.map String.toList) := by
  induction xs with
  | nil => simp [String.intercalate, Internal.joinSlashChars]
  | cons a rest ih =>
    cases rest with
    | nil =>
      rw [string_intercalate_eq_foldl]
      simp [Internal.joinSlashChars]
    | cons b bs =>
      rw [string_intercalate_slash_cons a b bs, String.toList_append, String.toList_append,
        show "/".toList = ['/'] by decide, List.append_assoc, List.singleton_append]
      exact congrArg (fun l => a.toList ++ '/' :: l) ih

/-- Canonical `pathOfSegs` equals `'/'` followed by `Internal.joinSlashChars`. -/
theorem pathOfSegs_eq_ofList_joinSlashChars (segs : List String) :
    pathOfSegs segs = String.ofList ('/' :: Internal.joinSlashChars (segs.map String.toList)) := by
  cases segs with
  | nil => rfl
  | cons a rest =>
    apply String.ext_iff.mpr
    simp only [pathOfSegs, String.toList_append, String.toList_ofList, show "/".toList = ['/'] by decide,
      List.singleton_append]
    exact congrArg ('/' :: ·) (intercalate_slash_toList (a :: rest))

private theorem validSeg_charProps (s : String) (h : validSeg s = true) :
    !s.toList.isEmpty ∧ s.toList != ['.'] ∧ '/' ∉ s.toList ∧ s.toList ≠ ['.', '.'] := by
  unfold validSeg at h
  simp only [Bool.and_eq_true, Bool.not_eq_true', bne_iff_ne, ne_eq] at h
  rcases h with ⟨⟨⟨⟨hEmp, hSl⟩, _⟩, hDot⟩, hDotDot⟩
  have hSlNot : '/' ∉ s.toList := fun hm => by simp [hm] at hSl
  have hNeNil : s.toList ≠ [] := by intro hn; rw [hn] at hEmp; simp at hEmp
  have hNotEmp : (!s.toList.isEmpty) = true := by cases htl : s.toList <;> simp_all
  have hNotDotL : (s.toList != ['.']) = true := bne_iff_ne.mpr fun heq => by
    apply hDot; rw [← String.ofList_toList (s := s), heq]; rfl
  have hNotDD : s.toList ≠ ['.', '.'] := fun heq => by
    apply hDotDot; rw [← String.ofList_toList (s := s), heq]; rfl
  exact ⟨hNotEmp, hNotDotL, hSlNot, hNotDD⟩

/-- `validSeg s = true` implies `Internal.validFileName s = true`. -/
theorem validFileName_of_validSeg (s : String) (h : validSeg s = true) :
    Internal.validFileName s = true := by
  unfold validSeg at h
  simp only [Bool.and_eq_true, Bool.not_eq_true', bne_iff_ne, ne_eq] at h
  rcases h with ⟨⟨⟨⟨hEmp, hSl⟩, _⟩, hDot⟩, hDotDot⟩
  simp only [Internal.validFileName, Bool.and_eq_true, Bool.not_eq_true', bne_iff_ne, ne_eq]
  exact ⟨⟨⟨hEmp, hSl⟩, hDot⟩, hDotDot⟩

private theorem model_splitCharList_eq_internal (sep : Char) (cs : List Char) :
    Model.splitCharList sep cs = Internal.splitCharList sep cs := by
  induction cs with
  | nil => rfl
  | cons c rest ih =>
    by_cases h : (c == sep) = true <;> (simp [Model.splitCharList, Internal.splitCharList, h, ih]; try rfl)

private theorem model_joinSlashChars_eq_internal (segs : List (List Char)) :
    Model.joinSlashChars segs = Internal.joinSlashChars segs := by
  induction segs with
  | nil => rfl
  | cons s rest ih =>
    cases rest with
    | nil => rfl
    | cons _ _ => simp only [Model.joinSlashChars, Internal.joinSlashChars, ih]

private theorem model_collapseChars_eq_internal (abs : Bool) (segs acc : List (List Char)) :
    Model.collapseChars abs segs acc = Internal.collapseChars abs segs acc := by
  induction segs generalizing acc with
  | nil => rfl
  | cons seg rest ih =>
    unfold Model.collapseChars Internal.collapseChars
    split
    · exact ih acc
    · split
      · cases acc with
        | nil => exact ih _
        | cons top tail =>
          dsimp only
          split
          · exact ih tail
          · exact ih _
      · exact ih (seg :: acc)

/-- Equivalence between `Model.normPath` and `Internal.normPath`. -/
theorem model_normPath_eq_internal (p : String) :
    Model.normPath p = Internal.normPath p := by
  unfold Model.normPath Internal.normPath
  simp only [model_splitCharList_eq_internal, model_collapseChars_eq_internal, model_joinSlashChars_eq_internal]
  rfl

private theorem vfsSplitSegs_joinSlashChars_valid (parts : List (List Char))
    (hParts : ∀ s ∈ parts, !s.isEmpty ∧ '/' ∉ s) :
    vfsSplitSegs (String.ofList ('/' :: Internal.joinSlashChars parts)) = parts.map String.ofList := by
  unfold vfsSplitSegs
  simp only [String.toList_ofList, model_splitCharList_eq_internal]
  cases parts with
  | nil => simp [Internal.joinSlashChars, Internal.splitCharList]
  | cons hd tl =>
    simp only [List.map_cons]
    rw [splitCharList_joinSlashChars (hd :: tl) (by simp) (fun s hs => (hParts s hs).2)]
    simp only [List.filterMap_cons]
    have hMap : ∀ xs : List (List Char), (∀ s ∈ xs, !s.isEmpty) →
        List.filterMap (fun cs => if cs.isEmpty then none else some (String.ofList cs)) xs = xs.map String.ofList := by
      intro xs hxs
      induction xs with
      | nil => rfl
      | cons x xt ihx =>
        rcases x with _ | ⟨c, cs⟩
        · have := hxs [] (by simp); simp at this
        · have hTail := ihx (fun y hy => hxs y (by simp [hy]))
          simpa using congrArg (String.ofList (c :: cs) :: ·) hTail
    rcases hd with _ | ⟨hc, hcs⟩
    · have := hParts [] (by simp); simp at this
    · have hTl := hMap tl (fun s hs => (hParts s (by simp [hs])).1)
      simpa using congrArg (String.ofList (hc :: hcs) :: ·) hTl

/-- Splitting `pathOfSegs segs` recovers `segs` whenever every segment is `validSeg`. -/
theorem vfsSplitSegs_pathOfSegs (segs : List String) (hValid : ∀ s ∈ segs, validSeg s = true) :
    vfsSplitSegs (pathOfSegs segs) = segs := by
  rw [pathOfSegs_eq_ofList_joinSlashChars, vfsSplitSegs_joinSlashChars_valid]
  · simp [List.map_map, Function.comp_def]
  · intro p hp
    simp only [List.mem_map] at hp
    rcases hp with ⟨s, hs, rfl⟩
    have hv := validSeg_charProps s (hValid s hs)
    exact ⟨hv.1, hv.2.2.1⟩

/-- Every `pathOfSegs segs` with `validSeg` segments satisfies `isCanonPath`. -/
theorem isCanonPath_pathOfSegs (segs : List String) (hValid : ∀ s ∈ segs, validSeg s = true) :
    isCanonPath (pathOfSegs segs) = true := by
  rw [pathOfSegs_eq_ofList_joinSlashChars]
  simp only [isCanonPath, Bool.and_eq_true, beq_iff_eq, model_normPath_eq_internal]
  refine ⟨by simp [Model.isAbsolute, Model.isAbsChars], ?_⟩
  simp only [Internal.normPath, String.toList_ofList, Internal.isAbsChars, ↓reduceIte]
  rw [show Internal.splitCharList '/' ('/' :: Internal.joinSlashChars (segs.map String.toList)) =
      [] :: Internal.splitCharList '/' (Internal.joinSlashChars (segs.map String.toList)) by
    simp [Internal.splitCharList]]
  rw [show Internal.collapseChars true ([] :: Internal.splitCharList '/' (Internal.joinSlashChars (segs.map String.toList))) [] =
      Internal.collapseChars true (Internal.splitCharList '/' (Internal.joinSlashChars (segs.map String.toList))) [] by
    simp [Internal.collapseChars]]
  cases segs with
  | nil => simp [Internal.joinSlashChars, Internal.splitCharList, Internal.collapseChars]
  | cons a rest =>
    have hParts : ∀ s ∈ (a :: rest).map String.toList, !s.isEmpty ∧ s != ['.'] ∧ '/' ∉ s ∧ s ≠ ['.', '.'] := by
      intro p hp
      simp only [List.mem_map] at hp
      rcases hp with ⟨s, hs, rfl⟩
      exact validSeg_charProps s (hValid s hs)
    rw [splitCharList_joinSlashChars _ (by simp) (fun s hs => (hParts s hs).2.2.1)]
    rw [collapseChars_noop_noDotDot _ [] (fun s hs => ⟨(hParts s hs).1, (hParts s hs).2.1⟩) (fun s hs => (hParts s hs).2.2.2)]
    simp

/-- Appending `c` to `pos` extends `pathOfSegs pos` by `prefixChars ++ c.toList`. -/
theorem pathOfSegs_snoc_toList (pos : List String) (c : String) (hPos : ∀ s ∈ pos, validSeg s = true) :
    (pathOfSegs (pos ++ [c])).toList =
      (if pathOfSegs pos == "/" then "/" else pathOfSegs pos ++ "/").toList ++ c.toList := by
  cases pos with
  | nil =>
    simp [pathOfSegs, String.toList_append, show "/".toList = ['/'] by decide]
  | cons a rest =>
    have hCanon := isCanonPath_pathOfSegs (a :: rest) hPos
    have hSp := vfsSplitSegs_pathOfSegs (a :: rest) hPos
    have hNeRoot : pathOfSegs (a :: rest) ≠ "/" := by
      intro hEq
      have h1 : vfsSplitSegs "/" = [] := by decide
      rw [hEq, h1] at hSp
      cases hSp
    rw [beq_false_of_ne hNeRoot]
    simp only [Bool.false_eq_true, ↓reduceIte, pathOfSegs_eq_ofList_joinSlashChars, List.map_append,
      List.map_singleton, String.toList_append, String.toList_ofList, show "/".toList = ['/'] by decide]
    rw [joinSlashChars_append_singleton ((a :: rest).map String.toList) (by simp) c.toList]
    simp [List.append_assoc]

/-- Injectivity of `pathOfSegs` on lists of `validSeg` segments. -/
theorem pathOfSegs_inj {s1 s2 : List String}
    (h1 : ∀ s ∈ s1, validSeg s = true) (h2 : ∀ s ∈ s2, validSeg s = true)
    (hEq : pathOfSegs s1 = pathOfSegs s2) : s1 = s2 := by
  have h := congrArg vfsSplitSegs hEq
  rwa [vfsSplitSegs_pathOfSegs s1 h1, vfsSplitSegs_pathOfSegs s2 h2] at h

/-- `vfsChildPath (pathOfSegs xs) a = pathOfSegs (xs ++ [a])`. -/
theorem vfsChildPath_pathOfSegs (xs : List String) (a : String) (hXs : ∀ s ∈ xs, validSeg s = true) :
    vfsChildPath (pathOfSegs xs) a = pathOfSegs (xs ++ [a]) := by
  cases xs with
  | nil => simp [vfsChildPath, pathOfSegs]
  | cons x rest =>
    have hSp := vfsSplitSegs_pathOfSegs (x :: rest) hXs
    have hNeRoot : pathOfSegs (x :: rest) ≠ "/" := by
      intro hEq
      have h1 : vfsSplitSegs "/" = [] := by decide
      rw [hEq, h1] at hSp
      cases hSp
    simp only [vfsChildPath, beq_false_of_ne hNeRoot, Bool.false_eq_true, ↓reduceIte]
    apply String.ext_iff.mpr
    have hSnoc := pathOfSegs_snoc_toList (x :: rest) a hXs
    rw [beq_false_of_ne hNeRoot] at hSnoc
    simp only [Bool.false_eq_true, ↓reduceIte, String.toList_append, show "/".toList = ['/'] by decide] at hSnoc ⊢
    exact hSnoc.symm

private def evalDigits10 (cs : List Char) : Nat :=
  cs.foldl (fun acc c => acc * 10 + (c.toNat - '0'.toNat)) 0

private theorem evalDigits10_append_singleton (xs : List Char) (d : Char) :
    evalDigits10 (xs ++ [d]) = evalDigits10 xs * 10 + (d.toNat - '0'.toNat) := by
  simp [evalDigits10, List.foldl_append]

private theorem digitChar_val (d : Nat) (hd : d < 10) :
    (Nat.digitChar d).toNat - '0'.toNat = d := by
  rcases d with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | k
  all_goals first | decide | omega

private theorem toDigitsCore_append (fuel n : Nat) (acc : List Char) :
    Nat.toDigitsCore 10 fuel n acc = Nat.toDigitsCore 10 fuel n [] ++ acc := by
  induction fuel generalizing n acc with
  | zero => simp [Nat.toDigitsCore]
  | succ f ih =>
    simp only [Nat.toDigitsCore]
    split
    · rfl
    · rw [ih (n / 10) (Nat.digitChar (n % 10) :: acc), ih (n / 10) [Nat.digitChar (n % 10)]]
      simp

private theorem toDigitsCore_val (fuel n : Nat) (hLt : n < fuel) :
    evalDigits10 (Nat.toDigitsCore 10 fuel n []) = n := by
  induction fuel generalizing n with
  | zero => omega
  | succ f ih =>
    simp only [Nat.toDigitsCore]
    split
    · next hq =>
      have hLt : n < 10 := Nat.lt_of_div_eq_zero (by decide) hq
      simp only [evalDigits10, List.foldl_cons, List.foldl_nil, Nat.zero_mul, Nat.zero_add]
      rw [Nat.mod_eq_of_lt hLt]
      exact digitChar_val n hLt
    · next hq =>
      have hnPos : 10 ≤ n := Nat.le_of_not_lt fun h => hq (Nat.div_eq_of_lt h)
      have hDivLt : n / 10 < f := by omega
      rw [toDigitsCore_append f (n / 10) [Nat.digitChar (n % 10)]]
      rw [evalDigits10_append_singleton, ih (n / 10) hDivLt, digitChar_val (n % 10) (by omega)]
      omega

/-- Decimal `toString` on `Nat` is injective. -/
theorem nat_toString_inj {n m : Nat} (h : toString n = toString m) : n = m := by
  have hl := congrArg String.toList h
  have hn : (toString n).toList = Nat.toDigits 10 n := by simp [toString, Nat.repr]
  have hm : (toString m).toList = Nat.toDigits 10 m := by simp [toString, Nat.repr]
  rw [hn, hm] at hl
  have h1 := toDigitsCore_val (n + 1) n (by omega)
  have h2 := toDigitsCore_val (m + 1) m (by omega)
  unfold Nat.toDigits at hl
  rw [← h1, ← h2, hl]

private theorem mem_eraseDups_iff {α : Type} [BEq α] [LawfulBEq α] {xs : List α} {a : α} :
    a ∈ xs.eraseDups ↔ a ∈ xs := by
  simp

private theorem eraseDups_nodup {α : Type} [BEq α] [LawfulBEq α] (xs : List α) :
    xs.eraseDups.Nodup := by
  match xs with
  | [] => simp
  | a :: as =>
    rw [List.eraseDups_cons, List.nodup_cons]
    refine ⟨?_, eraseDups_nodup _⟩
    intro hm
    rw [List.mem_eraseDups, List.mem_filter] at hm
    simp at hm
termination_by xs.length
decreasing_by exact Nat.lt_succ_of_le (List.length_filter_le _ _)

private theorem list_filterMap_nodup_of_inj {α β : Type} {f : α → Option β} {xs : List α}
    (hNd : xs.Nodup) (hInj : ∀ {a₁ a₂ : α} {b : β}, f a₁ = some b → f a₂ = some b → a₁ = a₂) :
    (xs.filterMap f).Nodup := by
  induction xs with
  | nil => simp
  | cons a tl ih =>
    rw [List.nodup_cons] at hNd
    have ih' := ih hNd.2
    simp only [List.filterMap_cons]
    cases hfa : f a with
    | none => exact ih'
    | some b =>
      rw [List.nodup_cons]
      refine ⟨?_, ih'⟩
      intro hMem
      rw [List.mem_filterMap] at hMem
      rcases hMem with ⟨a', ha', hfa'⟩
      have heq := hInj hfa hfa'
      subst heq
      exact hNd.1 ha'

/-- `(mVfsReadDirAtEntries st pos).toList` never contains duplicate entry names. -/
theorem mVfsReadDirAtEntries_nodup (st : VfsState) (pos : List String) :
    (mVfsReadDirAtEntries st pos).toList.Nodup := by
  unfold mVfsReadDirAtEntries
  dsimp only
  refine list_filterMap_nodup_of_inj (eraseDups_nodup st.keys) ?_
  intro k₁ k₂ e h1 h2
  by_cases hN1 : (st.nodes k₁).isSome = true
  · simp only [hN1, ↓reduceIte] at h1
    by_cases hP1 : (k₁ != pathOfSegs pos &&
        (if pathOfSegs pos == "/" then "/" else pathOfSegs pos ++ "/").toList.isPrefixOf k₁.toList) = true
    · simp only [hP1, ↓reduceIte] at h1
      by_cases hV1 : validSeg (String.ofList (k₁.toList.drop
          (if pathOfSegs pos == "/" then "/" else pathOfSegs pos ++ "/").toList.length)) = true
      · simp only [hV1, ↓reduceDIte, Option.some.injEq] at h1
        by_cases hN2 : (st.nodes k₂).isSome = true
        · simp only [hN2, ↓reduceIte] at h2
          by_cases hP2 : (k₂ != pathOfSegs pos &&
              (if pathOfSegs pos == "/" then "/" else pathOfSegs pos ++ "/").toList.isPrefixOf k₂.toList) = true
          · simp only [hP2, ↓reduceIte] at h2
            by_cases hV2 : validSeg (String.ofList (k₂.toList.drop
                (if pathOfSegs pos == "/" then "/" else pathOfSegs pos ++ "/").toList.length)) = true
            · simp only [hV2, ↓reduceDIte, Option.some.injEq] at h2
              have hPref1 := List.isPrefixOf_iff_prefix.mp ((Bool.and_eq_true _ _).mp hP1).2
              have hPref2 := List.isPrefixOf_iff_prefix.mp ((Bool.and_eq_true _ _).mp hP2).2
              rcases hPref1 with ⟨t1, ht1⟩
              rcases hPref2 with ⟨t2, ht2⟩
              have hVal : String.ofList (k₁.toList.drop _) = String.ofList (k₂.toList.drop _) :=
                congrArg EntryName.val (h1.trans h2.symm)
              have hDrop := congrArg String.toList hVal
              simp only [String.toList_ofList] at hDrop
              rw [← ht1, ← ht2, List.drop_left, List.drop_left] at hDrop
              apply String.ext_iff.mpr
              rw [← ht1, ← ht2, hDrop]
            · simp only [hV2] at h2; cases h2
          · simp only [hP2, Bool.false_eq_true, ↓reduceIte] at h2; cases h2
        · simp only [hN2, Bool.false_eq_true, ↓reduceIte] at h2; cases h2
      · simp only [hV1] at h1; cases h1
    · simp only [hP1, Bool.false_eq_true, ↓reduceIte] at h1; cases h1
  · simp only [hN1, Bool.false_eq_true, ↓reduceIte] at h1; cases h1

/-- Every entry produced by `mVfsReadDirAtEntries st pos` exists as a live node at `pos ++ [e.val]` in `st.tree`. -/
theorem mVfsReadDirAtEntries_mem_sound (st : VfsState) (pos : List String)
    (hPos : ∀ s ∈ pos, validSeg s = true) (e : EntryName)
    (hMem : e ∈ (mVfsReadDirAtEntries st pos).toList) :
    nodeAt st.tree (pos ++ [e.val]) ≠ none := by
  unfold mVfsReadDirAtEntries at hMem
  dsimp only at hMem
  simp only [List.mem_filterMap] at hMem
  rcases hMem with ⟨k, _, hk⟩
  by_cases hIsSome : (st.nodes k).isSome = true
  · simp only [hIsSome, ↓reduceIte] at hk
    by_cases hCond : (k != pathOfSegs pos &&
        (if pathOfSegs pos == "/" then "/" else pathOfSegs pos ++ "/").toList.isPrefixOf k.toList) = true
    · simp only [hCond, ↓reduceIte] at hk
      by_cases hVal : validSeg (String.ofList (k.toList.drop
          (if pathOfSegs pos == "/" then "/" else pathOfSegs pos ++ "/").toList.length)) = true
      · simp only [hVal, ↓reduceDIte, Option.some.injEq] at hk
        have hPref := List.isPrefixOf_iff_prefix.mp ((Bool.and_eq_true _ _).mp hCond).2
        rcases hPref with ⟨tail, hTail⟩
        have hValEq : String.ofList (k.toList.drop _) = e.val := congrArg EntryName.val hk
        have hTailEq : tail = e.val.toList := by
          have ht := congrArg String.toList hValEq
          simp only [String.toList_ofList] at ht
          rw [← hTail, List.drop_left] at ht
          exact ht
        have hkEq : k = pathOfSegs (pos ++ [e.val]) := by
          apply String.ext_iff.mpr
          rw [← hTail, hTailEq]
          exact (pathOfSegs_snoc_toList pos e.val hPos).symm
        have hAllValid : ∀ s ∈ pos ++ [e.val], validSeg s = true := by
          intro s hs
          simp only [List.mem_append, List.mem_singleton] at hs
          rcases hs with hs | rfl
          · exact hPos s hs
          · exact e.valid
        have hCanon := isCanonPath_pathOfSegs (pos ++ [e.val]) hAllValid
        have hSp := vfsSplitSegs_pathOfSegs (pos ++ [e.val]) hAllValid
        rw [hkEq] at hIsSome
        intro hNone
        have hN : st.nodes (pathOfSegs (pos ++ [e.val])) = none := by
          simp [VfsState.nodes, vfsTreeNodes, hCanon, hSp, hNone]
        simp [hN] at hIsSome
      · simp only [hVal] at hk; cases hk
    · simp only [hCond, Bool.false_eq_true, ↓reduceIte] at hk; cases hk
  · simp only [hIsSome, Bool.false_eq_true, ↓reduceIte] at hk; cases hk

/-- Under `VfsKeysComplete`, every live entry `pos ++ [e.val]` appears in `mVfsReadDirAtEntries st pos`. -/
theorem mVfsReadDirAtEntries_mem_complete (st : VfsState) (pos : List String)
    (hComp : VfsKeysComplete st) (hPos : ∀ s ∈ pos, validSeg s = true) (e : EntryName)
    (hLive : nodeAt st.tree (pos ++ [e.val]) ≠ none) :
    e ∈ (mVfsReadDirAtEntries st pos).toList := by
  let k := pathOfSegs (pos ++ [e.val])
  have hInKeys : k ∈ st.keys := hComp (pos ++ [e.val]) hLive
  have hAllValid : ∀ s ∈ pos ++ [e.val], validSeg s = true := by
    intro s hs
    simp only [List.mem_append, List.mem_singleton] at hs
    rcases hs with hs | rfl
    · exact hPos s hs
    · exact e.valid
  have hCanon := isCanonPath_pathOfSegs (pos ++ [e.val]) hAllValid
  have hSp := vfsSplitSegs_pathOfSegs (pos ++ [e.val]) hAllValid
  have hNodeSome : (st.nodes k).isSome = true := by
    have hNodesEq : st.nodes k = nodeAt st.tree (pos ++ [e.val]) := by
      simp [VfsState.nodes, vfsTreeNodes, hCanon, hSp, k]
    rw [hNodesEq]
    cases hNa : nodeAt st.tree (pos ++ [e.val]) with
    | none => exact absurd hNa hLive
    | some _ => rfl
  have hSnoc := pathOfSegs_snoc_toList pos e.val hPos
  have hkNe : k ≠ pathOfSegs pos := by
    intro hEq
    have hLen := congrArg (·.toList.length) hEq
    rw [hSnoc, List.length_append] at hLen
    have hValLen : 0 < e.val.toList.length := by
      have hv := (validSeg_charProps e.val e.valid).1
      cases he : e.val.toList <;> simp_all
    split at hLen
    · next he =>
      have : (pathOfSegs pos).toList.length = 1 := by simp [beq_iff_eq.mp he, show "/".toList = ['/'] by decide]
      simp [show "/".toList = ['/'] by decide] at hLen; omega
    · simp only [String.toList_append, List.length_append, show "/".toList = ['/'] by decide,
        List.length_cons, List.length_nil] at hLen
      omega
  unfold mVfsReadDirAtEntries
  dsimp only
  simp only [List.mem_filterMap]
  refine ⟨k, mem_eraseDups_iff.mpr hInKeys, ?_⟩
  have hBne : (k != pathOfSegs pos) = true := bne_iff_ne.mpr hkNe
  have hPref : ((if pathOfSegs pos == "/" then "/" else pathOfSegs pos ++ "/").toList.isPrefixOf k.toList) = true := by
    rw [hSnoc]
    exact List.isPrefixOf_iff_prefix.mpr ⟨e.val.toList, rfl⟩
  have hDrop : String.ofList (k.toList.drop (if pathOfSegs pos == "/" then "/" else pathOfSegs pos ++ "/").toList.length) = e.val := by
    rw [hSnoc, List.drop_left, String.ofList_toList]
  simp only [hNodeSome, ↓reduceIte, hBne, hPref, Bool.and_self]
  simp only [hDrop, e.valid, ↓reduceDIte]

/-- For any canonical path `k`, `pathOfSegs (vfsSplitSegs k) = k`. -/
theorem pathOfSegs_vfsSplitSegs {k : String} (hK : isCanonPath k = true) :
    pathOfSegs (vfsSplitSegs k) = k := by
  simp only [isCanonPath, Bool.and_eq_true, beq_iff_eq] at hK
  rcases hK with ⟨hAbs, hNorm⟩
  have hElem := collapseChars_elems_valid true (Internal.splitCharList '/' k.toList) []
    (fun _ h => by simp at h) (splitCharList_no_sep '/' k.toList)
  have hKEq : k = String.ofList ('/' :: Internal.joinSlashChars
      (Internal.collapseChars true (Internal.splitCharList '/' k.toList) [])) := by
    calc k = Internal.normPath k := (model_normPath_eq_internal k ▸ hNorm).symm
      _ = _ := by simp [Internal.normPath, show Internal.isAbsChars k.toList = true from hAbs]
  have hSp : vfsSplitSegs k =
      (Internal.collapseChars true (Internal.splitCharList '/' k.toList) []).map String.ofList := by
    calc vfsSplitSegs k
        = vfsSplitSegs (String.ofList ('/' :: Internal.joinSlashChars
            (Internal.collapseChars true (Internal.splitCharList '/' k.toList) []))) := congrArg vfsSplitSegs hKEq
      _ = _ := vfsSplitSegs_joinSlashChars_valid _ (fun s hs => ⟨(hElem s hs).1, (hElem s hs).2.2⟩)
  rw [hSp, pathOfSegs_eq_ofList_joinSlashChars, List.map_map]
  simp [Function.comp_def, hKEq.symm]

/-- A directory with no live descendants in `st.tree` has `mDirHasLiveChild st pos = false`. -/
theorem mDirHasLiveChild_false_of_treeEmpty (st : VfsState) (pos : List String)
    (hPos : ∀ s ∈ pos, validSeg s = true)
    (hEmpty : ∀ rest : List String, rest ≠ [] → nodeAt st.tree (pos ++ rest) = none) :
    mDirHasLiveChild st pos = false := by
  unfold mDirHasLiveChild
  dsimp only
  refine List.any_eq_false.mpr ?_
  intro k _
  by_cases hAll : ((st.nodes k).isSome && k != pathOfSegs pos &&
      (if pathOfSegs pos == "/" then "/" else pathOfSegs pos ++ "/").toList.isPrefixOf k.toList) = true
  · exfalso
    have h1 := (Bool.and_eq_true _ _).mp hAll
    have h2 := (Bool.and_eq_true _ _).mp h1.1
    have hNode := h2.1
    have hKNe : k ≠ pathOfSegs pos := bne_iff_ne.mp h2.2
    have hPref := List.isPrefixOf_iff_prefix.mp h1.2
    rcases hPref with ⟨tail, hTail⟩
    have hKCanon : isCanonPath k = true := by
      cases hc : isCanonPath k with
      | true => rfl
      | false => simp [VfsState.nodes, vfsTreeNodes, hc] at hNode
    have hPosSplit : vfsSplitSegs (pathOfSegs pos) = pos := vfsSplitSegs_pathOfSegs pos hPos
    have hPrePos : pos <+: vfsSplitSegs k := by
      cases pos with
      | nil => exact List.nil_prefix
      | cons a rest =>
        have hNeRoot : pathOfSegs (a :: rest) ≠ "/" := by
          intro hEq
          have h1 : vfsSplitSegs "/" = [] := by decide
          rw [hEq, h1] at hPosSplit
          cases hPosSplit
        rw [beq_false_of_ne hNeRoot] at hTail
        simp only [Bool.false_eq_true, ↓reduceIte, pathOfSegs_eq_ofList_joinSlashChars,
          String.toList_append, String.toList_ofList, show "/".toList = ['/'] by decide,
          List.append_assoc, List.singleton_append] at hTail
        simp only [vfsSplitSegs, ← hTail, List.cons_append, model_splitCharList_eq_internal]
        have hParts : ∀ s ∈ ((a :: rest).map String.toList), !s.isEmpty ∧ '/' ∉ s := by
          intro s hs
          simp only [List.mem_map] at hs
          rcases hs with ⟨w, hw, rfl⟩
          have hv := validSeg_charProps w (hPos w hw)
          exact ⟨hv.1, hv.2.2.1⟩
        rw [splitCharList_joinSlashChars_append ((a :: rest).map String.toList) (by simp) (fun s hs => (hParts s hs).2) tail]
        rw [List.filterMap_append]
        have hMap : ∀ xs : List (List Char), (∀ s ∈ xs, !s.isEmpty) →
            List.filterMap (fun cs => if cs.isEmpty then none else some (String.ofList cs)) xs = xs.map String.ofList := by
          intro xs hxs
          induction xs with
          | nil => rfl
          | cons x xt ihx =>
            rcases x with _ | ⟨c, cs⟩
            · have := hxs [] (by simp); simp at this
            · have hTl := ihx (fun y hy => hxs y (by simp [hy]))
              simpa using congrArg (String.ofList (c :: cs) :: ·) hTl
        rw [hMap _ (fun s hs => (hParts s hs).1), List.map_map, Function.comp_def]
        simp only [String.ofList_toList, List.map_id']
        exact List.prefix_append _ _
    rcases hPrePos with ⟨rest, hSpEq⟩
    have hRestNe : rest ≠ [] := by
      intro hEmptyRest
      rw [hEmptyRest, List.append_nil] at hSpEq
      have hPath : pathOfSegs (vfsSplitSegs k) = pathOfSegs pos := congrArg pathOfSegs hSpEq.symm
      have hKIsPath : pathOfSegs (vfsSplitSegs k) = k := pathOfSegs_vfsSplitSegs hKCanon
      exact hKNe (hKIsPath.symm.trans hPath)
    have hNone := hEmpty rest hRestNe
    rw [hSpEq] at hNone
    have hN : st.nodes k = none := by simp [VfsState.nodes, vfsTreeNodes, hKCanon, hNone]
    simp [hN] at hNode
  · exact hAll

/-- `vfsTreeGet t pos = some (.dir m ch)` with `∀ x, ch x = none` has no live descendants. -/
theorem nodeAt_dir_empty_none_desc (t : VfsTree) (pos : List String) (m : Nat)
    (ch : String → Option VfsTree) (hDir : vfsTreeGet t pos = some (.dir m ch))
    (hEmpty : ∀ x, ch x = none) :
    ∀ rest : List String, rest ≠ [] → nodeAt t (pos ++ rest) = none := by
  intro rest hNe
  cases rest with
  | nil => exact absurd rfl hNe
  | cons x xs =>
    have hGet : vfsTreeGet t (pos ++ (x :: xs)) = none := by
      have : ∀ (t : VfsTree) (p : List String), vfsTreeGet t p = some (.dir m ch) →
          vfsTreeGet t (p ++ (x :: xs)) = none := by
        intro t p hp
        induction p generalizing t with
        | nil =>
          cases t with
          | file _ _ | symlink _ _ => simp [vfsTreeGet] at hp
          | dir _ ch' =>
            simp only [vfsTreeGet] at hp
            cases hp
            simp [vfsTreeGet, hEmpty x]
        | cons b bs ih =>
          cases t with
          | file _ _ | symlink _ _ => simp [vfsTreeGet] at hp
          | dir _ ch' =>
            simp only [vfsTreeGet] at hp
            cases hcb : ch' b with
            | none => simp [hcb] at hp
            | some sub =>
              simp only [hcb] at hp
              simp [vfsTreeGet, hcb, ih sub hp]
      exact this t pos hDir
    simp [nodeAt, hGet]

/-- Sorting a duplicate-free list of `EntryName` yields strictly increasing `val` order. -/
theorem list_mergeSort_entryName_strict {xs : List EntryName} (hNodup : xs.Nodup) :
    List.Pairwise (fun a b => a.val < b.val) (xs.mergeSort (fun a b => decide (a.val ≤ b.val))) := by
  have hPerm : (xs.mergeSort (fun a b => decide (a.val ≤ b.val))).Perm xs :=
    List.mergeSort_perm xs (fun a b => decide (a.val ≤ b.val))
  have hNdSorted : (xs.mergeSort (fun a b => decide (a.val ≤ b.val))).Nodup :=
    hPerm.nodup_iff.mpr hNodup
  have hLe : List.Pairwise (fun a b => (decide (a.val ≤ b.val)) = true)
      (xs.mergeSort (fun a b => decide (a.val ≤ b.val))) := by
    refine List.pairwise_mergeSort (le := fun a b : EntryName => decide (a.val ≤ b.val)) ?_ ?_ xs
    · intro a b c hab hbc
      simp only [decide_eq_true_eq] at hab hbc ⊢
      exact Std.le_trans hab hbc
    · intro a b
      simp only [Bool.or_eq_true, decide_eq_true_eq]
      exact Std.le_total
  have hPairImp : ∀ {l : List EntryName},
      List.Pairwise (fun a b => (decide (a.val ≤ b.val)) = true) l → l.Nodup →
      List.Pairwise (fun a b => a.val < b.val) l := by
    intro l hp hn
    induction l with
    | nil => exact List.Pairwise.nil
    | cons a tl ih =>
      rw [List.pairwise_cons] at hp
      rw [List.nodup_cons] at hn
      refine List.pairwise_cons.mpr ⟨?_, ih hp.2 hn.2⟩
      intro b hb
      have hLeAB : a.val ≤ b.val := of_decide_eq_true (hp.1 b hb)
      have hNeAB : a ≠ b := fun heq => hn.1 (heq ▸ hb)
      have hNeVal : a.val ≠ b.val := fun heq => hNeAB (by cases a; cases b; simp at heq; subst heq; rfl)
      exact Classical.byContradiction fun hNot => hNeVal (Std.le_antisymm hLeAB (Std.not_lt.mp hNot))
  exact hPairImp hLe hNdSorted

end LeanSwe.Fs.Proofs
