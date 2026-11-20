import LeanSwe.LinuxSyscall.Files.Model

namespace LeanSwe.LinuxSyscall.Files

@[simp] private theorem byteGetD_eq_data_getD (b : ByteArray) (i : Nat) :
    byteGetD b i = b.data.getD i 0 := rfl

private theorem replicateZeroBytesLoop_size (n : Nat) (acc : ByteArray) :
    (replicateZeroBytesLoop n acc).data.size = acc.data.size + n := by
  induction n generalizing acc with
  | zero => simp [replicateZeroBytesLoop]
  | succ k ih =>
    simp only [replicateZeroBytesLoop, ih, ByteArray.push, Array.size_push]
    omega

@[simp] private theorem replicateZeroBytes_data_size (n : Nat) :
    (replicateZeroBytes n).data.size = n := by
  unfold replicateZeroBytes ByteArray.emptyWithCapacity
  rw [replicateZeroBytesLoop_size]
  exact Nat.zero_add n

@[simp] private theorem replicateZeroBytes_size (n : Nat) :
    (replicateZeroBytes n).size = n :=
  replicateZeroBytes_data_size n

@[simp] private theorem sliceBytes_data (b : ByteArray) (start len : Nat) :
    (sliceBytes b start len).data = b.data.extract start (min b.data.size (start + len)) := by
  unfold sliceBytes
  by_cases hFull : (start == 0 && decide (len ≥ b.size)) = true
  · simp only [hFull, ↓reduceIte]
    have h0 : start = 0 := by cases h : (start == 0) <;> simp_all
    have hGe : len ≥ b.data.size := by
      change (start == 0 && decide (len ≥ b.data.size)) = true at hFull
      simp [h0] at hFull
      exact hFull
    subst h0
    have hMin : min b.data.size (0 + len) = b.data.size := by omega
    rw [hMin]
    exact (Array.extract_size (xs := b.data)).symm
  · simp only [hFull, Bool.false_eq_true, ↓reduceIte]
    exact ByteArray.data_extract

private theorem bytesEqLoop_iff (a b : ByteArray) (hSz : a.data.size = b.data.size) :
    ∀ rem i, i + rem = a.data.size →
      (bytesEqLoop a b i rem = true ↔ ∀ j, i ≤ j → j < a.data.size → a.data.getD j 0 = b.data.getD j 0)
  | 0, _, _ => by
    simp only [bytesEqLoop, true_iff]
    intro _ _ _; omega
  | rem + 1, i, hSum => by
    unfold bytesEqLoop
    rw [byteGetD_eq_data_getD, byteGetD_eq_data_getD]
    by_cases hEq : (a.data.getD i 0 == b.data.getD i 0) = true
    · simp only [hEq, ↓reduceIte]
      rw [bytesEqLoop_iff a b hSz rem (i + 1) (by omega)]
      have hAiBi : a.data.getD i 0 = b.data.getD i 0 := beq_iff_eq.mp hEq
      constructor
      · intro hRest j hGe hLt
        by_cases hJi : j = i
        · subst hJi; exact hAiBi
        · exact hRest j (by omega) hLt
      · intro hAll j hGe hLt
        exact hAll j (by omega) hLt
    · simp only [hEq, Bool.false_eq_true, ↓reduceIte, false_iff]
      intro hAll
      exact hEq (beq_iff_eq.mpr (hAll i (Nat.le_refl i) (by omega)))

@[simp] private theorem bytesEq_eq_data_beq (a b : ByteArray) :
    bytesEq a b = (a.data == b.data) := by
  unfold bytesEq
  by_cases hSz : a.data.size = b.data.size
  · have hSzB : (a.size == b.size) = true := beq_iff_eq.mpr hSz
    rw [hSzB, Bool.true_and]
    apply Bool.eq_iff_iff.mpr
    rw [bytesEqLoop_iff a b hSz a.size 0 (Nat.zero_add _), beq_iff_eq]
    constructor
    · intro hAll
      apply Array.ext hSz
      intro j hjA hjB
      have h := hAll j (Nat.zero_le j) hjA
      simp only [Array.getD, hjA, hjB, ↓reduceDIte] at h
      exact h
    · intro hEq _ _ _
      rw [hEq]
  · have hSzB : (a.size == b.size) = false := beq_false_of_ne hSz
    rw [hSzB, Bool.false_and]
    symm
    rw [beq_eq_false_iff_ne]
    intro hEq
    exact hSz (congrArg Array.size hEq)

private theorem statInfo_beq_refl (st : StatInfo) : (st == st) = true := by
  rcases st with ⟨k, s, m, i, d, n, mt, mn, at_, an⟩
  cases k <;> simp [BEq.beq, instBEqStatInfo.beq, instBEqFileKind.beq]

private theorem outcomeEq_refl (o : FilesOutcome) : outcomeEq o o = true := by
  cases o with
  | unit => rfl
  | opened _ => simp [outcomeEq]
  | bytes b => simp [outcomeEq]
  | u32 _ => simp [outcomeEq]
  | u64 _ => simp [outcomeEq]
  | statted st => simp [outcomeEq, statInfo_beq_refl]
  | err _ => simp [outcomeEq]

private theorem sliceBytes_full (b : ByteArray) (off want : Nat)
    (hLt : off < b.data.size) (hLe : want ≤ b.data.size - off) :
    (sliceBytes b off want).data.size = want := by
  rw [sliceBytes_data]
  simp only [Array.size_extract]
  omega

private theorem pipePushSlotsRev_ge_written (revSlots : List (Nat × Nat)) (free rem written : Nat) :
    written ≤ (pipePushSlotsRev revSlots free rem written).2 := by
  induction free generalizing revSlots rem written with
  | zero => simp [pipePushSlotsRev]
  | succ f ih =>
    cases rem with
    | zero => simp [pipePushSlotsRev]
    | succ r =>
      rw [pipePushSlotsRev.eq_3 _ _ _ _ (by omega)]
      exact Nat.le_trans (Nat.le_add_right _ _) (ih _ _ _)

private theorem pipePushSlots_ge_written (slots : List (Nat × Nat)) (free rem written : Nat) :
    written ≤ (pipePushSlots slots free rem written).2 :=
  pipePushSlotsRev_ge_written slots.reverse free rem written

private theorem pipePushSlotsRev_mono (revSlots : List (Nat × Nat)) (f1 f2 rem written : Nat)
    (hLe : f1 ≤ f2) :
    (pipePushSlotsRev revSlots f1 rem written).2 ≤ (pipePushSlotsRev revSlots f2 rem written).2 := by
  induction f1 generalizing revSlots f2 rem written with
  | zero =>
    rw [pipePushSlotsRev.eq_1]
    exact pipePushSlotsRev_ge_written _ _ _ _
  | succ f1 ih =>
    cases f2 with
    | zero => omega
    | succ f2 =>
      cases rem with
      | zero => simp [pipePushSlotsRev]
      | succ r =>
        rw [pipePushSlotsRev.eq_3 _ _ _ _ (by omega), pipePushSlotsRev.eq_3 _ _ _ _ (by omega)]
        exact ih _ _ _ _ (by omega)

private theorem pipePushSlots_mono (slots : List (Nat × Nat)) (f1 f2 rem written : Nat)
    (hLe : f1 ≤ f2) :
    (pipePushSlots slots f1 rem written).2 ≤ (pipePushSlots slots f2 rem written).2 :=
  pipePushSlotsRev_mono slots.reverse f1 f2 rem written hLe

private theorem pipePushSlots_zero_imp (slots : List (Nat × Nat)) (free rem : Nat)
    (hRem : rem > 0) (hz : (pipePushSlots slots free rem 0).2 = 0) :
    free = 0 := by
  cases free with
  | zero => rfl
  | succ f =>
    cases rem with
    | zero => omega
    | succ r =>
      unfold pipePushSlots at hz
      rw [pipePushSlotsRev.eq_3 _ _ _ _ (by omega)] at hz
      have hGe := pipePushSlotsRev_ge_written
        ((min (r + 1) 4096, min (r + 1) 4096) :: slots.reverse)
        f (r + 1 - min (r + 1) 4096) (0 + min (r + 1) 4096)
      omega

private theorem pipeWriteSlots_mono (slots : List (Nat × Nat)) (m1 m2 len : Nat)
    (hLe : m1 ≤ m2) :
    (pipeWriteSlots slots m1 len).2 ≤ (pipeWriteSlots slots m2 len).2 := by
  unfold pipeWriteSlots
  split
  · exact Nat.le_refl 0
  · exact pipePushSlots_mono _ _ _ _ _ (by omega)

private theorem pipeWriteSlots_zero_imp (slots : List (Nat × Nat)) (capPages totalLen : Nat)
    (hLen : totalLen > 0) (hz : (pipeWriteSlots slots capPages totalLen).2 = 0) :
    max 1 capPages ≤ slots.length ∧ (pipeWriteSlots slots slots.length totalLen).2 = 0 := by
  unfold pipeWriteSlots at hz ⊢
  have hNe : (totalLen == 0) = false := beq_false_of_ne (by omega)
  simp only [hNe, Bool.false_eq_true, ↓reduceIte] at hz ⊢
  by_cases hChars : totalLen % 4096 > 0
  · simp only [hChars, ↓reduceIte] at hz ⊢
    cases hRev : slots.reverse with
    | nil =>
      rw [hRev] at hz
      dsimp only at hz ⊢
      have hFree := pipePushSlots_zero_imp slots (max 1 capPages - slots.length) totalLen hLen hz
      have hMax : max 1 capPages ≤ slots.length := by omega
      refine ⟨hMax, ?_⟩
      have hEq0 : max 1 slots.length - slots.length = 0 := by omega
      rw [hEq0]
      simp [pipePushSlots, pipePushSlotsRev]
    | cons hd tl =>
      cases hd with
      | mk tTail tLen =>
        rw [hRev] at hz
        dsimp only at hz ⊢
        by_cases hFit : tTail + totalLen % 4096 ≤ 4096
        · simp only [hFit, ↓reduceIte] at hz
          have hGe := pipePushSlots_ge_written
            (tl.reverse ++ [(tTail + totalLen % 4096, tLen + totalLen % 4096)])
            (max 1 capPages - (tl.reverse ++ [(tTail + totalLen % 4096, tLen + totalLen % 4096)]).length)
            (totalLen - totalLen % 4096) (totalLen % 4096)
          omega
        · simp only [hFit, ↓reduceIte] at hz ⊢
          have hFree := pipePushSlots_zero_imp slots (max 1 capPages - slots.length) totalLen hLen hz
          have hMax : max 1 capPages ≤ slots.length := by omega
          refine ⟨hMax, ?_⟩
          have hEq0 : max 1 slots.length - slots.length = 0 := by omega
          rw [hEq0]
          simp [pipePushSlots, pipePushSlotsRev]
  · simp only [hChars, ↓reduceIte] at hz ⊢
    have hFree := pipePushSlots_zero_imp slots (max 1 capPages - slots.length) totalLen hLen hz
    have hMax : max 1 capPages ≤ slots.length := by omega
    refine ⟨hMax, ?_⟩
    have hEq0 : max 1 slots.length - slots.length = 0 := by omega
    rw [hEq0]
    simp [pipePushSlots, pipePushSlotsRev]

private theorem pipeCap_min_le_max (c : PipeCapacity) : c.minPages ≤ c.maxPages := by
  cases c with
  | exact p => simp [PipeCapacity.minPages, PipeCapacity.maxPages]
  | uncalibrated lo hi =>
    simp [PipeCapacity.minPages, PipeCapacity.maxPages]
    omega

private theorem dirent64Reclen_bounds (nm : ByteArray) :
    dirent64Reclen nm ≥ 24 ∧ dirent64Reclen nm % 8 = 0 ∧
    19 + nm.data.size + 1 ≤ dirent64Reclen nm := by
  cases nm
  unfold dirent64Reclen ByteArray.size
  dsimp only
  omega

private theorem mkDirentEntryLoop_size (nm : ByteArray) (dType lo hi : UInt8)
    (dIno dOff : UInt64) (rem : Nat) :
    ∀ (i : Nat) (acc : ByteArray),
      (mkDirentEntryLoop nm dType lo hi dIno dOff i rem acc).data.size = acc.data.size + rem := by
  induction rem with
  | zero => simp [mkDirentEntryLoop]
  | succ k ih =>
    intro i acc
    simp only [mkDirentEntryLoop, ih, ByteArray.push, Array.size_push]
    omega

private theorem mkDirentEntry_size (nm : ByteArray) (dt : UInt8) (ino : UInt64) :
    (mkDirentEntry nm dt ino).data.size = dirent64Reclen nm := by
  unfold mkDirentEntry ByteArray.emptyWithCapacity
  rw [mkDirentEntryLoop_size]
  exact Nat.zero_add _

private theorem paintExtentLoop_size (pos eStart : Nat) (eData : ByteArray)
    (rem i : Nat) (buf : ByteArray) :
    (paintExtentLoop pos eStart eData rem i buf).data.size = buf.data.size := by
  induction rem generalizing i buf with
  | zero => rfl
  | succ rem ih =>
    simp only [paintExtentLoop]
    rw [ih]
    simp [ByteArray.set!]

private theorem foldl_paintExtent_size (pos rEnd : Nat) (xs : List (Nat × ByteArray))
    (buf : ByteArray) :
    (xs.foldl (fun b (eStart, eData) =>
      let eEnd := eStart + eData.size
      let ovStart := max pos eStart
      let ovEnd := min rEnd eEnd
      if ovStart < ovEnd then paintExtentLoop pos eStart eData (ovEnd - ovStart) ovStart b
      else b) buf).data.size = buf.data.size := by
  induction xs generalizing buf with
  | nil => rfl
  | cons hd tl ih =>
    rcases hd with ⟨eStart, eData⟩
    simp only [List.foldl_cons]
    rw [ih]
    split
    · exact paintExtentLoop_size _ _ _ _ _ _
    · rfl

private theorem regData_readSlice_size (rd : RegData) (pos len : Nat) :
    (rd.readSlice pos len).data.size = min len (if pos < rd.size then rd.size - pos else 0) := by
  unfold RegData.readSlice
  dsimp only
  by_cases hZ : min len (if pos < rd.size then rd.size - pos else 0) = 0
  · simp only [hZ]
    rfl
  · have hZBool : (min len (if pos < rd.size then rd.size - pos else 0) == 0) = false := beq_false_of_ne hZ
    simp only [hZBool, Bool.false_eq_true, ↓reduceIte]
    rw [foldl_paintExtent_size, replicateZeroBytes_data_size]

private def mkTypedDirentStubArr (entries : List (ByteArray × UInt8 × UInt64)) : Array UInt8 :=
  (mkTypedDirentStub entries).data

private theorem byteArray_empty_data : ByteArray.empty.data = #[] := rfl

private theorem byteArray_emptyCap_data (n : Nat) : (ByteArray.emptyWithCapacity n).data = #[] := rfl

private theorem byteArray_push_data (a : ByteArray) (b : UInt8) : (a.push b).data = a.data ++ #[b] := by
  show a.data.push b = a.data ++ #[b]
  exact Array.push_eq_append

private theorem mkDirentEntryLoop_data (nm : ByteArray) (dType lo hi : UInt8)
    (dIno dOff : UInt64) (rem : Nat) :
    ∀ (i : Nat) (acc : ByteArray),
      (mkDirentEntryLoop nm dType lo hi dIno dOff i rem acc).data =
        acc.data ++ (mkDirentEntryLoop nm dType lo hi dIno dOff i rem ByteArray.empty).data := by
  induction rem with
  | zero =>
    intro i acc
    unfold mkDirentEntryLoop
    rw [byteArray_empty_data, Array.append_empty]
  | succ k ih =>
    intro i acc
    unfold mkDirentEntryLoop
    rw [ih (i + 1) (acc.push _), ih (i + 1) (ByteArray.empty.push _),
      byteArray_push_data, byteArray_push_data, byteArray_empty_data,
      Array.empty_append, Array.append_assoc]

private theorem mkDirentEntryLoop_eq_mkDirentEntry (nm : ByteArray) (dt : UInt8) (ino : UInt64)
    (acc : ByteArray) :
    (mkDirentEntryLoop nm dt (UInt8.ofNat (dirent64Reclen nm % 256))
      (UInt8.ofNat ((dirent64Reclen nm / 256) % 256)) ino 1 0 (dirent64Reclen nm) acc).data =
    acc.data ++ (mkDirentEntry nm dt ino).data := by
  unfold mkDirentEntry
  dsimp only
  rw [mkDirentEntryLoop_data,
    mkDirentEntryLoop_data nm dt _ _ ino 1 (dirent64Reclen nm) 0 (ByteArray.emptyWithCapacity _),
    byteArray_emptyCap_data, Array.empty_append]

private theorem mkTypedDirentStubAux_data (xs : List (ByteArray × UInt8 × UInt64)) :
    ∀ (acc : ByteArray),
      (mkTypedDirentStubAux acc xs).data = acc.data ++ (mkTypedDirentStubAux ByteArray.empty xs).data := by
  induction xs with
  | nil =>
    intro acc
    unfold mkTypedDirentStubAux
    rw [byteArray_empty_data, Array.append_empty]
  | cons x xs ih =>
    rcases x with ⟨nm, dt, ino⟩
    intro acc
    let rl := dirent64Reclen nm
    let lo := UInt8.ofNat (rl % 256)
    let hi := UInt8.ofNat ((rl / 256) % 256)
    rw [mkTypedDirentStubAux.eq_2, mkTypedDirentStubAux.eq_2,
      ih (mkDirentEntryLoop nm dt lo hi ino 1 0 rl acc),
      ih (mkDirentEntryLoop nm dt lo hi ino 1 0 rl ByteArray.empty),
      mkDirentEntryLoop_eq_mkDirentEntry, mkDirentEntryLoop_eq_mkDirentEntry,
      byteArray_empty_data, Array.empty_append, Array.append_assoc]

private theorem mkTypedDirentStubArr_eq_empty (xs : List (ByteArray × UInt8 × UInt64)) :
    mkTypedDirentStubArr xs = (mkTypedDirentStubAux ByteArray.empty xs).data := by
  unfold mkTypedDirentStubArr mkTypedDirentStub
  rw [mkTypedDirentStubAux_data, byteArray_emptyCap_data, Array.empty_append]

@[simp] private theorem mkTypedDirentStubArr_nil :
    mkTypedDirentStubArr [] = #[] := rfl

private theorem mkTypedDirentStubArr_cons (nm : ByteArray) (dt : UInt8) (ino : UInt64)
    (xs : List (ByteArray × UInt8 × UInt64)) :
    mkTypedDirentStubArr ((nm, dt, ino) :: xs) =
      (mkDirentEntry nm dt ino).data ++ mkTypedDirentStubArr xs := by
  rw [mkTypedDirentStubArr_eq_empty, mkTypedDirentStubArr_eq_empty, mkTypedDirentStubAux.eq_2,
    mkTypedDirentStubAux_data, mkDirentEntryLoop_eq_mkDirentEntry,
    byteArray_empty_data, Array.empty_append]

private theorem mkTypedDirentStubArr_append (xs ys : List (ByteArray × UInt8 × UInt64)) :
    mkTypedDirentStubArr (xs ++ ys) = mkTypedDirentStubArr xs ++ mkTypedDirentStubArr ys := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    rcases x with ⟨nm, dt, ino⟩
    rw [List.cons_append, mkTypedDirentStubArr_cons, mkTypedDirentStubArr_cons, ih, Array.append_assoc]

private theorem mkTypedDirentStubArr_size_ge (xs : List (ByteArray × UInt8 × UInt64))
    (hPos : xs.length ≥ 1) :
    (mkTypedDirentStubArr xs).size ≥ 24 * xs.length := by
  induction xs with
  | nil => simp at hPos
  | cons x xs ih =>
    rcases x with ⟨nm, dt, ino⟩
    have hGe := (dirent64Reclen_bounds nm).1
    have hSz := mkDirentEntry_size nm dt ino
    cases xs with
    | nil =>
      rw [mkTypedDirentStubArr_cons]
      have hNil : mkTypedDirentStubArr [] = #[] := rfl
      rw [hNil, Array.append_empty, hSz]
      simp; omega
    | cons y ys =>
      have hTail := ih (by simp)
      rw [mkTypedDirentStubArr_cons, Array.size_append, hSz]
      simp at hTail ⊢
      omega

private theorem packFittingDirentsGen_go_nonempty {α : Type} (nameOf : α → ByteArray)
    (cap : Nat) (xs acc : List α) (used : Nat)
    (hNonempty : acc ≠ [] ∨ ∃ x xs', xs = x :: xs' ∧ used + dirent64Reclen (nameOf x) ≤ cap) :
    (packFittingDirentsGen.go nameOf cap xs used acc).length ≥ 1 := by
  induction xs generalizing used acc with
  | nil =>
    rcases hNonempty with hAcc | ⟨x, xs', hEq, _⟩
    · rw [packFittingDirentsGen.go.eq_1]
      cases acc with
      | nil => contradiction
      | cons _ _ => simp
    · cases hEq
  | cons nm rest ih =>
    rw [packFittingDirentsGen.go.eq_2]
    split
    · exact ih (nm :: acc) (used + dirent64Reclen (nameOf nm)) (Or.inl (List.cons_ne_nil _ _))
    · rename_i hGt
      rcases hNonempty with hAcc | ⟨x, xs', hEq, hFit⟩
      · cases acc with
        | nil => contradiction
        | cons _ _ => simp
      · cases hEq
        omega

private theorem packFittingDirentsGen_go_map {α β : Type} (f : α → β)
    (nameA : α → ByteArray) (nameB : β → ByteArray)
    (hName : ∀ x, nameB (f x) = nameA x)
    (cap : Nat) (xs acc : List α) (used : Nat) :
    (packFittingDirentsGen.go nameA cap xs used acc).map f =
    packFittingDirentsGen.go nameB cap (xs.map f) used (acc.map f) := by
  induction xs generalizing used acc with
  | nil =>
    rw [packFittingDirentsGen.go.eq_1, List.map_nil, packFittingDirentsGen.go.eq_1, List.map_reverse]
  | cons hd tl ih =>
    rw [packFittingDirentsGen.go.eq_2, List.map_cons, packFittingDirentsGen.go.eq_2, hName]
    split
    · simpa only [List.map_cons] using ih (hd :: acc) (used + dirent64Reclen (nameA hd))
    · exact List.map_reverse

private theorem getdentsRawDrop_map_eq_drop (s : FilesState) (desc : OpenDesc) (vn : VNode) (cursor : Nat) :
    (getdentsRawDrop desc vn cursor).map (materializeDirentEntry s) =
    (getdentsAllEntries s desc vn).drop cursor := by
  cases cursor with
  | zero =>
    simp [getdentsRawDrop, getdentsAllEntries, materializeDirentEntry, List.map_map]
  | succ c =>
    cases c with
    | zero =>
      simp [getdentsRawDrop, getdentsAllEntries, materializeDirentEntry, List.map_map]
    | succ c' =>
      simp only [getdentsRawDrop, getdentsAllEntries, List.map_drop, List.map_map]
      rfl

private theorem packFittingDirentsGen_go_mem {α : Type} (nameOf : α → ByteArray)
    (cap : Nat) (xs acc : List α) (used : Nat) :
    ∀ ent ∈ packFittingDirentsGen.go nameOf cap xs used acc, ent ∈ acc ∨ ent ∈ xs := by
  induction xs generalizing used acc with
  | nil =>
    intro ent hMem
    rw [packFittingDirentsGen.go.eq_1] at hMem
    exact Or.inl (List.mem_reverse.mp hMem)
  | cons hd tl ih =>
    intro ent hMem
    rw [packFittingDirentsGen.go.eq_2] at hMem
    split at hMem
    · rcases ih (hd :: acc) (used + dirent64Reclen (nameOf hd)) ent hMem with hIn | hTl
      · rcases List.mem_cons.mp hIn with rfl | hAcc
        · exact Or.inr List.mem_cons_self
        · exact Or.inl hAcc
      · exact Or.inr (List.mem_cons_of_mem _ hTl)
    · exact Or.inl (List.mem_reverse.mp hMem)

private theorem packFittingDirentsGen_go_size (cap : Nat)
    (xs acc : List (ByteArray × UInt8 × UInt64)) (used : Nat)
    (hUsed : (mkTypedDirentStubArr acc.reverse).size = used) (hLe : used ≤ cap) :
    (mkTypedDirentStubArr (packFittingDirentsGen.go Prod.fst cap xs used acc)).size ≤ cap := by
  induction xs generalizing used acc with
  | nil =>
    rw [packFittingDirentsGen.go.eq_1]
    omega
  | cons ent rest ih =>
    rcases ent with ⟨nm, dt, ino⟩
    rw [packFittingDirentsGen.go.eq_2]
    split
    · rename_i hFit
      apply ih ((nm, dt, ino) :: acc) (used + dirent64Reclen nm) _ hFit
      rw [List.reverse_cons, mkTypedDirentStubArr_append, Array.size_append, hUsed]
      have h1 : mkTypedDirentStubArr [(nm, dt, ino)] = (mkDirentEntry nm dt ino).data := by
        rw [mkTypedDirentStubArr_cons]
        have hNil : mkTypedDirentStubArr [] = #[] := rfl
        rw [hNil, Array.append_empty]
      rw [h1, mkDirentEntry_size]
    · omega

private theorem mkDirentEntry_getD (nm : ByteArray) (dt : UInt8) (ino : UInt64)
    (idx : Nat) (hIdx : idx < dirent64Reclen nm) :
    (mkDirentEntry nm dt ino).data.getD idx 0 =
      direntEntryByteAt nm dt (UInt8.ofNat (dirent64Reclen nm % 256))
        (UInt8.ofNat ((dirent64Reclen nm / 256) % 256)) ino 1 idx := by
  let lo := UInt8.ofNat (dirent64Reclen nm % 256)
  let hi := UInt8.ofNat ((dirent64Reclen nm / 256) % 256)
  have hLoop : ∀ rem i (acc : ByteArray),
      (mkDirentEntryLoop nm dt lo hi ino 1 i rem acc).data.getD idx 0 =
      if idx < acc.data.size then acc.data.getD idx 0
      else if idx < acc.data.size + rem then
        direntEntryByteAt nm dt lo hi ino 1 (i + (idx - acc.data.size))
      else 0 := by
    intro rem
    induction rem with
    | zero =>
      intro i acc
      unfold mkDirentEntryLoop
      by_cases hLtAcc : idx < acc.data.size
      · simp only [hLtAcc, ↓reduceIte]
      · have hNot : ¬ (idx < acc.data.size + 0) := by omega
        simp only [hLtAcc, hNot, ↓reduceIte, Array.getD, ↓reduceDIte]
    | succ k ih =>
      intro i acc
      unfold mkDirentEntryLoop
      rw [ih (i + 1) (acc.push _)]
      let b := direntEntryByteAt nm dt lo hi ino 1 i
      have hPushData : (acc.push b).data = acc.data.push b := rfl
      rw [hPushData, Array.size_push]
      by_cases hLtAcc : idx < acc.data.size
      · have hLtSucc : idx < acc.data.size + 1 := by omega
        simp only [hLtAcc, hLtSucc, ↓reduceIte, Array.getD, Array.size_push, ↓reduceDIte]
        exact Array.getElem_push_lt hLtAcc
      · by_cases hEqAcc : idx = acc.data.size
        · subst hEqAcc
          have hLtSucc : acc.data.size < acc.data.size + 1 := by omega
          have hLtRem : acc.data.size < acc.data.size + (k + 1) := by omega
          have hIrrefl : ¬ (acc.data.size < acc.data.size) := Nat.lt_irrefl _
          simp only [hIrrefl, hLtSucc, hLtRem, ↓reduceIte, Nat.sub_self, Nat.add_zero]
          simp only [Array.getD, Array.size_push, hLtSucc, ↓reduceDIte]
          exact Array.getElem_push_eq
        · have hNotSucc : ¬ (idx < acc.data.size + 1) := by omega
          have hAddEq : (idx < acc.data.size + 1 + k) = (idx < acc.data.size + (k + 1)) :=
            propext ⟨by omega, by omega⟩
          simp only [hLtAcc, hNotSucc, ↓reduceIte, hAddEq]
          split
          · congr 1; omega
          · rfl
  unfold mkDirentEntry
  dsimp only
  rw [hLoop, byteArray_emptyCap_data]
  have hEmptySz : (#[] : Array UInt8).size = 0 := rfl
  rw [hEmptySz, Nat.zero_add]
  have hNot0 : ¬ (idx < 0) := Nat.not_lt_zero idx
  simp only [hNot0, hIdx, ↓reduceIte, Nat.sub_zero, Nat.zero_add]
  rfl

private theorem mkDirentEntry_get16_17_18 (nm : ByteArray) (dt : UInt8) (ino : UInt64)
    (hLt : dirent64Reclen nm < 65536) :
    ((mkDirentEntry nm dt ino).data.getD 16 0).toNat +
      ((mkDirentEntry nm dt ino).data.getD 17 0).toNat * 256 = dirent64Reclen nm ∧
    (mkDirentEntry nm dt ino).data.getD 18 0 = dt := by
  have hGe : dirent64Reclen nm ≥ 24 := (dirent64Reclen_bounds nm).1
  rw [mkDirentEntry_getD nm dt ino 16 (by omega),
    mkDirentEntry_getD nm dt ino 17 (by omega),
    mkDirentEntry_getD nm dt ino 18 (by omega)]
  simp only [direntEntryByteAt]
  simp
  omega

private theorem array_getD_append_mid (a b c : Array UInt8) (idx : Nat) (hIdx : idx < b.size) :
    (a ++ (b ++ c)).getD (a.size + idx) 0 = b.getD idx 0 := by
  have h1 : a.size + idx < (a ++ (b ++ c)).size := by
    simp only [Array.size_append]; omega
  simp only [Array.getD, h1, hIdx, ↓reduceDIte]
  change (a ++ (b ++ c))[a.size + idx] = b[idx]
  rw [Array.getElem_append_right (by omega), Array.getElem_append_left (by omega)]
  congr 1; omega

private theorem mkDirentEntry_bodyByte (nm : ByteArray) (dt : UInt8) (ino : UInt64)
    (k : Nat) (hk : k ≤ nm.data.size) :
    (mkDirentEntry nm dt ino).data.getD (19 + k) 0 =
      if k < nm.data.size then nm.data.getD k 0 else 0 := by
  have hBound := (dirent64Reclen_bounds nm).2.2
  have hIdx : 19 + k < dirent64Reclen nm := by omega
  rw [mkDirentEntry_getD nm dt ino (19 + k) hIdx]
  unfold direntEntryByteAt
  simp only [ByteArray.size, byteGetD_eq_data_getD]
  have hNot8 : ¬ (19 + k < 8) := by omega
  have hNot16Lt : ¬ (19 + k < 16) := by omega
  have hNot16 : (19 + k == 16) = false := beq_false_of_ne (by omega)
  have hNot17 : (19 + k == 17) = false := beq_false_of_ne (by omega)
  have hNot18 : (19 + k == 18) = false := beq_false_of_ne (by omega)
  simp only [hNot8, hNot16Lt, hNot16, hNot17, hNot18, Bool.false_eq_true, ↓reduceIte]
  by_cases hLt : k < nm.data.size
  · have hCond : (decide (19 ≤ 19 + k) && decide (19 + k < 19 + nm.data.size)) = true := by
      rw [decide_eq_true (by omega), decide_eq_true (by omega)]; rfl
    simp only [hCond, hLt, ↓reduceIte]
    congr 1; omega
  · have hCond : (decide (19 ≤ 19 + k) && decide (19 + k < 19 + nm.data.size)) = false := by
      rw [decide_eq_true (show 19 ≤ 19 + k by omega),
        decide_eq_false (show ¬ (19 + k < 19 + nm.data.size) by omega)]; rfl
    simp only [hCond, hLt, Bool.false_eq_true, ↓reduceIte]

private theorem findNulInSliceAux_dirent (prefixArr restArr : Array UInt8)
    (bs : ByteArray) (nm : ByteArray) (dt : UInt8) (ino : UInt64)
    (pos k fuel : Nat)
    (hBs : bs.data = prefixArr ++ ((mkDirentEntry nm dt ino).data ++ restArr))
    (hPos : pos = prefixArr.size)
    (hNoNul : !nm.data.any (· == 0) = true)
    (hNoSlash : !nm.data.any (· == slashByte) = true)
    (hLe : k ≤ nm.data.size)
    (hFuel : fuel ≥ nm.data.size - k + 1) :
    findNulInSliceAux bs (pos + 19 + k) (pos + dirent64Reclen nm) fuel =
      some (pos + 19 + nm.data.size) := by
  have hBound := (dirent64Reclen_bounds nm).2.2
  have hEntrySz := mkDirentEntry_size nm dt ino
  have hStep : ∀ m k fuel, nm.data.size - k = m → k ≤ nm.data.size → fuel ≥ m + 1 →
      findNulInSliceAux bs (pos + 19 + k) (pos + dirent64Reclen nm) fuel =
        some (pos + 19 + nm.data.size) := by
    intro m
    induction m with
    | zero =>
      intro k fuel hm hk hf
      have hkEq : k = nm.data.size := by omega
      subst hkEq
      cases fuel with
      | zero => omega
      | succ f =>
        rw [findNulInSliceAux.eq_2]
        simp only [byteGetD_eq_data_getD]
        have hNotGe : ¬ (pos + 19 + nm.data.size ≥ pos + dirent64Reclen nm) := by omega
        have hGet : bs.data.getD (pos + 19 + nm.data.size) 0 = 0 := by
          have hInE : 19 + nm.data.size < (mkDirentEntry nm dt ino).data.size := by omega
          have hAssoc : pos + 19 + nm.data.size = prefixArr.size + (19 + nm.data.size) := by omega
          rw [hBs, hAssoc, array_getD_append_mid _ _ _ (19 + nm.data.size) hInE]
          have hB := mkDirentEntry_bodyByte nm dt ino nm.data.size (Nat.le_refl _)
          simp only [Nat.lt_irrefl, ↓reduceIte] at hB
          exact hB
        simp only [hNotGe, hGet, beq_self_eq_true, ↓reduceIte]
    | succ m ih =>
      intro k fuel hm hk hf
      have hkLt : k < nm.data.size := by omega
      cases fuel with
      | zero => omega
      | succ f =>
        rw [findNulInSliceAux.eq_2]
        simp only [byteGetD_eq_data_getD]
        have hNotGe : ¬ (pos + 19 + k ≥ pos + dirent64Reclen nm) := by omega
        have hGet : bs.data.getD (pos + 19 + k) 0 = nm.data[k] := by
          have hInE : 19 + k < (mkDirentEntry nm dt ino).data.size := by omega
          have hAssoc : pos + 19 + k = prefixArr.size + (19 + k) := by omega
          rw [hBs, hAssoc, array_getD_append_mid _ _ _ (19 + k) hInE]
          have hB := mkDirentEntry_bodyByte nm dt ino k hk
          simp only [hkLt, ↓reduceIte] at hB
          simp only [hB, Array.getD, hkLt, ↓reduceDIte]
          rfl
        have hNe0 : nm.data[k] ≠ 0 := by
          intro hZ
          have hAny : nm.data.any (· == 0) = true :=
            Array.any_eq_true.mpr ⟨k, hkLt, beq_iff_eq.mpr hZ⟩
          rw [hAny] at hNoNul
          exact absurd hNoNul (by decide)
        have hNeSlash : nm.data[k] ≠ slashByte := by
          intro hS
          have hAny : nm.data.any (· == slashByte) = true :=
            Array.any_eq_true.mpr ⟨k, hkLt, beq_iff_eq.mpr hS⟩
          rw [hAny] at hNoSlash
          exact absurd hNoSlash (by decide)
        have hNe0B : (bs.data.getD (pos + 19 + k) 0 == 0) = false := by
          rw [hGet]; exact beq_false_of_ne hNe0
        have hNeSlashB : (bs.data.getD (pos + 19 + k) 0 == slashByte) = false := by
          rw [hGet]; exact beq_false_of_ne hNeSlash
        simp only [hNotGe, ↓reduceIte]
        simp only [hNe0B, hNeSlashB, Bool.false_eq_true, ↓reduceIte]
        have hAdd : pos + 19 + k + 1 = pos + 19 + (k + 1) := by omega
        rw [hAdd]
        exact ih (k + 1) f (by omega) (by omega) (by omega)
  exact hStep (nm.data.size - k) k fuel rfl hLe hFuel

private theorem sliceBytes_direntName (prefixArr restArr : Array UInt8)
    (bs : ByteArray) (nm : ByteArray) (dt : UInt8) (ino : UInt64) (pos : Nat)
    (hBs : bs.data = prefixArr ++ ((mkDirentEntry nm dt ino).data ++ restArr))
    (hPos : pos = prefixArr.size) :
    sliceBytes bs (pos + 19) nm.data.size = nm := by
  have hBound := (dirent64Reclen_bounds nm).2.2
  have hEntrySz := mkDirentEntry_size nm dt ino
  have hSz : bs.data.size = prefixArr.size + dirent64Reclen nm + restArr.size := by
    rw [hBs]; simp [Array.size_append, hEntrySz]; omega
  apply ByteArray.ext
  apply Array.ext
  · rw [sliceBytes_data]; simp only [Array.size_extract]; omega
  · intro j hj1 hj2
    rw [sliceBytes_data] at hj1
    simp only [Array.size_extract] at hj1
    have hjLt : j < nm.data.size := by omega
    simp only [sliceBytes_data, Array.getElem_extract]
    have hInE : 19 + j < (mkDirentEntry nm dt ino).data.size := by omega
    have hIn : pos + 19 + j < bs.data.size := by omega
    have hL : bs.data[pos + 19 + j] = bs.data.getD (pos + 19 + j) 0 := by
      simp only [Array.getD, hIn, ↓reduceDIte]; rfl
    have hR : nm.data[j] = nm.data.getD j 0 := by
      simp only [Array.getD, hjLt, ↓reduceDIte]; rfl
    rw [hL, hR]
    have hAssoc : pos + 19 + j = prefixArr.size + (19 + j) := by omega
    rw [hBs, hAssoc, array_getD_append_mid _ _ _ (19 + j) hInE]
    have hB := mkDirentEntry_bodyByte nm dt ino j (Nat.le_of_lt hjLt)
    simp only [hjLt, ↓reduceIte] at hB
    exact hB

private theorem parseDirent64One_dirent (prefixArr restArr : Array UInt8)
    (bs : ByteArray) (nm : ByteArray) (dt : UInt8) (ino : UInt64) (pos : Nat)
    (hBs : bs.data = prefixArr ++ ((mkDirentEntry nm dt ino).data ++ restArr))
    (hPos : pos = prefixArr.size)
    (hNmGe1 : nm.data.size ≥ 1) (hNmBound : dirent64Reclen nm < 65536)
    (hNoNul : !nm.data.any (· == 0) = true) (hNoSlash : !nm.data.any (· == slashByte) = true) :
    parseDirent64One bs pos = some (nm, dt, pos + dirent64Reclen nm) := by
  unfold parseDirent64One
  simp only [ByteArray.size, byteGetD_eq_data_getD]
  have hReclen := dirent64Reclen_bounds nm
  have hEntrySz := mkDirentEntry_size nm dt ino
  have hBsSz : bs.data.size = pos + dirent64Reclen nm + restArr.size := by
    rw [hBs]; simp [Array.size_append, hPos, hEntrySz]; omega
  have hHas20 : ¬ (pos + 20 > bs.data.size) := by omega
  simp only [hHas20, ↓reduceIte]
  have hGetIdx : ∀ idx < dirent64Reclen nm,
      bs.data.getD (pos + idx) 0 = (mkDirentEntry nm dt ino).data.getD idx 0 := by
    intro idx hIdx
    have hAssoc : pos + idx = prefixArr.size + idx := by omega
    rw [hBs, hAssoc]
    exact array_getD_append_mid _ _ _ idx (by omega)
  obtain ⟨hRec0, hDt0⟩ := mkDirentEntry_get16_17_18 nm dt ino hNmBound
  have hRec : (bs.data.getD (pos + 16) 0).toNat + (bs.data.getD (pos + 17) 0).toNat * 256 =
      dirent64Reclen nm := by
    rw [hGetIdx 16 (by omega), hGetIdx 17 (by omega)]; exact hRec0
  have hDt : bs.data.getD (pos + 18) 0 = dt := by
    rw [hGetIdx 18 (by omega)]; exact hDt0
  simp only [hRec, hDt]
  have hNotGt : ¬ (pos + dirent64Reclen nm > bs.data.size) := by omega
  have hValid : (decide (dirent64Reclen nm < 24) || dirent64Reclen nm % 8 != 0 ||
      decide (pos + dirent64Reclen nm > bs.data.size)) = false := by
    simp only [show ¬ (dirent64Reclen nm < 24) by omega, hReclen.2.1, hNotGt,
      decide_false, bne_self_eq_false, Bool.or_false]
  simp only [hValid, Bool.false_eq_true, ↓reduceIte]
  have hNul := findNulInSliceAux_dirent prefixArr restArr bs nm dt ino
    pos 0 (dirent64Reclen nm - 18) hBs hPos hNoNul hNoSlash (Nat.zero_le _) (by omega)
  have hAdd0 : pos + 19 + 0 = pos + 19 := by omega
  rw [hAdd0] at hNul
  rw [hNul]
  dsimp only
  have hNe19 : (pos + 19 + nm.data.size == pos + 19) = false := beq_false_of_ne (by omega)
  simp only [hNe19, Bool.false_eq_true, ↓reduceIte]
  have hSub : pos + 19 + nm.data.size - (pos + 19) = nm.data.size := by omega
  rw [hSub, sliceBytes_direntName prefixArr restArr bs nm dt ino pos hBs hPos]

private theorem parseDirents64StrictAux_stubArr (prefixArr : Array UInt8)
    (rest : List (ByteArray × UInt8 × UInt64))
    (bs : ByteArray) (pos fuel : Nat) (acc : List (ByteArray × UInt8))
    (hBs : bs.data = prefixArr ++ mkTypedDirentStubArr rest)
    (hPos : pos = prefixArr.size)
    (hFuel : fuel ≥ rest.length + 1)
    (hBound : ∀ ent ∈ rest,
      ent.1.data.size ≥ 1 ∧ dirent64Reclen ent.1 < 65536 ∧
      !ent.1.data.any (· == 0) = true ∧ !ent.1.data.any (· == slashByte) = true) :
    parseDirents64StrictAux bs pos fuel acc =
      some (acc.reverse ++ rest.map fun ent => (ent.1, ent.2.1)) := by
  induction rest generalizing prefixArr bs pos fuel acc with
  | nil =>
    cases fuel with
    | zero => omega
    | succ f =>
      rw [parseDirents64StrictAux.eq_2]
      simp only [ByteArray.size]
      have hSz : bs.data.size = pos := by
        rw [hBs]; simp [hPos]
      simp [hSz]
  | cons hd tl ih =>
    rcases hd with ⟨nm, dt, ino⟩
    cases fuel with
    | zero => omega
    | succ f =>
      rw [parseDirents64StrictAux.eq_2]
      simp only [ByteArray.size]
      obtain ⟨hNmGe1, hNmBound, hNoNul, hNoSlash⟩ := hBound (nm, dt, ino) List.mem_cons_self
      have hEntrySz := mkDirentEntry_size nm dt ino
      have hBsEq : bs.data = prefixArr ++ ((mkDirentEntry nm dt ino).data ++ mkTypedDirentStubArr tl) := by
        rw [hBs, mkTypedDirentStubArr_cons]
      have hBsSz : bs.data.size = pos + dirent64Reclen nm + (mkTypedDirentStubArr tl).size := by
        rw [hBsEq]; simp [Array.size_append, hPos, hEntrySz]; omega
      have hReclenGe := (dirent64Reclen_bounds nm).1
      have hNotEnd : (pos == bs.data.size) = false := beq_false_of_ne (by omega)
      simp only [hNotEnd, Bool.false_eq_true, ↓reduceIte]
      rw [parseDirent64One_dirent prefixArr (mkTypedDirentStubArr tl) bs nm dt ino pos hBsEq hPos hNmGe1 hNmBound hNoNul hNoSlash]
      dsimp only
      have hNext := ih (prefixArr ++ (mkDirentEntry nm dt ino).data) bs (pos + dirent64Reclen nm) f
        ((nm, dt) :: acc)
        (by rw [hBsEq, Array.append_assoc])
        (by simp [Array.size_append, hPos, hEntrySz])
        (by simp at hFuel; omega)
        (fun x hx => hBound x (List.mem_cons_of_mem _ hx))
      rw [hNext]
      simp [List.append_assoc]

private def nondetActInv (s : FilesState) (act : NondetAction) : Prop :=
  match act with
  | .writeReg _ _ ino data _ _ _ _ => data.data.size < UInt32.size ∧ (assocGet s.inodes ino).isSome = true
  | .writeDiscard len _ _ => len < UInt32.size
  | .writeFifo _ _ data _ _ => data.data.size > 0 ∧ data.data.size < UInt32.size
  | .statNode ino vn => checkStatMatchInState s ino vn (mkStatFromVNode ino vn) = true
  | .getdents _ _ vn _ =>
    ∀ (nm : ByteArray) (c : InodeId), (nm, c) ∈ vn.children →
      nm.data.size ≥ 1 ∧ nm.data.size ≤ NAME_MAX ∧
      !nm.data.any (· == 0) = true ∧ !nm.data.any (· == slashByte) = true
  | .getcwdUnbound _ fb =>
    fb.data.size < PATH_MAX ∧ !hasEmbeddedNul fb ∧
    ((fb.data.size > 0 && fb.data.getD 0 0 == slashByte) || startsWithBytes fb unreachablePrefix)
  | _ => True

private theorem verifyNondet_writeReg_default (s : FilesState) (hid : HandleId) (desc : OpenDesc)
    (ino : InodeId) (data : ByteArray) (stripPriv isOverlay roMount copyUp : Bool)
    (hDataSz : data.data.size < UInt32.size)
    (hInoSome : (assocGet s.inodes ino).isSome = true) :
    verifyNondet s (.writeReg hid desc ino data stripPriv isOverlay roMount copyUp)
      (runNondetDefault s (.writeReg hid desc ino data stripPriv isOverlay roMount copyUp)).1 =
    some (runNondetDefault s (.writeReg hid desc ino data stripPriv isOverlay roMount copyUp)).2 := by
  unfold runNondetDefault verifyNondet
  simp only [ByteArray.size]
  cases roMount
  · simp only [Bool.false_eq_true, ↓reduceIte]
    by_cases hZ : data.data.size = 0
    · have hB : (data.data.size == 0) = true := beq_iff_eq.mpr hZ
      simp only [hB, ↓reduceIte]
      rfl
    · have hB : (data.data.size == 0) = false := beq_false_of_ne hZ
      have hPos : data.data.size ≥ 1 := Nat.pos_of_ne_zero hZ
      simp only [hB, Bool.false_eq_true, ↓reduceIte]
      cases hIno : assocGet s.inodes ino with
      | none => simp [hIno] at hInoSome
      | some vn =>
        dsimp only
        have hZero : (((0 : UInt32) &&& (0x04 : UInt32)) != (0 : UInt32)) = false := rfl
        have hToNatFull : (UInt32.ofNat data.data.size).toNat = data.data.size := by
          rw [UInt32.toNat_ofNat']; exact Nat.mod_eq_of_lt hDataSz
        cases hData : vn.data with
        | reg r =>
          cases hSeals : r.seals with
          | unsealable =>
            simp only [hZero, Bool.false_and, Bool.false_eq_true, ↓reduceIte,
              hToNatFull, hPos, Nat.le_refl, decide_true, Bool.and_self]
          | sealable m =>
            cases hG : ((m &&& (0x04 : UInt32)) != (0 : UInt32))
            · simp only [Bool.false_and, Bool.false_eq_true, ↓reduceIte,
                hToNatFull, hPos, Nat.le_refl, decide_true, Bool.and_self]
            · by_cases hGe : (if desc.append then r.size else desc.pos.offset) ≥ r.size
              · have hGt : (if desc.append then r.size else desc.pos.offset) + data.data.size > r.size :=
                  Nat.lt_of_le_of_lt hGe (Nat.lt_add_of_pos_right hPos)
                have hPosGt : decide (data.data.size > 0) = true :=
                  decide_eq_true (Nat.lt_of_succ_le hPos)
                have hEp : (Errno.EPERM == Errno.EROFS) = false := rfl
                have hEb : (Errno.EPERM == Errno.EFBIG) = false := rfl
                have hGeB : decide ((if desc.append then r.size else desc.pos.offset) ≥ r.size) = true :=
                  decide_eq_true hGe
                simp only [hGeB, Bool.false_eq_true, ↓reduceIte, hPosGt, hGt,
                  hEp, hEb, beq_self_eq_true, Bool.and_false, Bool.and_self, decide_true]
              · have hGeB : decide ((if desc.append then r.size else desc.pos.offset) ≥ r.size) = false :=
                  decide_eq_false hGe
                have hLt : (if desc.append then r.size else desc.pos.offset) < r.size :=
                  Nat.lt_of_not_le hGe
                have hNPos : min data.data.size
                    (r.size - (if desc.append then r.size else desc.pos.offset)) ≥ 1 :=
                  Nat.le_min.mpr ⟨hPos, Nat.sub_pos_of_lt hLt⟩
                have hNLt : min data.data.size
                    (r.size - (if desc.append then r.size else desc.pos.offset)) < UInt32.size :=
                  Nat.lt_of_le_of_lt (Nat.min_le_left _ _) hDataSz
                have hToNat : (UInt32.ofNat (min data.data.size
                    (r.size - (if desc.append then r.size else desc.pos.offset)))).toNat =
                    min data.data.size (r.size - (if desc.append then r.size else desc.pos.offset)) := by
                  rw [UInt32.toNat_ofNat']; exact Nat.mod_eq_of_lt hNLt
                simp only [Bool.true_and, hGeB, Bool.false_eq_true, ↓reduceIte,
                  hToNat, hNPos, Nat.le_refl, decide_true, Bool.and_self]
        | dir _ | symlink _ | fifo _ | charDev _ | socket | blockDev | other =>
          simp only [hZero, Bool.false_and, Bool.false_eq_true, ↓reduceIte,
            hToNatFull, hPos, Nat.le_refl, decide_true, Bool.and_self]
  · simp only [↓reduceIte, Bool.true_and, beq_self_eq_true]

private theorem verifyNondet_runNondetDefault (s : FilesState) (act : NondetAction)
    (hInv : nondetActInv s act) :
    verifyNondet s act (runNondetDefault s act).1 = some (runNondetDefault s act).2 ∨
    (verifyNondet s act (runNondetDefault s act).1 = none ∧
     (runNondetDefault s act).2 = s ∧
     ∃ e, (runNondetDefault s act).1 = .err e ∧ e.isTransientOsErrno = true) := by
  cases act with
  | openFifoUncertain sOpen hid sClose =>
    left; simp [runNondetDefault, verifyNondet]
  | readReg hid desc rd cap =>
    left
    unfold runNondetDefault verifyNondet
    dsimp only
    by_cases hZ : min (if desc.pos.offset < rd.size then rd.size - desc.pos.offset else 0) (min cap MAX_READ_BYTES.toNat) = 0
    · have hMaxPos : MAX_READ_BYTES.toNat > 0 := by decide
      have hW0 : min cap (if desc.pos.offset < rd.size then rd.size - desc.pos.offset else 0) = 0 := by omega
      have hZBool : (min (if desc.pos.offset < rd.size then rd.size - desc.pos.offset else 0) (min cap MAX_READ_BYTES.toNat) == 0) = true :=
        beq_iff_eq.mpr hZ
      have hW0Bool : (min cap (if desc.pos.offset < rd.size then rd.size - desc.pos.offset else 0) == 0) = true :=
        beq_iff_eq.mpr hW0
      simp only [hZBool, ↓reduceIte, hW0Bool]
      rfl
    · have hWLeCap : min (if desc.pos.offset < rd.size then rd.size - desc.pos.offset else 0) (min cap MAX_READ_BYTES.toNat) ≤
          min cap (if desc.pos.offset < rd.size then rd.size - desc.pos.offset else 0) := by omega
      have hWPos : min (if desc.pos.offset < rd.size then rd.size - desc.pos.offset else 0) (min cap MAX_READ_BYTES.toNat) ≥ 1 :=
        Nat.pos_of_ne_zero hZ
      have hWNe0 : (min (if desc.pos.offset < rd.size then rd.size - desc.pos.offset else 0) (min cap MAX_READ_BYTES.toNat) == 0) = false :=
        beq_false_of_ne hZ
      have hAvailNe0 : (min cap (if desc.pos.offset < rd.size then rd.size - desc.pos.offset else 0) == 0) = false :=
        beq_false_of_ne (by omega)
      have hSz : (rd.readSlice desc.pos.offset (min (if desc.pos.offset < rd.size then rd.size - desc.pos.offset else 0) (min cap MAX_READ_BYTES.toNat))).data.size =
          min (if desc.pos.offset < rd.size then rd.size - desc.pos.offset else 0) (min cap MAX_READ_BYTES.toNat) := by
        rw [regData_readSlice_size]; exact Nat.min_eq_left (Nat.min_le_left _ _)
      have hOk : ((rd.readSlice desc.pos.offset (min (if desc.pos.offset < rd.size then rd.size - desc.pos.offset else 0) (min cap MAX_READ_BYTES.toNat))).size ≥ 1 &&
          (rd.readSlice desc.pos.offset (min (if desc.pos.offset < rd.size then rd.size - desc.pos.offset else 0) (min cap MAX_READ_BYTES.toNat))).size ≤
            min cap (if desc.pos.offset < rd.size then rd.size - desc.pos.offset else 0) &&
          bytesEq (rd.readSlice desc.pos.offset (min (if desc.pos.offset < rd.size then rd.size - desc.pos.offset else 0) (min cap MAX_READ_BYTES.toNat)))
            (rd.readSlice desc.pos.offset (rd.readSlice desc.pos.offset (min (if desc.pos.offset < rd.size then rd.size - desc.pos.offset else 0) (min cap MAX_READ_BYTES.toNat))).size)) = true := by
        change ((rd.readSlice desc.pos.offset (min (if desc.pos.offset < rd.size then rd.size - desc.pos.offset else 0) (min cap MAX_READ_BYTES.toNat))).data.size ≥ 1 &&
          (rd.readSlice desc.pos.offset (min (if desc.pos.offset < rd.size then rd.size - desc.pos.offset else 0) (min cap MAX_READ_BYTES.toNat))).data.size ≤
            min cap (if desc.pos.offset < rd.size then rd.size - desc.pos.offset else 0) &&
          bytesEq (rd.readSlice desc.pos.offset (min (if desc.pos.offset < rd.size then rd.size - desc.pos.offset else 0) (min cap MAX_READ_BYTES.toNat)))
            (rd.readSlice desc.pos.offset (rd.readSlice desc.pos.offset (min (if desc.pos.offset < rd.size then rd.size - desc.pos.offset else 0) (min cap MAX_READ_BYTES.toNat))).data.size)) = true
        rw [hSz]
        simp only [hWPos, hWLeCap, bytesEq_eq_data_beq, beq_self_eq_true, Bool.true_and, decide_true]
      simp only [hWNe0, hAvailNe0, hOk, Bool.false_eq_true, ↓reduceIte]
      simp only [ByteArray.size, hSz]
  | readZeroDev cap =>
    left
    unfold runNondetDefault verifyNondet
    dsimp only
    have hPos : (cap == 0 || decide (cap ≥ 1)) = true := by
      cases cap <;> simp
    have hAll : allBytesZeroLoop (replicateZeroBytes cap) 0 cap = true :=
      allBytesZeroLoop_replicate_zero cap cap 0
    simp only [replicateZeroBytes_size, Nat.le_refl, decide_true, hPos, hAll, Bool.true_and, ↓reduceIte]
  | readDynamic hid desc cap nonblock isCharDev =>
    left; simp [runNondetDefault, verifyNondet, ByteArray.size]
  | readFifo ino ring cap nonblock isDynamic =>
    left
    unfold runNondetDefault verifyNondet
    dsimp only
    simp only [ByteArray.size]
    by_cases hEmpty : ring.buf.data.size = 0
    · simp [hEmpty, ByteArray.empty, ByteArray.emptyWithCapacity]
      intro h; exact absurd rfl h
    · by_cases hCap0 : cap = 0
      · subst hCap0
        simp only [Nat.zero_min, beq_self_eq_true, ↓reduceIte, ByteArray.empty, ByteArray.emptyWithCapacity]
        split <;> simp
        · intro h; exact absurd rfl h
        · rfl
      · have hLt : 0 < ring.buf.data.size := Nat.pos_of_ne_zero hEmpty
        have hZ : min cap ring.buf.data.size ≠ 0 := by omega
        have hLe : min cap ring.buf.data.size ≤ ring.buf.data.size - 0 := by
          simpa using Nat.min_le_right cap ring.buf.data.size
        have hSz : (sliceBytes ring.buf 0 (min cap ring.buf.data.size)).data.size =
            min cap ring.buf.data.size := sliceBytes_full ring.buf 0 _ hLt hLe
        have hB : (min cap ring.buf.data.size == 0) = false := beq_false_of_ne hZ
        have hMinPos : min cap ring.buf.data.size ≥ 1 := Nat.pos_of_ne_zero hZ
        have hCond : (decide ((sliceBytes ring.buf 0 (min cap ring.buf.data.size)).data.size ≥ 1) &&
            decide ((sliceBytes ring.buf 0 (min cap ring.buf.data.size)).data.size ≤ min cap ring.buf.data.size) &&
            bytesEq (sliceBytes ring.buf 0 (min cap ring.buf.data.size))
              (sliceBytes ring.buf 0 (sliceBytes ring.buf 0 (min cap ring.buf.data.size)).data.size)) = true := by
          simp only [bytesEq_eq_data_beq, hSz, hMinPos, Nat.le_refl, decide_true, Bool.true_and, beq_self_eq_true]
        split
        · rename_i hEq0
          exact False.elim (hEmpty (beq_iff_eq.mp hEq0))
        · simp only [hB, Bool.false_eq_true, ↓reduceIte]
          cases assocGet s.inodes ino with
          | none => simp only [hCond, ↓reduceIte]
          | some _ =>
            simp only [hCond, ↓reduceIte]
            rw [hSz]
  | writeReg hid desc ino data stripPriv isOverlay roMount copyUp =>
    exact Or.inl (verifyNondet_writeReg_default s hid desc ino data stripPriv isOverlay roMount copyUp hInv.1 hInv.2)
  | writeDiscard len extraErrs nonblockEagain =>
    left
    have hToNat : (UInt32.ofNat len).toNat = len := by
      rw [UInt32.toNat_ofNat']; exact Nat.mod_eq_of_lt hInv
    unfold runNondetDefault verifyNondet
    dsimp only
    rw [hToNat]
    by_cases hZ : len = 0
    · subst hZ; simp
    · have hPos : len ≥ 1 := Nat.pos_of_ne_zero hZ
      simp [beq_false_of_ne hZ, hPos]
  | writeFifo ino ring data nonblock isDyn =>
    rcases hInv with ⟨hDataPos, hDataSz⟩
    unfold runNondetDefault verifyNondet
    simp only [ByteArray.size]
    by_cases hEpipe : (!isDyn && (fifoCounts s ino ring).2.1 == 0) = true
    · left
      rw [hEpipe]
      have hDynF : isDyn = false := by cases isDyn <;> simp_all
      have hR0 : ring.readers = 0 := by simp [fifoCounts, hDynF] at hEpipe; exact hEpipe
      have hMin0 : (fifoCounts s ino ring).1 = 0 := by simp [fifoCounts, hR0]
      simp [hDynF, hMin0]
    · have hEpipeF : (!isDyn && (fifoCounts s ino ring).2.1 == 0) = false :=
        Bool.eq_false_iff.mpr hEpipe
      rw [hEpipeF]
      simp only [Bool.false_eq_true, ↓reduceIte]
      let n := if isDyn then data.data.size else min data.data.size
        (if !nonblock && (pipeWriteSlots ring.slots ring.capacity.minPages data.data.size).2 == 0
         then (pipeWriteSlots ring.slots ring.capacity.maxPages data.data.size).2
         else (pipeWriteSlots ring.slots ring.capacity.minPages data.data.size).2)
      by_cases hEagain : (!isDyn && nonblock && n == 0) = true
      · left
        have hDynF : isDyn = false := by cases isDyn <;> simp_all
        have hNbT : nonblock = true := by cases nonblock <;> simp_all
        have hN0 : n = 0 := by simp [hDynF, hNbT] at hEagain; exact hEagain
        have hCanW0 : (pipeWriteSlots ring.slots ring.capacity.minPages data.data.size).2 = 0 := by
          dsimp only [n] at hN0
          simp only [hDynF, hNbT, Bool.not_true, Bool.false_and, Bool.false_eq_true, ↓reduceIte] at hN0
          omega
        have hZeroImp := pipeWriteSlots_zero_imp ring.slots ring.capacity.minPages data.data.size hDataPos hCanW0
        have hGeMinP : ring.slots.length ≥ ring.capacity.minPages := by omega
        have hPipeErr : (Errno.EAGAIN == Errno.EPIPE) = false := rfl
        have hEagain' : (!isDyn && nonblock && (if isDyn then data.data.size else min data.data.size
            (if !nonblock && (pipeWriteSlots ring.slots ring.capacity.minPages data.data.size).2 == 0
             then (pipeWriteSlots ring.slots ring.capacity.maxPages data.data.size).2
             else (pipeWriteSlots ring.slots ring.capacity.minPages data.data.size).2)) == 0) = true := hEagain
        rw [hEagain']
        simp only [hPipeErr, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
        have hEagainEq : (Errno.EAGAIN == Errno.EAGAIN) = true := rfl
        have hZeroEq : (0 == 0) = true := rfl
        cases s.ambientSeccomp <;> cases assocGet s.inodes ino <;>
          simp only [hDynF, hNbT, hGeMinP, hZeroImp.2, Bool.not_false, Bool.true_and,
            hEagainEq, hZeroEq, Bool.true_or, decide_true, Bool.false_eq_true, ↓reduceIte]
      · have hEagainF : (!isDyn && nonblock && (if isDyn then data.data.size else min data.data.size
            (if !nonblock && (pipeWriteSlots ring.slots ring.capacity.minPages data.data.size).2 == 0
             then (pipeWriteSlots ring.slots ring.capacity.maxPages data.data.size).2
             else (pipeWriteSlots ring.slots ring.capacity.minPages data.data.size).2)) == 0) = false :=
          Bool.eq_false_iff.mpr hEagain
        rw [hEagainF]
        simp only [Bool.false_eq_true, ↓reduceIte]
        by_cases hN0 : n = 0
        · right
          have hNB : (n == 0) = true := beq_iff_eq.mpr hN0
          rw [hNB]
          have hEp : (Errno.EINTR == Errno.EPIPE) = false := rfl
          have hEa : (Errno.EINTR == Errno.EAGAIN) = false := rfl
          refine ⟨?_, rfl, Errno.EINTR, rfl, by decide⟩
          simp [hEp, hEa]
        · left
          have hNB : (n == 0) = false := beq_false_of_ne hN0
          have hNGe1 : n ≥ 1 := Nat.pos_of_ne_zero hN0
          have hLeData : n ≤ data.data.size := by
            dsimp only [n]; cases isDyn <;> simp <;> omega
          have hToNat : (UInt32.ofNat n).toNat = n := by
            rw [UInt32.toNat_ofNat']; exact Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt hLeData hDataSz)
          have hMono := pipeWriteSlots_mono ring.slots ring.capacity.minPages ring.capacity.maxPages data.data.size
            (pipeCap_min_le_max ring.capacity)
          have hLeBound : n ≤ (if isDyn then data.data.size else min data.data.size
              (pipeWriteSlots ring.slots ring.capacity.maxPages data.data.size).2) := by
            dsimp only [n]; cases isDyn
            · simp only [Bool.false_eq_true, ↓reduceIte]; split <;> omega
            · exact Nat.le_refl _
          dsimp only [n] at hNB hToNat hNGe1 hLeBound
          rw [hNB]
          simp only [Bool.false_eq_true, ↓reduceIte, hToNat, hNGe1, hLeBound, decide_true, Bool.and_self]
  | statNode ino vn =>
    left
    dsimp only [nondetActInv] at hInv
    simp [runNondetDefault, verifyNondet, hInv]
  | readlinkDynamic cap =>
    left; simp [runNondetDefault, verifyNondet, ByteArray.size]
  | getdents hid desc vn bufBytes =>
    left
    dsimp only [nondetActInv] at hInv
    unfold runNondetDefault verifyNondet
    simp only [ByteArray.size]
    by_cases hEof : desc.pos.dirAtEof = true
    · simp [hEof]
    · simp only [hEof, Bool.false_eq_true, ↓reduceIte]
      by_cases hSmall : bufBytes.toNat < 24
      · have hCapLt : min bufBytes.toNat MAX_READ_BYTES.toNat < 24 := by
          have : MAX_READ_BYTES.toNat = 16777216 := rfl
          omega
        simp only [hSmall, hCapLt, ↓reduceIte]
        by_cases hCur : desc.pos.dirCursor ≥ 2
        · simp [hCur]
        · simp [hCur]
      · have hCapGe : ¬ (min bufBytes.toNat MAX_READ_BYTES.toNat < 24) := by
          have : MAX_READ_BYTES.toNat = 16777216 := rfl
          omega
        simp only [hSmall, hCapGe, ↓reduceIte]
        cases hRemRaw : getdentsRawDrop desc vn desc.pos.dirCursor with
        | nil =>
          have hRem : List.drop desc.pos.dirCursor (getdentsAllEntries s desc vn) = [] := by
            rw [← getdentsRawDrop_map_eq_drop, hRemRaw]; rfl
          have hCurGe2 : desc.pos.dirCursor ≥ 2 := by
            have hLen := congrArg List.length hRem
            simp [getdentsAllEntries] at hLen
            omega
          simp [hCurGe2]
        | cons firstRaw tailRaw =>
          let first := materializeDirentEntry s firstRaw
          let tail := tailRaw.map (materializeDirentEntry s)
          have hFirst1 : first.1 = firstRaw.1 := rfl
          have hRem : List.drop desc.pos.dirCursor (getdentsAllEntries s desc vn) = first :: tail := by
            rw [← getdentsRawDrop_map_eq_drop, hRemRaw]; rfl
          by_cases hTooBig : dirent64Reclen firstRaw.1 > min bufBytes.toNat MAX_READ_BYTES.toNat
          · simp only [hTooBig, ↓reduceIte]
            have hTooBig' : dirent64Reclen first.1 > min bufBytes.toNat MAX_READ_BYTES.toNat := hTooBig
            have hNotDot : first.1 ≠ dotBytes ∧ first.1 ≠ dotDotBytes := by
              have hD1 : dirent64Reclen dotBytes = 24 := by decide
              have hD2 : dirent64Reclen dotDotBytes = 24 := by decide
              constructor <;> intro hEq <;> rw [hEq] at hTooBig' <;> omega
            have hMemAll : first ∈ getdentsAllEntries s desc vn :=
              List.mem_of_mem_drop (by rw [hRem]; exact List.mem_cons_self)
            have hMemChildren : ∃ nm c, (nm, c) ∈ vn.children ∧ nm = first.1 := by
              simp only [getdentsAllEntries, List.mem_append, List.mem_cons, List.mem_nil_iff,
                or_false, List.mem_map] at hMemAll
              rcases hMemAll with (hE1 | hE2) | ⟨⟨nm, c⟩, hMemC, hEqF⟩
              · exact False.elim (hNotDot.1 (congrArg Prod.fst hE1))
              · exact False.elim (hNotDot.2 (congrArg Prod.fst hE2))
              · exact ⟨nm, c, hMemC, congrArg Prod.fst hEqF⟩
            rcases hMemChildren with ⟨nm, c, hMemC, hEqNm⟩
            have hAny : (vn.children.any fun x => decide (dirent64Reclen x.1 > min bufBytes.toNat MAX_READ_BYTES.toNat)) = true :=
              List.any_eq_true.mpr ⟨(nm, c), hMemC, decide_eq_true (by rw [hEqNm]; exact hTooBig')⟩
            simp [hAny]
          · simp only [hTooBig, ↓reduceIte]
            have hMapPack : (packFittingDirentsGen Prod.fst (firstRaw :: tailRaw)
                (min bufBytes.toNat MAX_READ_BYTES.toNat)).map (materializeDirentEntry s) =
                packFittingDirentsGen Prod.fst (first :: tail) (min bufBytes.toNat MAX_READ_BYTES.toNat) := by
              unfold packFittingDirentsGen
              exact packFittingDirentsGen_go_map (materializeDirentEntry s) Prod.fst Prod.fst
                (fun _ => rfl) (min bufBytes.toNat MAX_READ_BYTES.toNat) (firstRaw :: tailRaw) [] 0
            rw [hMapPack]
            let packed := packFittingDirentsGen Prod.fst (first :: tail) (min bufBytes.toNat MAX_READ_BYTES.toNat)
            have hFirstFit : 0 + dirent64Reclen first.1 ≤ min bufBytes.toNat MAX_READ_BYTES.toNat := by
              rw [hFirst1]; omega
            have hPackedLen : packed.length ≥ 1 :=
              packFittingDirentsGen_go_nonempty Prod.fst _ _ _ 0 (Or.inr ⟨first, tail, rfl, hFirstFit⟩)
            have hStubSzLe : (mkTypedDirentStub packed).data.size ≤
                min bufBytes.toNat MAX_READ_BYTES.toNat := by
              apply packFittingDirentsGen_go_size _ _ _ 0
              · rfl
              · omega
            have hStubSzGe : (mkTypedDirentStub packed).data.size ≥ 24 := by
              have hGe := mkTypedDirentStubArr_size_ge packed hPackedLen
              change (mkTypedDirentStubArr packed).size ≥ 24
              omega
            have hNotZero : ((mkTypedDirentStub packed).data.size == 0) = false :=
              beq_false_of_ne (by omega)
            have hMemAllOfPacked : ∀ ent ∈ packed, ent ∈ getdentsAllEntries s desc vn := by
              intro ent hMemP
              rcases packFittingDirentsGen_go_mem Prod.fst _ _ _ 0 ent hMemP with hAcc | hInRem
              · cases hAcc
              · exact List.mem_of_mem_drop (by rw [hRem]; exact hInRem)
            have hBoundPacked : ∀ ent ∈ packed,
                ent.1.data.size ≥ 1 ∧ dirent64Reclen ent.1 < 65536 ∧
                !ent.1.data.any (· == 0) = true ∧ !ent.1.data.any (· == slashByte) = true := by
              intro ent hMemP
              have hInAll := hMemAllOfPacked ent hMemP
              simp only [getdentsAllEntries, List.mem_append, List.mem_cons, List.mem_nil_iff,
                or_false, List.mem_map] at hInAll
              rcases hInAll with (rfl | rfl) | ⟨⟨nm', c⟩, hMemC, rfl⟩
              · exact ⟨by dsimp; decide, by dsimp; decide, by simp [dotBytes], by simp [dotBytes, slashByte]⟩
              · exact ⟨by dsimp; decide, by dsimp; decide, by simp [dotDotBytes], by simp [dotDotBytes, slashByte]⟩
              · obtain ⟨hGe1, hNmLe, hNoNul, hNoSlash⟩ := hInv nm' c hMemC
                have : NAME_MAX = 255 := rfl
                refine ⟨hGe1, ?_, hNoNul, hNoSlash⟩
                cases nm'
                unfold dirent64Reclen ByteArray.size
                dsimp only at *
                omega
            have hParse : parseDirents64Strict (mkTypedDirentStub packed) =
                some (packed.map fun ent => (ent.1, ent.2.1)) := by
              unfold parseDirents64Strict ByteArray.size
              have h := parseDirents64StrictAux_stubArr #[] packed (mkTypedDirentStub packed)
                0 ((mkTypedDirentStub packed).data.size + 1) []
                (by simp [mkTypedDirentStubArr]) rfl
                (by
                  have hGe := mkTypedDirentStubArr_size_ge packed hPackedLen
                  change (mkTypedDirentStubArr packed).size + 1 ≥ packed.length + 1
                  omega)
                hBoundPacked
              simpa using h
            have hEntriesOk : (packed.map fun ent => (ent.1, ent.2.1)).all (fun x =>
                ((bytesEq x.1 dotBytes || bytesEq x.1 dotDotBytes) && (x.2 == 0 || x.2 == 4)) ||
                vn.children.any (fun x_1 =>
                  bytesEq x_1.1 x.1 && (x.2 == 0 || match assocGet s.inodes x_1.2 with
                    | some cvn => x.2 == fileKindToDType cvn.kind
                    | none => true)) ||
                desc.dirCachedEntries.any (fun x_1 =>
                  bytesEq x_1.1 x.1 && (x.2 == 0 || match x_1.2 with
                    | some k => x.2 == fileKindToDType k
                    | none => true))) = true := by
              rw [List.all_eq_true]
              intro p hp
              rcases List.mem_map.mp hp with ⟨ent, hMemP, rfl⟩
              have hInAll := hMemAllOfPacked ent hMemP
              simp only [getdentsAllEntries, List.mem_append, List.mem_cons, List.mem_nil_iff,
                or_false, List.mem_map] at hInAll
              rcases hInAll with (rfl | rfl) | ⟨⟨nm', c⟩, hMemC, rfl⟩
              · refine Bool.or_eq_true_iff.mpr (Or.inl (Bool.or_eq_true_iff.mpr (Or.inl ?_)))
                simp [bytesEq_eq_data_beq, dotBytes]
              · refine Bool.or_eq_true_iff.mpr (Or.inl (Bool.or_eq_true_iff.mpr (Or.inl ?_)))
                simp [bytesEq_eq_data_beq, dotDotBytes]
              · refine Bool.or_eq_true_iff.mpr (Or.inl (Bool.or_eq_true_iff.mpr (Or.inr ?_)))
                refine List.any_eq_true.mpr ⟨(nm', c), hMemC, ?_⟩
                have hSelf : bytesEq nm' nm' = true := by simp [bytesEq_eq_data_beq]
                dsimp only
                rw [hSelf, Bool.true_and]
                cases hCvn : assocGet s.inodes c with
                | none => simp
                | some cvn => simp
            have hCond : ((mkTypedDirentStub packed).data.size >= 24 &&
                (mkTypedDirentStub packed).data.size <= min bufBytes.toNat MAX_READ_BYTES.toNat) = true := by
              rw [decide_eq_true (show (mkTypedDirentStub packed).data.size >= 24 from hStubSzGe),
                decide_eq_true hStubSzLe]; rfl
            rw [hNotZero]
            simp only [Bool.false_eq_true, ↓reduceIte]
            rw [hCond]
            simp only [↓reduceIte]
            rw [hParse]
            dsimp only
            rw [List.length_map]
            split
            · rfl
            · rename_i hF
              exact absurd (by rw [Bool.and_eq_true]; exact ⟨decide_eq_true hPackedLen, Bool.or_eq_true_iff.mpr (Or.inr hEntriesOk)⟩) hF
  | flockUncertain sWin sLose nb =>
    left; simp [runNondetDefault, verifyNondet]
  | getcwdUnbound cap fallback =>
    left
    rcases hInv with ⟨hPath, hNul, hPrefix⟩
    unfold runNondetDefault verifyNondet
    dsimp only
    by_cases hSmall : cap.toNat ≤ fallback.size
    · have hCapLt : cap.toNat < PATH_MAX := Nat.lt_of_le_of_lt hSmall hPath
      simp only [hSmall, ↓reduceIte]
      simp [hCapLt]
    · have hLtCap : fallback.size < cap.toNat := by omega
      have hLtMax : fallback.size < MAX_READ_BYTES.toNat := by
        have : PATH_MAX = 4096 := rfl
        have : MAX_READ_BYTES.toNat = 16777216 := rfl
        change fallback.data.size < _
        omega
      have hLtMin : fallback.size < min cap.toNat MAX_READ_BYTES.toNat := Nat.lt_min.mpr ⟨hLtCap, hLtMax⟩
      have hPath' : fallback.size < PATH_MAX := hPath
      have hPrefix' : ((decide (fallback.size > 0) && byteGetD fallback 0 == slashByte) ||
          startsWithBytes fallback unreachablePrefix) = true := hPrefix
      simp only [hSmall, ↓reduceIte, hPrefix', hNul, hLtMin, hPath', decide_true, Bool.true_and]
  | lseekDir hid desc =>
    left; simp [runNondetDefault, verifyNondet]
  | lseekDynamic hid desc =>
    left
    unfold runNondetDefault verifyNondet
    cases desc.pos <;> simp
  | dupStdio slot =>
    left
    unfold runNondetDefault verifyNondet
    simp [Nat.max_eq_right (Nat.le_succ s.nextHid)]
  | reopenExternalStdio desc =>
    left; simp [runNondetDefault, verifyNondet]
  | getFlExternal =>
    left; simp [runNondetDefault, verifyNondet]
  | getSealsExternal =>
    left; simp [runNondetDefault, verifyNondet]
  | externalStdioOpen _ | externalStdioStat | externalStdioUnit =>
    left; simp [runNondetDefault, verifyNondet]; decide


/-- Well-formedness preconditions on state and request ensuring `evalModel` refines `verifyStep`. -/
def WellFormedStep (s : FilesState) (req : FilesReq) : Prop :=
  (∀ ino vn, assocGet s.inodes ino = some vn →
    checkStatMatchInState s ino vn (mkStatFromVNode ino vn) = true ∧
    (∀ nm c, (nm, c) ∈ vn.children →
      nm.data.size ≥ 1 ∧ nm.data.size ≤ NAME_MAX ∧
      !nm.data.any (· == 0) = true ∧ !nm.data.any (· == slashByte) = true)) ∧
  (∀ fb, s.cwdPath = .unbound fb →
    fb.data.size < PATH_MAX ∧ !hasEmbeddedNul fb ∧
    ((fb.data.size > 0 && fb.data.getD 0 0 == slashByte) || startsWithBytes fb unreachablePrefix)) ∧
  (∀ hid data, req = .write hid data → data.data.size < UInt32.size)

private theorem withOpenat2Eagain_nondet (strictOpenat2 : Bool) (resolve : ResolveFlags)
    (touchedDotDot : Bool) (core : StepResult) (act : NondetAction) (ex : List Errno)
    (h : withOpenat2Eagain strictOpenat2 resolve touchedDotDot core = .nondet act ex) :
    ∃ ex0, core = .nondet act ex0 := by
  cases core <;> simp [withOpenat2Eagain] at h
  rcases h with ⟨rfl, _⟩
  exact ⟨_, rfl⟩

private theorem ite_nondet_inv {P : Prop} {c : Prop} [Decidable c] {t e : StepResult}
    {act : NondetAction} {ex : List Errno}
    (h : (if c then t else e) = .nondet act ex)
    (ht : c → t = .nondet act ex → P)
    (he : ¬c → e = .nondet act ex → P) : P := by
  by_cases hc : c
  · simp [hc] at h; exact ht hc h
  · simp [hc] at h; exact he hc h

private theorem evalOpen_nondet_inv (s : FilesState) (dir : Option HandleId) (path : ByteArray)
    (rawFlags : OpenFlags) (mode : Mode) (resolve : ResolveFlags) (strictOpenat2 : Bool)
    (act : NondetAction) (ex : List Errno)
    (h : evalOpen s dir path rawFlags mode resolve strictOpenat2 = .nondet act ex) :
    nondetActInv s act := by
  unfold evalOpen at h
  iterate 6 (first
    | (apply ite_nondet_inv (h := h); (clear h; intro _ h; cases h); (clear h; intro _ h))
    | skip)
  dsimp only at h
  obtain ⟨ex0, hCore⟩ := withOpenat2Eagain_nondet _ _ _ _ _ _ h
  clear h
  let flags : OpenFlags :=
    if !strictOpenat2 && rawFlags.path then
      { access := .rdonly, directory := rawFlags.directory, nofollow := rawFlags.nofollow,
        cloexec := rawFlags.cloexec, path := true }
    else rawFlags
  cases hWalk : (resolveOpenTargetWalk s dir path (!flags.nofollow && !(flags.creat && flags.excl))
      (flags.creat && flags.excl) resolve flags.creat).1 with
  | error re =>
    rw [hWalk] at hCore
    cases hCore
  | ok res =>
    rw [hWalk] at hCore
    try dsimp only at hCore
    cases res with
    | externalOpaque _ =>
      dsimp only at hCore
      cases hCore
      exact trivial
    | missingInParent parentIno leaf trailing =>
      try dsimp only at hCore
      repeat (first
        | (cases hCore <;> fail)
        | (apply ite_nondet_inv (h := hCore) <;> (clear hCore; intro _ hCore))
        | (cases hP : assocGet s.inodes parentIno <;> rw [hP] at hCore <;> try dsimp only at hCore)
        | split at hCore)
    | existing targetIno trailing isSpecialDotRoot parentIno? leaf? _ =>
      dsimp only at hCore
      iterate 3 (first
        | (apply ite_nondet_inv (h := hCore); (clear hCore; intro _ hCore; cases hCore); (clear hCore; intro _ hCore))
        | skip)
      cases hIno : assocGet s.inodes targetIno with
      | none => rw [hIno] at hCore; cases hCore
      | some vn =>
        rw [hIno] at hCore
        dsimp only at hCore
        apply ite_nondet_inv (h := hCore)
        · clear hCore; intro _ hCore
          cases hData : vn.data <;> rw [hData] at hCore <;> (try dsimp only at hCore) <;>
            repeat (first
              | (cases hCore <;> exact trivial)
              | (apply ite_nondet_inv (h := hCore) <;> (clear hCore; intro _ hCore)))
        · clear hCore; intro _ hCore
          cases hData : vn.data with
          | symlink _ =>
            rw [hData] at hCore
            dsimp only at hCore
            repeat (first | (cases hCore <;> fail) | (apply ite_nondet_inv (h := hCore) <;> (clear hCore; intro _ hCore)))
          | dir _ =>
            rw [hData] at hCore
            dsimp only at hCore
            repeat (first | (cases hCore <;> fail) | (apply ite_nondet_inv (h := hCore) <;> (clear hCore; intro _ hCore)))
          | socket =>
            rw [hData] at hCore
            dsimp only at hCore
            repeat (first | (cases hCore <;> fail) | (apply ite_nondet_inv (h := hCore) <;> (clear hCore; intro _ hCore)))
          | charDev dk =>
            rw [hData] at hCore
            dsimp only at hCore
            apply ite_nondet_inv (h := hCore)
            · clear hCore; intro _ hCore; cases hCore
            · clear hCore; intro _ hCore
              cases dk <;> dsimp only at hCore <;>
                repeat (first | (cases hCore <;> fail) | (apply ite_nondet_inv (h := hCore) <;> (clear hCore; intro _ hCore)))
          | fifo ring =>
            rw [hData] at hCore
            dsimp only at hCore
            repeat (first
              | (cases hCore <;> exact trivial)
              | (apply ite_nondet_inv (h := hCore) <;> (clear hCore; intro _ hCore)))
          | reg _ | blockDev | other =>
            rw [hData] at hCore
            dsimp only at hCore
            repeat (first
              | (cases hCore <;> exact trivial)
              | (apply ite_nondet_inv (h := hCore) <;> (clear hCore; intro _ hCore)))

private theorem evalRead_nondet_inv (s : FilesState) (hid : HandleId) (maxBytes : UInt32)
    (act : NondetAction) (ex : List Errno)
    (h : evalRead s hid maxBytes = .nondet act ex) :
    nondetActInv s act := by
  unfold evalRead at h
  repeat (first | (cases h <;> exact trivial) | split at h | dsimp only at h)

private theorem evalWrite_nondet_inv (s : FilesState) (hid : HandleId) (data : ByteArray)
    (act : NondetAction) (ex : List Errno)
    (hSz : data.data.size < UInt32.size)
    (h : evalWrite s hid data = .nondet act ex) :
    nondetActInv s act := by
  unfold evalWrite at h
  cases hFd : assocGet s.fds hid with
  | none => rw [hFd] at h; cases h
  | some desc =>
    rw [hFd] at h
    dsimp only at h
    split at h
    · cases h
    · split at h
      · cases h; exact hSz
      · cases hIno : assocGet s.inodes desc.ino with
        | none => rw [hIno] at h; cases h
        | some vn =>
          rw [hIno] at h
          dsimp only at h
          cases hData : vn.data with
          | dir _ => rw [hData] at h; cases h
          | charDev dk =>
            rw [hData] at h
            dsimp only at h
            split at h
            · cases h; exact hSz
            · cases dk <;> dsimp only at h
              all_goals first
                | (cases h <;> fail)
                | (cases h <;> exact hSz)
                | (split at h <;> (cases h <;> exact hSz))
          | fifo ring =>
            rw [hData] at h
            dsimp only at h
            split at h
            · split at h <;> cases h
            · split at h
              · cases h
              · rename_i hNotZero
                have hPos : data.data.size > 0 :=
                  Nat.pos_of_ne_zero (fun h0 => hNotZero (by simp [ByteArray.size, h0]))
                split at h
                · cases h
                · cases h; exact ⟨hPos, hSz⟩
          | _ =>
            rw [hData] at h
            try dsimp only at h
            cases hPseudo : vn.isPseudo with
            | false =>
              simp only [hPseudo, Bool.false_eq_true, ↓reduceIte] at h
              apply ite_nondet_inv (h := h)
              · clear h; intro _ h; cases h
              · clear h; intro _ h
                apply ite_nondet_inv (h := h)
                · clear h; intro _ h; cases h
                · clear h; intro _ h; cases h; exact ⟨hSz, by simp [hIno]⟩
            | true =>
              simp only [hPseudo, ↓reduceIte] at h
              cases h
              exact hSz

private theorem evalStat_nondet_inv (s : FilesState) (req : FilesReq)
    (act : NondetAction) (ex : List Errno)
    (hStat : ∀ ino vn, assocGet s.inodes ino = some vn →
      checkStatMatchInState s ino vn (mkStatFromVNode ino vn) = true)
    (h : evalStat s req = .nondet act ex) :
    nondetActInv s act := by
  unfold evalStat at h
  repeat (first
    | (cases h <;> (first | exact hStat _ _ ‹assocGet s.inodes _ = some _› | exact trivial))
    | split at h
    | dsimp only at h)

private theorem evalAccess_nondet_inv (s : FilesState) (dir : Option HandleId) (path : ByteArray)
    (mask : AccessModeMask) (flags : AtFlags) (act : NondetAction) (ex : List Errno)
    (h : evalAccess s dir path mask flags = .nondet act ex) :
    nondetActInv s act := by
  unfold evalAccess at h
  repeat (first | (cases h <;> exact trivial) | (apply ite_nondet_inv (h := h) <;> (clear h; intro _ h)) | split at h | dsimp only at h)

private theorem evalMkdir_nondet_inv (s : FilesState) (dir : Option HandleId) (path : ByteArray)
    (mode : Mode) (act : NondetAction) (ex : List Errno)
    (h : evalMkdir s dir path mode = .nondet act ex) :
    nondetActInv s act := by
  unfold evalMkdir at h
  repeat (first | (cases h <;> exact trivial) | split at h | dsimp only at h)

private theorem evalUnlink_nondet_inv (s : FilesState) (dir : Option HandleId) (path : ByteArray)
    (removeDir : Bool) (act : NondetAction) (ex : List Errno)
    (h : evalUnlink s dir path removeDir = .nondet act ex) :
    nondetActInv s act := by
  unfold evalUnlink at h
  repeat (first | (cases h <;> exact trivial) | (apply ite_nondet_inv (h := h) <;> (clear h; intro _ h)) | split at h | dsimp only at h)

private theorem evalRename_nondet_inv (s : FilesState) (oldDir : Option HandleId) (oldPath : ByteArray)
    (newDir : Option HandleId) (newPath : ByteArray) (flags : RenameFlags)
    (act : NondetAction) (ex : List Errno)
    (h : evalRename s oldDir oldPath newDir newPath flags = .nondet act ex) :
    nondetActInv s act := by
  unfold evalRename at h
  repeat (first | (cases h <;> exact trivial) | (apply ite_nondet_inv (h := h) <;> (clear h; intro _ h)) | split at h | dsimp only at h)

private theorem evalSymlink_nondet_inv (s : FilesState) (target : ByteArray) (dir : Option HandleId)
    (linkPath : ByteArray) (act : NondetAction) (ex : List Errno)
    (h : evalSymlink s target dir linkPath = .nondet act ex) :
    nondetActInv s act := by
  unfold evalSymlink at h
  repeat (first | (cases h <;> exact trivial) | (apply ite_nondet_inv (h := h) <;> (clear h; intro _ h)) | split at h | dsimp only at h)

private theorem evalReadlink_nondet_inv (s : FilesState) (dir : Option HandleId) (path : ByteArray)
    (cap : UInt32) (act : NondetAction) (ex : List Errno)
    (h : evalReadlink s dir path cap = .nondet act ex) :
    nondetActInv s act := by
  unfold evalReadlink at h
  repeat (first | (cases h <;> exact trivial) | split at h | dsimp only at h)

private theorem evalGetdents_nondet_inv (s : FilesState) (hid : HandleId) (bufBytes : UInt32)
    (act : NondetAction) (ex : List Errno)
    (hKids : ∀ ino vn, assocGet s.inodes ino = some vn →
      ∀ nm c, (nm, c) ∈ vn.children →
        nm.data.size ≥ 1 ∧ nm.data.size ≤ NAME_MAX ∧
        !nm.data.any (· == 0) = true ∧ !nm.data.any (· == slashByte) = true)
    (h : evalGetdents s hid bufBytes = .nondet act ex) :
    nondetActInv s act := by
  unfold evalGetdents at h
  repeat (first
    | (cases h <;> (first | exact hKids _ _ ‹assocGet s.inodes _ = some _› | (intro _ _ hm; cases hm)))
    | split at h | dsimp only at h)

private theorem bool_ite_cases (c : Bool) (t e r : StepResult)
    (h : (if c then t else e) = r) : t = r ∨ e = r := by
  cases c
  · exact Or.inr (by simpa using h)
  · exact Or.inl (by simpa using h)

private theorem evalChmodNode_no_nondet (s : FilesState) (ino : InodeId) (vn : VNode) (mode : Mode)
    (parentLeaf? : Option (InodeId × ByteArray)) (updateDesc? : Option (HandleId × OpenDesc))
    (act : NondetAction) (ex : List Errno)
    (h : evalChmodNode s ino vn mode parentLeaf? updateDesc? = .nondet act ex) : False := by
  unfold evalChmodNode at h
  rcases bool_ite_cases _ _ _ _ h with h | h; · cases h
  rcases bool_ite_cases _ _ _ _ h with h | h; · cases h
  rcases bool_ite_cases _ _ _ _ h with h | h; · cases h
  rcases bool_ite_cases _ _ _ _ h with h | h; · cases h
  rcases bool_ite_cases _ _ _ _ h with h | h; · cases h
  rcases bool_ite_cases _ _ _ _ h with h | h
  · dsimp only at h
    split at h <;> cases h
  · dsimp only at h
    rcases bool_ite_cases _ _ _ _ h with h | h
    · cases h
    · cases h

private theorem evalFlock_nondet_inv (s : FilesState) (hid : HandleId) (op : FlockOp)
    (act : NondetAction) (ex : List Errno)
    (h : evalFlock s hid op = .nondet act ex) :
    nondetActInv s act := by
  unfold evalFlock at h
  repeat (first | (cases h <;> exact trivial) | split at h | dsimp only at h)

private theorem evalFcntl_nondet_inv (s : FilesState) (hid : HandleId) (cmd : FcntlCmd)
    (act : NondetAction) (ex : List Errno)
    (h : evalFcntl s hid cmd = .nondet act ex) :
    nondetActInv s act := by
  unfold evalFcntl at h
  repeat (first | (cases h <;> exact trivial) | split at h | dsimp only at h)

private theorem evalFsync_no_nondet (s : FilesState) (hid : HandleId)
    (act : NondetAction) (ex : List Errno)
    (h : evalFsync s hid = .nondet act ex) : False := by
  unfold evalFsync at h
  repeat (first | (cases h <;> fail) | split at h | dsimp only at h)

private theorem evalGetcwd_nondet_inv (s : FilesState) (cap : UInt32)
    (act : NondetAction) (ex : List Errno)
    (hCwd : ∀ fb, s.cwdPath = .unbound fb →
      fb.data.size < PATH_MAX ∧ !hasEmbeddedNul fb ∧
      ((fb.data.size > 0 && fb.data.getD 0 0 == slashByte) || startsWithBytes fb unreachablePrefix))
    (h : evalGetcwd s cap = .nondet act ex) :
    nondetActInv s act := by
  unfold evalGetcwd at h
  repeat (first | (cases h <;> exact hCwd _ ‹s.cwdPath = CwdPath.unbound _›) | split at h | dsimp only at h)

private theorem evalLseek_nondet_inv (s : FilesState) (hid : HandleId) (offset : Int64) (whence : SeekWhence)
    (act : NondetAction) (ex : List Errno)
    (h : evalLseek s hid offset whence = .nondet act ex) :
    nondetActInv s act := by
  unfold evalLseek at h
  repeat (first | (cases h <;> exact trivial) | split at h | dsimp only at h)

private theorem evalReopenReadOnly_nondet_inv (s : FilesState) (hid : HandleId)
    (act : NondetAction) (ex : List Errno)
    (h : evalReopenReadOnly s hid = .nondet act ex) :
    nondetActInv s act := by
  unfold evalReopenReadOnly at h
  repeat (first | (cases h <;> exact trivial) | split at h | dsimp only at h)

private theorem evalReq_nondet_inv (s : FilesState) (req : FilesReq)
    (act : NondetAction) (ex : List Errno)
    (hWf : WellFormedStep s req)
    (h : evalReq s req = .nondet act ex) :
    nondetActInv s act := by
  unfold evalReq at h
  split at h
  · cases h
  · cases req with
    | openat d p f m =>
      dsimp only at h
      split at h
      · cases h
      · split at h
        · cases h; exact trivial
        · exact evalOpen_nondet_inv s d p f m {} false act ex h
    | openat2 d p how =>
      dsimp only at h
      split at h
      · cases h
      · split at h
        · cases h; exact trivial
        · exact evalOpen_nondet_inv s d p how.flags how.mode how.resolve true act ex h
    | close hid =>
      dsimp only at h
      split at h <;> cases h
    | read hid maxBytes => exact evalRead_nondet_inv s hid maxBytes act ex h
    | write hid data => exact evalWrite_nondet_inv s hid data act ex (hWf.2.2 hid data rfl) h
    | fstat hid => exact evalStat_nondet_inv s (.fstat hid) act ex (fun i v hv => (hWf.1 i v hv).1) h
    | fstatat d p f =>
      dsimp only at h
      split at h
      · cases h
      · split at h
        · cases h
        · split at h
          · cases h; exact trivial
          · exact evalStat_nondet_inv s (.fstatat d p f) act ex (fun i v hv => (hWf.1 i v hv).1) h
    | faccessat d p m f =>
      dsimp only at h
      split at h
      · cases h
      · split at h
        · cases h; exact trivial
        · exact evalAccess_nondet_inv s d p m f act ex h
    | mkdirat d p m =>
      dsimp only at h
      split at h
      · cases h
      · split at h
        · cases h; exact trivial
        · exact evalMkdir_nondet_inv s d p m act ex h
    | unlinkat d p rd =>
      dsimp only at h
      split at h
      · cases h
      · split at h
        · cases h; exact trivial
        · exact evalUnlink_nondet_inv s d p rd act ex h
    | renameat2 od op nd np f =>
      dsimp only at h
      repeat (first | (cases h <;> exact trivial) | split at h)
      exact evalRename_nondet_inv s od op nd np f act ex h
    | symlinkat t d l =>
      dsimp only at h
      split at h
      · cases h
      · split at h
        · cases h; exact trivial
        · exact evalSymlink_nondet_inv s t d l act ex h
    | readlinkat d p cap =>
      dsimp only at h
      split at h
      · cases h
      · split at h
        · cases h; exact trivial
        · exact evalReadlink_nondet_inv s d p cap act ex h
    | getdents64 hid bufBytes =>
      exact evalGetdents_nondet_inv s hid bufBytes act ex (fun i v hv => (hWf.1 i v hv).2) h
    | fchmodat d p m =>
      dsimp only at h
      split at h
      · cases h
      · split at h
        · cases h; exact trivial
        · repeat (first | (cases h <;> exact trivial) | split at h | dsimp only at h)
          exact False.elim (evalChmodNode_no_nondet _ _ _ _ _ _ act ex h)
    | fchmod hid m =>
      dsimp only at h
      repeat (first | (cases h <;> fail) | split at h | dsimp only at h)
      exact False.elim (evalChmodNode_no_nondet _ _ _ _ _ _ act ex h)
    | flock hid op => exact evalFlock_nondet_inv s hid op act ex h
    | fcntl hid cmd => exact evalFcntl_nondet_inv s hid cmd act ex h
    | fsync hid => exact False.elim (evalFsync_no_nondet s hid act ex h)
    | getcwd cap => exact evalGetcwd_nondet_inv s cap act ex hWf.2.1 h
    | lseek hid off w => exact evalLseek_nondet_inv s hid off w act ex h
    | reopenReadOnly hid => exact evalReopenReadOnly_nondet_inv s hid act ex h
    | dupStdio slot =>
      dsimp only [evalDupStdio] at h
      by_cases hFree : s.freeStdioSlots.contains slot = true
      · simp [hFree] at h
      · simp only [hFree, Bool.false_eq_true, ↓reduceIte] at h
        cases hM : assocGet s.managedStdioMap slot with
        | none =>
          rw [hM] at h; cases h; exact trivial
        | some baseHid =>
          rw [hM] at h
          dsimp only at h
          cases hD : assocGet s.fds baseHid with
          | none => rw [hD] at h; cases h
          | some baseDesc => rw [hD] at h; cases h

/-- Every `evalModel` transition `(out, s')` on a well-formed step is accepted by `verifyStep` with identical next state `some s'`. -/
theorem evalModel_state_refines_verifyStep_aux (s : FilesState) (req : FilesReq)
    (hWf : WellFormedStep s req) :
    verifyStep s (evalReq s req) (evalModel s req).1 = some (evalModel s req).2 := by
  cases hRes : evalReq s req with
  | wrapperErr e =>
    simp [evalModel, verifyStep, hRes, isOutcomeErr]
  | err e alts st? =>
    simp [evalModel, verifyStep, hRes]
  | ok out next extraErrs =>
    simp [evalModel, verifyStep, hRes, outcomeEq_refl]
  | nondet act extraErrs =>
    have hInv := evalReq_nondet_inv s req act extraErrs hWf hRes
    rcases verifyNondet_runNondetDefault s act hInv with hSome | ⟨hNone, hSt, e, hErr, hTrans⟩
    · simp only [evalModel, verifyStep, hRes, hSome]
    · rw [hErr] at hNone
      simp only [evalModel, verifyStep, hRes, hErr, hNone, hTrans, Bool.or_true, ↓reduceIte, hSt]

/-- Every `evalModel` outcome on a well-formed step is accepted by `verifyStep`. -/
theorem evalModel_refines_verifyStep_aux (s : FilesState) (req : FilesReq)
    (hWf : WellFormedStep s req) :
    (verifyStep s (evalReq s req) (evalModel s req).1).isSome = true := by
  rw [evalModel_state_refines_verifyStep_aux s req hWf]
  rfl

end LeanSwe.LinuxSyscall.Files
