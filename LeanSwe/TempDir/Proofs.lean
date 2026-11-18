import LeanSwe.TempDir.Proofs.Shared
import LeanSwe.TempDir.Proofs.WithTempDirProofs
import LeanSwe.TempDir.Proofs.LockedProofs

set_option Elab.async false

namespace LeanSwe.TempDir.Proofs

open Core
open Core.NondetTest
open LeanSwe.Fs (FsApiM FsError FsErrorKind EntryKind FileStat LockMode)
open LeanSwe.Time (TimeOpsM)
open LeanSwe.Uuid (UuidApiM Uuid)
open LeanSwe.EnvVars (EnvVarsApiM)

private def pValidPrefix (p : String) : Bool :=
  !p.isEmpty && p.toList.head? != some '.' && !('/' ∈ p.toList) && !(Char.ofNat 0 ∈ p.toList)

private def pValidRoot (r : String) : Bool :=
  !r.isEmpty && !(Char.ofNat 0 ∈ r.toList)

private def pValidEntryName (n : String) : Bool :=
  !n.isEmpty && n != "." && n != ".." && !('/' ∈ n.toList) && !(Char.ofNat 0 ∈ n.toList)

private def pHasRwx (st : FileStat) : Prop :=
  st.kind = .dir ∧ (st.mode / 256) % 2 = 1 ∧ (st.mode / 128) % 2 = 1 ∧ (st.mode / 64) % 2 = 1

private def pHasPath (xs : Array String) (p : String) : Bool :=
  xs.toList.contains p

private def pIsSorted (xs : Array String) : Bool :=
  xs.toList.Pairwise (· ≤ ·)

private theorem validEntryName_parts (n : String) (h : pValidEntryName n = true) :
    n ≠ "" ∧ n ≠ "." ∧ n ≠ ".." ∧ ¬('/' ∈ n.toList) := by
  have h1 := h
  unfold pValidEntryName at h1
  simp only [Bool.and_eq_true, Bool.not_eq_true', bne_iff_ne, ne_eq] at h1
  rcases h1 with ⟨⟨⟨⟨hnEmpty, hDot⟩, hDotDot⟩, hSlash⟩, _⟩
  exact ⟨fun he => by rw [he] at hnEmpty; simp [String.isEmpty] at hnEmpty, hDot, hDotDot, by simpa using hSlash⟩

private theorem nodup_eraseDupStringsAux (seen xs : List String) (hs : seen.Nodup) :
    (∀ y ∈ seen, y ∉ eraseDupStringsAux seen xs) ∧ (eraseDupStringsAux seen xs).Nodup := by
  induction xs generalizing seen with
  | nil => exact ⟨fun _ _ h => (nomatch h), List.nodup_nil⟩
  | cons x xs ih =>
    simp only [eraseDupStringsAux]
    split
    · exact ih seen hs
    · next hnx =>
      have hs' : (x :: seen).Nodup := List.nodup_cons.mpr ⟨hnx, hs⟩
      have ⟨hMem, hNd⟩ := ih (x :: seen) hs'
      refine ⟨?_, List.nodup_cons.mpr ⟨hMem x List.mem_cons_self, hNd⟩⟩
      intro y hy hyOut
      simp only [List.mem_cons] at hyOut
      rcases hyOut with rfl | hyTail
      · exact hnx hy
      · exact hMem y (List.mem_cons_of_mem x hy) hyTail

private theorem nodup_eraseDupStrings (xs : List String) : (eraseDupStrings xs).Nodup :=
  (nodup_eraseDupStringsAux [] xs List.nodup_nil).2

private theorem nodup_insertSorted (x : String) (xs : List String)
    (hNd : xs.Nodup) (hx : x ∉ xs) : (Internal.insertSorted x xs).Nodup := by
  induction xs with
  | nil => exact List.nodup_cons.mpr ⟨by simp, List.nodup_nil⟩
  | cons y ys ih =>
    simp only [Internal.insertSorted]
    split
    · exact List.nodup_cons.mpr ⟨hx, hNd⟩
    · have ⟨hyYs, hYsNd⟩ := List.nodup_cons.mp hNd
      have hxYs : x ∉ ys := fun h => hx (List.mem_cons_of_mem y h)
      have hxy : y ≠ x := fun h => hx (h ▸ List.mem_cons_self)
      refine List.nodup_cons.mpr ⟨?_, ih hYsNd hxYs⟩
      intro hyIn
      rw [mem_insertSorted] at hyIn
      rcases hyIn with rfl | hyInYs
      · exact hxy rfl
      · exact hyYs hyInYs

private theorem nodup_sortStrings (xs : List String) (hNd : xs.Nodup) :
    (Internal.sortStrings xs).Nodup := by
  induction xs with
  | nil => exact List.nodup_nil
  | cons x xs ih =>
    have ⟨hx, hXs⟩ := List.nodup_cons.mp hNd
    exact nodup_insertSorted x (Internal.sortStrings xs) (ih hXs) (by rwa [mem_sortStrings])

private theorem list_nodup_split {α : Type} (xs : List α) (x : α) (hNd : xs.Nodup) (hx : x ∈ xs) :
    ∃ a b, xs = a ++ x :: b ∧ x ∉ a ∧ x ∉ b := by
  induction xs with
  | nil => cases hx
  | cons y ys ih =>
    have ⟨hy, hYs⟩ := List.nodup_cons.mp hNd
    simp only [List.mem_cons] at hx
    rcases hx with rfl | hxYs
    · exact ⟨[], ys, rfl, fun h => (nomatch h), hy⟩
    · obtain ⟨a, b, hEq, hna, hnb⟩ := ih hYs hxYs
      have hxy : x ≠ y := fun h => hy (h ▸ hxYs)
      exact ⟨y :: a, b, by simp [hEq], fun h => by
        simp only [List.mem_cons] at h
        rcases h with rfl | ha
        · exact hxy rfl
        · exact hna ha, hnb⟩

private theorem list_filter_filterMap_eq {α β : Type} (xs : List α) (keep : α → Bool) (f : α → Option β)
    (h : ∀ x, (f x).isSome = true → keep x = true) :
    (xs.filter keep).filterMap f = xs.filterMap f := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    cases hx : f x with
    | none =>
      by_cases hk : keep x = true <;> simp [hk, hx, ih]
    | some v =>
      have hk : keep x = true := h x (by simp [hx])
      simp [hk, hx, ih]

private theorem hasPath_toArray_mem (xs : List String) (p : String) :
    pHasPath xs.toArray p = true ↔ p ∈ xs := by
  simp [pHasPath]

private theorem isSorted_sortStrings (xs : List String) :
    pIsSorted (Internal.sortStrings xs).toArray = true := by
  simpa [pIsSorted] using pairwise_sortStrings xs

private theorem mockFs_withFileLock_existing_conflict_run (s : TempDirMockState) (p : String)
    (mode : LockMode) (createIfMissing : Bool)
    (ino : Nat) (c : String) (t : Int) (m : Nat)
    (hnorm : normKey p = p)
    (hnode : lookupNode s.nodes p = some (.file ino c t m))
    (hconf : mockHasConflict s.locks ino mode = true)
    {β : Type} (act : StateM TempDirMockState (Except FsError β)) :
    (mockFs.withFileLock p mode createIfMissing act).run s =
      (.error { kind := .wouldBlock, path := some p, message := "wouldBlock" }, s) := by
  dsimp only [mockFs, resolveParentTarget]
  rw [stateM_bind_run, stateM_get_run]
  dsimp only
  rw [hnorm, hnode]
  dsimp only
  rw [hconf]
  simp only [↓reduceIte, stateM_pure_run]

private theorem mockFs_withFileLock_existing_ok_run (s : TempDirMockState) (p : String)
    (mode : LockMode) (createIfMissing : Bool)
    (ino : Nat) (c : String) (t : Int) (m : Nat)
    (hnorm : normKey p = p)
    (hnode : lookupNode s.nodes p = some (.file ino c t m))
    (hconf : mockHasConflict s.locks ino mode = false)
    {β : Type} (act : StateM TempDirMockState (Except FsError β)) :
    (mockFs.withFileLock p mode createIfMissing act).run s =
      let (r, s1) := act.run { s with locks := (ino, mode) :: s.locks }
      (r, { s1 with locks := mockRemoveFirstLock ino mode s1.locks }) := by
  dsimp only [mockFs, resolveParentTarget]
  rw [stateM_bind_run, stateM_get_run]
  dsimp only
  rw [hnorm, hnode]
  dsimp only
  rw [hconf]
  simp only [Bool.false_eq_true, ↓reduceIte, stateM_bind_run, stateM_set_run]
  generalize act.run { s with locks := (ino, mode) :: s.locks } = res
  rcases res with ⟨r, s1⟩
  rfl

private theorem mockFs_unlink_existing_run (s : TempDirMockState) (p : String) (miss : Bool)
    (ino : Nat) (c : String) (t : Int) (m : Nat)
    (hnorm : normKey p = p)
    (hnode : lookupNode s.nodes p = some (.file ino c t m)) :
    (mockFs.unlink p miss).run s =
      (.ok (), { s with nodes := s.nodes.filter (fun e => normKey e.1 != p) }) := by
  dsimp only [mockFs, resolveParentTarget]
  rw [stateM_bind_run, stateM_get_run]
  dsimp only
  rw [hnorm, hnode]
  simp only [stateM_bind_run, stateM_set_run, stateM_pure_run]

private theorem mockFs_rmdir_dir_run (s : TempDirMockState) (p : String) (t : Int) (m : Nat)
    (hnorm : normKey p = p)
    (hnode : lookupNode s.nodes p = some (.dir t m)) :
    (mockFs.rmdir p).run s =
      (.ok (), { s with nodes := s.nodes.filter (fun e => normKey e.1 != p) }) := by
  dsimp only [mockFs, resolveParentTarget]
  rw [stateM_bind_run, stateM_get_run]
  dsimp only
  rw [hnorm, hnode]
  simp only [stateM_bind_run, stateM_set_run, stateM_pure_run]

private theorem mockParentChild_self_join (root name : String) (hr : root ≠ "") (hn : pValidEntryName name = true) :
    mockParentChild (normKey root) (mockJoin root name) = some name := by
  have ⟨hne, hDot, hDotDot, hNoSlash⟩ := validEntryName_parts name hn
  have hjNorm := normKey_mockJoin root name hne hNoSlash
  have hList := mockJoin_eq_append_of_ne_empty root name hr
  unfold mockParentChild
  rw [normKey_idem, hjNorm]
  have hrNormNe : normKey root ≠ "" := normKey_ne_empty root hr
  have hrNormEmpty : (normKey root).isEmpty = false := by
    cases hb : (normKey root).isEmpty with
    | false => rfl
    | true => exact absurd ((string_isEmpty_iff_eq_empty _).mp hb) hrNormNe
  dsimp only
  simp only [hrNormEmpty, Bool.false_eq_true, ↓reduceIte]
  have hPref : (if (normKey root == "/") = true then "/" else normKey root ++ "/").toList =
      if (normKey root == "/") = true then ['/'] else (normKey root).toList ++ ['/'] := by
    by_cases h : (normKey root == "/") = true
    · simp only [h, ↓reduceIte]; rfl
    · simp only [h, Bool.false_eq_true, ↓reduceIte, String.toList_append]; rfl
  have hIsPref : (if (normKey root == "/") = true then "/" else normKey root ++ "/").toList.isPrefixOf
      (mockJoin root name).toList = true := by
    rw [List.isPrefixOf_iff_prefix, hPref, hList]
    exact ⟨name.toList, rfl⟩
  rw [hIsPref]
  have hLen : (if (normKey root == "/") = true then "/" else normKey root ++ "/").length =
      (if (normKey root == "/") = true then ['/'] else (normKey root).toList ++ ['/']).length := by
    rw [← String.length_toList, hPref]
  have hDrop : String.ofList ((mockJoin root name).toList.drop
      (if (normKey root == "/") = true then "/" else normKey root ++ "/").length) = name := by
    rw [hList, hLen, List.drop_left, String.ofList_toList]
  rw [hDrop]
  have hValidEq : pValidEntryName name = (!name.isEmpty && name != "." && name != ".." && !('/' ∈ name.toList) && !(Char.ofNat 0 ∈ name.toList)) := rfl
  rw [← hValidEq, hn]
  rfl

private theorem mockParentChild_eq_of_normKey (dir a b : String) (h : normKey a = normKey b) :
    mockParentChild dir a = mockParentChild dir b := by
  unfold mockParentChild
  rw [h]

private theorem mockFs_listDir_run_of_rwx (s : TempDirMockState) (dir : String)
    (st : FileStat) (hStat : mockStatPure s dir = .ok st) (hRwx : pHasRwx st) :
    let rp := normKey dir
    let names := Internal.sortStrings (eraseDupStrings (s.nodes.filterMap (fun e => mockParentChild rp e.1)))
    (mockFs.listDir dir).run s = (.ok names.toArray, s) ∧
    names.Nodup ∧
    (∀ nm ∈ names, pValidEntryName nm = true) := by
  intro rp names
  obtain ⟨nd, hLook, hSt⟩ := lookupNode_of_lstat_ok s dir st hStat
  have hLookRp : lookupNode s.nodes rp = some nd := by simpa [lookupNode, rp, normKey_idem] using hLook
  have hRx : hasRx st = true := hasRx_of_hasRwx st hRwx
  have hNotDir : (st.kind != .dir) = false := by
    have hDir : st.kind = .dir := hRwx.1
    rw [hDir]; rfl
  have hRun : (mockFs.listDir dir).run s = (.ok names.toArray, s) := by
    dsimp only [mockFs]
    rw [stateM_bind_run, stateM_get_run]
    dsimp only
    rw [hLookRp]
    dsimp only
    rw [hSt, hNotDir, hRx]
    simp only [Bool.false_eq_true, ↓reduceIte, Bool.not_true]
    rfl
  have hNd : names.Nodup := nodup_sortStrings _ (nodup_eraseDupStrings _)
  have hValid : ∀ nm ∈ names, pValidEntryName nm = true := by
    intro nm hnm
    rw [mem_sortStrings, mem_eraseDupStrings, List.mem_filterMap] at hnm
    rcases hnm with ⟨e, _, he⟩
    exact validEntryName_of_mockParentChild rp e.1 nm he
  exact ⟨hRun, hNd, hValid⟩

private theorem mockFs_listDir_mem_of_lookupNode (s : TempDirMockState) (dir childName : String)
    (hd : dir ≠ "") (hn : pValidEntryName childName = true)
    (ndChild : MockNode) (hLookChild : lookupNode s.nodes (mockJoin dir childName) = some ndChild) :
    let rp := normKey dir
    let names := Internal.sortStrings (eraseDupStrings (s.nodes.filterMap (fun e => mockParentChild rp e.1)))
    childName ∈ names := by
  intro rp names
  have ⟨hcNe, _, _, hcNoSlash⟩ := validEntryName_parts childName hn
  have hJoinNorm : normKey (mockJoin dir childName) = mockJoin dir childName := normKey_mockJoin dir childName hcNe hcNoSlash
  unfold lookupNode at hLookChild
  dsimp only at hLookChild
  cases hf : s.nodes.find? (fun e => normKey e.1 == normKey (mockJoin dir childName)) with
  | none => simp [hf] at hLookChild
  | some p =>
    have hpMem : p ∈ s.nodes := List.mem_of_find?_eq_some hf
    have hpEq : normKey p.1 = mockJoin dir childName := by
      have hb := List.find?_some hf
      rw [hJoinNorm, beq_iff_eq] at hb
      exact hb
    have hPc : mockParentChild rp p.1 = some childName := by
      rw [mockParentChild_eq_of_normKey rp p.1 (mockJoin dir childName) (by rw [hpEq, hJoinNorm])]
      exact mockParentChild_self_join dir childName hd hn
    rw [mem_sortStrings, mem_eraseDupStrings, List.mem_filterMap]
    exact ⟨p, hpMem, hPc⟩

private def NodesFilteredPres (P : String → Prop) (s s' : TempDirMockState) : Prop :=
  (∃ keep : String → Bool,
    (∀ k, P k → keep k = true) ∧
    s'.nodes = s.nodes.filter (fun e => keep e.1)) ∧
  s'.locks = s.locks ∧ s'.nextInode = s.nextInode ∧
  s'.tmpdir = s.tmpdir ∧ s'.nowSec = s.nowSec ∧ s'.nextUuid = s.nextUuid

private theorem nodesFilteredPres_refl (P : String → Prop) (s : TempDirMockState) :
    NodesFilteredPres P s s := by
  refine ⟨⟨fun _ => true, fun _ _ => rfl, ?_⟩, rfl, rfl, rfl, rfl, rfl⟩
  induction s.nodes with
  | nil => rfl
  | cons x xs ih => exact congrArg (List.cons x) ih

private theorem nodesFilteredPres_trans {P : String → Prop} {s s1 s2 : TempDirMockState}
    (h1 : NodesFilteredPres P s s1) (h2 : NodesFilteredPres P s1 s2) :
    NodesFilteredPres P s s2 := by
  rcases h1 with ⟨⟨k1, hk1, hn1⟩, hl1, hi1, ht1, hs1, hu1⟩
  rcases h2 with ⟨⟨k2, hk2, hn2⟩, hl2, hi2, ht2, hs2, hu2⟩
  refine ⟨⟨fun p => k1 p && k2 p, fun p hp => by simp [hk1 p hp, hk2 p hp], ?_⟩,
    hl2.trans hl1, hi2.trans hi1, ht2.trans ht1, hs2.trans hs1, hu2.trans hu1⟩
  rw [hn2, hn1, List.filter_filter]
  congr 1
  funext e
  exact Bool.and_comm (k2 e.1) (k1 e.1)

private theorem nodesFilteredPres_mono {P Q : String → Prop} {s s' : TempDirMockState}
    (hPQ : ∀ k, Q k → P k) (h : NodesFilteredPres P s s') :
    NodesFilteredPres Q s s' := by
  rcases h with ⟨⟨keep, hk, hn⟩, hl, hi, ht, hs, hu⟩
  exact ⟨⟨keep, fun k hq => hk k (hPQ k hq), hn⟩, hl, hi, ht, hs, hu⟩

private theorem nodesFilteredPres_lookupNode {P : String → Prop} {s s' : TempDirMockState}
    (hPres : NodesFilteredPres P s s') (p : String)
    (hp : ∀ k, normKey k = normKey p → P k) :
    lookupNode s'.nodes p = lookupNode s.nodes p := by
  rcases hPres with ⟨⟨keep, hk, hn⟩, _⟩
  unfold lookupNode
  dsimp only
  rw [hn]
  congr 1
  induction s.nodes with
  | nil => rfl
  | cons x xs ih =>
    by_cases hxp : (normKey x.1 == normKey p) = true
    · have hkx : keep x.1 = true := hk x.1 (hp x.1 (beq_iff_eq.mp hxp))
      rw [List.filter_cons]; simp only [hkx, ↓reduceIte, List.find?_cons, hxp]
    · have hxpF : (normKey x.1 == normKey p) = false := Bool.eq_false_iff.mpr hxp
      by_cases hkx : keep x.1 = true
      · rw [List.filter_cons]; simp only [hkx, ↓reduceIte, List.find?_cons, hxpF]
        exact ih
      · have hkxF : keep x.1 = false := Bool.eq_false_iff.mpr hkx
        rw [List.filter_cons]; simp only [hkxF, Bool.false_eq_true, ↓reduceIte, List.find?_cons, hxpF]
        exact ih

private theorem nodesFilteredPres_listDir {P : String → Prop} {s s' : TempDirMockState}
    (hPres : NodesFilteredPres P s s') (dir : String) (hd : dir ≠ "")
    (hDirP : ∀ k, normKey k = normKey dir → P k)
    (hUnderP : ∀ k, underDir dir k = true → P k) :
    ((mockFs.listDir dir).run s').1 = ((mockFs.listDir dir).run s).1 ∧
    ((mockFs.listDir dir).run s').2 = s' := by
  have hLook : lookupNode s'.nodes (normKey dir) = lookupNode s.nodes (normKey dir) :=
    nodesFilteredPres_lookupNode hPres (normKey dir) (fun k hk => hDirP k (by simpa [normKey_idem] using hk))
  have hUnderOfPc : ∀ k nm, mockParentChild (normKey dir) k = some nm → underDir dir k = true := by
    intro k nm hpc
    unfold mockParentChild at hpc
    rw [normKey_idem] at hpc
    have hdNorm : normKey dir ≠ "" := normKey_ne_empty dir hd
    have hdEmpty : (normKey dir).isEmpty = false := by
      cases hb : (normKey dir).isEmpty with
      | false => rfl
      | true => exact absurd ((string_isEmpty_iff_eq_empty _).mp hb) hdNorm
    simp only [hdEmpty, Bool.false_eq_true, ↓reduceIte] at hpc
    split at hpc
    · rename_i hSlash
      split at hpc
      · rename_i hPref
        unfold underDir
        simp only [hSlash, ↓reduceIte, hPref, Bool.or_true]
      · simp at hpc
    · rename_i hNotSlash
      split at hpc
      · rename_i hPref
        unfold underDir
        have hNotSlashF : (normKey dir == "/") = false := Bool.eq_false_iff.mpr hNotSlash
        simp only [hNotSlashF, Bool.false_eq_true, ↓reduceIte, hPref, Bool.or_true]
      · simp at hpc
  rcases hPres with ⟨⟨keep, hk, hn⟩, _⟩
  have hFm : s'.nodes.filterMap (fun e => mockParentChild (normKey dir) e.1) =
      s.nodes.filterMap (fun e => mockParentChild (normKey dir) e.1) := by
    rw [hn]
    apply list_filter_filterMap_eq
    intro e he
    cases hpc : mockParentChild (normKey dir) e.1 with
    | none => simp [hpc] at he
    | some nm => exact hk e.1 (hUnderP e.1 (hUnderOfPc e.1 nm hpc))
  dsimp only [mockFs]
  rw [stateM_bind_run, stateM_get_run, stateM_bind_run, stateM_get_run]
  dsimp only
  rw [hLook]
  cases hl : lookupNode s.nodes (normKey dir) with
  | none => exact ⟨rfl, rfl⟩
  | some nd =>
    dsimp only
    by_cases h1 : ((mockNodeStat nd).kind != EntryKind.dir) = true
    · simp only [h1, ↓reduceIte]; constructor <;> rfl
    · have h1f : ((mockNodeStat nd).kind != EntryKind.dir) = false := Bool.eq_false_iff.mpr h1
      by_cases h2 : (!hasRx (mockNodeStat nd)) = true
      · simp only [h1f, h2, Bool.false_eq_true, ↓reduceIte]; constructor <;> rfl
      · have h2f : (!hasRx (mockNodeStat nd)) = false := Bool.eq_false_iff.mpr h2
        simp only [h1f, h2f, Bool.false_eq_true, ↓reduceIte, hFm]; constructor <;> rfl

private structure SweepFsOps (fs : FsApiM (StateM TempDirMockState)) : Prop where
  hJoin : fs.join = mockJoin
  hStat : fs.stat = mockFs.stat
  hLstat : fs.lstat = mockFs.lstat
  hListDir : fs.listDir = mockFs.listDir
  hTryWfl : ∀ {α : Type}, @fs.tryWithFileLock α = @mockFs.tryWithFileLock α
  hRm : fs.rmtree = mockFs.rmtree
  hRmdir : fs.rmdir = mockFs.rmdir
  hUnlink : ∀ p miss s,
    (fs.unlink p miss).run s = (mockFs.unlink p miss).run s ∨
    ∃ fe, (fs.unlink p miss).run s = (.error fe, s)

private theorem sweepFsOps_mockFs : SweepFsOps mockFs :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, fun _ _ _ => Or.inl rfl⟩

private theorem cleanupDirIgnoringNotFound_filteredPres
    (fs : FsApiM (StateM TempDirMockState)) (hRm : fs.rmtree = mockFs.rmtree)
    (target : String) (s : TempDirMockState) :
    let (_, s') := (Internal.cleanupDirIgnoringNotFound fs target).run s
    NodesFilteredPres (fun k => underDir target k = false) s s' := by
  dsimp only [Internal.cleanupDirIgnoringNotFound]
  rw [hRm]
  dsimp only [mockFs, mockRmtreePure, resolveParentTarget]
  rw [stateM_bind_run, stateM_bind_run, stateM_get_run]
  dsimp only
  cases hl : lookupNode s.nodes (normKey target) with
  | none => exact nodesFilteredPres_refl _ s
  | some nd =>
    cases nd with
    | dir t m =>
      simp only [stateM_bind_run, stateM_set_run, stateM_pure_run]
      refine ⟨⟨fun k => !underDir (normKey target) k, fun k hk => ?_, rfl⟩, rfl, rfl, rfl, rfl, rfl⟩
      have hu : underDir (normKey target) k = underDir target k := by unfold underDir; rw [normKey_idem]
      simp [hu, hk]
    | file _ _ _ _ => exact nodesFilteredPres_refl _ s
    | symlink _ _ => exact nodesFilteredPres_refl _ s

private theorem unlink_filteredPres
    (fs : FsApiM (StateM TempDirMockState))
    (hUnlink : ∀ p miss s, (fs.unlink p miss).run s = (mockFs.unlink p miss).run s ∨ ∃ fe, (fs.unlink p miss).run s = (.error fe, s))
    (p : String) (miss : Bool) (s : TempDirMockState) :
    NodesFilteredPres (fun k => normKey k ≠ normKey p) s ((fs.unlink p miss).run s).2 := by
  rcases hUnlink p miss s with hEq | ⟨fe, hErr⟩
  · rw [hEq]
    dsimp only [mockFs, resolveParentTarget]
    rw [stateM_bind_run, stateM_get_run]
    dsimp only
    cases hl : lookupNode s.nodes (normKey p) with
    | none =>
      cases miss <;> exact nodesFilteredPres_refl _ s
    | some nd =>
      cases nd with
      | dir _ _ => exact nodesFilteredPres_refl _ s
      | file _ _ _ _ =>
        simp only [stateM_bind_run, stateM_set_run, stateM_pure_run]
        refine ⟨⟨fun k => normKey k != normKey p, fun k hk => bne_iff_ne.mpr hk, rfl⟩, rfl, rfl, rfl, rfl, rfl⟩
      | symlink _ _ =>
        simp only [stateM_bind_run, stateM_set_run, stateM_pure_run]
        refine ⟨⟨fun k => normKey k != normKey p, fun k hk => bne_iff_ne.mpr hk, rfl⟩, rfl, rfl, rfl, rfl, rfl⟩
  · rw [hErr]
    exact nodesFilteredPres_refl _ s

private theorem rmdir_filteredPres
    (fs : FsApiM (StateM TempDirMockState)) (hRmdir : fs.rmdir = mockFs.rmdir)
    (p : String) (s : TempDirMockState) :
    NodesFilteredPres (fun k => normKey k ≠ normKey p) s ((fs.rmdir p).run s).2 := by
  rw [hRmdir]
  dsimp only [mockFs, resolveParentTarget]
  rw [stateM_bind_run, stateM_get_run]
  dsimp only
  cases hl : lookupNode s.nodes (normKey p) with
  | none => exact nodesFilteredPres_refl _ s
  | some nd =>
    cases nd with
    | dir _ _ =>
      simp only [stateM_bind_run, stateM_set_run, stateM_pure_run]
      refine ⟨⟨fun k => normKey k != normKey p, fun k hk => bne_iff_ne.mpr hk, rfl⟩, rfl, rfl, rfl, rfl, rfl⟩
    | file _ _ _ _ => exact nodesFilteredPres_refl _ s
    | symlink _ _ => exact nodesFilteredPres_refl _ s

private theorem removeNonLockChildren_filteredPres
    (fs : FsApiM (StateM TempDirMockState)) (hOps : SweepFsOps fs)
    (other : String) (hoNe : other ≠ "") (hoNorm : normKey other = other) (hoSlash : other ≠ "/")
    (names : List String) (hValid : ∀ nm ∈ names, pValidEntryName nm = true) (s : TempDirMockState) :
    NodesFilteredPres (fun k => underDir other k = false) s
      ((Internal.removeNonLockChildren fs other names).run s).2 := by
  induction names generalizing s with
  | nil =>
    dsimp only [Internal.removeNonLockChildren]
    rw [stateM_pure_run]
    exact nodesFilteredPres_refl _ s
  | cons nm rest ih =>
    have hnmV : pValidEntryName nm = true := hValid nm (List.mem_cons_self)
    have hrestV : ∀ x ∈ rest, pValidEntryName x = true := fun x hx => hValid x (List.mem_cons_of_mem nm hx)
    dsimp only [Internal.removeNonLockChildren]
    by_cases hLock : (nm == ".lock") = true
    · simp only [hLock, ↓reduceIte]
      exact ih hrestV s
    · have hLockF : (nm == ".lock") = false := Bool.eq_false_iff.mpr hLock
      simp only [hLockF, Bool.false_eq_true, ↓reduceIte]
      rw [stateM_bind_run, hOps.hLstat, mockFs_lstat_run, hOps.hJoin]
      have ⟨hnmNe, _, _, hnmSlash⟩ := validEntryName_parts nm hnmV
      have hUnderEntry : ∀ k, underDir (mockJoin other nm) k = true → underDir other k = true :=
        fun k hk => underDir_mockJoin_child other nm k hoNe hoNorm hoSlash hnmNe hnmSlash hk
      have hNotUnderOtherEntry : ∀ k, underDir other k = false → underDir (mockJoin other nm) k = false := by
        intro k hk
        cases hb : underDir (mockJoin other nm) k with
        | false => rfl
        | true => exact absurd (hUnderEntry k hb) (by rw [hk]; decide)
      have hNotNormEq : ∀ k, underDir other k = false → normKey k ≠ normKey (mockJoin other nm) := by
        intro k hk hEq
        have hu1 : underDir (mockJoin other nm) k = true := by
          unfold underDir
          rw [hEq]
          exact underDir_refl (mockJoin other nm) (normKey_mockJoin other nm hnmNe hnmSlash)
        exact absurd (hUnderEntry k hu1) (by rw [hk]; decide)
      cases hl : mockLstatPure s (mockJoin other nm) with
      | error fe =>
        dsimp only
        by_cases hnf : (fe.kind == .notFound) = true
        · simp only [hnf, ↓reduceIte]; exact ih hrestV s
        · simp only [Bool.eq_false_iff.mpr hnf, Bool.false_eq_true, ↓reduceIte, stateM_pure_run]
          exact nodesFilteredPres_refl _ s
      | ok st =>
        dsimp only
        by_cases hDir : (st.kind == .dir) = true
        · simp only [hDir, ↓reduceIte]
          rw [stateM_bind_run]
          have hStep := cleanupDirIgnoringNotFound_filteredPres fs hOps.hRm (mockJoin other nm) s
          cases hc : (Internal.cleanupDirIgnoringNotFound fs (mockJoin other nm)).run s with
          | mk rc sc =>
            dsimp only at hStep ⊢
            rw [hc] at hStep
            dsimp only at hStep
            have hStep' : NodesFilteredPres (fun k => underDir other k = false) s sc :=
              nodesFilteredPres_mono hNotUnderOtherEntry hStep
            cases rc with
            | error _ => rw [stateM_pure_run]; exact hStep'
            | ok _ => exact nodesFilteredPres_trans hStep' (ih hrestV sc)
        · have hDirF : (st.kind == .dir) = false := Bool.eq_false_iff.mpr hDir
          simp only [hDirF, Bool.false_eq_true, ↓reduceIte]
          rw [stateM_bind_run]
          have h1 := unlink_filteredPres fs hOps.hUnlink (mockJoin other nm) true s
          cases hu : (fs.unlink (mockJoin other nm) true).run s with
          | mk ru su =>
            dsimp only at h1 ⊢
            rw [hu] at h1
            dsimp only at h1
            have h1' : NodesFilteredPres (fun k => underDir other k = false) s su :=
              nodesFilteredPres_mono hNotNormEq h1
            cases ru with
            | error _ =>
              dsimp only
              rw [stateM_bind_run, stateM_pure_run]
              dsimp only
              rw [stateM_pure_run]
              exact h1'
            | ok _ => exact nodesFilteredPres_trans h1' (ih hrestV su)

private theorem removeLockedTempDir_filteredPres
    (fs : FsApiM (StateM TempDirMockState)) (hOps : SweepFsOps fs)
    (other : String) (hoNe : other ≠ "") (hoNorm : normKey other = other) (hoSlash : other ≠ "/")
    (s : TempDirMockState) :
    NodesFilteredPres (fun k => underDir other k = false) s
      ((Internal.removeLockedTempDir fs other (mockJoin other ".lock")).run s).2 := by
  dsimp only [Internal.removeLockedTempDir]
  rw [stateM_bind_run, hOps.hListDir]
  cases hList : (mockFs.listDir other).run s with
  | mk resList sList =>
    have hsListEq : sList = s := by
      dsimp only [mockFs] at hList
      rw [stateM_bind_run, stateM_get_run] at hList
      dsimp only at hList
      cases hl : lookupNode s.nodes (normKey other) with
      | none =>
        rw [hl] at hList
        dsimp only [pure, StateT.pure] at hList
        exact (Prod.mk.inj hList).2.symm
      | some nd =>
        rw [hl] at hList
        dsimp only at hList
        by_cases h1 : (mockNodeStat nd).kind != EntryKind.dir <;> by_cases h2 : !hasRx (mockNodeStat nd) <;>
          simp [h1, h2] at hList
        · exact (Prod.mk.inj hList).2.symm
        · exact (Prod.mk.inj hList).2.symm
        · exact (Prod.mk.inj hList).2.symm
        · exact (Prod.mk.inj hList).2.symm
    have hList' : (mockFs.listDir other).run s = (resList, s) := by rw [hList, hsListEq]
    subst sList
    dsimp only
    cases resList with
    | error fe =>
      by_cases hnf : (fe.kind == .notFound) = true
      · simp only [hnf, ↓reduceIte, stateM_pure_run]; exact nodesFilteredPres_refl _ s
      · simp only [Bool.eq_false_iff.mpr hnf, Bool.false_eq_true, ↓reduceIte, stateM_pure_run]
        exact nodesFilteredPres_refl _ s
    | ok arr =>
      have hValidArr : ∀ nm ∈ arr.toList, pValidEntryName nm = true := by
        intro nm hnm
        dsimp only [mockFs] at hList'
        rw [stateM_bind_run, stateM_get_run] at hList'
        dsimp only [Pure.pure] at hList'
        cases hl : lookupNode s.nodes (normKey other) with
        | none =>
          simp only [hl] at hList'
          dsimp only [StateT.pure, StateT.run] at hList'
          cases (Prod.mk.inj hList').1
        | some nd =>
          rw [hl] at hList'
          dsimp only at hList'
          by_cases h1 : ((mockNodeStat nd).kind != EntryKind.dir) = true
          · simp only [h1, ↓reduceIte] at hList'
            dsimp only [StateT.pure, StateT.run] at hList'
            cases (Prod.mk.inj hList').1
          · have h1f : ((mockNodeStat nd).kind != EntryKind.dir) = false := Bool.eq_false_iff.mpr h1
            by_cases h2 : (!hasRx (mockNodeStat nd)) = true
            · simp only [h1f, h2, Bool.false_eq_true, ↓reduceIte] at hList'
              try dsimp only [Bind.bind, StateT.bind, StateT.pure, Pure.pure] at hList'
              cases (Prod.mk.inj hList').1
            · have h2f : (!hasRx (mockNodeStat nd)) = false := Bool.eq_false_iff.mpr h2
              simp only [h1f, h2f, Bool.false_eq_true, ↓reduceIte] at hList'
              try dsimp only [Bind.bind, StateT.bind, StateT.pure, Pure.pure] at hList'
              have hArr : arr = (Internal.sortStrings (eraseDupStrings (s.nodes.filterMap (fun e => mockParentChild (normKey other) e.1)))).toArray :=
                (Except.ok.inj (Prod.mk.inj hList').1).symm
              have hnm' : nm ∈ Internal.sortStrings (eraseDupStrings (s.nodes.filterMap (fun e => mockParentChild (normKey other) e.1))) := by
                rw [hArr] at hnm; exact hnm
              rw [mem_sortStrings, mem_eraseDupStrings, List.mem_filterMap] at hnm'
              rcases hnm' with ⟨e, _, he⟩
              exact validEntryName_of_mockParentChild (normKey other) e.1 nm he
      have hRem := removeNonLockChildren_filteredPres fs hOps other hoNe hoNorm hoSlash arr.toList hValidArr s
      rw [stateM_bind_run]
      cases hr : (Internal.removeNonLockChildren fs other arr.toList).run s with
      | mk rRem s1 =>
        rw [hr] at hRem
        dsimp only at hRem
        cases rRem with
        | error te =>
          rw [stateM_pure_run]
          exact hRem
        | ok _ =>
          rw [stateM_bind_run]
          have hUnlinkLock := unlink_filteredPres fs hOps.hUnlink (mockJoin other ".lock") true s1
          have hNotLock : ∀ k, underDir other k = false → normKey k ≠ normKey (mockJoin other ".lock") := by
            intro k hk hEq
            have hu : underDir other (mockJoin other ".lock") = true :=
              underDir_mockJoin_self other ".lock" hoNe hoNorm hoSlash (by decide) (by decide)
            have hu2 : underDir other k = true := by
              rwa [underDir_eq_of_normKey_eq other k (mockJoin other ".lock") hEq]
            rw [hu2] at hk
            exact Bool.noConfusion hk
          have hUnlinkPres : NodesFilteredPres (fun k => underDir other k = false) s1
              ((fs.unlink (mockJoin other ".lock") true).run s1).2 :=
            nodesFilteredPres_mono hNotLock hUnlinkLock
          cases hu : (fs.unlink (mockJoin other ".lock") true).run s1 with
          | mk ru s2 =>
            dsimp only at hUnlinkPres ⊢
            rw [hu] at hUnlinkPres
            dsimp only at hUnlinkPres
            cases ru with
            | error fe =>
              rw [stateM_pure_run]
              exact nodesFilteredPres_trans hRem hUnlinkPres
            | ok _ =>
              rw [stateM_bind_run]
              have hRmDir := rmdir_filteredPres fs hOps.hRmdir other s2
              have hNotSelf : ∀ k, underDir other k = false → normKey k ≠ normKey other := by
                intro k hk hEq
                have hu : underDir other k = true := by
                  rw [underDir_eq_of_normKey_eq other k other hEq, underDir_refl other hoNorm]
                rw [hu] at hk
                exact Bool.noConfusion hk
              have hRmPres : NodesFilteredPres (fun k => underDir other k = false) s2
                  ((fs.rmdir other).run s2).2 :=
                nodesFilteredPres_mono hNotSelf hRmDir
              cases hd : (fs.rmdir other).run s2 with
              | mk rd s3 =>
                dsimp only at hRmPres ⊢
                rw [hd] at hRmPres
                dsimp only at hRmPres
                have hAll := nodesFilteredPres_trans hRem (nodesFilteredPres_trans hUnlinkPres hRmPres)
                cases rd with
                | ok _ =>
                  rw [stateM_pure_run]; exact hAll
                | error fe =>
                  by_cases hnf : (fe.kind == .notFound) = true
                  · simp only [hnf, ↓reduceIte, stateM_pure_run]; exact hAll
                  · simp only [Bool.eq_false_iff.mpr hnf, Bool.false_eq_true, ↓reduceIte, stateM_pure_run]; exact hAll

private theorem sweepEntry_other_preserves
    (fs : FsApiM (StateM TempDirMockState)) (hOps : SweepFsOps fs)
    (root dirPrefix childName otherName : String) (maxAgeSec : Nat) (nowSec : Int)
    (hr : root ≠ "") (hcV : pValidEntryName childName = true) (hoV : pValidEntryName otherName = true)
    (hNe : otherName ≠ childName) (rep : CleanupReport) (s : TempDirMockState) :
    let child := mockJoin root childName
    let P : String → Prop := fun k => underDir child k = true ∨ normKey k = normKey root
    let (rep', s') := (Internal.sweepEntry fs root dirPrefix maxAgeSec nowSec rep otherName).run s
    NodesFilteredPres P s s' ∧
    (child ∈ rep'.removed.toList ↔ child ∈ rep.removed.toList) ∧
    (child ∈ rep'.keptLocked.toList ↔ child ∈ rep.keptLocked.toList) ∧
    (child ∈ rep'.keptFresh.toList ↔ child ∈ rep.keptFresh.toList) ∧
    (child ∈ rep'.skipped.toList ↔ child ∈ rep.skipped.toList) ∧
    (rep.failed.isEmpty = false → rep'.failed.isEmpty = false) ∧
    (∀ e ∈ rep.failed.toList, e ∈ rep'.failed.toList) := by
  intro child P
  have ⟨hcNe, _, _, hcSlash⟩ := validEntryName_parts childName hcV
  have ⟨hoNe, _, _, hoSlash⟩ := validEntryName_parts otherName hoV
  let other := mockJoin root otherName
  have hoFullNe : other ≠ "" := mockJoin_ne_empty root otherName hoNe
  have hoFullNorm : normKey other = other := normKey_mockJoin root otherName hoNe hoSlash
  have hoFullSlash : other ≠ "/" := mockJoin_ne_slash root otherName hr hoNe
  have hOtherNeChild : other ≠ child := by
    intro hEq
    have hu1 : underDir child other = true := by
      rw [hEq]; exact underDir_refl child (normKey_mockJoin root childName hcNe hcSlash)
    have hu2 : underDir other other = true := underDir_refl other hoFullNorm
    exact disjoint_underDir_mockJoin root otherName childName other hr hoNe hcNe hoSlash hcSlash hNe hu2 hu1
  have hDisjointP : ∀ k, P k → underDir other k = false := by
    intro k hk
    rcases hk with hChild | hRoot
    · cases hb : underDir other k with
      | false => rfl
      | true => exact absurd (disjoint_underDir_mockJoin root otherName childName k hr hoNe hcNe hoSlash hcSlash hNe hb hChild) False.elim
    · exact not_underDir_mockJoin_root root otherName k hr hoNe hoSlash hRoot
  have hSameState :
      NodesFilteredPres P s s ∧
      (child ∈ rep.removed.toList ↔ child ∈ rep.removed.toList) ∧
      (child ∈ rep.keptLocked.toList ↔ child ∈ rep.keptLocked.toList) ∧
      (child ∈ rep.keptFresh.toList ↔ child ∈ rep.keptFresh.toList) ∧
      (child ∈ rep.skipped.toList ↔ child ∈ rep.skipped.toList) ∧
      (rep.failed.isEmpty = false → rep.failed.isEmpty = false) ∧
      (∀ e ∈ rep.failed.toList, e ∈ rep.failed.toList) :=
    ⟨nodesFilteredPres_refl P s, Iff.rfl, Iff.rfl, Iff.rfl, Iff.rfl, id, fun _ h => h⟩
  have hPushFailed : ∀ err : TempDirError,
      NodesFilteredPres P s s ∧
      (child ∈ rep.removed.toList ↔ child ∈ rep.removed.toList) ∧
      (child ∈ rep.keptLocked.toList ↔ child ∈ rep.keptLocked.toList) ∧
      (child ∈ rep.keptFresh.toList ↔ child ∈ rep.keptFresh.toList) ∧
      (child ∈ rep.skipped.toList ↔ child ∈ rep.skipped.toList) ∧
      (rep.failed.isEmpty = false → (rep.failed.push err).isEmpty = false) ∧
      (∀ e ∈ rep.failed.toList, e ∈ (rep.failed.push err).toList) := by
    intro err
    refine ⟨nodesFilteredPres_refl P s, Iff.rfl, Iff.rfl, Iff.rfl, Iff.rfl, ?_, ?_⟩
    · intro _; simp
    · intro e he; simp [Array.toList_push, he]
  dsimp only [Internal.sweepEntry]
  rw [hOps.hJoin]
  by_cases hPref : (!dirPrefix.toList.isPrefixOf otherName.toList) = true
  · simp only [hPref, ↓reduceIte, stateM_pure_run]
    refine ⟨nodesFilteredPres_refl P s, trivial, trivial, trivial, ?_, id, fun _ h => h⟩
    dsimp only [other] at hOtherNeChild
    simp [Array.toList_push, hOtherNeChild.symm]
  · have hPrefF : (!dirPrefix.toList.isPrefixOf otherName.toList) = false := Bool.eq_false_iff.mpr hPref
    simp only [hPrefF, Bool.false_eq_true, ↓reduceIte]
    rw [stateM_bind_run, hOps.hLstat, mockFs_lstat_run]
    cases hlChild : mockLstatPure s other with
    | error fe =>
      dsimp only
      by_cases hnf : (fe.kind == .notFound) = true
      · simp only [hnf, ↓reduceIte, stateM_pure_run]
        exact ⟨nodesFilteredPres_refl P s, trivial, trivial, trivial, trivial, id, fun _ h => h⟩
      · simp only [Bool.eq_false_iff.mpr hnf, Bool.false_eq_true, ↓reduceIte, stateM_pure_run]
        refine ⟨nodesFilteredPres_refl P s, trivial, trivial, trivial, trivial, fun _ => by simp, fun e he => by simp [Array.toList_push, he]⟩
    | ok stChild =>
      dsimp only
      by_cases hNotDir : (stChild.kind != .dir) = true
      · simp only [hNotDir, ↓reduceIte, stateM_pure_run]
        refine ⟨nodesFilteredPres_refl P s, trivial, trivial, trivial, ?_, id, fun _ h => h⟩
        dsimp only [other] at hOtherNeChild
        simp [Array.toList_push, hOtherNeChild.symm]
      · simp only [Bool.eq_false_iff.mpr hNotDir, Bool.false_eq_true, ↓reduceIte]
        rw [stateM_bind_run, mockFs_lstat_run]
        cases hlLock : mockLstatPure s (mockJoin other ".lock") with
        | error fe =>
          dsimp only
          by_cases hnf : (fe.kind != .notFound) = true
          · simp only [hnf, ↓reduceIte, stateM_pure_run]
            refine ⟨nodesFilteredPres_refl P s, trivial, trivial, trivial, trivial, fun _ => by simp, fun e he => by simp [Array.toList_push, he]⟩
          · simp only [Bool.eq_false_iff.mpr hnf, Bool.false_eq_true, ↓reduceIte]
            by_cases hFresh : (nowSec - stChild.modifiedSec ≤ (maxAgeSec : Int))
            · simp only [hFresh, ↓reduceIte, stateM_pure_run]
              refine ⟨nodesFilteredPres_refl P s, trivial, trivial, ?_, trivial, id, fun _ h => h⟩
              dsimp only [other] at hOtherNeChild
              simp [Array.toList_push, hOtherNeChild.symm]
            · simp only [hFresh, ↓reduceIte]
              rw [stateM_bind_run]
              have hClean := cleanupDirIgnoringNotFound_filteredPres fs hOps.hRm other s
              cases hc : (Internal.cleanupDirIgnoringNotFound fs other).run s with
              | mk rc sc =>
                dsimp only at hClean ⊢
                rw [hc] at hClean
                dsimp only at hClean
                have hPres : NodesFilteredPres P s sc := nodesFilteredPres_mono hDisjointP hClean
                cases rc with
                | ok _ =>
                  rw [stateM_pure_run]
                  refine ⟨hPres, ?_, Iff.rfl, Iff.rfl, Iff.rfl, id, fun _ h => h⟩
                  dsimp only [other] at hOtherNeChild
                  simp [Array.toList_push, hOtherNeChild.symm]
                | error te =>
                  rw [stateM_pure_run]
                  refine ⟨hPres, Iff.rfl, Iff.rfl, Iff.rfl, Iff.rfl, ?_, ?_⟩
                  · intro _; simp
                  · intro e he; simp [Array.toList_push, he]
        | ok stLock =>
          dsimp only
          by_cases hNotFile : (stLock.kind != .file) = true
          · simp only [hNotFile, ↓reduceIte, stateM_pure_run]
            refine ⟨nodesFilteredPres_refl P s, trivial, trivial, trivial, trivial, fun _ => by simp, fun e he => by simp [Array.toList_push, he]⟩
          · simp only [Bool.eq_false_iff.mpr hNotFile, Bool.false_eq_true, ↓reduceIte]
            rw [stateM_bind_run, hOps.hTryWfl]
            obtain ⟨ndLock, hLookLock, hStLock⟩ := lookupNode_of_lstat_ok s (mockJoin other ".lock") stLock hlLock
            have hNotFileEq : stLock.kind = .file := by revert hNotFile; cases stLock.kind <;> decide
            have hLockNorm : normKey (mockJoin other ".lock") = mockJoin other ".lock" :=
              normKey_mockJoin other ".lock" (by decide) (by decide)
            cases ndLock with
            | dir _ _ => dsimp only [mockNodeStat] at hStLock; rw [← hStLock] at hNotFileEq; exact EntryKind.noConfusion hNotFileEq
            | symlink _ _ => dsimp only [mockNodeStat] at hStLock; rw [← hStLock] at hNotFileEq; exact EntryKind.noConfusion hNotFileEq
            | file ino c t m =>
              by_cases hConf : mockHasConflict s.locks ino .exclusive = true
              · rw [mockFs_tryWithFileLock_existing_conflict_run s (mockJoin other ".lock") .exclusive false ino c t m hLockNorm hLookLock hConf]
                dsimp only
                rw [stateM_pure_run]
                refine ⟨nodesFilteredPres_refl P s, Iff.rfl, ?_, Iff.rfl, Iff.rfl, id, fun _ h => h⟩
                dsimp only [other] at hOtherNeChild
                simp [Array.toList_push, hOtherNeChild.symm]
              · have hConfF : mockHasConflict s.locks ino .exclusive = false := Bool.eq_false_iff.mpr hConf
                rw [mockFs_tryWithFileLock_existing_ok_run s (mockJoin other ".lock") .exclusive false ino c t m hLockNorm hLookLock hConfF]
                dsimp only
                have hRemLock := removeLockedTempDir_filteredPres fs hOps other hoFullNe hoFullNorm hoFullSlash { s with locks := (ino, .exclusive) :: s.locks }
                cases hrl : (Internal.removeLockedTempDir fs other (mockJoin other ".lock")).run { s with locks := (ino, .exclusive) :: s.locks } with
                | mk rrl srl =>
                  dsimp only at hRemLock ⊢
                  rw [hrl] at hRemLock
                  dsimp only at hRemLock
                  have hLocksEq : srl.locks = (ino, .exclusive) :: s.locks := hRemLock.2.1
                  have hUnlocks : mockRemoveFirstLock ino .exclusive srl.locks = s.locks := by
                    rw [hLocksEq, mockRemoveFirstLock_head]
                  have hPres : NodesFilteredPres P s { srl with locks := mockRemoveFirstLock ino .exclusive srl.locks } := by
                    rcases hRemLock with ⟨⟨keep, hk, hn⟩, _, hi, ht, hs, hu⟩
                    refine ⟨⟨keep, fun k hkP => hk k (hDisjointP k hkP), hn⟩, hUnlocks, hi, ht, hs, hu⟩
                  cases rrl with
                  | error fe =>
                    dsimp only [Except.map]
                    by_cases hnf : (fe.kind == .notFound) = true
                    · simp only [hnf, ↓reduceIte, stateM_pure_run]
                      exact ⟨hPres, trivial, trivial, trivial, trivial, id, fun _ h => h⟩
                    · simp only [Bool.eq_false_iff.mpr hnf, Bool.false_eq_true, ↓reduceIte, stateM_pure_run]
                      refine ⟨hPres, trivial, trivial, trivial, trivial, ?_, ?_⟩
                      · intro _; simp
                      · intro e he; simp [Array.toList_push, he]
                  | ok rInner =>
                    dsimp only [Except.map]
                    cases rInner with
                    | ok _ =>
                      rw [stateM_pure_run]
                      refine ⟨hPres, ?_, Iff.rfl, Iff.rfl, Iff.rfl, id, fun _ h => h⟩
                      dsimp only [other] at hOtherNeChild
                      simp [Array.toList_push, hOtherNeChild.symm]
                    | error te =>
                      rw [stateM_pure_run]
                      refine ⟨hPres, Iff.rfl, Iff.rfl, Iff.rfl, Iff.rfl, ?_, ?_⟩
                      · intro _; simp
                      · intro e he; simp [Array.toList_push, he]

private theorem sweepEntries_append (fs : FsApiM (StateM TempDirMockState))
    (root dirPrefix : String) (maxAgeSec : Nat) (nowSec : Int)
    (rep : CleanupReport) (xs ys : List String) (s : TempDirMockState) :
    (Internal.sweepEntries fs root dirPrefix maxAgeSec nowSec rep (xs ++ ys)).run s =
      let (rep1, s1) := (Internal.sweepEntries fs root dirPrefix maxAgeSec nowSec rep xs).run s
      (Internal.sweepEntries fs root dirPrefix maxAgeSec nowSec rep1 ys).run s1 := by
  induction xs generalizing rep s with
  | nil => rfl
  | cons x xs ih =>
    dsimp only [List.cons_append, Internal.sweepEntries]
    rw [stateM_bind_run, stateM_bind_run]
    cases hStep : (Internal.sweepEntry fs root dirPrefix maxAgeSec nowSec rep x).run s with
    | mk rep1 s1 => exact ih rep1 s1

private theorem sweepEntries_other_preserves
    (fs : FsApiM (StateM TempDirMockState)) (hOps : SweepFsOps fs)
    (root dirPrefix childName : String) (maxAgeSec : Nat) (nowSec : Int)
    (hr : root ≠ "") (hcV : pValidEntryName childName = true)
    (names : List String) (hValid : ∀ nm ∈ names, pValidEntryName nm = true) (hNotIn : childName ∉ names)
    (rep : CleanupReport) (s : TempDirMockState) :
    let child := mockJoin root childName
    let P : String → Prop := fun k => underDir child k = true ∨ normKey k = normKey root
    let (rep', s') := (Internal.sweepEntries fs root dirPrefix maxAgeSec nowSec rep names).run s
    NodesFilteredPres P s s' ∧
    (child ∈ rep'.removed.toList ↔ child ∈ rep.removed.toList) ∧
    (child ∈ rep'.keptLocked.toList ↔ child ∈ rep.keptLocked.toList) ∧
    (child ∈ rep'.keptFresh.toList ↔ child ∈ rep.keptFresh.toList) ∧
    (child ∈ rep'.skipped.toList ↔ child ∈ rep.skipped.toList) ∧
    (rep.failed.isEmpty = false → rep'.failed.isEmpty = false) ∧
    (∀ e ∈ rep.failed.toList, e ∈ rep'.failed.toList) := by
  induction names generalizing rep s with
  | nil =>
    dsimp only [Internal.sweepEntries]
    rw [stateM_pure_run]
    exact ⟨nodesFilteredPres_refl _ s, Iff.rfl, Iff.rfl, Iff.rfl, Iff.rfl, id, fun _ h => h⟩
  | cons nm rest ih =>
    have hnmV : pValidEntryName nm = true := hValid nm (List.mem_cons_self)
    have hrestV : ∀ x ∈ rest, pValidEntryName x = true := fun x hx => hValid x (List.mem_cons_of_mem nm hx)
    have hNe : nm ≠ childName := fun h => hNotIn (h ▸ List.mem_cons_self)
    have hRestNotIn : childName ∉ rest := fun h => hNotIn (List.mem_cons_of_mem nm h)
    dsimp only [Internal.sweepEntries]
    rw [stateM_bind_run]
    have hStep := sweepEntry_other_preserves fs hOps root dirPrefix childName nm maxAgeSec nowSec hr hcV hnmV hNe rep s
    cases h1 : (Internal.sweepEntry fs root dirPrefix maxAgeSec nowSec rep nm).run s with
    | mk rep1 s1 =>
      dsimp only at hStep ⊢
      rw [h1] at hStep
      dsimp only at hStep
      have hTail := ih hrestV hRestNotIn rep1 s1
      cases h2 : (Internal.sweepEntries fs root dirPrefix maxAgeSec nowSec rep1 rest).run s1 with
      | mk rep2 s2 =>
        dsimp only at hTail ⊢
        rw [h2] at hTail
        dsimp only at hTail
        exact ⟨nodesFilteredPres_trans hStep.1 hTail.1,
          hTail.2.1.trans hStep.2.1,
          hTail.2.2.1.trans hStep.2.2.1,
          hTail.2.2.2.1.trans hStep.2.2.2.1,
          hTail.2.2.2.2.1.trans hStep.2.2.2.2.1,
          fun h => hTail.2.2.2.2.2.1 (hStep.2.2.2.2.2.1 h),
          fun e he => hTail.2.2.2.2.2.2 e (hStep.2.2.2.2.2.2 e he)⟩

private theorem cleanupStaleTempDirs_split_exec
    (fs : FsApiM (StateM TempDirMockState)) (hOps : SweepFsOps fs)
    (s₀ : TempDirMockState) (root dirPrefix childName : String) (maxAgeSec : Nat)
    (hvr : pValidRoot root = true) (hvp : pValidPrefix dirPrefix = true) (hcV : pValidEntryName childName = true)
    (stRoot : FileStat) (hRoot : mockStatPure s₀ root = .ok stRoot) (hRwx : pHasRwx stRoot)
    (ndChild : MockNode) (hChild : lookupNode s₀.nodes (mockJoin root childName) = some ndChild) :
    let child := mockJoin root childName
    let nowSec := (mockTime.nowTimestamp.run s₀).1.toSecondsSinceUnixEpoch.val
    let P : String → Prop := fun k => underDir child k = true ∨ normKey k = normKey root
    ∃ before after : List String, ∃ repBefore : CleanupReport, ∃ sBefore : TempDirMockState,
      (∀ nm ∈ before, pValidEntryName nm = true) ∧
      (∀ nm ∈ after, pValidEntryName nm = true) ∧
      childName ∉ before ∧
      childName ∉ after ∧
      NodesFilteredPres P s₀ sBefore ∧
      (child ∈ repBefore.removed.toList ↔ False) ∧
      (child ∈ repBefore.keptLocked.toList ↔ False) ∧
      (child ∈ repBefore.keptFresh.toList ↔ False) ∧
      (child ∈ repBefore.skipped.toList ↔ False) ∧
      (∀ (repMid : CleanupReport) (sMid : TempDirMockState),
        (Internal.sweepEntry fs root dirPrefix maxAgeSec nowSec repBefore childName).run sBefore = (repMid, sMid) →
        let (repAfter, sFinal) := (Internal.sweepEntries fs root dirPrefix maxAgeSec nowSec repMid after).run sMid
        let finalRep : CleanupReport :=
          { removed := (Internal.sortStrings repAfter.removed.toList).toArray
            keptLocked := (Internal.sortStrings repAfter.keptLocked.toList).toArray
            keptFresh := (Internal.sortStrings repAfter.keptFresh.toList).toArray
            skipped := (Internal.sortStrings repAfter.skipped.toList).toArray
            failed := repAfter.failed }
        ((Internal.mkApiM fs mockTime mockUuid mockEnv).cleanupStaleTempDirs (some root) dirPrefix maxAgeSec).run s₀ =
          (.ok finalRep, sFinal) ∧
        NodesFilteredPres P sMid sFinal ∧
        (pHasPath finalRep.removed child ↔ child ∈ repMid.removed.toList) ∧
        (pHasPath finalRep.keptLocked child ↔ child ∈ repMid.keptLocked.toList) ∧
        (pHasPath finalRep.keptFresh child ↔ child ∈ repMid.keptFresh.toList) ∧
        (pHasPath finalRep.skipped child ↔ child ∈ repMid.skipped.toList) ∧
        (repMid.failed.isEmpty = false → finalRep.failed.isEmpty = false) ∧
        (∀ e ∈ repMid.failed.toList, e ∈ finalRep.failed.toList)) := by
  intro child nowSec P
  have hrNe : root ≠ "" := validRoot_ne_empty root hvr
  have ⟨hListRun, hListNd, hListValid⟩ := mockFs_listDir_run_of_rwx s₀ root stRoot hRoot hRwx
  have hMem : childName ∈ Internal.sortStrings (eraseDupStrings (s₀.nodes.filterMap (fun e => mockParentChild (normKey root) e.1))) :=
    mockFs_listDir_mem_of_lookupNode s₀ root childName hrNe hcV ndChild hChild
  obtain ⟨before, after, hSplit, hNotBefore, hNotAfter⟩ := list_nodup_split _ childName hListNd hMem
  have hBeforeV : ∀ nm ∈ before, pValidEntryName nm = true := fun nm hnm =>
    hListValid nm (by rw [hSplit]; exact List.mem_append_left _ hnm)
  have hAfterV : ∀ nm ∈ after, pValidEntryName nm = true := fun nm hnm =>
    hListValid nm (by rw [hSplit]; exact List.mem_append_right _ (List.mem_cons_of_mem childName hnm))
  have hBeforePres := sweepEntries_other_preserves fs hOps root dirPrefix childName maxAgeSec nowSec hrNe hcV
    before hBeforeV hNotBefore {} s₀
  cases hBeforeRun : (Internal.sweepEntries fs root dirPrefix maxAgeSec nowSec {} before).run s₀ with
  | mk repBefore sBefore =>
    dsimp only at hBeforePres
    rw [hBeforeRun] at hBeforePres
    dsimp only at hBeforePres
    refine ⟨before, after, repBefore, sBefore, hBeforeV, hAfterV, hNotBefore, hNotAfter,
      hBeforePres.1, ?_, ?_, ?_, ?_, ?_⟩
    · simpa using hBeforePres.2.1
    · simpa using hBeforePres.2.2.1
    · simpa using hBeforePres.2.2.2.1
    · simpa using hBeforePres.2.2.2.2.1
    · intro repMid sMid hMid
      have hAfterPres := sweepEntries_other_preserves fs hOps root dirPrefix childName maxAgeSec nowSec hrNe hcV
        after hAfterV hNotAfter repMid sMid
      cases hAfterRun : (Internal.sweepEntries fs root dirPrefix maxAgeSec nowSec repMid after).run sMid with
      | mk repAfter sFinal =>
        dsimp only at hAfterPres ⊢
        rw [hAfterRun] at hAfterPres
        dsimp only at hAfterPres
        have hRunClean :
            ((Internal.mkApiM fs mockTime mockUuid mockEnv).cleanupStaleTempDirs (some root) dirPrefix maxAgeSec).run s₀ =
              (.ok { removed := (Internal.sortStrings repAfter.removed.toList).toArray
                     keptLocked := (Internal.sortStrings repAfter.keptLocked.toList).toArray
                     keptFresh := (Internal.sortStrings repAfter.keptFresh.toList).toArray
                     skipped := (Internal.sortStrings repAfter.skipped.toList).toArray
                     failed := repAfter.failed }, sFinal) := by
          rw [mkApiM_cleanupStaleTempDirs_eq]
          dsimp only [Internal.cleanupStaleTempDirsM, Internal.validPrefix]
          have hResRoot : (Internal.resolveRoot fs mockEnv (some root)).run s₀ = (.ok root, s₀) := by
            dsimp only [Internal.resolveRoot, Internal.validRoot]
            rw [stateM_bind_run, stateM_pure_run]
            dsimp only
            have hvr' : (!root.isEmpty && !(Char.ofNat 0 ∈ root.toList)) = true := hvr
            simp only [hvr', Bool.not_true, Bool.false_eq_true, ↓reduceIte]
            rw [stateM_bind_run, hOps.hStat, mockFs_stat_run, hRoot]
            dsimp only
            simp only [hRwx.1, show (EntryKind.dir != EntryKind.dir) = false from rfl,
              Bool.false_eq_true, ↓reduceIte, stateM_pure_run]
          have hvp' : (!dirPrefix.isEmpty && dirPrefix.toList.head? != some '.' && !('/' ∈ dirPrefix.toList) && !(Char.ofNat 0 ∈ dirPrefix.toList)) = true := hvp
          simp only [hvp', Bool.not_true, Bool.false_eq_true, ↓reduceIte]
          rw [stateM_bind_run, hResRoot]
          dsimp only
          rw [stateM_bind_run]
          have hNowState : (mockTime.nowTimestamp.run s₀).2 = s₀ := rfl
          cases hTime : mockTime.nowTimestamp.run s₀ with
          | mk nowTs sTime =>
            have hsTime : sTime = s₀ := by rw [← hNowState, hTime]
            subst sTime
            have hNowEq : nowTs.toSecondsSinceUnixEpoch.val = nowSec := by
              dsimp only [nowSec]
              rw [hTime]
            dsimp only
            rw [stateM_bind_run, hOps.hListDir, hListRun]
            dsimp only
            rw [hNowEq, stateM_bind_run, hSplit, sweepEntries_append, hBeforeRun]
            dsimp only [Internal.sweepEntries]
            rw [stateM_bind_run, hMid]
            dsimp only
            rw [hAfterRun]
            dsimp only
            exact stateM_pure_run _ _
        refine ⟨hRunClean, hAfterPres.1, ?_, ?_, ?_, ?_, hAfterPres.2.2.2.2.2.1, hAfterPres.2.2.2.2.2.2⟩
        · simpa [hasPath_toArray_mem, mem_sortStrings] using hAfterPres.2.1
        · simpa [hasPath_toArray_mem, mem_sortStrings] using hAfterPres.2.2.1
        · simpa [hasPath_toArray_mem, mem_sortStrings] using hAfterPres.2.2.2.1
        · simpa [hasPath_toArray_mem, mem_sortStrings] using hAfterPres.2.2.2.2.1

private theorem list_find_filter_none {α : Type} (p : α → Bool) (keep : α → Bool) (xs : List α)
    (h : xs.find? p = none) : (xs.filter keep).find? p = none := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.find?_cons] at h
    cases hpx : p x with
    | true => simp [hpx] at h
    | false =>
      rw [hpx] at h
      dsimp only at h
      by_cases hk : keep x = true
      · rw [List.filter_cons, hk]; simp [hpx, ih h]
      · have hkf : keep x = false := Bool.eq_false_iff.mpr hk
        rw [List.filter_cons, hkf]; exact ih h

private theorem nodesFilteredPres_lookupNode_none {P : String → Prop} {s s' : TempDirMockState}
    (hPres : NodesFilteredPres P s s') (p : String)
    (hNone : lookupNode s.nodes p = none) :
    lookupNode s'.nodes p = none := by
  rcases hPres with ⟨⟨keep, _, hn⟩, _⟩
  unfold lookupNode at hNone ⊢
  rw [hn]
  exact congrArg (Option.map Prod.snd) (list_find_filter_none _ _ s.nodes (by
    cases hf : s.nodes.find? (fun e => normKey e.1 == normKey p) with
    | none => rfl
    | some _ => simp [hf] at hNone))

private theorem nodesFilteredPres_lstat {P : String → Prop} {s s' : TempDirMockState}
    (hPres : NodesFilteredPres P s s') (p : String)
    (hp : ∀ k, normKey k = normKey p → P k) :
    (mockFs.lstat p).run s' = (((mockFs.lstat p).run s).1, s') := by
  have hLook := nodesFilteredPres_lookupNode hPres p hp
  simp only [mockFs_lstat_run, mockLstatPure, hLook]

private theorem nodesFilteredPres_child_P {root childName : String}
    (hcV : pValidEntryName childName = true) :
    let child := mockJoin root childName
    let lockPath := mockJoin child ".lock"
    let P : String → Prop := fun k => underDir child k = true ∨ normKey k = normKey root
    (∀ k, normKey k = normKey child → P k) ∧
    (∀ k, underDir child k = true → P k) ∧
    (∀ k, normKey k = normKey lockPath → P k) ∧
    (∀ k, normKey k = normKey root → P k) := by
  have ⟨hcNe, _, _, hcSlash⟩ := validEntryName_parts childName hcV
  have hChildNorm : normKey (mockJoin root childName) = mockJoin root childName :=
    normKey_mockJoin root childName hcNe hcSlash
  have hChildNe : mockJoin root childName ≠ "" := mockJoin_ne_empty root childName hcNe
  have hChildNeSlash : mockJoin root childName ≠ "/" := by
    by_cases hRoot : root = ""
    · subst hRoot
      intro hEq
      have hJ : mockJoin "" childName = childName := rfl
      rw [hJ] at hEq
      rw [hEq] at hcSlash
      exact hcSlash (by decide)
    · exact mockJoin_ne_slash root childName hRoot hcNe
  have hUnderLock : underDir (mockJoin root childName) (mockJoin (mockJoin root childName) ".lock") = true :=
    underDir_mockJoin_self (mockJoin root childName) ".lock" hChildNe hChildNorm hChildNeSlash (by decide) (by decide)
  refine ⟨?_, fun k hk => Or.inl hk, ?_, fun k hk => Or.inr hk⟩
  · intro k hk
    refine Or.inl ?_
    rw [underDir_eq_of_normKey_eq _ k (mockJoin root childName) hk]
    exact underDir_refl _ hChildNorm
  · intro k hk
    refine Or.inl ?_
    rw [underDir_eq_of_normKey_eq _ k (mockJoin (mockJoin root childName) ".lock") hk]
    exact hUnderLock

private theorem disjoint_mockJoin_entry_target {dir nm tgt : String}
    (hdNe : dir ≠ "") (hnmV : pValidEntryName nm = true) (htV : pValidEntryName tgt = true) (hNe : nm ≠ tgt) :
    ∀ k, normKey k = normKey (mockJoin dir tgt) →
      underDir (mockJoin dir nm) k = false ∧ normKey k ≠ normKey (mockJoin dir nm) := by
  have ⟨hnmNe, _, _, hnmSlash⟩ := validEntryName_parts nm hnmV
  have ⟨htNe, _, _, htSlash⟩ := validEntryName_parts tgt htV
  have htNorm : normKey (mockJoin dir tgt) = mockJoin dir tgt := normKey_mockJoin dir tgt htNe htSlash
  have hnmNorm : normKey (mockJoin dir nm) = mockJoin dir nm := normKey_mockJoin dir nm hnmNe hnmSlash
  intro k hk
  have hNotUnder : underDir (mockJoin dir nm) k = false := by
    cases hb : underDir (mockJoin dir nm) k with
    | false => rfl
    | true =>
      exfalso
      have hSub : underDir (mockJoin dir nm) (mockJoin dir tgt) = true := by
        rwa [← underDir_eq_of_normKey_eq _ k (mockJoin dir tgt) hk]
      have hu2 : underDir (mockJoin dir tgt) (mockJoin dir tgt) = true := underDir_refl _ htNorm
      exact disjoint_underDir_mockJoin dir nm tgt (mockJoin dir tgt) hdNe hnmNe htNe hnmSlash htSlash hNe hSub hu2
  have hNotEq : normKey k ≠ normKey (mockJoin dir nm) := by
    intro hEq
    have hSub : underDir (mockJoin dir nm) (mockJoin dir tgt) = true := by
      rw [← underDir_eq_of_normKey_eq _ k (mockJoin dir tgt) hk]
      rw [underDir_eq_of_normKey_eq _ k (mockJoin dir nm) hEq]
      exact underDir_refl _ hnmNorm
    have hu2 : underDir (mockJoin dir tgt) (mockJoin dir tgt) = true := underDir_refl _ htNorm
    exact disjoint_underDir_mockJoin dir nm tgt (mockJoin dir tgt) hdNe hnmNe htNe hnmSlash htSlash hNe hSub hu2
  exact ⟨hNotUnder, hNotEq⟩

private theorem removeNonLockChildren_fail_with_lock_intact
    (child payload : String) (hcNe : child ≠ "")
    (hPayEq : payload = mockJoin child "locked_child.txt")
    (fs : FsApiM (StateM TempDirMockState))
    (hLstat : fs.lstat = mockFs.lstat) (hJoin : fs.join = mockJoin) (hRm : fs.rmtree = mockFs.rmtree)
    (hUnl : ∀ p miss s,
      (fs.unlink p miss).run s =
        if p == payload then (.error { kind := .permissionDenied, path := some p, message := "cannot unlink" }, s)
        else (mockFs.unlink p miss).run s)
    (names : List String) (hValid : ∀ nm ∈ names, pValidEntryName nm = true) (hNd : names.Nodup)
    (hPayMem : "locked_child.txt" ∈ names) (s : TempDirMockState)
    (hPayNode : ∃ ino c t m, lookupNode s.nodes payload = some (.file ino c t m)) :
    let lockPath := mockJoin child ".lock"
    ∃ te s', (Internal.removeNonLockChildren fs child names).run s = (.error te, s') ∧
      NodesFilteredPres (fun k => normKey k = normKey lockPath) s s' := by
  intro lockPath
  induction names generalizing s with
  | nil => cases hPayMem
  | cons nm rest ih =>
    have hnmV : pValidEntryName nm = true := hValid nm List.mem_cons_self
    have hrestV : ∀ x ∈ rest, pValidEntryName x = true := fun x hx => hValid x (List.mem_cons_of_mem nm hx)
    have ⟨_, hRestNd⟩ := List.nodup_cons.mp hNd
    dsimp only [Internal.removeNonLockChildren]
    by_cases hLock : nm = ".lock"
    · subst hLock
      have hPayInRest : "locked_child.txt" ∈ rest := by
        simp only [List.mem_cons] at hPayMem
        rcases hPayMem with hEq | hMem
        · exact absurd hEq (by decide)
        · exact hMem
      simpa using ih hrestV hRestNd hPayInRest s hPayNode
    · have hLockBne : (nm == ".lock") = false := beq_false_of_ne hLock
      simp only [hLockBne, Bool.false_eq_true, ↓reduceIte, hJoin]
      rw [stateM_bind_run, hLstat, mockFs_lstat_run]
      by_cases hIsPay : nm = "locked_child.txt"
      · subst hIsPay
        rw [← hPayEq]
        rcases hPayNode with ⟨ino, c, t, m, hLookPay⟩
        have hPayLstat : mockLstatPure s payload = .ok (mockNodeStat (.file ino c t m)) := by
          unfold mockLstatPure; rw [hLookPay]
        rw [hPayLstat]
        dsimp only
        have hNotDir : ((mockNodeStat (.file ino c t m)).kind == EntryKind.dir) = false := rfl
        simp only [hNotDir, Bool.false_eq_true, ↓reduceIte]
        rw [stateM_bind_run, hUnl payload true s]
        simp only [beq_self_eq_true, ↓reduceIte]
        exact ⟨_, s, stateM_pure_run _ _, nodesFilteredPres_refl _ s⟩
      · have hPayInRest : "locked_child.txt" ∈ rest := by
          simp only [List.mem_cons] at hPayMem
          rcases hPayMem with hEq | hMem
          · exact absurd hEq.symm hIsPay
          · exact hMem
        have hDisjLock := disjoint_mockJoin_entry_target (dir := child) hcNe hnmV (by decide) hLock
        have hDisjPay := disjoint_mockJoin_entry_target (dir := child) hcNe hnmV (by decide) hIsPay
        have hUnlMock : ∀ miss s1, (fs.unlink (mockJoin child nm) miss).run s1 = (mockFs.unlink (mockJoin child nm) miss).run s1 := by
          intro miss s1
          rw [hUnl]
          have hNePay : (mockJoin child nm == payload) = false := by
            rw [hPayEq, beq_false_of_ne]
            have ⟨_, hNe⟩ := hDisjPay (mockJoin child "locked_child.txt") rfl
            exact fun h => hNe (congrArg normKey h.symm)
          rw [hNePay]; rfl
        have hUnlOps : ∀ p miss s1,
            (fs.unlink p miss).run s1 = (mockFs.unlink p miss).run s1 ∨ ∃ fe, (fs.unlink p miss).run s1 = (.error fe, s1) := by
          intro p miss s1
          rw [hUnl]; split; exact Or.inr ⟨_, rfl⟩; exact Or.inl rfl
        cases hl : mockLstatPure s (mockJoin child nm) with
        | error fe =>
          dsimp only
          by_cases hnf : (fe.kind == .notFound) = true
          · simp only [hnf, ↓reduceIte]
            exact ih hrestV hRestNd hPayInRest s hPayNode
          · simp only [Bool.eq_false_iff.mpr hnf, Bool.false_eq_true, ↓reduceIte]
            exact ⟨_, s, stateM_pure_run _ _, nodesFilteredPres_refl _ s⟩
        | ok st =>
          dsimp only
          by_cases hDir : (st.kind == .dir) = true
          · simp only [hDir, ↓reduceIte]
            rw [stateM_bind_run]
            have h1 := cleanupDirIgnoringNotFound_filteredPres fs hRm (mockJoin child nm) s
            cases hc : (Internal.cleanupDirIgnoringNotFound fs (mockJoin child nm)).run s with
            | mk rc sc =>
              dsimp only at h1 ⊢
              rw [hc] at h1
              dsimp only at h1
              have hPresLock := nodesFilteredPres_mono (fun k hk => (hDisjLock k hk).1) h1
              have hPresPay := nodesFilteredPres_mono (fun k hk => (hDisjPay k (by rwa [← hPayEq])).1) h1
              cases rc with
              | error te => exact ⟨te, sc, stateM_pure_run _ _, hPresLock⟩
              | ok _ =>
                have hPaySc : ∃ ino c t m, lookupNode sc.nodes payload = some (.file ino c t m) := by
                  rcases hPayNode with ⟨ino, c, t, m, hLookPay⟩
                  exact ⟨ino, c, t, m, by rw [nodesFilteredPres_lookupNode hPresPay payload (fun _ hk => hk), hLookPay]⟩
                obtain ⟨te, s', hRec, hPresRec⟩ := ih hrestV hRestNd hPayInRest sc hPaySc
                exact ⟨te, s', hRec, nodesFilteredPres_trans hPresLock hPresRec⟩
          · have hDirF : (st.kind == .dir) = false := Bool.eq_false_iff.mpr hDir
            simp only [hDirF, Bool.false_eq_true, ↓reduceIte]
            rw [stateM_bind_run]
            have h1 := unlink_filteredPres fs hUnlOps (mockJoin child nm) true s
            cases hu : (fs.unlink (mockJoin child nm) true).run s with
            | mk ru su =>
              dsimp only at h1 ⊢
              rw [hu] at h1
              dsimp only at h1
              have hPresLock := nodesFilteredPres_mono (fun k hk => (hDisjLock k hk).2) h1
              have hPresPay := nodesFilteredPres_mono (fun k hk => (hDisjPay k (by rwa [← hPayEq])).2) h1
              cases ru with
              | error fe =>
                dsimp only
                rw [stateM_bind_run, stateM_pure_run]
                dsimp only
                rw [stateM_pure_run]
                exact ⟨_, su, stateM_pure_run _ _, hPresLock⟩
              | ok _ =>
                rw [stateM_bind_run, stateM_pure_run]
                dsimp only
                have hPaySu : ∃ ino c t m, lookupNode su.nodes payload = some (.file ino c t m) := by
                  rcases hPayNode with ⟨ino, c, t, m, hLookPay⟩
                  exact ⟨ino, c, t, m, by rw [nodesFilteredPres_lookupNode hPresPay payload (fun _ hk => hk), hLookPay]⟩
                obtain ⟨te, s', hRec, hPresRec⟩ := ih hrestV hRestNd hPayInRest su hPaySu
                exact ⟨te, s', hRec, nodesFilteredPres_trans hPresLock hPresRec⟩

/-- Spec 11: `cleanupStaleTempDirs` keeps any matching directory with an active lock regardless of age. -/
theorem proof_tempdir_cleanupStaleTempDirs_liveLockKeptRegardlessOfAge :
    AllPass (test_tempdir_cleanupStaleTempDirs_liveLockKeptRegardlessOfAge
      (S := TempDirMockState) Internal.mkApiM mockFs mockTime mockUuid mockEnv) := by
  dsimp only [test_tempdir_cleanupStaleTempDirs_liveLockKeptRegardlessOfAge, AllPass]
  intro s₀ root dirPrefix childName maxAgeSec ⟨hvr, hvp⟩ hcV hPref ⟨stRoot, hRoot, hRwx⟩ ⟨stChild, hChild, hcDir⟩ ⟨stLock, hLock, hlFile⟩
  have hRootPure : mockStatPure s₀ root = .ok stRoot := by rw [mockFs_stat_run] at hRoot; exact hRoot
  have hChildPure : mockLstatPure s₀ (mockFs.join root childName) = .ok stChild := by
    rw [mockFs_lstat_run] at hChild; exact hChild
  have hLockPure : mockLstatPure s₀ (mockFs.join (mockFs.join root childName) ".lock") = .ok stLock := by
    rw [mockFs_lstat_run] at hLock; exact hLock
  rw [mockFs_join_eq] at hChildPure hLockPure ⊢
  dsimp only [mockTime]
  rw [stateM_bind_run, stateM_get_run, stateM_pure_run]
  dsimp only
  rw [mockFs_lstat_run, hChildPure]
  dsimp only
  rw [allPass_assume]
  intro _
  have hrNe : root ≠ "" := validRoot_ne_empty root hvr
  have ⟨hcNe, _, _, hcSlash⟩ := validEntryName_parts childName hcV
  let child := mockJoin root childName
  let lockPath := mockJoin child ".lock"
  have hChildNorm : normKey child = child := normKey_mockJoin root childName hcNe hcSlash
  have hLockNorm : normKey lockPath = lockPath := normKey_mockJoin child ".lock" (by decide) (by decide)
  obtain ⟨ndChild, hLookChild, _⟩ := lookupNode_of_lstat_ok s₀ child stChild hChildPure
  obtain ⟨ndLock, hLookLock, hStLock⟩ := lookupNode_of_lstat_ok s₀ lockPath stLock hLockPure
  cases ndLock with
  | dir _ _ => simp [mockNodeStat] at hStLock; rw [← hStLock] at hlFile; cases hlFile
  | symlink _ _ => simp [mockNodeStat] at hStLock; rw [← hStLock] at hlFile; cases hlFile
  | file lockIno lockC lockT lockM =>
    by_cases hConf : mockHasConflict s₀.locks lockIno .shared = true
    · rw [mockFs_withFileLock_existing_conflict_run s₀ lockPath .shared false lockIno lockC lockT lockM hLockNorm hLookLock hConf]
      dsimp only
      intro hFalse; cases hFalse
    · have hConfF : mockHasConflict s₀.locks lockIno .shared = false := Bool.eq_false_iff.mpr hConf
      let sLock : TempDirMockState := { s₀ with locks := (lockIno, .shared) :: s₀.locks }
      have hRootLock : mockStatPure sLock root = .ok stRoot := hRootPure
      have hChildLock : lookupNode sLock.nodes child = some ndChild := hLookChild
      have hChildLockPure : mockLstatPure sLock child = .ok stChild := hChildPure
      have hLockLockPure : mockLstatPure sLock lockPath = .ok stLock := hLockPure
      have hLookLockLock : lookupNode sLock.nodes lockPath = some (.file lockIno lockC lockT lockM) := hLookLock
      obtain ⟨before, after, repBefore, sBefore, _, _, _, _, hBeforePres, hNotRmB, hNotKLB, _, _, hExec⟩ :=
        cleanupStaleTempDirs_split_exec mockFs sweepFsOps_mockFs sLock root dirPrefix childName maxAgeSec
          hvr hvp hcV stRoot hRootLock hRwx ndChild hChildLock
      obtain ⟨hPChild, _, hPLock, _⟩ := nodesFilteredPres_child_P (root := root) hcV
      have hLocksBefore : sBefore.locks = sLock.locks := hBeforePres.2.1
      have hLstatChildBefore : (mockFs.lstat child).run sBefore = (.ok stChild, sBefore) := by
        rw [nodesFilteredPres_lstat hBeforePres child hPChild, mockFs_lstat_run]
        dsimp only
        rw [hChildLockPure]
      have hLstatLockBefore : (mockFs.lstat lockPath).run sBefore = (.ok stLock, sBefore) := by
        rw [nodesFilteredPres_lstat hBeforePres lockPath hPLock, mockFs_lstat_run]
        dsimp only
        rw [hLockLockPure]
      have hLookLockBefore : lookupNode sBefore.nodes lockPath = some (.file lockIno lockC lockT lockM) := by
        rw [nodesFilteredPres_lookupNode hBeforePres lockPath hPLock]; exact hLookLockLock
      have hConfExclBefore : mockHasConflict sBefore.locks lockIno .exclusive = true := by
        rw [hLocksBefore]; simp [sLock, mockHasConflict]; exact Or.inl (Or.inl rfl)
      let nowSec := (mockTime.nowTimestamp.run sLock).1.toSecondsSinceUnixEpoch.val
      let repMid : CleanupReport := { repBefore with keptLocked := repBefore.keptLocked.push child }
      have hSweepMid : (Internal.sweepEntry mockFs root dirPrefix maxAgeSec nowSec repBefore childName).run sBefore =
          (repMid, sBefore) := by
        dsimp only [Internal.sweepEntry]
        rw [mockFs_join_eq]
        dsimp only [child, lockPath] at hLstatChildBefore hLstatLockBefore hLookLockBefore
        have hPrefF : (!dirPrefix.toList.isPrefixOf childName.toList) = false := by simp [hPref]
        simp only [hPrefF, Bool.false_eq_true, ↓reduceIte]
        rw [stateM_bind_run, hLstatChildBefore]
        dsimp only
        have hcDirF : (stChild.kind != EntryKind.dir) = false := by rw [hcDir]; rfl
        simp only [hcDirF, Bool.false_eq_true, ↓reduceIte]
        rw [stateM_bind_run, hLstatLockBefore]
        dsimp only
        have hlFileF : (stLock.kind != EntryKind.file) = false := by rw [hlFile]; rfl
        simp only [hlFileF, Bool.false_eq_true, ↓reduceIte]
        rw [stateM_bind_run, mockFs_tryWithFileLock_existing_conflict_run sBefore (mockJoin (mockJoin root childName) ".lock") .exclusive false
          lockIno lockC lockT lockM hLockNorm hLookLockBefore hConfExclBefore]
        exact stateM_pure_run _ _
      obtain ⟨hCleanRun, hAfterPres, hRmIff, hKLIff, _, _, _, _⟩ := hExec repMid sBefore hSweepMid
      let sFinal := (Internal.sweepEntries mockFs root dirPrefix maxAgeSec nowSec repMid after).run sBefore |>.2
      let repAfter := (Internal.sweepEntries mockFs root dirPrefix maxAgeSec nowSec repMid after).run sBefore |>.1
      let finalRep : CleanupReport :=
        { removed := (Internal.sortStrings repAfter.removed.toList).toArray
          keptLocked := (Internal.sortStrings repAfter.keptLocked.toList).toArray
          keptFresh := (Internal.sortStrings repAfter.keptFresh.toList).toArray
          skipped := (Internal.sortStrings repAfter.skipped.toList).toArray
          failed := repAfter.failed }
      have hTotPres : NodesFilteredPres (fun k => underDir child k = true ∨ normKey k = normKey root) sLock sFinal :=
        nodesFilteredPres_trans hBeforePres hAfterPres
      have hLookLockFin : lookupNode sFinal.nodes lockPath = some (.file lockIno lockC lockT lockM) := by
        rw [nodesFilteredPres_lookupNode hTotPres lockPath hPLock]; exact hLookLockLock
      have hConfExclFin : mockHasConflict sFinal.locks lockIno .exclusive = true := by
        rw [hTotPres.2.1]; simp [sLock, mockHasConflict]; exact Or.inl (Or.inl rfl)
      have hProbeRun : (mockFs.tryWithFileLock lockPath .exclusive false (pure (.ok ()))).run sFinal = (.ok none, sFinal) :=
        mockFs_tryWithFileLock_existing_conflict_run sFinal lockPath .exclusive false
          lockIno lockC lockT lockM hLockNorm hLookLockFin hConfExclFin (pure (.ok ()))
      have hLstatFin : (mockFs.lstat child).run sFinal = (.ok stChild, sFinal) := by
        rw [nodesFilteredPres_lstat hTotPres child hPChild, mockFs_lstat_run]
        dsimp only
        rw [hChildLockPure]
      have hBody :
          (do
            let rep ← (Internal.mkApiM mockFs mockTime mockUuid mockEnv).cleanupStaleTempDirs (some root) dirPrefix maxAgeSec
            let innerProbe ← mockFs.tryWithFileLock lockPath .exclusive false (pure (.ok ()))
            let stillExists ← mockFs.lstat child
            return (.ok (rep, innerProbe, stillExists.isOk) : Except FsError _)).run sLock =
          ((.ok (.ok finalRep, .ok none, true) : Except FsError _), { sFinal with locks := sFinal.locks }) := by
        dsimp only [child, lockPath, sFinal, finalRep, nowSec] at hProbeRun hLstatFin hCleanRun ⊢
        rw [stateM_bind_run, hCleanRun]
        dsimp only
        rw [stateM_bind_run]
        erw [hProbeRun]
        dsimp only
        rw [stateM_bind_run]
        erw [hLstatFin]
        dsimp only
        exact stateM_pure_run _ _
      rw [mockFs_withFileLock_existing_ok_run s₀ lockPath .shared false lockIno lockC lockT lockM hLockNorm hLookLock hConfF]
      dsimp only [sLock, lockPath, child] at hBody ⊢
      erw [hBody]
      dsimp only
      rw [allPass_assert, allPass_assert_end]
      have hKLMem : child ∈ repMid.keptLocked.toList := by simp [repMid, Array.toList_push]
      have hNotRmMem : ¬ (child ∈ repMid.removed.toList) := hNotRmB.mp
      exact ⟨⟨hKLIff.mpr hKLMem, fun h => hNotRmMem (hRmIff.mp h)⟩, ⟨rfl, rfl⟩, trivial⟩

/-- Non-vacuity `CanReach` witness for Spec 11 (`test_tempdir_cleanupStaleTempDirs_liveLockKeptRegardlessOfAge`). -/
theorem reach_tempdir_cleanupStaleTempDirs_liveLockKeptRegardlessOfAge :
    CanReach (test_tempdir_cleanupStaleTempDirs_liveLockKeptRegardlessOfAge
      (S := TempDirMockState) Internal.mkApiM mockFs mockTime mockUuid mockEnv) := by
  dsimp only [test_tempdir_cleanupStaleTempDirs_liveLockKeptRegardlessOfAge, CanReach]
  let s₀ : TempDirMockState :=
    { nodes := [("/tmp", .dir 0 0o755), ("/tmp/tmp-a", .dir 0 0o755), ("/tmp/tmp-a/.lock", .file 1 "" 0 0o644)]
      nowSec := 100 }
  refine ⟨s₀, ?_⟩
  dsimp only
  rw [canReach_nondet]; refine ⟨"/tmp", ?_⟩
  rw [canReach_nondet]; refine ⟨"tmp-", ?_⟩
  rw [canReach_nondet]; refine ⟨"tmp-a", ?_⟩
  rw [canReach_nondet]; refine ⟨10, ?_⟩
  rw [canReach_assume]; refine ⟨⟨by decide, by decide⟩, ?_⟩
  rw [canReach_assume]; refine ⟨by decide, ?_⟩
  rw [canReach_assume]; refine ⟨by decide, ?_⟩
  rw [canReach_assume]; refine ⟨⟨mockNodeStat (.dir 0 0o755), rfl, ⟨rfl, rfl, rfl, rfl⟩⟩, ?_⟩
  rw [canReach_assume]; refine ⟨⟨mockNodeStat (.dir 0 0o755), rfl, rfl⟩, ?_⟩
  rw [canReach_assume]; refine ⟨⟨mockNodeStat (.file 1 "" 0 0o644), rfl, rfl⟩, ?_⟩
  rw [mockFs_lstat_run]
  rw [show mockLstatPure s₀ (mockFs.join "/tmp" "tmp-a") = .ok (mockNodeStat (.dir 0 0o755)) from rfl]
  dsimp only
  have hTime : mockTime.nowTimestamp.run s₀ = (.ofSecondsSinceUnixEpoch (.ofInt 100), s₀) := rfl
  rw [hTime]
  dsimp only
  rw [canReach_assume]; refine ⟨by decide, ?_⟩
  try dsimp only
  have hRes :
      ((mockFs.withFileLock (mockFs.join (mockFs.join "/tmp" "tmp-a") ".lock") .shared false do
        let rep ← (Internal.mkApiM mockFs mockTime mockUuid mockEnv).cleanupStaleTempDirs (some "/tmp") "tmp-" 10
        let innerProbe ← mockFs.tryWithFileLock (mockFs.join (mockFs.join "/tmp" "tmp-a") ".lock") .exclusive false (pure (.ok ()))
        let stillExists ← mockFs.lstat (mockFs.join "/tmp" "tmp-a")
        return (Except.ok (rep, innerProbe, stillExists.isOk))).run s₀).1 =
      Except.ok (Except.ok { removed := #[], keptLocked := #["/tmp/tmp-a"], keptFresh := #[], skipped := #[], failed := #[] }, Except.ok none, true) := by
    rfl
  cases hRun : (mockFs.withFileLock (mockFs.join (mockFs.join "/tmp" "tmp-a") ".lock") .shared false do
        let rep ← (Internal.mkApiM mockFs mockTime mockUuid mockEnv).cleanupStaleTempDirs (some "/tmp") "tmp-" 10
        let innerProbe ← mockFs.tryWithFileLock (mockFs.join (mockFs.join "/tmp" "tmp-a") ".lock") .exclusive false (pure (.ok ()))
        let stillExists ← mockFs.lstat (mockFs.join "/tmp" "tmp-a")
        return (Except.ok (rep, innerProbe, stillExists.isOk))).run s₀ with
  | mk res snd =>
    rw [hRun] at hRes
    dsimp only at hRes
    rw [hRes]
    dsimp only
    rw [canReach_assert, canReach_assert_end]
    exact ⟨by decide, ⟨rfl, rfl⟩, trivial⟩

private theorem mockFs_lstat_notFound_lookup_none (s : TempDirMockState) (p : String) (e : FsError)
    (hl : ((mockFs.lstat p).run s).1 = .error e) :
    lookupNode s.nodes p = none := by
  rw [mockFs_lstat_run] at hl
  unfold mockLstatPure at hl
  cases hk : lookupNode s.nodes p with
  | none => rfl
  | some nd => simp [hk] at hl

private theorem lookupNode_filter_ne_none (nodes : List (String × MockNode)) (p : String) (hp : normKey p = p) :
    lookupNode (nodes.filter (fun e => normKey e.1 != p)) p = none := by
  unfold lookupNode
  dsimp only
  rw [hp]
  induction nodes with
  | nil => rfl
  | cons x xs ih =>
    rw [List.filter_cons]
    cases hb : (normKey x.1 == p) with
    | false =>
      by_cases hne : (normKey x.1 != p) = true
      · simp only [hne, ↓reduceIte]; rw [List.find?_cons, hb]; exact ih
      · simp only [Bool.eq_false_iff.mpr hne, Bool.false_eq_true, ↓reduceIte]; exact ih
    | true =>
      have hEq : normKey x.1 = p := beq_iff_eq.mp hb
      simp only [hEq, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
      exact ih

private theorem tryWithFileLock_excl_false_conflict (s : TempDirMockState) (p : String)
    (hp : normKey p = p) (ino : Nat) (c : String) (t : Int) (m : Nat)
    (hLook : lookupNode s.nodes p = some (.file ino c t m))
    (hTry : ((mockFs.tryWithFileLock p .exclusive false (pure (.ok ()))).run s).1 = .ok (some ())) :
    mockHasConflict s.locks ino .exclusive = false := by
  cases hc : mockHasConflict s.locks ino .exclusive with
  | false => rfl
  | true =>
    exfalso
    have hConf := mockFs_tryWithFileLock_existing_conflict_run s p .exclusive false ino c t m hp hLook hc (pure (.ok ()))
    rw [hConf] at hTry
    cases hTry

private theorem list_filter_filter_and {α : Type} (xs : List α) (p q : α → Bool) :
    (xs.filter p).filter q = xs.filter (fun x => p x && q x) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => cases hp : p x <;> cases hq : q x <;> simp [List.filter, hp, hq, ih]

private theorem string_bne_true_of_ne (a b : String) (h : a ≠ b) : (a != b) = true :=
  bne_iff_ne.mpr h

private theorem mockFs_listDir_with_locks (s : TempDirMockState) (locks' : List (Nat × LockMode))
    (dir : String) :
    let s' := { s with locks := locks' }
    (mockFs.listDir dir).run s' = (((mockFs.listDir dir).run s).1, s') := by
  intro s'
  have hListEq : ((mockFs.listDir dir).run s').1 = ((mockFs.listDir dir).run s).1 := by
    dsimp only [s', mockFs]
    rw [stateM_bind_run, stateM_get_run, stateM_bind_run, stateM_get_run]
    dsimp only
    cases lookupNode s.nodes (normKey dir) with
    | none => rw [stateM_pure_run, stateM_pure_run]
    | some node =>
      dsimp only
      split
      · rw [stateM_pure_run, stateM_pure_run]
      · split
        · rw [stateM_pure_run, stateM_pure_run]
        · rw [stateM_pure_run, stateM_pure_run]
  have hListSt : ((mockFs.listDir dir).run s').2 = s' := by
    dsimp only [s', mockFs]
    rw [stateM_bind_run, stateM_get_run]
    dsimp only
    cases lookupNode s.nodes (normKey dir) with
    | none => exact (stateM_pure_run _ _).symm ▸ rfl
    | some nd =>
      dsimp only
      split
      · rfl
      · split <;> rfl
  exact Prod.ext hListEq hListSt

private theorem spec12_sweepEntry_deadLock (s₀ sBefore : TempDirMockState)
    (root dirPrefix childName : String) (maxAgeSec : Nat) (nowSec : Int)
    (repBefore : CleanupReport) (stChild stLock : FileStat)
    (lockIno : Nat) (lockC : String) (lockT : Int) (lockM : Nat)
    (childNode : MockNode) (hcDir : pHasRwx stChild) (hlFile : stLock.kind = .file)
    (hvr : pValidRoot root = true) (hcV : pValidEntryName childName = true) (hPref : dirPrefix.toList.isPrefixOf childName.toList = true)
    (hLookChild : lookupNode s₀.nodes (mockJoin root childName) = some childNode)
    (hStChild : mockNodeStat childNode = stChild)
    (hLookLock : lookupNode s₀.nodes (mockJoin (mockJoin root childName) ".lock") = some (.file lockIno lockC lockT lockM))
    (hStLock : mockNodeStat (.file lockIno lockC lockT lockM) = stLock)
    (hListZero : ((mockFs.listDir (mockJoin root childName)).run s₀).1 = .ok #[".lock"])
    (hConfF : mockHasConflict s₀.locks lockIno .exclusive = false)
    (hBeforePres : NodesFilteredPres (fun k => underDir (mockJoin root childName) k = true ∨ normKey k = normKey root) s₀ sBefore) :
    let child := mockJoin root childName
    let lockPath := mockJoin child ".lock"
    ∃ sMid : TempDirMockState,
      (Internal.sweepEntry mockFs root dirPrefix maxAgeSec nowSec repBefore childName).run sBefore =
        ({ repBefore with removed := repBefore.removed.push child }, sMid) ∧
      NodesFilteredPres (fun k => normKey k = normKey root) sBefore sMid ∧
      lookupNode sMid.nodes child = none ∧
      lookupNode sMid.nodes lockPath = none := by
  intro child lockPath
  have hrNe : root ≠ "" := validRoot_ne_empty root hvr
  have ⟨hcNe, _, _, hcSlash⟩ := validEntryName_parts childName hcV
  have hcFullNe : child ≠ "" := mockJoin_ne_empty root childName hcNe
  have hcFullNorm : normKey child = child := normKey_mockJoin root childName hcNe hcSlash
  have hLockNorm : normKey lockPath = lockPath := normKey_mockJoin child ".lock" (by decide) (by decide)
  obtain ⟨hPChild, hPUnder, hPLock, hPRoot⟩ := nodesFilteredPres_child_P (root := root) hcV
  have hChildBefore : lookupNode sBefore.nodes child = some childNode := by
    rw [nodesFilteredPres_lookupNode hBeforePres child hPChild]; exact hLookChild
  have hLockBefore : lookupNode sBefore.nodes lockPath = some (.file lockIno lockC lockT lockM) := by
    rw [nodesFilteredPres_lookupNode hBeforePres lockPath hPLock]; exact hLookLock
  have hConfBefore : mockHasConflict sBefore.locks lockIno .exclusive = false := by
    rw [hBeforePres.2.1]; exact hConfF
  have hChildPure : mockLstatPure sBefore child = .ok stChild := by
    dsimp only [mockLstatPure]; rw [hChildBefore]; exact congrArg Except.ok hStChild
  have hLockPure : mockLstatPure sBefore lockPath = .ok stLock := by
    dsimp only [mockLstatPure]; rw [hLockBefore]; exact congrArg Except.ok hStLock
  have hListBefore : ((mockFs.listDir child).run sBefore).1 = .ok #[".lock"] := by
    rw [(nodesFilteredPres_listDir hBeforePres child hcFullNe hPChild hPUnder).1]; exact hListZero
  have hLockNeChild : normKey lockPath ≠ child :=
    payload_ne_dir root childName ".lock" hrNe hcNe hcSlash (by decide) (by decide)
  have hRootUnderChild : underDir child (normKey root) = false := by
    simpa [underDir, normKey_idem] using underDir_mockJoin_root_false root childName hrNe hcNe hcSlash
  have hRootNeLock : normKey (normKey root) ≠ lockPath := by
    intro hEq
    have hEq' : normKey (normKey root) = normKey lockPath := by
      simpa [hLockNorm, normKey_idem] using hEq
    have hu : underDir child (normKey root) = true := by
      rw [underDir_eq_of_normKey_eq child (normKey root) lockPath hEq']
      exact underDir_mockJoin_self child ".lock" hcFullNe hcFullNorm (mockJoin_ne_slash root childName hrNe hcNe) (by decide) (by decide)
    rw [hRootUnderChild] at hu
    exact Bool.noConfusion hu
  have hRootNeChild : normKey (normKey root) ≠ child := by
    intro hEq
    have hEq' : normKey (normKey root) = normKey child := by
      simpa [hcFullNorm, normKey_idem] using hEq
    have hu : underDir child (normKey root) = true := by
      rw [underDir_eq_of_normKey_eq child (normKey root) child hEq']
      exact underDir_refl child hcFullNorm
    rw [hRootUnderChild] at hu
    exact Bool.noConfusion hu
  let sLock := { sBefore with locks := (lockIno, .exclusive) :: sBefore.locks }
  have hListLock : (mockFs.listDir child).run sLock = (.ok #[".lock"], sLock) := by
    rw [mockFs_listDir_with_locks sBefore ((lockIno, .exclusive) :: sBefore.locks) child, hListBefore]
  let s1 := { sLock with nodes := sLock.nodes.filter (fun e => normKey e.1 != lockPath) }
  have hUnlinkLock : (mockFs.unlink lockPath true).run sLock = (.ok (), s1) :=
    mockFs_unlink_existing_run sLock lockPath true lockIno lockC lockT lockM hLockNorm hLockBefore
  have hNeLockOfChild : ∀ e : String × MockNode, e ∈ sBefore.nodes → normKey e.1 = normKey child →
      (normKey e.1 != lockPath) = true := fun e _ h =>
    string_bne_true_of_ne (normKey e.1) lockPath (by rw [h, hcFullNorm, ← hLockNorm]; exact ne_comm.mp hLockNeChild)
  have hChildDir : ∃ tChild mChild, childNode = .dir tChild mChild ∧ lookupNode s1.nodes child = some (.dir tChild mChild) := by
    cases childNode with
    | file _ _ _ _ => simp [mockNodeStat] at hStChild; rw [← hStChild] at hcDir; cases hcDir.1
    | symlink _ _ => simp [mockNodeStat] at hStChild; rw [← hStChild] at hcDir; cases hcDir.1
    | dir tC mC =>
      refine ⟨tC, mC, rfl, ?_⟩
      have hNodesEq1 : s1.nodes = sBefore.nodes.filter (fun e => normKey e.1 != lockPath) := rfl
      rw [hNodesEq1, lookupNode_filter_of_preserved sBefore.nodes _ child hNeLockOfChild]
      exact hChildBefore
  rcases hChildDir with ⟨tC, mC, _, hLookChild1⟩
  let s2 := { s1 with nodes := s1.nodes.filter (fun e => normKey e.1 != child) }
  have hRmdir : (mockFs.rmdir child).run s1 = (.ok (), s2) :=
    mockFs_rmdir_dir_run s1 child tC mC hcFullNorm hLookChild1
  have hRemLocked : (Internal.removeLockedTempDir mockFs child lockPath).run sLock = (.ok (.ok ()), s2) := by
    dsimp only [Internal.removeLockedTempDir]
    rw [stateM_bind_run, hListLock]
    dsimp only [Array.toList]
    rw [stateM_bind_run]
    dsimp only [Internal.removeNonLockChildren]
    simp only [beq_self_eq_true, ↓reduceIte]
    rw [stateM_pure_run]
    dsimp only
    rw [stateM_bind_run, hUnlinkLock]
    dsimp only
    rw [stateM_bind_run, hRmdir]
    dsimp only
    exact stateM_pure_run _ _
  let sMid := { s2 with locks := mockRemoveFirstLock lockIno .exclusive s2.locks }
  have hMidLocks : sMid.locks = sBefore.locks := by
    change mockRemoveFirstLock lockIno .exclusive sLock.locks = sBefore.locks
    exact mockRemoveFirstLock_head lockIno .exclusive sBefore.locks
  have hLookChildMid : lookupNode sMid.nodes child = none := by
    change lookupNode (s1.nodes.filter (fun e => normKey e.1 != child)) child = none
    exact lookupNode_filter_ne_none s1.nodes child hcFullNorm
  have hLookLockMid : lookupNode sMid.nodes lockPath = none := by
    have hLookLock1 : lookupNode s1.nodes lockPath = none := by
      change lookupNode (sLock.nodes.filter (fun e => normKey e.1 != lockPath)) lockPath = none
      exact lookupNode_filter_ne_none sLock.nodes lockPath hLockNorm
    change lookupNode (s1.nodes.filter (fun e => normKey e.1 != child)) lockPath = none
    exact lookupNode_filter_none_of_none s1.nodes _ lockPath hLookLock1
  have hNodesEq : sMid.nodes = sBefore.nodes.filter (fun e => (normKey e.1 != lockPath) && (normKey e.1 != child)) :=
    list_filter_filter_and sBefore.nodes (fun e => normKey e.1 != lockPath) (fun e => normKey e.1 != child)
  have hPresMid : NodesFilteredPres (fun k => normKey k = normKey root) sBefore sMid := by
    refine ⟨⟨fun k => (normKey k != lockPath) && (normKey k != child), fun k hk => by
      have hn1 : normKey k ≠ lockPath := by rw [hk, ← normKey_idem root]; exact hRootNeLock
      have hn2 : normKey k ≠ child := by rw [hk, ← normKey_idem root]; exact hRootNeChild
      rw [Bool.and_eq_true]
      exact ⟨string_bne_true_of_ne (normKey k) lockPath hn1, string_bne_true_of_ne (normKey k) child hn2⟩, hNodesEq⟩, hMidLocks, rfl, rfl, rfl, rfl⟩
  refine ⟨sMid, ?_, hPresMid, hLookChildMid, hLookLockMid⟩
  dsimp only [Internal.sweepEntry]
  rw [mockFs_join_eq]
  have hPrefF : (!dirPrefix.toList.isPrefixOf childName.toList) = false := by rw [hPref]; rfl
  simp only [hPrefF, Bool.false_eq_true, ↓reduceIte]
  rw [stateM_bind_run, mockFs_lstat_run, hChildPure]; dsimp only
  have hNotDir : (stChild.kind != .dir) = false := by rw [hcDir.1]; rfl
  simp only [hNotDir, Bool.false_eq_true, ↓reduceIte]
  rw [stateM_bind_run, mockFs_lstat_run, hLockPure]; dsimp only
  have hNotFile : (stLock.kind != .file) = false := by rw [hlFile]; rfl
  simp only [hNotFile, Bool.false_eq_true, ↓reduceIte]
  rw [stateM_bind_run, mockFs_tryWithFileLock_existing_ok_run sBefore lockPath .exclusive false lockIno lockC lockT lockM hLockNorm hLockBefore hConfBefore]
  rw [hRemLocked]
  dsimp only [Except.map]
  exact stateM_pure_run _ _

/-- Spec 12: `cleanupStaleTempDirs` immediately removes a dead locked temp directory regardless of `maxAgeSec`, leaving zero locks held. -/
theorem proof_tempdir_cleanupStaleTempDirs_deadLockRemovedImmediately :
    AllPass (test_tempdir_cleanupStaleTempDirs_deadLockRemovedImmediately
      (S := TempDirMockState) Internal.mkApiM mockFs mockTime mockUuid mockEnv) := by
  dsimp only [test_tempdir_cleanupStaleTempDirs_deadLockRemovedImmediately, AllPass]
  intro s₀ root dirPrefix childName maxAgeSec ⟨hvr, hvp, _⟩ hcV hPref ⟨stRoot, hRoot, hRwx⟩
    ⟨stChild, hChild, hcDir⟩ ⟨stLock, hLock, hlFile⟩ hListZero hTryExcl
  have hrNe : root ≠ "" := validRoot_ne_empty root hvr
  have ⟨hcNe, _, _, hcSlash⟩ := validEntryName_parts childName hcV
  let child := mockJoin root childName
  let lockPath := mockJoin child ".lock"
  have hChildNorm : normKey child = child := normKey_mockJoin root childName hcNe hcSlash
  have hLockNorm : normKey lockPath = lockPath := normKey_mockJoin child ".lock" (by decide) (by decide)
  have hRootPure : mockStatPure s₀ root = .ok stRoot := by rw [mockFs_stat_run] at hRoot; exact hRoot
  have hChildPure : mockLstatPure s₀ child = .ok stChild := by rw [mockFs_lstat_run, mockFs_join_eq] at hChild; exact hChild
  have hLockPure : mockLstatPure s₀ lockPath = .ok stLock := by rw [mockFs_lstat_run, mockFs_join_eq] at hLock; exact hLock
  rw [mockFs_join_eq] at hListZero hTryExcl ⊢
  obtain ⟨rootNode, hLookRoot, hStRoot⟩ := lookupNode_of_lstat_ok s₀ root stRoot hRootPure
  obtain ⟨childNode, hLookChild, hStChild⟩ := lookupNode_of_lstat_ok s₀ child stChild hChildPure
  obtain ⟨ndLock, hLookLock, hStLock⟩ := lookupNode_of_lstat_ok s₀ lockPath stLock hLockPure
  cases ndLock with
  | dir _ _ => simp [mockNodeStat] at hStLock; rw [← hStLock] at hlFile; cases hlFile
  | symlink _ _ => simp [mockNodeStat] at hStLock; rw [← hStLock] at hlFile; cases hlFile
  | file lockIno lockC lockT lockM =>
    have hConfF := tryWithFileLock_excl_false_conflict s₀ lockPath hLockNorm lockIno lockC lockT lockM hLookLock hTryExcl
    dsimp only [mockTime]
    rw [stateM_bind_run, stateM_get_run, stateM_pure_run]
    dsimp only
    rw [mockFs_lstat_run, hChildPure]
    dsimp only
    rw [allPass_assume]
    intro _
    obtain ⟨before, after, repBefore, sBefore, _, _, _, _, hBeforePres, _, hNotKLB, hNotKFB, _, hExec⟩ :=
      cleanupStaleTempDirs_split_exec mockFs sweepFsOps_mockFs s₀ root dirPrefix childName maxAgeSec
        hvr hvp hcV stRoot hRootPure hRwx childNode hLookChild
    obtain ⟨sMid, hSweepMid, hPresMid, hChildNoneMid, hLockNoneMid⟩ :=
      spec12_sweepEntry_deadLock s₀ sBefore root dirPrefix childName maxAgeSec
        ((mockTime.nowTimestamp.run s₀).1.toSecondsSinceUnixEpoch.val) repBefore stChild stLock
        lockIno lockC lockT lockM childNode hcDir hlFile hvr hcV hPref hLookChild hStChild
        hLookLock hStLock hListZero hConfF hBeforePres
    cases hAfterRun : (Internal.sweepEntries mockFs root dirPrefix maxAgeSec ((mockTime.nowTimestamp.run s₀).1.toSecondsSinceUnixEpoch.val) { repBefore with removed := repBefore.removed.push child } after).run sMid with
    | mk repAfter sFinal =>
      have hExec' := hExec { repBefore with removed := repBefore.removed.push child } sMid hSweepMid
      rw [hAfterRun] at hExec'
      dsimp only at hExec'
      obtain ⟨hCleanRun, hAfterPres, hRmIff, hKLIff, hKFIff, _, _, _⟩ := hExec'
      obtain ⟨hPChild, _, _, hPRoot⟩ := nodesFilteredPres_child_P (root := root) hcV
      let finalRep : CleanupReport :=
        { removed := (Internal.sortStrings repAfter.removed.toList).toArray
          keptLocked := (Internal.sortStrings repAfter.keptLocked.toList).toArray
          keptFresh := (Internal.sortStrings repAfter.keptFresh.toList).toArray
          skipped := (Internal.sortStrings repAfter.skipped.toList).toArray
          failed := repAfter.failed }
      rw [mkApiM_cleanupStaleTempDirs_eq] at hCleanRun
      dsimp only [StateT.run, mockTime] at hCleanRun
      dsimp only [Internal.mkApiM, StateT.run]
      rw [hCleanRun]
      dsimp only [AllPass]
      rw [allPass_assert, allPass_assert, allPass_assert_end]
      have hRmMem : pHasPath finalRep.removed child = true := hRmIff.mpr (by simp [child, Array.toList_push])
      have hNotKL : ¬ (pHasPath finalRep.keptLocked child = true) := fun h => hNotKLB.mp (hKLIff.mp h)
      have hNotKF : ¬ (pHasPath finalRep.keptFresh child = true) := fun h => hNotKFB.mp (hKFIff.mp h)
      have hChildNoneFin : lookupNode sFinal.nodes child = none := nodesFilteredPres_lookupNode_none hAfterPres child hChildNoneMid
      have hLookRootBefore : lookupNode sBefore.nodes (normKey root) = some rootNode := by
        rw [nodesFilteredPres_lookupNode hBeforePres (normKey root) (fun k hk => hPRoot k (by simpa [normKey_idem] using hk))]
        simpa [lookupNode, normKey_idem] using hLookRoot
      have hLookRootMid : lookupNode sMid.nodes (normKey root) = some rootNode := by
        rw [nodesFilteredPres_lookupNode hPresMid (normKey root) (fun k hk => by simpa [normKey_idem] using hk)]
        exact hLookRootBefore
      have hLookRootFin : lookupNode sFinal.nodes (normKey root) = some rootNode := by
        rw [nodesFilteredPres_lookupNode hAfterPres (normKey root) (fun k hk => hPRoot k (by simpa [normKey_idem] using hk))]
        exact hLookRootMid
      have hProbe := probe_exclusive_lock_after_cleanup_run sFinal root childName hrNe hcNe hcSlash
        rootNode stRoot hLookRootFin hStRoot hRwx hChildNoneFin
      refine ⟨?_, ?_, ?_, trivial⟩
      · exact ⟨hRmMem, hNotKL, hNotKF⟩
      · exact mockFs_lstat_isOk_false_of_lookup_none sFinal child hChildNoneFin
      · dsimp only [StateT.run] at hProbe
        exact hProbe

/-- Non-vacuity `CanReach` witness for Spec 12 (`test_tempdir_cleanupStaleTempDirs_deadLockRemovedImmediately`). -/
theorem reach_tempdir_cleanupStaleTempDirs_deadLockRemovedImmediately :
    CanReach (test_tempdir_cleanupStaleTempDirs_deadLockRemovedImmediately
      (S := TempDirMockState) Internal.mkApiM mockFs mockTime mockUuid mockEnv) := by
  dsimp only [test_tempdir_cleanupStaleTempDirs_deadLockRemovedImmediately, CanReach]
  let s₀ : TempDirMockState :=
    { nodes := [("/tmp", .dir 0 0o755), ("/tmp/tmp-a", .dir 0 0o755), ("/tmp/tmp-a/.lock", .file 1 "" 0 0o644)]
      nowSec := 5 }
  refine ⟨s₀, "/tmp", "tmp-", "tmp-a", 10, ⟨by decide, by decide, by decide⟩, by decide, by decide,
    ⟨mockNodeStat (.dir 0 0o755), rfl, ⟨rfl, rfl, rfl, rfl⟩⟩,
    ⟨mockNodeStat (.dir 0 0o755), rfl, ⟨rfl, rfl, rfl, rfl⟩⟩,
    ⟨mockNodeStat (.file 1 "" 0 0o644), rfl, rfl⟩, rfl, rfl, ?_⟩
  rw [show mockTime.nowTimestamp.run s₀ = (.ofSecondsSinceUnixEpoch (.ofInt 5), s₀) from rfl]
  rw [mockFs_lstat_run]
  rw [show mockLstatPure s₀ (mockFs.join "/tmp" "tmp-a") = .ok (mockNodeStat (.dir 0 0o755)) from rfl]
  dsimp only
  rw [canReach_assume]; refine ⟨by decide, ?_⟩
  try dsimp only
  have hRes :
      ((Internal.mkApiM mockFs mockTime mockUuid mockEnv).cleanupStaleTempDirs (some "/tmp") "tmp-" 10).run s₀ =
        (.ok { removed := #["/tmp/tmp-a"], keptLocked := #[], keptFresh := #[], skipped := #[], failed := #[] },
         { nodes := [("/tmp", .dir 0 0o755)], locks := [], nextInode := 1, tmpdir := none, nowSec := 5, nextUuid := 1 }) := rfl
  rw [hRes]
  dsimp only
  rw [canReach_assert, canReach_assert, canReach_assert_end]
  refine ⟨⟨by decide, by decide, by decide⟩, rfl, ?_, trivial⟩
  rfl

/-- Spec 13: for matching unlocked temp directories, `cleanupStaleTempDirs` keeps directories within `age ≤ maxAgeSec` and removes those with `age > maxAgeSec`. -/
theorem proof_tempdir_cleanupStaleTempDirs_graceWindowAndOldUnlocked :
    AllPass (test_tempdir_cleanupStaleTempDirs_graceWindowAndOldUnlocked
      (S := TempDirMockState) Internal.mkApiM mockFs mockTime mockUuid mockEnv) := by
  dsimp only [test_tempdir_cleanupStaleTempDirs_graceWindowAndOldUnlocked, AllPass]
  intro s₀ root dirPrefix childName maxAgeSec ⟨hvr, hvp⟩ hcV hPref ⟨stRoot, hRoot, hRwx⟩
    ⟨stChild, hChild, hcDir⟩ ⟨eNf, hLock, _⟩
  have hrNe : root ≠ "" := validRoot_ne_empty root hvr
  have ⟨hcNe, _, _, hcSlash⟩ := validEntryName_parts childName hcV
  let child := mockJoin root childName
  let lockPath := mockJoin child ".lock"
  have hRootPure : mockStatPure s₀ root = .ok stRoot := by rw [mockFs_stat_run] at hRoot; exact hRoot
  have hChildPure : mockLstatPure s₀ child = .ok stChild := by rw [mockFs_lstat_run, mockFs_join_eq] at hChild; exact hChild
  have hLockNone : lookupNode s₀.nodes lockPath = none := by
    rw [mockFs_join_eq] at hLock
    exact mockFs_lstat_notFound_lookup_none s₀ lockPath eNf hLock
  rw [mockFs_join_eq]
  obtain ⟨childNode, hLookChild, _⟩ := lookupNode_of_lstat_ok s₀ child stChild hChildPure
  dsimp only [mockTime]
  rw [stateM_bind_run, stateM_get_run, stateM_pure_run]
  dsimp only
  rw [mockFs_lstat_run, hChildPure]
  dsimp only
  let nowSec := (_root_.Std.Time.Timestamp.ofSecondsSinceUnixEpoch (_root_.Std.Time.Second.Offset.ofInt s₀.nowSec)).toSecondsSinceUnixEpoch.val
  let ageSec := nowSec - stChild.modifiedSec
  obtain ⟨before, after, repBefore, sBefore, _, _, _, _, hBeforePres, hNotRmB, _, hNotKFB, _, hExec⟩ :=
    cleanupStaleTempDirs_split_exec mockFs sweepFsOps_mockFs s₀ root dirPrefix childName maxAgeSec
      hvr hvp hcV stRoot hRootPure hRwx childNode hLookChild
  obtain ⟨hPChild, _, hPLock, _⟩ := nodesFilteredPres_child_P (root := root) hcV
  have hChildBefore : (mockFs.lstat child).run sBefore = (.ok stChild, sBefore) := by
    rw [nodesFilteredPres_lstat hBeforePres child hPChild, mockFs_lstat_run]; dsimp only; rw [hChildPure]
  have hLockBeforeNone : lookupNode sBefore.nodes lockPath = none :=
    nodesFilteredPres_lookupNode_none hBeforePres lockPath hLockNone
  have hLockBefore : (mockFs.lstat lockPath).run sBefore = (.error { kind := .notFound, path := some lockPath, message := "not found" }, sBefore) := by
    rw [mockFs_lstat_run]; unfold mockLstatPure; rw [hLockBeforeNone]
  have hPrefF : (!dirPrefix.toList.isPrefixOf childName.toList) = false := by rw [hPref]; rfl
  have hNotDir : (stChild.kind != .dir) = false := by rw [hcDir.1]; rfl
  have hNotNf : (FsErrorKind.notFound != .notFound) = false := rfl
  by_cases hFresh : ageSec ≤ (maxAgeSec : Int)
  · let repMid : CleanupReport := { repBefore with keptFresh := repBefore.keptFresh.push child }
    have hSweepMid : (Internal.sweepEntry mockFs root dirPrefix maxAgeSec nowSec repBefore childName).run sBefore =
        (repMid, sBefore) := by
      dsimp only [Internal.sweepEntry]
      rw [mockFs_join_eq]
      simp only [hPrefF, Bool.false_eq_true, ↓reduceIte]
      rw [stateM_bind_run, hChildBefore]; dsimp only
      simp only [hNotDir, Bool.false_eq_true, ↓reduceIte]
      rw [stateM_bind_run, hLockBefore]; dsimp only
      simp only [hNotNf, Bool.false_eq_true, ↓reduceIte]
      dsimp only [nowSec, ageSec] at hFresh ⊢
      simp only [hFresh, ↓reduceIte]
      exact stateM_pure_run _ _
    obtain ⟨hCleanRun, hAfterPres, hRmIff, _, hKFIff, _, _, _⟩ := hExec repMid sBefore hSweepMid
    let repAfter := (Internal.sweepEntries mockFs root dirPrefix maxAgeSec nowSec repMid after).run sBefore |>.1
    let sFinal := (Internal.sweepEntries mockFs root dirPrefix maxAgeSec nowSec repMid after).run sBefore |>.2
    let finalRep : CleanupReport :=
      { removed := (Internal.sortStrings repAfter.removed.toList).toArray
        keptLocked := (Internal.sortStrings repAfter.keptLocked.toList).toArray
        keptFresh := (Internal.sortStrings repAfter.keptFresh.toList).toArray
        skipped := (Internal.sortStrings repAfter.skipped.toList).toArray
        failed := repAfter.failed }
    rw [mkApiM_cleanupStaleTempDirs_eq] at hCleanRun
    dsimp only [StateT.run, mockTime] at hCleanRun
    dsimp only [Internal.mkApiM, StateT.run]
    rw [hCleanRun]
    dsimp only [AllPass]
    dsimp only [nowSec, ageSec] at hFresh
    simp only [hFresh, ↓reduceIte]
    rw [allPass_assert, allPass_assert_end]
    have hKFMem : pHasPath finalRep.keptFresh child = true := hKFIff.mpr (by simp [repMid, child, Array.toList_push])
    have hNotRm : ¬ (pHasPath finalRep.removed child = true) := fun h => hNotRmB.mp (hRmIff.mp h)
    have hAfterPres' : NodesFilteredPres (fun k => underDir child k = true ∨ normKey k = normKey root) sBefore sFinal := hAfterPres
    have hChildFin : ((mockFs.lstat child).run sFinal).1.isOk = true := by
      rw [nodesFilteredPres_lstat (nodesFilteredPres_trans hBeforePres hAfterPres') child hPChild, mockFs_lstat_run]
      dsimp only; rw [hChildPure]; rfl
    exact ⟨⟨hKFMem, hNotRm⟩, hChildFin, trivial⟩
  · have hStChild : mockNodeStat childNode = stChild := by
      dsimp only [mockLstatPure] at hChildPure
      rw [hLookChild] at hChildPure
      exact Except.ok.inj hChildPure
    have hRmUnder : (Internal.cleanupDirIgnoringNotFound mockFs child).run sBefore =
        (.ok (), { sBefore with nodes := sBefore.nodes.filter (fun e => !underDir child e.1) }) := by
      have hLookChildBefore : lookupNode sBefore.nodes child = some childNode := by
        rw [nodesFilteredPres_lookupNode hBeforePres child hPChild]
        exact hLookChild
      cases childNode with
      | file _ _ _ _ => dsimp only [mockNodeStat] at hStChild; rw [← hStChild] at hcDir; cases hcDir.1
      | symlink _ _ => dsimp only [mockNodeStat] at hStChild; rw [← hStChild] at hcDir; cases hcDir.1
      | dir tC mC =>
        exact cleanupDir_mock_run sBefore child (normKey_mockJoin root childName hcNe hcSlash) ⟨tC, mC, hLookChildBefore⟩
    let sMid := { sBefore with nodes := sBefore.nodes.filter (fun e => !underDir child e.1) }
    let repMid : CleanupReport := { repBefore with removed := repBefore.removed.push child }
    have hSweepMid : (Internal.sweepEntry mockFs root dirPrefix maxAgeSec nowSec repBefore childName).run sBefore =
        (repMid, sMid) := by
      dsimp only [Internal.sweepEntry]
      rw [mockFs_join_eq]
      simp only [hPrefF, Bool.false_eq_true, ↓reduceIte]
      rw [stateM_bind_run, hChildBefore]; dsimp only
      simp only [hNotDir, Bool.false_eq_true, ↓reduceIte]
      rw [stateM_bind_run, hLockBefore]; dsimp only
      simp only [hNotNf, Bool.false_eq_true, ↓reduceIte]
      dsimp only [nowSec, ageSec] at hFresh ⊢
      simp only [hFresh, ↓reduceIte]
      rw [stateM_bind_run, hRmUnder]
      exact stateM_pure_run _ _
    obtain ⟨hCleanRun, hAfterPres, hRmIff, _, hKFIff, _, _, _⟩ := hExec repMid sMid hSweepMid
    let repAfter := (Internal.sweepEntries mockFs root dirPrefix maxAgeSec nowSec repMid after).run sMid |>.1
    let sFinal := (Internal.sweepEntries mockFs root dirPrefix maxAgeSec nowSec repMid after).run sMid |>.2
    let finalRep : CleanupReport :=
      { removed := (Internal.sortStrings repAfter.removed.toList).toArray
        keptLocked := (Internal.sortStrings repAfter.keptLocked.toList).toArray
        keptFresh := (Internal.sortStrings repAfter.keptFresh.toList).toArray
        skipped := (Internal.sortStrings repAfter.skipped.toList).toArray
        failed := repAfter.failed }
    rw [mkApiM_cleanupStaleTempDirs_eq] at hCleanRun
    dsimp only [StateT.run, mockTime] at hCleanRun
    dsimp only [Internal.mkApiM, StateT.run]
    rw [hCleanRun]
    dsimp only [AllPass]
    dsimp only [nowSec, ageSec] at hFresh
    simp only [hFresh, ↓reduceIte]
    rw [allPass_assume]
    intro _
    rw [allPass_assert, allPass_assert_end]
    have hRmMem : pHasPath finalRep.removed child = true := hRmIff.mpr (by simp [repMid, child, Array.toList_push])
    have hNotKF : ¬ (pHasPath finalRep.keptFresh child = true) := fun h => hNotKFB.mp (hKFIff.mp h)
    have hChildNoneMid : lookupNode sMid.nodes child = none :=
      lookupNode_filter_none_of_underDir sBefore.nodes child child (underDir_refl child (normKey_mockJoin root childName hcNe hcSlash))
    have hAfterPres' : NodesFilteredPres (fun k => underDir child k = true ∨ normKey k = normKey root) sMid sFinal := hAfterPres
    have hChildNoneFin : lookupNode sFinal.nodes child = none :=
      nodesFilteredPres_lookupNode_none hAfterPres' child hChildNoneMid
    exact ⟨⟨hRmMem, hNotKF⟩, mockFs_lstat_isOk_false_of_lookup_none sFinal child hChildNoneFin, trivial⟩

/-- Non-vacuity `CanReach` witness for Spec 13 (`test_tempdir_cleanupStaleTempDirs_graceWindowAndOldUnlocked`). -/
theorem reach_tempdir_cleanupStaleTempDirs_graceWindowAndOldUnlocked :
    CanReach (test_tempdir_cleanupStaleTempDirs_graceWindowAndOldUnlocked
      (S := TempDirMockState) Internal.mkApiM mockFs mockTime mockUuid mockEnv) := by
  dsimp only [test_tempdir_cleanupStaleTempDirs_graceWindowAndOldUnlocked, CanReach]
  let s₀ : TempDirMockState :=
    { nodes := [("/tmp", .dir 0 0o755), ("/tmp/tmp-a", .dir 95 0o755)], nowSec := 100 }
  refine ⟨s₀, "/tmp", "tmp-", "tmp-a", 10, ⟨by decide, by decide⟩, by decide, by decide,
    ⟨mockNodeStat (.dir 0 0o755), rfl, ⟨rfl, rfl, rfl, rfl⟩⟩,
    ⟨mockNodeStat (.dir 95 0o755), rfl, ⟨rfl, rfl, rfl, rfl⟩⟩,
    ⟨{ kind := .notFound, path := some "/tmp/tmp-a/.lock", message := "not found" }, rfl, rfl⟩, ?_⟩
  rw [show mockTime.nowTimestamp.run s₀ = (.ofSecondsSinceUnixEpoch (.ofInt 100), s₀) from rfl]
  rw [mockFs_lstat_run]
  rw [show mockLstatPure s₀ (mockFs.join "/tmp" "tmp-a") = .ok (mockNodeStat (.dir 95 0o755)) from rfl]
  dsimp only
  have hRes :
      ((Internal.mkApiM mockFs mockTime mockUuid mockEnv).cleanupStaleTempDirs (some "/tmp") "tmp-" 10).run s₀ =
        (.ok { removed := #[], keptLocked := #[], keptFresh := #["/tmp/tmp-a"], skipped := #[], failed := #[] }, s₀) := rfl
  rw [hRes]
  dsimp only
  have hCond : (_root_.Std.Time.Timestamp.ofSecondsSinceUnixEpoch (_root_.Std.Time.Second.Offset.ofInt 100)).toSecondsSinceUnixEpoch.val -
      (mockNodeStat (.dir 95 0o755)).modifiedSec ≤ (↑10 : Int) := of_decide_eq_true rfl
  split
  · rw [canReach_assert, canReach_assert_end]
    exact ⟨⟨by decide, by decide⟩, rfl, trivial⟩
  · next hNot => exact absurd hCond hNot

/-- Spec 14: `cleanupStaleTempDirs` skips non-matching names, files, and symlinks without removing them, and returns sorted arrays. -/
theorem proof_tempdir_cleanupStaleTempDirs_scopeAndSymlinkSafety :
    AllPass (test_tempdir_cleanupStaleTempDirs_scopeAndSymlinkSafety
      (S := TempDirMockState) Internal.mkApiM mockFs mockTime mockUuid mockEnv) := by
  dsimp only [test_tempdir_cleanupStaleTempDirs_scopeAndSymlinkSafety, AllPass]
  intro s₀ root dirPrefix entryName maxAgeSec ⟨hvr, hvp⟩ hcV ⟨stRoot, hRoot, hRwx⟩ ⟨stChild, hChild, hSkipCond⟩
  let child := mockJoin root entryName
  have hRootPure : mockStatPure s₀ root = .ok stRoot := by rw [mockFs_stat_run] at hRoot; exact hRoot
  have hChildPure : mockLstatPure s₀ child = .ok stChild := by rw [mockFs_lstat_run, mockFs_join_eq] at hChild; exact hChild
  rw [mockFs_join_eq]
  obtain ⟨childNode, hLookChild, _⟩ := lookupNode_of_lstat_ok s₀ child stChild hChildPure
  obtain ⟨before, after, repBefore, sBefore, _, _, _, _, hBeforePres, hNotRmB, _, _, _, hExec⟩ :=
    cleanupStaleTempDirs_split_exec mockFs sweepFsOps_mockFs s₀ root dirPrefix entryName maxAgeSec
      hvr hvp hcV stRoot hRootPure hRwx childNode hLookChild
  obtain ⟨hPChild, _, _, _⟩ := nodesFilteredPres_child_P (root := root) hcV
  let repMid : CleanupReport := { repBefore with skipped := repBefore.skipped.push child }
  have hSweepMid : (Internal.sweepEntry mockFs root dirPrefix maxAgeSec
      ((mockTime.nowTimestamp.run s₀).1.toSecondsSinceUnixEpoch.val) repBefore entryName).run sBefore =
      (repMid, sBefore) := by
    dsimp only [Internal.sweepEntry]
    rw [mockFs_join_eq]
    rcases hSkipCond with hNotPref | hNotDir
    · have hPrefT : (!dirPrefix.toList.isPrefixOf entryName.toList) = true := by
        cases hb : dirPrefix.toList.isPrefixOf entryName.toList
        · rfl
        · exact absurd hb hNotPref
      simp only [hPrefT, ↓reduceIte]; exact stateM_pure_run _ _
    · by_cases hPref : (!dirPrefix.toList.isPrefixOf entryName.toList) = true
      · simp only [hPref, ↓reduceIte]; exact stateM_pure_run _ _
      · have hPrefF : (!dirPrefix.toList.isPrefixOf entryName.toList) = false := Bool.eq_false_iff.mpr hPref
        simp only [hPrefF, Bool.false_eq_true, ↓reduceIte]
        have hChildBefore : (mockFs.lstat child).run sBefore = (.ok stChild, sBefore) := by
          rw [nodesFilteredPres_lstat hBeforePres child hPChild, mockFs_lstat_run]; dsimp only; rw [hChildPure]
        rw [stateM_bind_run, hChildBefore]; dsimp only
        have hNotDirT : (stChild.kind != .dir) = true := by revert hNotDir; cases stChild.kind <;> decide
        simp only [hNotDirT, ↓reduceIte]; exact stateM_pure_run _ _
  obtain ⟨hCleanRun, hAfterPres, hRmIff, _, _, hSkIff, _, _⟩ := hExec repMid sBefore hSweepMid
  let repAfter := (Internal.sweepEntries mockFs root dirPrefix maxAgeSec ((mockTime.nowTimestamp.run s₀).1.toSecondsSinceUnixEpoch.val) repMid after).run sBefore |>.1
  let sFinal := (Internal.sweepEntries mockFs root dirPrefix maxAgeSec ((mockTime.nowTimestamp.run s₀).1.toSecondsSinceUnixEpoch.val) repMid after).run sBefore |>.2
  let finalRep : CleanupReport :=
    { removed := (Internal.sortStrings repAfter.removed.toList).toArray
      keptLocked := (Internal.sortStrings repAfter.keptLocked.toList).toArray
      keptFresh := (Internal.sortStrings repAfter.keptFresh.toList).toArray
      skipped := (Internal.sortStrings repAfter.skipped.toList).toArray
      failed := repAfter.failed }
  rw [mkApiM_cleanupStaleTempDirs_eq] at hCleanRun
  dsimp only [StateT.run, mockTime] at hCleanRun
  dsimp only [Internal.mkApiM, StateT.run, mockTime]
  rw [hCleanRun]
  dsimp only [AllPass]
  rw [allPass_assert, allPass_assert, allPass_assert_end]
  have hSkMem : pHasPath finalRep.skipped child = true := hSkIff.mpr (by simp [repMid, child, Array.toList_push])
  have hNotRm : ¬ (pHasPath finalRep.removed child = true) := fun h => hNotRmB.mp (hRmIff.mp h)
  have hAfterPres' : NodesFilteredPres (fun k => underDir child k = true ∨ normKey k = normKey root) sBefore sFinal := hAfterPres
  have hChildFin : ((mockFs.lstat child).run sFinal).1.isOk = true := by
    rw [nodesFilteredPres_lstat (nodesFilteredPres_trans hBeforePres hAfterPres') child hPChild, mockFs_lstat_run]
    dsimp only; rw [hChildPure]; rfl
  exact ⟨⟨hSkMem, hNotRm⟩, hChildFin,
    ⟨isSorted_sortStrings _, isSorted_sortStrings _, isSorted_sortStrings _, isSorted_sortStrings _⟩, trivial⟩

/-- Non-vacuity `CanReach` witness for Spec 14 (`test_tempdir_cleanupStaleTempDirs_scopeAndSymlinkSafety`). -/
theorem reach_tempdir_cleanupStaleTempDirs_scopeAndSymlinkSafety :
    CanReach (test_tempdir_cleanupStaleTempDirs_scopeAndSymlinkSafety
      (S := TempDirMockState) Internal.mkApiM mockFs mockTime mockUuid mockEnv) := by
  dsimp only [test_tempdir_cleanupStaleTempDirs_scopeAndSymlinkSafety, CanReach]
  let s₀ : TempDirMockState :=
    { nodes := [("/tmp", .dir 0 0o755), ("/tmp/keep-me", .dir 0 0o755)], nowSec := 100 }
  refine ⟨s₀, "/tmp", "tmp-", "keep-me", 10, ⟨by decide, by decide⟩, by decide,
    ⟨mockNodeStat (.dir 0 0o755), rfl, ⟨rfl, rfl, rfl, rfl⟩⟩,
    ⟨mockNodeStat (.dir 0 0o755), rfl, Or.inl (by decide)⟩, ?_⟩
  have hRes :
      ((Internal.mkApiM mockFs mockTime mockUuid mockEnv).cleanupStaleTempDirs (some "/tmp") "tmp-" 10).run s₀ =
        (.ok { removed := #[], keptLocked := #[], keptFresh := #[], skipped := #["/tmp/keep-me"], failed := #[] }, s₀) := rfl
  rw [hRes]
  dsimp only
  rw [canReach_assert, canReach_assert, canReach_assert_end]
  exact ⟨⟨by decide, by decide⟩, rfl, ⟨by decide, by decide, by decide, by decide⟩, trivial⟩

private theorem spec15_partialFail_exec (s₀ : TempDirMockState)
    (root dirPrefix childName : String) (maxAgeSec : Nat)
    (hvr : pValidRoot root = true) (hvp : pValidPrefix dirPrefix = true)
    (hcV : pValidEntryName childName = true) (hPref : dirPrefix.toList.isPrefixOf childName.toList = true)
    (stRoot stChild stLock : FileStat)
    (hRootPure : mockStatPure s₀ root = .ok stRoot) (hRwx : pHasRwx stRoot)
    (childNode : MockNode) (hLookChild : lookupNode s₀.nodes (mockJoin root childName) = some childNode)
    (hStChild : mockNodeStat childNode = stChild) (hcDir : pHasRwx stChild)
    (lockIno : Nat) (lockC : String) (lockT : Int) (lockM : Nat)
    (hLookLock : lookupNode s₀.nodes (mockJoin (mockJoin root childName) ".lock") = some (.file lockIno lockC lockT lockM))
    (hStLock : mockNodeStat (.file lockIno lockC lockT lockM) = stLock) (hlFile : stLock.kind = .file)
    (payIno : Nat) (payC : String) (payT : Int) (payM : Nat)
    (hLookPay : lookupNode s₀.nodes (mockJoin (mockJoin root childName) "locked_child.txt") = some (.file payIno payC payT payM))
    (hConfF : mockHasConflict s₀.locks lockIno .exclusive = false) :
    let child := mockJoin root childName
    let lockPath := mockJoin child ".lock"
    let payload := mockJoin child "locked_child.txt"
    let fsFailChild : FsApiM (StateM TempDirMockState) :=
      { mockFs with
        unlink := fun p miss =>
          if p == payload then pure (.error { kind := .permissionDenied, path := some p, message := "cannot unlink" })
          else mockFs.unlink p miss }
    ∃ rep s₁,
      ((Internal.mkApiM fsFailChild mockTime mockUuid mockEnv).cleanupStaleTempDirs (some root) dirPrefix maxAgeSec).run s₀ = (.ok rep, s₁) ∧
      ¬ pHasPath rep.removed child = true ∧
      ¬ pHasPath rep.keptFresh child = true ∧
      (!rep.failed.isEmpty) = true ∧
      ((mockFs.lstat lockPath).run s₁).1.isOk = true ∧
      ((mockFs.tryWithFileLock lockPath .exclusive false (pure (.ok ()))).run s₁).1 = .ok (some ()) := by
  intro child lockPath payload fsFailChild
  have hrNe : root ≠ "" := validRoot_ne_empty root hvr
  have ⟨hcNe, _, _, hcSlash⟩ := validEntryName_parts childName hcV
  have hcFullNe : child ≠ "" := mockJoin_ne_empty root childName hcNe
  have hLockNorm : normKey lockPath = lockPath := normKey_mockJoin child ".lock" (by decide) (by decide)
  have hFsJoin : fsFailChild.join = mockJoin := by dsimp only [fsFailChild, mockFs]; try rfl
  have hFsLstat : fsFailChild.lstat = mockFs.lstat := by dsimp only [fsFailChild]; try rfl
  have hFsStat : fsFailChild.stat = mockFs.stat := by dsimp only [fsFailChild]; try rfl
  have hFsList : fsFailChild.listDir = mockFs.listDir := by dsimp only [fsFailChild]; try rfl
  have hFsRm : fsFailChild.rmtree = mockFs.rmtree := by dsimp only [fsFailChild]; try rfl
  have hFsRmdir : fsFailChild.rmdir = mockFs.rmdir := by dsimp only [fsFailChild]; try rfl
  have hFsTry : ∀ {α : Type}, @fsFailChild.tryWithFileLock α = @mockFs.tryWithFileLock α :=
    fun {_} => by dsimp only [fsFailChild]; try rfl
  have hOpsFail : SweepFsOps fsFailChild :=
    ⟨hFsJoin, hFsStat, hFsLstat, hFsList, hFsTry, hFsRm, hFsRmdir, fun p miss s => by
      dsimp only [fsFailChild]
      split
      · exact Or.inr ⟨_, rfl⟩
      · exact Or.inl rfl⟩
  obtain ⟨before, after, repBefore, sBefore, _, _, _, _, hBeforePres, hNotRmB, _, hNotKFB, _, hExec⟩ :=
    cleanupStaleTempDirs_split_exec fsFailChild hOpsFail s₀ root dirPrefix childName maxAgeSec
      hvr hvp hcV stRoot hRootPure hRwx childNode hLookChild
  obtain ⟨hPChild, hPUnder, hPLock, _⟩ := nodesFilteredPres_child_P (root := root) hcV
  have hLookLockBefore : lookupNode sBefore.nodes lockPath = some (.file lockIno lockC lockT lockM) := by
    rw [nodesFilteredPres_lookupNode hBeforePres lockPath hPLock]; exact hLookLock
  have hConfBefore : mockHasConflict sBefore.locks lockIno .exclusive = false := by
    rw [hBeforePres.2.1]; exact hConfF
  have hChildLstatBefore : (mockFs.lstat child).run sBefore = (.ok stChild, sBefore) := by
    rw [nodesFilteredPres_lstat hBeforePres child hPChild, mockFs_lstat_run]
    dsimp only [mockLstatPure]; rw [hLookChild]; exact Prod.ext (congrArg Except.ok hStChild) rfl
  have hLockLstatBefore : (mockFs.lstat lockPath).run sBefore = (.ok stLock, sBefore) := by
    rw [nodesFilteredPres_lstat hBeforePres lockPath hPLock, mockFs_lstat_run]
    dsimp only [mockLstatPure]; rw [hLookLock]; exact Prod.ext (congrArg Except.ok hStLock) rfl
  let sLockBefore := { sBefore with locks := (lockIno, .exclusive) :: sBefore.locks }
  have hChildStatBefore : mockStatPure sBefore child = .ok stChild := by
    dsimp only [mockStatPure, mockLstatPure]
    rw [nodesFilteredPres_lookupNode hBeforePres child hPChild, hLookChild]
    exact congrArg Except.ok hStChild
  have ⟨hListChildBefore, hNdNames, hValidNames⟩ :=
    mockFs_listDir_run_of_rwx sBefore child stChild hChildStatBefore hcDir
  have hPayUnder : underDir child payload = true :=
    underDir_mockJoin_self child "locked_child.txt" hcFullNe (normKey_mockJoin root childName hcNe hcSlash)
      (mockJoin_ne_slash root childName hrNe hcNe) (by decide) (by decide)
  have hPPay : ∀ k, normKey k = normKey payload → underDir child k = true ∨ normKey k = normKey root :=
    fun k hk => hPUnder k (by rw [underDir_eq_of_normKey_eq _ k payload hk]; exact hPayUnder)
  have hPayBefore : lookupNode sBefore.nodes payload = some (.file payIno payC payT payM) := by
    rw [nodesFilteredPres_lookupNode hBeforePres payload hPPay]
    exact hLookPay
  have hPayMem : "locked_child.txt" ∈
      Internal.sortStrings (eraseDupStrings (sBefore.nodes.filterMap (fun e => mockParentChild (normKey child) e.1))) :=
    mockFs_listDir_mem_of_lookupNode sBefore child "locked_child.txt" hcFullNe (by decide) (.file payIno payC payT payM) hPayBefore
  let names := Internal.sortStrings (eraseDupStrings (sBefore.nodes.filterMap (fun e => mockParentChild (normKey child) e.1)))
  obtain ⟨te, sInner, hFailRun, hLockPresInner⟩ :=
    removeNonLockChildren_fail_with_lock_intact child payload hcFullNe rfl fsFailChild hFsLstat hFsJoin hFsRm
      (fun p miss s => by dsimp only [fsFailChild]; split <;> rfl)
      names hValidNames hNdNames hPayMem sLockBefore ⟨payIno, payC, payT, payM, hPayBefore⟩
  have hListLock : (mockFs.listDir child).run sLockBefore = (.ok names.toArray, sLockBefore) := by
    rw [mockFs_listDir_with_locks sBefore ((lockIno, .exclusive) :: sBefore.locks) child, congrArg Prod.fst hListChildBefore]
  have hRemLocked : (Internal.removeLockedTempDir fsFailChild child lockPath).run sLockBefore = (.ok (.error te), sInner) := by
    dsimp only [Internal.removeLockedTempDir]
    rw [hFsList, stateM_bind_run, hListLock]
    dsimp only [Array.toList]
    rw [stateM_bind_run, hFailRun]
    exact stateM_pure_run _ _
  let sMid := { sInner with locks := mockRemoveFirstLock lockIno .exclusive sInner.locks }
  let repMid : CleanupReport := { repBefore with failed := repBefore.failed.push te }
  have hSweepMid : (Internal.sweepEntry fsFailChild root dirPrefix maxAgeSec
      ((mockTime.nowTimestamp.run s₀).1.toSecondsSinceUnixEpoch.val) repBefore childName).run sBefore =
      (repMid, sMid) := by
    dsimp only [Internal.sweepEntry]
    rw [hFsJoin]
    have hPrefF : (!dirPrefix.toList.isPrefixOf childName.toList) = false := by rw [hPref]; rfl
    simp only [hPrefF, Bool.false_eq_true, ↓reduceIte]
    rw [hFsLstat, stateM_bind_run, hChildLstatBefore]; dsimp only
    have hNotDir : (stChild.kind != .dir) = false := by rw [hcDir.1]; rfl
    simp only [hNotDir, Bool.false_eq_true, ↓reduceIte]
    rw [stateM_bind_run, hLockLstatBefore]; dsimp only
    have hNotFile : (stLock.kind != .file) = false := by rw [hlFile]; rfl
    simp only [hNotFile, Bool.false_eq_true, ↓reduceIte]
    rw [hFsTry, stateM_bind_run, mockFs_tryWithFileLock_existing_ok_run sBefore lockPath .exclusive false lockIno lockC lockT lockM hLockNorm hLookLockBefore hConfBefore]
    rw [hRemLocked]
    dsimp only [Except.map]
    exact stateM_pure_run _ _
  cases hAfterRun : (Internal.sweepEntries fsFailChild root dirPrefix maxAgeSec ((mockTime.nowTimestamp.run s₀).1.toSecondsSinceUnixEpoch.val) repMid after).run sMid with
  | mk repAfter sFinal =>
    have hExec' := hExec repMid sMid hSweepMid
    rw [hAfterRun] at hExec'
    dsimp only at hExec'
    obtain ⟨hCleanRun, hAfterPres, hRmIff, _, hKFIff, _, hFailNonEmpty, _⟩ := hExec'
    let finalRep : CleanupReport :=
      { removed := (Internal.sortStrings repAfter.removed.toList).toArray
        keptLocked := (Internal.sortStrings repAfter.keptLocked.toList).toArray
        keptFresh := (Internal.sortStrings repAfter.keptFresh.toList).toArray
        skipped := (Internal.sortStrings repAfter.skipped.toList).toArray
        failed := repAfter.failed }
    have hNotRm : ¬ (pHasPath finalRep.removed child = true) := fun h => hNotRmB.mp (hRmIff.mp h)
    have hNotKF : ¬ (pHasPath finalRep.keptFresh child = true) := fun h => hNotKFB.mp (hKFIff.mp h)
    have hMidFail : repMid.failed.isEmpty = false := by
      simp only [repMid, Array.isEmpty, Array.size_push]
      exact decide_eq_false (Nat.succ_ne_zero _)
    have hFinFail : (!finalRep.failed.isEmpty) = true := by
      rw [hFailNonEmpty hMidFail]; rfl
    have hLockMidLocks : sMid.locks = sBefore.locks := by
      change mockRemoveFirstLock lockIno .exclusive sInner.locks = sBefore.locks
      rw [hLockPresInner.2.1]; exact mockRemoveFirstLock_head lockIno .exclusive sBefore.locks
    have hPresLock0B : NodesFilteredPres (fun k => normKey k = normKey lockPath) s₀ sBefore :=
      nodesFilteredPres_mono hPLock hBeforePres
    have hPresLockBM : NodesFilteredPres (fun k => normKey k = normKey lockPath) sBefore sMid :=
      ⟨hLockPresInner.1, hLockMidLocks, hLockPresInner.2.2.1, hLockPresInner.2.2.2.1, hLockPresInner.2.2.2.2.1, hLockPresInner.2.2.2.2.2⟩
    have hPresLockMF : NodesFilteredPres (fun k => normKey k = normKey lockPath) sMid sFinal :=
      nodesFilteredPres_mono hPLock hAfterPres
    have hPresLock0F := nodesFilteredPres_trans hPresLock0B (nodesFilteredPres_trans hPresLockBM hPresLockMF)
    have hLookLockFin : lookupNode sFinal.nodes lockPath = some (.file lockIno lockC lockT lockM) := by
      rw [nodesFilteredPres_lookupNode hPresLock0F lockPath (fun _ hk => hk)]; exact hLookLock
    have hLockFinIsOk : ((mockFs.lstat lockPath).run sFinal).1.isOk = true := by
      rw [mockFs_lstat_run]; unfold mockLstatPure; rw [hLookLockFin]; rfl
    have hConfFin : mockHasConflict sFinal.locks lockIno .exclusive = false := by
      rw [hPresLock0F.2.1]; exact hConfF
    have hTryFin : ((mockFs.tryWithFileLock lockPath .exclusive false (pure (.ok ()))).run sFinal).1 = .ok (some ()) := by
      rw [mockFs_tryWithFileLock_existing_ok_run sFinal lockPath .exclusive false lockIno lockC lockT lockM hLockNorm hLookLockFin hConfFin]
      rfl
    refine ⟨finalRep, sFinal, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact hCleanRun
    · exact hNotRm
    · exact hNotKF
    · exact hFinFail
    · exact hLockFinIsOk
    · exact hTryFin

/-- Spec 15: `cleanupStaleTempDirs` rejects non-regular `.lock` files into `failed` and preserves `.lock` intact and unlocked if deleting a payload fails. -/
theorem proof_tempdir_cleanupStaleTempDirs_nonRegularLockAndPartialFailureSafety :
    AllPass (test_tempdir_cleanupStaleTempDirs_nonRegularLockAndPartialFailureSafety
      (S := TempDirMockState) Internal.mkApiM mockFs mockTime mockUuid mockEnv) := by
  dsimp only [test_tempdir_cleanupStaleTempDirs_nonRegularLockAndPartialFailureSafety, AllPass]
  intro s₀ root dirPrefix childName maxAgeSec ⟨hvr, hvp⟩ hcV hPref ⟨stRoot, hRoot, hRwx⟩ ⟨stChild, hChild, hcDir⟩
  let child := mockJoin root childName
  let lockPath := mockJoin child ".lock"
  have hRootPure : mockStatPure s₀ root = .ok stRoot := by rw [mockFs_stat_run] at hRoot; exact hRoot
  have hChildPure : mockLstatPure s₀ child = .ok stChild := by rw [mockFs_lstat_run, mockFs_join_eq] at hChild; exact hChild
  rw [mockFs_join_eq]
  obtain ⟨childNode, hLookChild, hStChild⟩ := lookupNode_of_lstat_ok s₀ child stChild hChildPure
  rw [mockFs_lstat_run]
  cases hlLock : mockLstatPure s₀ lockPath with
  | error fe =>
    dsimp only
    intro hFalse; cases hFalse
  | ok stLock =>
    dsimp only
    by_cases hNotFile : (stLock.kind != .file) = true
    · simp only [hNotFile, ↓reduceIte]
      obtain ⟨before, after, repBefore, sBefore, _, _, _, _, hBeforePres, hNotRmB, _, hNotKFB, _, hExec⟩ :=
        cleanupStaleTempDirs_split_exec mockFs sweepFsOps_mockFs s₀ root dirPrefix childName maxAgeSec
          hvr hvp hcV stRoot hRootPure hRwx childNode hLookChild
      obtain ⟨hPChild, _, hPLock, _⟩ := nodesFilteredPres_child_P (root := root) hcV
      have hChildBefore : (mockFs.lstat child).run sBefore = (.ok stChild, sBefore) := by
        rw [nodesFilteredPres_lstat hBeforePres child hPChild, mockFs_lstat_run]; dsimp only; rw [hChildPure]
      have hLockBefore : (mockFs.lstat lockPath).run sBefore = (.ok stLock, sBefore) := by
        rw [nodesFilteredPres_lstat hBeforePres lockPath hPLock, mockFs_lstat_run]; dsimp only; rw [hlLock]
      let errExp : TempDirError := { kind := .invalidInput, path := some lockPath, message := "lock entry is not a regular file" }
      let repMid : CleanupReport := { repBefore with failed := repBefore.failed.push errExp }
      have hSweepMid : (Internal.sweepEntry mockFs root dirPrefix maxAgeSec
          ((mockTime.nowTimestamp.run s₀).1.toSecondsSinceUnixEpoch.val) repBefore childName).run sBefore =
          (repMid, sBefore) := by
        dsimp only [Internal.sweepEntry]
        rw [mockFs_join_eq]
        have hPrefF : (!dirPrefix.toList.isPrefixOf childName.toList) = false := by rw [hPref]; rfl
        have hNotDir : (stChild.kind != .dir) = false := by rw [hcDir.1]; rfl
        simp only [hPrefF, Bool.false_eq_true, ↓reduceIte]
        rw [stateM_bind_run, hChildBefore]; dsimp only
        simp only [hNotDir, Bool.false_eq_true, ↓reduceIte]
        rw [stateM_bind_run, hLockBefore]; dsimp only
        simp only [hNotFile, ↓reduceIte]
        exact stateM_pure_run _ _
      obtain ⟨hCleanRun, hAfterPres, hRmIff, _, hKFIff, _, _, hFailMem⟩ := hExec repMid sBefore hSweepMid
      let repAfter := (Internal.sweepEntries mockFs root dirPrefix maxAgeSec ((mockTime.nowTimestamp.run s₀).1.toSecondsSinceUnixEpoch.val) repMid after).run sBefore |>.1
      let sFinal := (Internal.sweepEntries mockFs root dirPrefix maxAgeSec ((mockTime.nowTimestamp.run s₀).1.toSecondsSinceUnixEpoch.val) repMid after).run sBefore |>.2
      let finalRep : CleanupReport :=
        { removed := (Internal.sortStrings repAfter.removed.toList).toArray
          keptLocked := (Internal.sortStrings repAfter.keptLocked.toList).toArray
          keptFresh := (Internal.sortStrings repAfter.keptFresh.toList).toArray
          skipped := (Internal.sortStrings repAfter.skipped.toList).toArray
          failed := repAfter.failed }
      rw [mkApiM_cleanupStaleTempDirs_eq] at hCleanRun
      dsimp only [StateT.run, mockTime] at hCleanRun
      dsimp only [Internal.mkApiM, StateT.run, mockTime]
      rw [hCleanRun]
      dsimp only [AllPass]
      rw [allPass_assert, allPass_assert, allPass_assert_end]
      have hNotRm : ¬ (pHasPath finalRep.removed child = true) := fun h => hNotRmB.mp (hRmIff.mp h)
      have hNotKF : ¬ (pHasPath finalRep.keptFresh child = true) := fun h => hNotKFB.mp (hKFIff.mp h)
      have hErrInFin : errExp ∈ finalRep.failed.toList := hFailMem errExp (by simp [repMid, Array.toList_push])
      have hAnyErr : finalRep.failed.any (fun e => e.kind == .invalidInput && e.path == some lockPath) = true := by
        rw [← Array.any_toList, List.any_eq_true]
        exact ⟨errExp, hErrInFin, by simp [errExp]; rfl⟩
      have hAfterPres' : NodesFilteredPres (fun k => underDir child k = true ∨ normKey k = normKey root) sBefore sFinal := hAfterPres
      have hChildFin : ((mockFs.lstat child).run sFinal).1.isOk = true := by
        rw [nodesFilteredPres_lstat (nodesFilteredPres_trans hBeforePres hAfterPres') child hPChild, mockFs_lstat_run]
        dsimp only; rw [hChildPure]; rfl
      exact ⟨⟨hNotRm, hNotKF⟩, hAnyErr, hChildFin, trivial⟩
    · have hNotFileF : (stLock.kind != .file) = false := Bool.eq_false_iff.mpr hNotFile
      have hlFile : stLock.kind = .file := by revert hNotFileF; cases stLock.kind <;> decide
      simp only [hNotFileF, Bool.false_eq_true, ↓reduceIte]
      intro ⟨stP, hPay, hpFile⟩ hTryExcl
      have hPayPure : mockLstatPure s₀ (mockJoin child "locked_child.txt") = .ok stP := by
        rw [mockFs_lstat_run] at hPay; exact hPay
      obtain ⟨ndPay, hLookPay, hStPay⟩ := lookupNode_of_lstat_ok s₀ (mockJoin child "locked_child.txt") stP hPayPure
      obtain ⟨ndLock, hLookLock, hStLock⟩ := lookupNode_of_lstat_ok s₀ lockPath stLock hlLock
      cases ndLock with
      | dir _ _ => simp [mockNodeStat] at hStLock; rw [← hStLock] at hlFile; cases hlFile
      | symlink _ _ => simp [mockNodeStat] at hStLock; rw [← hStLock] at hlFile; cases hlFile
      | file lockIno lockC lockT lockM =>
        cases ndPay with
        | dir _ _ => simp [mockNodeStat] at hStPay; rw [← hStPay] at hpFile; cases hpFile
        | symlink _ _ => simp [mockNodeStat] at hStPay; rw [← hStPay] at hpFile; cases hpFile
        | file payIno payC payT payM =>
          have hLockNorm : normKey lockPath = lockPath := normKey_mockJoin child ".lock" (by decide) (by decide)
          have hConfF := tryWithFileLock_excl_false_conflict s₀ lockPath hLockNorm lockIno lockC lockT lockM hLookLock hTryExcl
          obtain ⟨rep, s₁, hRun, h1, h2, h3, h4, h5⟩ := spec15_partialFail_exec s₀ root dirPrefix childName maxAgeSec hvr hvp hcV hPref
            stRoot stChild stLock hRootPure hRwx childNode hLookChild hStChild hcDir
            lockIno lockC lockT lockM hLookLock hStLock hlFile payIno payC payT payM hLookPay hConfF
          rw [mkApiM_cleanupStaleTempDirs_eq] at hRun
          dsimp only [StateT.run, mockTime] at hRun
          have hJoinEq : mockFs.join = mockJoin := rfl
          rw [hJoinEq] at hRun
          dsimp only [Internal.mkApiM, StateT.run, mockTime]
          rw [hRun]
          dsimp only [AllPass]
          rw [allPass_assert, allPass_assert, allPass_assert, allPass_assert_end]
          exact ⟨⟨h1, h2⟩, h3, h4, h5, trivial⟩

/-- Non-vacuity `CanReach` witness for Spec 15 (`test_tempdir_cleanupStaleTempDirs_nonRegularLockAndPartialFailureSafety`). -/
theorem reach_tempdir_cleanupStaleTempDirs_nonRegularLockAndPartialFailureSafety :
    CanReach (test_tempdir_cleanupStaleTempDirs_nonRegularLockAndPartialFailureSafety
      (S := TempDirMockState) Internal.mkApiM mockFs mockTime mockUuid mockEnv) := by
  dsimp only [test_tempdir_cleanupStaleTempDirs_nonRegularLockAndPartialFailureSafety, CanReach]
  let s₀ : TempDirMockState :=
    { nodes := [("/tmp", .dir 0 0o755), ("/tmp/tmp-a", .dir 0 0o755), ("/tmp/tmp-a/.lock", .symlink "/etc/passwd" 0)],
      nowSec := 100 }
  refine ⟨s₀, "/tmp", "tmp-", "tmp-a", 10, ⟨by decide, by decide⟩, by decide, by decide,
    ⟨mockNodeStat (.dir 0 0o755), rfl, ⟨rfl, rfl, rfl, rfl⟩⟩,
    ⟨mockNodeStat (.dir 0 0o755), rfl, ⟨rfl, rfl, rfl, rfl⟩⟩, ?_⟩
  rw [mockFs_lstat_run]
  rw [show mockLstatPure s₀ (mockFs.join (mockFs.join "/tmp" "tmp-a") ".lock") = .ok (mockNodeStat (.symlink "/etc/passwd" 0)) from rfl]
  dsimp only
  have hNotFile : ((mockNodeStat (.symlink "/etc/passwd" 0)).kind != .file) = true := rfl
  simp only [hNotFile, ↓reduceIte]
  have hRes :
      ((Internal.mkApiM mockFs mockTime mockUuid mockEnv).cleanupStaleTempDirs (some "/tmp") "tmp-" 10).run s₀ =
        (.ok { removed := #[], keptLocked := #[], keptFresh := #[], skipped := #[],
               failed := #[{ kind := .invalidInput, path := some "/tmp/tmp-a/.lock", message := "lock entry is not a regular file" }] }, s₀) := rfl
  rw [hRes]
  dsimp only
  rw [canReach_assert, canReach_assert, canReach_assert_end]
  simp only [mockFs_join_eq]
  rw [show mockJoin "/tmp" "tmp-a" = "/tmp/tmp-a" from rfl,
      show mockJoin "/tmp/tmp-a" ".lock" = "/tmp/tmp-a/.lock" from rfl]
  refine ⟨⟨by decide, by decide⟩, ?_, rfl, trivial⟩
  rw [← Array.any_toList, List.any_eq_true]
  exact ⟨_, List.Mem.head _, rfl⟩

end LeanSwe.TempDir.Proofs
