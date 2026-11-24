import LeanSwe.TempDir.Proofs.Shared
import LeanSwe.TempDir.Proofs.WithTempDirProofs
import LeanSwe.TempDir.Proofs.LockedProofs
/-!
Shared preservation lemmas and split execution theorem for `LeanSwe.TempDir` stale-directory sweep proofs.
-/
namespace LeanSwe.TempDir.Proofs
open Core Core.NondetTest LeanSwe.Time LeanSwe.Uuid LeanSwe.EnvVars
open LeanSwe.Fs (FsApiM FsError FsErrorKind EntryKind FileStat LockMode)
open LeanSwe.TempDir.Model
open LeanSwe.TempDir.Model.Internal
/-- Helper predicate checking a valid temporary directory prefix string. -/
def pValidPrefix (p : String) : Bool := !p.isEmpty && p.toList.head? != some '.' && !('/' ∈ p.toList) && !(Char.ofNat 0 ∈ p.toList)
/-- Helper predicate checking a valid root directory path string. -/
def pValidRoot (r : String) : Bool := !r.isEmpty && !(Char.ofNat 0 ∈ r.toList)
/-- Helper predicate checking a valid single directory entry name. -/
def pValidEntryName (n : String) : Bool := !n.isEmpty && n != "." && n != ".." && !('/' ∈ n.toList) && !(Char.ofNat 0 ∈ n.toList)
/-- Helper predicate asserting directory `rwx` permission bits on `FileStat`. -/
def pHasRwx (st : FileStat) : Prop := st.kind = .dir ∧ (st.mode / 256) % 2 = 1 ∧ (st.mode / 128) % 2 = 1 ∧ (st.mode / 64) % 2 = 1
/-- Helper predicate testing whether `xs` contains path `p`. -/
def pHasPath (xs : Array String) (p : String) : Bool := xs.toList.contains p
/-- Helper predicate testing whether `xs` is lexicographically sorted. -/
def pIsSorted (xs : Array String) : Bool := xs.toList.Pairwise (· ≤ ·)
theorem validEntryName_parts (n : String) (h : pValidEntryName n = true) : n ≠ "" ∧ n ≠ "." ∧ n ≠ ".." ∧ ¬('/' ∈ n.toList) := by
  unfold pValidEntryName at h; simp only [Bool.and_eq_true, Bool.not_eq_true', bne_iff_ne, ne_eq] at h
  rcases h with ⟨⟨⟨⟨hn, h1⟩, h2⟩, h3⟩, _⟩; exact ⟨fun he => by rw [he] at hn; simp [String.isEmpty] at hn, h1, h2, by simpa using h3⟩
theorem list_nodup_split {α : Type} (xs : List α) (x : α) (hNd : xs.Nodup) (hx : x ∈ xs) : ∃ a b, xs = a ++ x :: b ∧ x ∉ a ∧ x ∉ b := by
  induction xs with | nil => cases hx | cons y ys ih =>
    have ⟨hy, hYs⟩ := List.nodup_cons.mp hNd; simp only [List.mem_cons] at hx
    rcases hx with rfl | hxYs; · exact ⟨[], ys, rfl, List.not_mem_nil, hy⟩
    · obtain ⟨a, b, hEq, hna, hnb⟩ := ih hYs hxYs
      exact ⟨y :: a, b, by simp [hEq], fun h => by rcases List.mem_cons.mp h with rfl | ha; exact hy hxYs; exact hna ha, hnb⟩
theorem list_filter_filterMap_eq {α β : Type} (xs : List α) (keep : α → Bool) (f : α → Option β) (h : ∀ x, (f x).isSome = true → keep x = true) : (xs.filter keep).filterMap f = xs.filterMap f := by
  induction xs with | nil => rfl | cons x xs ih => cases hx : f x with | none => by_cases hk : keep x = true <;> simp [hk, hx, ih] | some v => simp [h x (by simp [hx]), hx, ih]
theorem hasPath_toArray_mem (xs : List String) (p : String) : pHasPath xs.toArray p = true ↔ p ∈ xs := by simp [pHasPath]
theorem mem_push_ne {xs : Array String} {q p : String} (hne : p ≠ q) : p ∈ (xs.push q).toList ↔ p ∈ xs.toList := by simp [Array.toList_push, hne]
theorem isSorted_sortStrings (xs : List String) : pIsSorted (Internal.sortStrings xs).toArray = true := by simpa [pIsSorted] using pairwise_sortStrings xs
theorem list_find_filter_none {α : Type} (p keep : α → Bool) (xs : List α) (h : xs.find? p = none) : (xs.filter keep).find? p = none := by
  induction xs with | nil => rfl | cons x xs ih =>
    simp only [List.find?_cons] at h; cases hpx : p x with | true => simp [hpx] at h | false =>
      rw [hpx] at h; dsimp only at h; by_cases hk : keep x = true
      · rw [List.filter_cons]; simp [hk, hpx, ih h]
      · rw [List.filter_cons, Bool.eq_false_iff.mpr hk]; exact ih h
theorem list_filter_filter_and {α : Type} (xs : List α) (p q : α → Bool) : (xs.filter p).filter q = xs.filter (fun x => p x && q x) := by
  induction xs with | nil => rfl | cons x xs ih => cases hp : p x <;> cases hq : q x <;> simp [List.filter, hp, hq, ih]
theorem mockFs_lstat_notFound_lookup_none (s : TempDirMockState) (p : String) (e : FsError) (hl : ((mockFs.lstat p).run s).1 = .error e) : lookupNode s.nodes p = none := by
  rw [mockFs_lstat_run] at hl; unfold mockLstatPure at hl; cases hk : lookupNode s.nodes p <;> simp_all
theorem lookupNode_filter_ne_none (nodes : List (String × MockNode)) (p : String) (hp : normKey p = p) : lookupNode (nodes.filter (fun e => normKey e.1 != p)) p = none := by
  unfold lookupNode; rw [hp]; induction nodes with | nil => rfl | cons x xs ih =>
    rw [List.filter_cons]; cases hb : normKey x.1 == p with | true => simp [beq_iff_eq.mp hb] | false =>
      by_cases hne : (normKey x.1 != p) = true
      · simp only [hne, ↓reduceIte, List.find?_cons, hb]; exact ih
      · simp only [Bool.eq_false_iff.mpr hne, Bool.false_eq_true, ↓reduceIte]; exact ih
theorem tryWithFileLock_excl_false_conflict (s : TempDirMockState) (p : String) (hp : normKey p = p) (ino : Nat) (c : String) (t : Int) (m : Nat)
    (hLook : lookupNode s.nodes p = some (.file ino c t m)) (hTry : ((mockFs.tryWithFileLock p .exclusive false (pure (.ok ()))).run s).1 = .ok (some ())) : mockHasConflict s.locks ino .exclusive = false := by
  cases hc : mockHasConflict s.locks ino .exclusive with | false => rfl | true =>
    exfalso; rw [mockFs_tryWithFileLock_existing_conflict_run s p .exclusive false ino c t m hp hLook hc (pure (.ok ()))] at hTry; cases hTry
theorem mockFs_unlink_existing_run (s : TempDirMockState) (p : String) (miss : Bool) (ino : Nat) (c : String) (t : Int) (m : Nat) (hnorm : normKey p = p) (hnode : lookupNode s.nodes p = some (.file ino c t m)) :
    (mockFs.unlink p miss).run s = (.ok (), { s with nodes := s.nodes.filter (fun e => normKey e.1 != p) }) := by
  dsimp only [mockFs]; rw [stateM_bind_run, stateM_get_run]; dsimp only; rw [hnorm, hnode]; simp only [stateM_bind_run, stateM_set_run, stateM_pure_run]
theorem mockFs_rmdir_dir_run (s : TempDirMockState) (p : String) (t : Int) (m : Nat) (hnorm : normKey p = p) (hnode : lookupNode s.nodes p = some (.dir t m)) :
    (mockFs.rmdir p).run s = (.ok (), { s with nodes := s.nodes.filter (fun e => normKey e.1 != p) }) := by
  dsimp only [mockFs]; rw [stateM_bind_run, stateM_get_run]; dsimp only; rw [hnorm, hnode]; simp only [stateM_bind_run, stateM_set_run, stateM_pure_run]
theorem mockParentChild_self_join (root name : String) (hr : root ≠ "") (hn : pValidEntryName name = true) : mockParentChild (normKey root) (mockJoin root name) = some name := by
  have ⟨hne, _, _, hNoSlash⟩ := validEntryName_parts name hn; have hList := mockJoin_toList root name hr
  unfold mockParentChild; rw [normKey_idem, normKey_mockJoin root name hne hNoSlash]
  have hrE : (normKey root).isEmpty = false := Bool.eq_false_iff.mpr fun h => normKey_ne_empty hr ((string_isEmpty_iff_eq_empty _).mp h)
  have hP : (if (normKey root == "/") = true then "/" else normKey root ++ "/").toList = if (normKey root == "/") = true then ['/'] else (normKey root).toList ++ ['/'] := by by_cases h : (normKey root == "/") = true <;> simp [h, String.toList_append]
  have hIP : (if (normKey root == "/") = true then "/" else normKey root ++ "/").toList.isPrefixOf (mockJoin root name).toList = true := by rw [List.isPrefixOf_iff_prefix, hP, hList]; exact ⟨name.toList, rfl⟩
  have hD : String.ofList ((mockJoin root name).toList.drop (if (normKey root == "/") = true then "/" else normKey root ++ "/").length) = name := by
    rw [hList, show (if (normKey root == "/") = true then "/" else normKey root ++ "/").length = (if (normKey root == "/") = true then ['/'] else (normKey root).toList ++ ['/']).length by rw [← String.length_toList, hP], List.drop_left, String.ofList_toList]
  simp only [hrE, Bool.false_eq_true, ↓reduceIte, hIP, hD]; rw [show (!name.isEmpty && name != "." && name != ".." && !('/' ∈ name.toList) && !(Char.ofNat 0 ∈ name.toList)) = pValidEntryName name from rfl, hn]; rfl
theorem mockFs_listDir_prop (s : TempDirMockState) (dir : String) :
    ((mockFs.listDir dir).run s).2 = s ∧ (∀ arr, ((mockFs.listDir dir).run s).1 = .ok arr → ∀ nm ∈ arr.toList, pValidEntryName nm = true) := by
  dsimp only [mockFs]; rw [stateM_bind_run, stateM_get_run]; dsimp only
  cases lookupNode s.nodes (normKey dir) with | none => exact ⟨rfl, fun arr h => by cases h⟩ | some nd =>
    dsimp only; by_cases h1 : ((mockNodeStat nd).kind != EntryKind.dir) = true
    · simp only [h1, ↓reduceIte, stateM_pure_run]; exact ⟨trivial, fun arr h => by cases h⟩
    · simp only [Bool.eq_false_iff.mpr h1, Bool.false_eq_true, ↓reduceIte]; by_cases h2 : (!hasRx (mockNodeStat nd)) = true
      · simp only [h2, ↓reduceIte, stateM_pure_run]; exact ⟨trivial, fun arr h => by cases h⟩
      · simp only [Bool.eq_false_iff.mpr h2, Bool.false_eq_true, ↓reduceIte, stateM_pure_run]; refine ⟨trivial, fun arr hArr nm hnm => ?_⟩
        rw [← Except.ok.inj hArr, mem_sortStrings, mem_eraseDupStrings, List.mem_filterMap] at hnm; rcases hnm with ⟨e, _, he⟩; exact validEntryName_of_mockParentChild (normKey dir) e.1 nm he
theorem mockFs_listDir_run_of_rwx (s : TempDirMockState) (dir : String) (st : FileStat) (hStat : mockStatPure s dir = .ok st) (hRwx : pHasRwx st) :
    let rp := normKey dir; let names := Internal.sortStrings (eraseDupStrings (s.nodes.filterMap (fun e => mockParentChild rp e.1)))
    (mockFs.listDir dir).run s = (.ok names.toArray, s) ∧ names.Nodup ∧ (∀ nm ∈ names, pValidEntryName nm = true) := by
  intro rp names; obtain ⟨nd, hLook, hSt⟩ := lookupNode_of_lstat_ok s dir st hStat; have hLookRp : lookupNode s.nodes rp = some nd := by simpa [lookupNode, rp, normKey_idem] using hLook
  refine ⟨?_, nodup_sortStrings _ (nodup_eraseDupStrings _), fun nm hnm => ?_⟩
  · dsimp only [mockFs]; rw [stateM_bind_run, stateM_get_run]; dsimp only; rw [hLookRp]; dsimp only; rw [hSt, show (st.kind != .dir) = false by rw [hRwx.1]; rfl, hasRx_of_hasRwx st hRwx]; simp only [Bool.false_eq_true, ↓reduceIte, Bool.not_true]; rfl
  · rw [mem_sortStrings, mem_eraseDupStrings, List.mem_filterMap] at hnm; rcases hnm with ⟨e, _, he⟩; exact validEntryName_of_mockParentChild rp e.1 nm he
theorem mockFs_listDir_mem_of_lookupNode (s : TempDirMockState) (dir childName : String) (hd : dir ≠ "") (hn : pValidEntryName childName = true)
    (ndChild : MockNode) (hLookChild : lookupNode s.nodes (mockJoin dir childName) = some ndChild) : childName ∈ Internal.sortStrings (eraseDupStrings (s.nodes.filterMap (fun e => mockParentChild (normKey dir) e.1))) := by
  have ⟨hcNe, _, _, hcNoSlash⟩ := validEntryName_parts childName hn; have hJoinNorm := normKey_mockJoin dir childName hcNe hcNoSlash; unfold lookupNode at hLookChild
  cases hf : s.nodes.find? (fun e => normKey e.1 == normKey (mockJoin dir childName)) with | none => simp [hf] at hLookChild | some p =>
    have hpEq : normKey p.1 = mockJoin dir childName := by have hb := List.find?_some hf; rwa [hJoinNorm, beq_iff_eq] at hb
    have hPc : mockParentChild (normKey dir) p.1 = some childName := by rw [show mockParentChild (normKey dir) p.1 = mockParentChild (normKey dir) (mockJoin dir childName) by unfold mockParentChild; rw [hpEq, hJoinNorm]]; exact mockParentChild_self_join dir childName hd hn
    rw [mem_sortStrings, mem_eraseDupStrings, List.mem_filterMap]; exact ⟨p, List.mem_of_find?_eq_some hf, hPc⟩
theorem mockFs_listDir_with_locks (s : TempDirMockState) (locks' : List (Nat × LockMode)) (dir : String) :
    (mockFs.listDir dir).run { s with locks := locks' } = (((mockFs.listDir dir).run s).1, { s with locks := locks' }) := by
  dsimp only [mockFs]; rw [stateM_bind_run, stateM_get_run, stateM_bind_run, stateM_get_run]; dsimp only
  cases lookupNode s.nodes (normKey dir) with | none => rfl | some _ => dsimp only; split <;> first | rfl | (split <;> rfl)
/-- Monotonic node-filter preservation invariant between two `TempDirMockState` snapshots. -/
def NodesFilteredPres (P : String → Prop) (s s' : TempDirMockState) : Prop :=
  (∃ keep : String → Bool, (∀ k, P k → keep k = true) ∧ s'.nodes = s.nodes.filter (fun e => keep e.1)) ∧
  s'.locks = s.locks ∧ s'.nextInode = s.nextInode ∧ s'.tmpdir = s.tmpdir ∧ s'.nowSec = s.nowSec ∧ s'.nextUuid = s.nextUuid
theorem nodesFilteredPres_refl (P : String → Prop) (s : TempDirMockState) : NodesFilteredPres P s s :=
  ⟨⟨fun _ => true, fun _ _ => rfl, by induction s.nodes with | nil => rfl | cons x xs ih => exact congrArg (x :: ·) ih⟩, rfl, rfl, rfl, rfl, rfl⟩
theorem nodesFilteredPres_trans {P : String → Prop} {s s1 s2 : TempDirMockState} (h1 : NodesFilteredPres P s s1) (h2 : NodesFilteredPres P s1 s2) : NodesFilteredPres P s s2 := by
  rcases h1 with ⟨⟨k1, hk1, hn1⟩, hl1, hi1, ht1, hs1, hu1⟩; rcases h2 with ⟨⟨k2, hk2, hn2⟩, hl2, hi2, ht2, hs2, hu2⟩
  refine ⟨⟨fun p => k1 p && k2 p, fun p hp => by simp [hk1 p hp, hk2 p hp], ?_⟩, hl2.trans hl1, hi2.trans hi1, ht2.trans ht1, hs2.trans hs1, hu2.trans hu1⟩
  rw [hn2, hn1, List.filter_filter]; congr 1; funext e; exact Bool.and_comm (k2 e.1) (k1 e.1)
theorem nodesFilteredPres_mono {P Q : String → Prop} {s s' : TempDirMockState} (hPQ : ∀ k, Q k → P k) (h : NodesFilteredPres P s s') : NodesFilteredPres Q s s' := by
  rcases h with ⟨⟨keep, hk, hn⟩, r⟩; exact ⟨⟨keep, fun k hq => hk k (hPQ k hq), hn⟩, r⟩
theorem nodesFilteredPres_lookupNode {P : String → Prop} {s s' : TempDirMockState} (hPres : NodesFilteredPres P s s') (p : String) (hp : ∀ k, normKey k = normKey p → P k) :
    lookupNode s'.nodes p = lookupNode s.nodes p := by
  rcases hPres with ⟨⟨keep, hk, hn⟩, _⟩; unfold lookupNode; rw [hn]; congr 1
  induction s.nodes with
  | nil => rfl
  | cons x xs ih =>
    by_cases hxp : (normKey x.1 == normKey p) = true
    · simp only [List.filter_cons, hk x.1 (hp x.1 (beq_iff_eq.mp hxp)), ↓reduceIte, List.find?_cons, hxp]
    · have hxpF : (normKey x.1 == normKey p) = false := Bool.eq_false_iff.mpr hxp
      by_cases hkx : keep x.1 = true
      · simp only [List.filter_cons, hkx, ↓reduceIte, List.find?_cons, hxpF]; exact ih
      · simp only [List.filter_cons, Bool.eq_false_iff.mpr hkx, Bool.false_eq_true, ↓reduceIte, List.find?_cons, hxpF]; exact ih
theorem nodesFilteredPres_lookupNode_none {P : String → Prop} {s s' : TempDirMockState} (hPres : NodesFilteredPres P s s') (p : String) (hNone : lookupNode s.nodes p = none) : lookupNode s'.nodes p = none := by
  rcases hPres with ⟨⟨keep, _, hn⟩, _⟩; unfold lookupNode at hNone ⊢; rw [hn]
  exact congrArg (Option.map Prod.snd) (list_find_filter_none _ _ s.nodes (by cases hf : s.nodes.find? (fun e => normKey e.1 == normKey p) with | none => rfl | some _ => simp [hf] at hNone))
theorem nodesFilteredPres_lstat {P : String → Prop} {s s' : TempDirMockState} (hPres : NodesFilteredPres P s s') (p : String) (hp : ∀ k, normKey k = normKey p → P k) :
    (mockFs.lstat p).run s' = (((mockFs.lstat p).run s).1, s') := by simp only [mockFs_lstat_run, mockLstatPure, nodesFilteredPres_lookupNode hPres p hp]
theorem nodesFilteredPres_listDir {P : String → Prop} {s s' : TempDirMockState} (hPres : NodesFilteredPres P s s') (dir : String)
    (hd : dir ≠ "") (hDirP : ∀ k, normKey k = normKey dir → P k) (hUnderP : ∀ k, underDir dir k = true → P k) :
    ((mockFs.listDir dir).run s').1 = ((mockFs.listDir dir).run s).1 ∧ ((mockFs.listDir dir).run s').2 = s' := by
  have hLook := nodesFilteredPres_lookupNode hPres (normKey dir) (fun k hk => hDirP k (by simpa [normKey_idem] using hk))
  have hUnderOfPc : ∀ k nm, mockParentChild (normKey dir) k = some nm → underDir dir k = true := by
    intro k nm hpc; unfold mockParentChild at hpc; rw [normKey_idem] at hpc
    have hdEmpty : (normKey dir).isEmpty = false := Bool.eq_false_iff.mpr fun h => normKey_ne_empty hd ((string_isEmpty_iff_eq_empty _).mp h)
    simp only [hdEmpty, Bool.false_eq_true, ↓reduceIte] at hpc
    (split at hpc <;> rename_i hSlash <;> split at hpc <;> try (simp at hpc))
    · rename_i hPref; unfold underDir; simp only [hSlash, ↓reduceIte, hPref, Bool.or_true]
    · rename_i hPref; unfold underDir; simp only [Bool.eq_false_iff.mpr hSlash, Bool.false_eq_true, ↓reduceIte, hPref, Bool.or_true]
  rcases hPres with ⟨⟨keep, hk, hn⟩, _⟩
  have hFm : s'.nodes.filterMap (fun e => mockParentChild (normKey dir) e.1) = s.nodes.filterMap (fun e => mockParentChild (normKey dir) e.1) := by
    rw [hn]; apply list_filter_filterMap_eq; intro e he; cases hpc : mockParentChild (normKey dir) e.1 with | none => simp [hpc] at he | some nm => exact hk e.1 (hUnderP e.1 (hUnderOfPc e.1 nm hpc))
  dsimp only [mockFs]; rw [stateM_bind_run, stateM_get_run, stateM_bind_run, stateM_get_run]; dsimp only; rw [hLook]
  cases lookupNode s.nodes (normKey dir) with
  | none => exact ⟨rfl, rfl⟩
  | some nd =>
    dsimp only; by_cases h1 : ((mockNodeStat nd).kind != EntryKind.dir) = true
    · simp only [h1, ↓reduceIte]; exact ⟨rfl, rfl⟩
    · have h1f : ((mockNodeStat nd).kind != EntryKind.dir) = false := Bool.eq_false_iff.mpr h1
      by_cases h2 : (!hasRx (mockNodeStat nd)) = true
      · simp only [h1f, h2, Bool.false_eq_true, ↓reduceIte]; exact ⟨rfl, rfl⟩
      · simp only [h1f, Bool.eq_false_iff.mpr h2, Bool.false_eq_true, ↓reduceIte, hFm]; exact ⟨rfl, rfl⟩
theorem nodesFilteredPres_child_P {root childName : String} (hcV : pValidEntryName childName = true) :
    let child := mockJoin root childName; let lockPath := mockJoin child ".lock"
    let P : String → Prop := fun k => underDir child k = true ∨ normKey k = normKey root
    (∀ k, normKey k = normKey child → P k) ∧ (∀ k, underDir child k = true → P k) ∧ (∀ k, normKey k = normKey lockPath → P k) ∧ (∀ k, normKey k = normKey root → P k) := by
  have ⟨hcNe, _, _, hcSlash⟩ := validEntryName_parts childName hcV; have hChildNorm := normKey_mockJoin root childName hcNe hcSlash
  have hChildNeSlash : mockJoin root childName ≠ "/" := by
    by_cases hRoot : root = ""
    · subst hRoot; intro hEq; rw [show mockJoin "" childName = childName from rfl] at hEq; exact hcSlash (hEq ▸ by decide)
    · exact mockJoin_ne_slash root childName hRoot hcNe
  have hUnderLock := underDir_mockJoin_self (mockJoin root childName) ".lock" (mockJoin_ne_empty root childName hcNe) hChildNorm hChildNeSlash (by decide) (by decide)
  refine ⟨fun k hk => Or.inl ?_, fun k hk => Or.inl hk, fun k hk => Or.inl ?_, fun k hk => Or.inr hk⟩
  · rw [underDir_eq_of_normKey_eq _ k (mockJoin root childName) hk]; exact underDir_refl _ hChildNorm
  · rw [underDir_eq_of_normKey_eq _ k (mockJoin (mockJoin root childName) ".lock") hk]; exact hUnderLock
/-- Report membership preservation across sweeping entries disjoint from `child`. -/
structure ReportPres (child : String) (r r' : CleanupReport) : Prop where
  /-- Preserves `removed` membership of `child`. -/ rm : child ∈ r'.removed.toList ↔ child ∈ r.removed.toList
  /-- Preserves `keptLocked` membership of `child`. -/ kl : child ∈ r'.keptLocked.toList ↔ child ∈ r.keptLocked.toList
  /-- Preserves `keptFresh` membership of `child`. -/ kf : child ∈ r'.keptFresh.toList ↔ child ∈ r.keptFresh.toList
  /-- Preserves `skipped` membership of `child`. -/ sk : child ∈ r'.skipped.toList ↔ child ∈ r.skipped.toList
  /-- Preserves non-emptiness of `failed`. -/ failNe : r.failed.isEmpty = false → r'.failed.isEmpty = false
  /-- Preserves element membership in `failed`. -/ failMem : ∀ e ∈ r.failed.toList, e ∈ r'.failed.toList
theorem reportPres_refl (child : String) (r : CleanupReport) : ReportPres child r r := ⟨Iff.rfl, Iff.rfl, Iff.rfl, Iff.rfl, id, fun _ h => h⟩
theorem reportPres_trans {child : String} {r r1 r2 : CleanupReport} (h1 : ReportPres child r r1) (h2 : ReportPres child r1 r2) : ReportPres child r r2 :=
  ⟨h2.rm.trans h1.rm, h2.kl.trans h1.kl, h2.kf.trans h1.kf, h2.sk.trans h1.sk, fun h => h2.failNe (h1.failNe h), fun e he => h2.failMem e (h1.failMem e he)⟩
/-- Bundled `FsApiM` agreement hypotheses for `cleanupStaleTempDirs` sweep proofs. -/
structure SweepFsOps (fs : FsApiM (StateM TempDirMockState)) : Prop where
  /-- `join` agrees with `mockJoin`. -/ hJoin : fs.join = mockJoin
  /-- `stat` agrees with `mockFs.stat`. -/ hStat : fs.stat = mockFs.stat
  /-- `lstat` agrees with `mockFs.lstat`. -/ hLstat : fs.lstat = mockFs.lstat
  /-- `listDir` agrees with `mockFs.listDir`. -/ hListDir : fs.listDir = mockFs.listDir
  /-- `tryWithFileLock` agrees with `mockFs.tryWithFileLock`. -/ hTryWfl : ∀ {α : Type}, @fs.tryWithFileLock α = @mockFs.tryWithFileLock α
  /-- `rmtree` agrees with `mockFs.rmtree`. -/ hRm : fs.rmtree = mockFs.rmtree
  /-- `rmdir` agrees with `mockFs.rmdir`. -/ hRmdir : fs.rmdir = mockFs.rmdir
  /-- `unlink` either agrees with `mockFs.unlink` or returns an error without modifying state. -/ hUnlink : ∀ p miss s, (fs.unlink p miss).run s = (mockFs.unlink p miss).run s ∨ ∃ fe, (fs.unlink p miss).run s = (.error fe, s)
theorem sweepFsOps_mockFs : SweepFsOps mockFs := ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, fun _ _ _ => Or.inl rfl⟩
theorem cleanupDirIgnoringNotFound_filteredPres (fs : FsApiM (StateM TempDirMockState)) (hRm : fs.rmtree = mockFs.rmtree)
    (target : String) (s : TempDirMockState) : NodesFilteredPres (fun k => underDir target k = false) s ((Internal.cleanupDirIgnoringNotFound fs target).run s).2 := by
  dsimp only [Internal.cleanupDirIgnoringNotFound]; rw [hRm]; dsimp only [mockFs, mockRmtreePure]; rw [stateM_bind_run, stateM_bind_run, stateM_get_run]; dsimp only
  cases lookupNode s.nodes (normKey target) with | none => exact nodesFilteredPres_refl _ s | some nd => cases nd with
    | file _ _ _ _ | symlink _ _ => exact nodesFilteredPres_refl _ s
    | dir _ _ => simp only [stateM_bind_run, stateM_set_run, stateM_pure_run]; exact ⟨⟨fun k => !underDir (normKey target) k, fun k hk => by simp [show underDir (normKey target) k = underDir target k by unfold underDir; rw [normKey_idem], hk], rfl⟩, rfl, rfl, rfl, rfl, rfl⟩
theorem unlink_filteredPres (fs : FsApiM (StateM TempDirMockState))
    (hUnlink : ∀ p miss s, (fs.unlink p miss).run s = (mockFs.unlink p miss).run s ∨ ∃ fe, (fs.unlink p miss).run s = (.error fe, s))
    (p : String) (miss : Bool) (s : TempDirMockState) : NodesFilteredPres (fun k => normKey k ≠ normKey p) s ((fs.unlink p miss).run s).2 := by
  rcases hUnlink p miss s with hEq | ⟨fe, hErr⟩
  · rw [hEq]; dsimp only [mockFs]; rw [stateM_bind_run, stateM_get_run]; dsimp only
    cases lookupNode s.nodes (normKey p) with
    | none => cases miss <;> exact nodesFilteredPres_refl _ s
    | some nd => cases nd with | dir _ _ => exact nodesFilteredPres_refl _ s | file _ _ _ _ | symlink _ _ =>
      simp only [stateM_bind_run, stateM_set_run, stateM_pure_run]; exact ⟨⟨fun k => normKey k != normKey p, fun k hk => bne_iff_ne.mpr hk, rfl⟩, rfl, rfl, rfl, rfl, rfl⟩
  · rw [hErr]; exact nodesFilteredPres_refl _ s
theorem rmdir_filteredPres (fs : FsApiM (StateM TempDirMockState)) (hRmdir : fs.rmdir = mockFs.rmdir) (p : String) (s : TempDirMockState) :
    NodesFilteredPres (fun k => normKey k ≠ normKey p) s ((fs.rmdir p).run s).2 := by
  rw [hRmdir]; dsimp only [mockFs]; rw [stateM_bind_run, stateM_get_run]; dsimp only
  cases lookupNode s.nodes (normKey p) with
  | none => exact nodesFilteredPres_refl _ s
  | some nd => cases nd with | file _ _ _ _ | symlink _ _ => exact nodesFilteredPres_refl _ s | dir _ _ =>
    simp only [stateM_bind_run, stateM_set_run, stateM_pure_run]; exact ⟨⟨fun k => normKey k != normKey p, fun k hk => bne_iff_ne.mpr hk, rfl⟩, rfl, rfl, rfl, rfl, rfl⟩
theorem removeNonLockChildren_filteredPres (fs : FsApiM (StateM TempDirMockState)) (hOps : SweepFsOps fs)
    (other : String) (hoNe : other ≠ "") (hoNorm : normKey other = other) (hoSlash : other ≠ "/") (names : List String)
    (hValid : ∀ nm ∈ names, pValidEntryName nm = true) (s : TempDirMockState) :
    NodesFilteredPres (fun k => underDir other k = false) s ((Internal.removeNonLockChildren fs other names).run s).2 := by
  induction names generalizing s with
  | nil => dsimp only [Internal.removeNonLockChildren]; rw [stateM_pure_run]; exact nodesFilteredPres_refl _ s
  | cons nm rest ih =>
    have hnmV := hValid nm List.mem_cons_self; have hrestV : ∀ x ∈ rest, pValidEntryName x = true := fun x hx => hValid x (List.mem_cons_of_mem nm hx)
    dsimp only [Internal.removeNonLockChildren]
    by_cases hLock : (nm == ".lock") = true
    · simp only [hLock, ↓reduceIte]; exact ih hrestV s
    · simp only [Bool.eq_false_iff.mpr hLock, Bool.false_eq_true, ↓reduceIte, stateM_bind_run, hOps.hLstat, mockFs_lstat_run, hOps.hJoin]
      have ⟨hnmNe, _, _, hnmSlash⟩ := validEntryName_parts nm hnmV
      have hSub : ∀ k, underDir (mockJoin other nm) k = true → underDir other k = true := fun k hk => underDir_mockJoin_child other nm k hoNe hoNorm hoSlash hnmNe hnmSlash hk
      have hNotSub : ∀ k, underDir other k = false → underDir (mockJoin other nm) k = false := fun k hk => by cases hb : underDir (mockJoin other nm) k with | false => rfl | true => exact absurd (hSub k hb) (by rw [hk]; decide)
      have hNotEq : ∀ k, underDir other k = false → normKey k ≠ normKey (mockJoin other nm) := fun k hk hEq => by
        have hu : underDir (mockJoin other nm) k = true := by rw [underDir_eq_of_normKey_eq _ k _ hEq]; exact underDir_refl _ (normKey_mockJoin other nm hnmNe hnmSlash)
        rw [hSub k hu] at hk; cases hk
      cases mockLstatPure s (mockJoin other nm) with
      | error fe =>
        by_cases hnf : (fe.kind == .notFound) = true
        · simp only [hnf, ↓reduceIte]; exact ih hrestV s
        · simp only [Bool.eq_false_iff.mpr hnf, Bool.false_eq_true, ↓reduceIte, stateM_pure_run]; exact nodesFilteredPres_refl _ s
      | ok st =>
        by_cases hDir : (st.kind == .dir) = true
        · simp only [hDir, ↓reduceIte, stateM_bind_run]; have hStep := cleanupDirIgnoringNotFound_filteredPres fs hOps.hRm (mockJoin other nm) s
          cases hc : (Internal.cleanupDirIgnoringNotFound fs (mockJoin other nm)).run s with
          | mk rc sc => rw [hc] at hStep; dsimp only at hStep; have hS' := nodesFilteredPres_mono hNotSub hStep; cases rc with | error _ => rw [stateM_pure_run]; exact hS' | ok _ => exact nodesFilteredPres_trans hS' (ih hrestV sc)
        · simp only [Bool.eq_false_iff.mpr hDir, Bool.false_eq_true, ↓reduceIte, stateM_bind_run]; have h1 := unlink_filteredPres fs hOps.hUnlink (mockJoin other nm) true s
          cases hu : (fs.unlink (mockJoin other nm) true).run s with
          | mk ru su => rw [hu] at h1; dsimp only at h1; have h1' := nodesFilteredPres_mono hNotEq h1; cases ru with | error _ => dsimp only; rw [stateM_bind_run, stateM_pure_run]; dsimp only; rw [stateM_pure_run]; exact h1' | ok _ => exact nodesFilteredPres_trans h1' (ih hrestV su)
theorem removeLockedTempDir_filteredPres (fs : FsApiM (StateM TempDirMockState)) (hOps : SweepFsOps fs)
    (other : String) (hoNe : other ≠ "") (hoNorm : normKey other = other) (hoSlash : other ≠ "/") (s : TempDirMockState) :
    NodesFilteredPres (fun k => underDir other k = false) s ((Internal.removeLockedTempDir fs other (mockJoin other ".lock")).run s).2 := by
  dsimp only [Internal.removeLockedTempDir]; rw [stateM_bind_run, hOps.hListDir]; have ⟨hsEq, hValidArr0⟩ := mockFs_listDir_prop s other
  cases hList : (mockFs.listDir other).run s with
  | mk resList sList =>
    have hsListEq : sList = s := by rw [← hsEq, hList]
    subst sList; dsimp only
    cases resList with
    | error fe =>
      by_cases hnf : (fe.kind == .notFound) = true
      · simp only [hnf, ↓reduceIte, stateM_pure_run]; exact nodesFilteredPres_refl _ s
      · simp only [Bool.eq_false_iff.mpr hnf, Bool.false_eq_true, ↓reduceIte, stateM_pure_run]; exact nodesFilteredPres_refl _ s
    | ok arr =>
      have hRem := removeNonLockChildren_filteredPres fs hOps other hoNe hoNorm hoSlash arr.toList (hValidArr0 arr (by rw [hList])) s
      rw [stateM_bind_run]; cases hr : (Internal.removeNonLockChildren fs other arr.toList).run s with
      | mk rRem s1 =>
        rw [hr] at hRem; dsimp only at hRem
        cases rRem with
        | error _ => rw [stateM_pure_run]; exact hRem
        | ok _ =>
          rw [stateM_bind_run]
          have hNotLock : ∀ k, underDir other k = false → normKey k ≠ normKey (mockJoin other ".lock") := fun k hk hEq => by
            rw [underDir_eq_of_normKey_eq other k _ hEq, underDir_mockJoin_self other ".lock" hoNe hoNorm hoSlash (by decide) (by decide)] at hk; cases hk
          have hUnlinkLock := unlink_filteredPres fs hOps.hUnlink (mockJoin other ".lock") true s1
          cases hu : (fs.unlink (mockJoin other ".lock") true).run s1 with
          | mk ru s2 =>
            rw [hu] at hUnlinkLock; dsimp only at hUnlinkLock; have hUnlinkPres := nodesFilteredPres_mono hNotLock hUnlinkLock
            cases ru with
            | error _ => rw [stateM_pure_run]; exact nodesFilteredPres_trans hRem hUnlinkPres
            | ok _ =>
              rw [stateM_bind_run]
              have hNotSelf : ∀ k, underDir other k = false → normKey k ≠ normKey other := fun k hk hEq => by rw [underDir_eq_of_normKey_eq other k other hEq, underDir_refl other hoNorm] at hk; cases hk
              have hRmDir := rmdir_filteredPres fs hOps.hRmdir other s2
              cases hd : (fs.rmdir other).run s2 with
              | mk rd s3 =>
                rw [hd] at hRmDir; dsimp only at hRmDir; have hAll := nodesFilteredPres_trans hRem (nodesFilteredPres_trans hUnlinkPres (nodesFilteredPres_mono hNotSelf hRmDir))
                cases rd with
                | ok _ => rw [stateM_pure_run]; exact hAll
                | error fe =>
                  by_cases hnf : (fe.kind == .notFound) = true
                  · simp only [hnf, ↓reduceIte, stateM_pure_run]; exact hAll
                  · simp only [Bool.eq_false_iff.mpr hnf, Bool.false_eq_true, ↓reduceIte, stateM_pure_run]; exact hAll
theorem sweepEntry_other_preserves (fs : FsApiM (StateM TempDirMockState)) (hOps : SweepFsOps fs)
    (root dirPrefix childName otherName : String) (maxAgeSec : Nat) (nowSec : Int) (hr : root ≠ "")
    (hcV : pValidEntryName childName = true) (hoV : pValidEntryName otherName = true) (hNe : otherName ≠ childName) (rep : CleanupReport) (s : TempDirMockState) :
    let child := mockJoin root childName; let P : String → Prop := fun k => underDir child k = true ∨ normKey k = normKey root
    let (rep', s') := (Internal.sweepEntry fs root dirPrefix maxAgeSec nowSec rep otherName).run s
    NodesFilteredPres P s s' ∧ ReportPres child rep rep' := by
  intro child P; have ⟨hcNe, _, _, hcSlash⟩ := validEntryName_parts childName hcV; have ⟨hoNe, _, _, hoSlash⟩ := validEntryName_parts otherName hoV
  let other := mockJoin root otherName; have hoFullNe := mockJoin_ne_empty root otherName hoNe
  have hoFullNorm := normKey_mockJoin root otherName hoNe hoSlash; have hoFullSlash := mockJoin_ne_slash root otherName hr hoNe
  have hNeC : child ≠ other := fun hEq => disjoint_underDir_mockJoin root otherName childName other hr hoNe hcNe hoSlash hcSlash hNe (underDir_refl other hoFullNorm) (hEq.symm ▸ underDir_refl child (normKey_mockJoin root childName hcNe hcSlash))
  have hDisjointP : ∀ k, P k → underDir other k = false := fun k hk => by
    rcases hk with hChild | hRoot
    · cases hb : underDir other k with | false => rfl | true => exact absurd (disjoint_underDir_mockJoin root otherName childName k hr hoNe hcNe hoSlash hcSlash hNe hb hChild) False.elim
    · exact not_underDir_mockJoin_root root otherName k hr hoNe hoSlash hRoot
  have hFail : ∀ err, ReportPres child rep { rep with failed := rep.failed.push err } := fun err => ⟨Iff.rfl, Iff.rfl, Iff.rfl, Iff.rfl, fun _ => by simp, fun e he => by simp [Array.toList_push, he]⟩
  dsimp only [Internal.sweepEntry]; rw [hOps.hJoin]
  by_cases hPref : (!dirPrefix.toList.isPrefixOf otherName.toList) = true
  · simp only [hPref, ↓reduceIte, stateM_pure_run]; exact ⟨nodesFilteredPres_refl P s, ⟨Iff.rfl, Iff.rfl, Iff.rfl, mem_push_ne hNeC, id, fun _ h => h⟩⟩
  · simp only [Bool.eq_false_iff.mpr hPref, Bool.false_eq_true, ↓reduceIte, stateM_bind_run, hOps.hLstat, mockFs_lstat_run]
    cases mockLstatPure s other with
    | error fe =>
      by_cases hnf : (fe.kind == .notFound) = true
      · simp only [hnf, ↓reduceIte, stateM_pure_run]; exact ⟨nodesFilteredPres_refl P s, reportPres_refl child rep⟩
      · simp only [Bool.eq_false_iff.mpr hnf, Bool.false_eq_true, ↓reduceIte, stateM_pure_run]; exact ⟨nodesFilteredPres_refl P s, hFail _⟩
    | ok stChild =>
      by_cases hNotDir : (stChild.kind != .dir) = true
      · simp only [hNotDir, ↓reduceIte, stateM_pure_run]; exact ⟨nodesFilteredPres_refl P s, ⟨Iff.rfl, Iff.rfl, Iff.rfl, mem_push_ne hNeC, id, fun _ h => h⟩⟩
      · simp only [Bool.eq_false_iff.mpr hNotDir, Bool.false_eq_true, ↓reduceIte, stateM_bind_run, mockFs_lstat_run]
        cases hlLock : mockLstatPure s (mockJoin other ".lock") with
        | error fe =>
          dsimp only; by_cases hnf : (fe.kind != .notFound) = true
          · simp only [hnf, ↓reduceIte, stateM_pure_run]; exact ⟨nodesFilteredPres_refl P s, hFail _⟩
          · simp only [Bool.eq_false_iff.mpr hnf, Bool.false_eq_true, ↓reduceIte]; by_cases hFresh : (nowSec - stChild.modifiedSec ≤ (maxAgeSec : Int))
            · simp only [hFresh, ↓reduceIte, stateM_pure_run]; exact ⟨nodesFilteredPres_refl P s, ⟨Iff.rfl, Iff.rfl, mem_push_ne hNeC, Iff.rfl, id, fun _ h => h⟩⟩
            · simp only [hFresh, ↓reduceIte, stateM_bind_run]; have hClean := cleanupDirIgnoringNotFound_filteredPres fs hOps.hRm other s
              cases hc : (Internal.cleanupDirIgnoringNotFound fs other).run s with | mk rc sc =>
                rw [hc] at hClean; dsimp only at hClean; have hPres := nodesFilteredPres_mono hDisjointP hClean
                cases rc with | ok _ => rw [stateM_pure_run]; exact ⟨hPres, ⟨mem_push_ne hNeC, Iff.rfl, Iff.rfl, Iff.rfl, id, fun _ h => h⟩⟩ | error _ => rw [stateM_pure_run]; exact ⟨hPres, hFail _⟩
        | ok stLock =>
          dsimp only; by_cases hNotFile : (stLock.kind != .file) = true
          · simp only [hNotFile, ↓reduceIte, stateM_pure_run]; exact ⟨nodesFilteredPres_refl P s, hFail _⟩
          · simp only [Bool.eq_false_iff.mpr hNotFile, Bool.false_eq_true, ↓reduceIte, stateM_bind_run, hOps.hTryWfl]
            obtain ⟨ndLock, hLookLock, hStLock⟩ := lookupNode_of_lstat_ok s (mockJoin other ".lock") stLock hlLock
            have hNotFileEq : stLock.kind = .file := by revert hNotFile; cases stLock.kind <;> decide
            have hLockNorm := normKey_mockJoin other ".lock" (by decide) (by decide)
            cases ndLock with | dir _ _ | symlink _ _ => dsimp only [mockNodeStat] at hStLock; rw [← hStLock] at hNotFileEq; cases hNotFileEq | file ino c t m =>
              by_cases hConf : mockHasConflict s.locks ino .exclusive = true
              · rw [mockFs_tryWithFileLock_existing_conflict_run s (mockJoin other ".lock") .exclusive false ino c t m hLockNorm hLookLock hConf]; dsimp only; rw [stateM_pure_run]; exact ⟨nodesFilteredPres_refl P s, ⟨Iff.rfl, mem_push_ne hNeC, Iff.rfl, Iff.rfl, id, fun _ h => h⟩⟩
              · rw [mockFs_tryWithFileLock_existing_ok_run s (mockJoin other ".lock") .exclusive false ino c t m hLockNorm hLookLock (Bool.eq_false_iff.mpr hConf)]; dsimp only
                have hRemLock := removeLockedTempDir_filteredPres fs hOps other hoFullNe hoFullNorm hoFullSlash { s with locks := (ino, .exclusive) :: s.locks }
                cases hrl : (Internal.removeLockedTempDir fs other (mockJoin other ".lock")).run { s with locks := (ino, .exclusive) :: s.locks } with | mk rrl srl =>
                  rw [hrl] at hRemLock; dsimp only at hRemLock
                  have hPres : NodesFilteredPres P s { srl with locks := mockRemoveFirstLock ino .exclusive srl.locks } := by rcases hRemLock with ⟨⟨keep, hk, hn⟩, hL, hi, ht, hs, hu⟩; exact ⟨⟨keep, fun k hkP => hk k (hDisjointP k hkP), hn⟩, by rw [hL, mockRemoveFirstLock_head], hi, ht, hs, hu⟩
                  cases rrl with
                  | error fe =>
                    dsimp only [Except.map]; by_cases hnf : (fe.kind == .notFound) = true
                    · simp only [hnf, ↓reduceIte, stateM_pure_run]; exact ⟨hPres, reportPres_refl child rep⟩
                    · simp only [Bool.eq_false_iff.mpr hnf, Bool.false_eq_true, ↓reduceIte, stateM_pure_run]; exact ⟨hPres, hFail _⟩
                  | ok rInner => dsimp only [Except.map]; cases rInner with | ok _ => rw [stateM_pure_run]; exact ⟨hPres, ⟨mem_push_ne hNeC, Iff.rfl, Iff.rfl, Iff.rfl, id, fun _ h => h⟩⟩ | error _ => rw [stateM_pure_run]; exact ⟨hPres, hFail _⟩
theorem sweepEntries_append (fs : FsApiM (StateM TempDirMockState)) (root dirPrefix : String) (maxAgeSec : Nat) (nowSec : Int)
    (rep : CleanupReport) (xs ys : List String) (s : TempDirMockState) :
    (Internal.sweepEntries fs root dirPrefix maxAgeSec nowSec rep (xs ++ ys)).run s =
      let (rep1, s1) := (Internal.sweepEntries fs root dirPrefix maxAgeSec nowSec rep xs).run s
      (Internal.sweepEntries fs root dirPrefix maxAgeSec nowSec rep1 ys).run s1 := by
  induction xs generalizing rep s with | nil => rfl | cons x xs ih =>
    dsimp only [List.cons_append, Internal.sweepEntries]; rw [stateM_bind_run, stateM_bind_run]; cases (Internal.sweepEntry fs root dirPrefix maxAgeSec nowSec rep x).run s with | mk r1 s1 => exact ih r1 s1
theorem sweepEntries_other_preserves (fs : FsApiM (StateM TempDirMockState)) (hOps : SweepFsOps fs)
    (root dirPrefix childName : String) (maxAgeSec : Nat) (nowSec : Int) (hr : root ≠ "") (hcV : pValidEntryName childName = true)
    (names : List String) (hValid : ∀ nm ∈ names, pValidEntryName nm = true) (hNotIn : childName ∉ names) (rep : CleanupReport) (s : TempDirMockState) :
    let child := mockJoin root childName; let P : String → Prop := fun k => underDir child k = true ∨ normKey k = normKey root
    let (rep', s') := (Internal.sweepEntries fs root dirPrefix maxAgeSec nowSec rep names).run s; NodesFilteredPres P s s' ∧ ReportPres child rep rep' := by
  induction names generalizing rep s with | nil => dsimp only [Internal.sweepEntries]; rw [stateM_pure_run]; exact ⟨nodesFilteredPres_refl _ s, reportPres_refl _ rep⟩ | cons nm rest ih =>
    dsimp only [Internal.sweepEntries]; rw [stateM_bind_run]
    have hStep := sweepEntry_other_preserves fs hOps root dirPrefix childName nm maxAgeSec nowSec hr hcV (hValid nm List.mem_cons_self) (fun h => hNotIn (h ▸ List.mem_cons_self)) rep s
    cases h1 : (Internal.sweepEntry fs root dirPrefix maxAgeSec nowSec rep nm).run s with | mk rep1 s1 =>
      rw [h1] at hStep; dsimp only at hStep; have hTail := ih (fun x hx => hValid x (List.mem_cons_of_mem nm hx)) (fun h => hNotIn (List.mem_cons_of_mem nm h)) rep1 s1
      cases h2 : (Internal.sweepEntries fs root dirPrefix maxAgeSec nowSec rep1 rest).run s1 with | mk rep2 s2 =>
        rw [h2] at hTail; dsimp only at hTail; exact ⟨nodesFilteredPres_trans hStep.1 hTail.1, reportPres_trans hStep.2 hTail.2⟩
theorem cleanupStaleTempDirs_split_exec (fs : FsApiM (StateM TempDirMockState)) (hOps : SweepFsOps fs)
    (s₀ : TempDirMockState) (root dirPrefix childName : String) (maxAgeSec : Nat) (hvr : pValidRoot root = true) (hvp : pValidPrefix dirPrefix = true)
    (hcV : pValidEntryName childName = true) (stRoot : FileStat) (hRoot : mockStatPure s₀ root = .ok stRoot) (hRwx : pHasRwx stRoot) (ndChild : MockNode) (hChild : lookupNode s₀.nodes (mockJoin root childName) = some ndChild) :
    let child := mockJoin root childName; let nowSec := (mockTime.nowTimestamp.run s₀).1.toSecondsSinceUnixEpoch.val; let P : String → Prop := fun k => underDir child k = true ∨ normKey k = normKey root
    ∃ _before after : List String, ∃ repBefore : CleanupReport, ∃ sBefore : TempDirMockState,
      NodesFilteredPres P s₀ sBefore ∧ (child ∉ repBefore.removed.toList) ∧ (child ∉ repBefore.keptLocked.toList) ∧ (child ∉ repBefore.keptFresh.toList) ∧ (child ∉ repBefore.skipped.toList) ∧
      (∀ (repMid : CleanupReport) (sMid : TempDirMockState), (Internal.sweepEntry fs root dirPrefix maxAgeSec nowSec repBefore childName).run sBefore = (repMid, sMid) →
        let (repAfter, sFinal) := (Internal.sweepEntries fs root dirPrefix maxAgeSec nowSec repMid after).run sMid
        let finalRep : CleanupReport := ⟨(Internal.sortStrings repAfter.removed.toList).toArray, (Internal.sortStrings repAfter.keptLocked.toList).toArray,
          (Internal.sortStrings repAfter.keptFresh.toList).toArray, (Internal.sortStrings repAfter.skipped.toList).toArray, repAfter.failed⟩
        ((Internal.mkApiM fs mockTime mockUuid mockEnv).cleanupStaleTempDirs (some root) dirPrefix maxAgeSec).run s₀ = (.ok finalRep, sFinal) ∧
        NodesFilteredPres P sMid sFinal ∧ (pHasPath finalRep.removed child ↔ child ∈ repMid.removed.toList) ∧ (pHasPath finalRep.keptLocked child ↔ child ∈ repMid.keptLocked.toList) ∧
        (pHasPath finalRep.keptFresh child ↔ child ∈ repMid.keptFresh.toList) ∧ (pHasPath finalRep.skipped child ↔ child ∈ repMid.skipped.toList) ∧
        (repMid.failed.isEmpty = false → finalRep.failed.isEmpty = false) ∧ (∀ e ∈ repMid.failed.toList, e ∈ finalRep.failed.toList)) := by
  intro child nowSec P; have hrNe := validRoot_ne_empty root hvr; have ⟨hListRun, hListNd, hListValid⟩ := mockFs_listDir_run_of_rwx s₀ root stRoot hRoot hRwx
  obtain ⟨before, after, hSplit, hNotBefore, hNotAfter⟩ := list_nodup_split _ childName hListNd (mockFs_listDir_mem_of_lookupNode s₀ root childName hrNe hcV ndChild hChild)
  have hBeforePres := sweepEntries_other_preserves fs hOps root dirPrefix childName maxAgeSec nowSec hrNe hcV before (fun nm hnm => hListValid nm (hSplit ▸ List.mem_append_left _ hnm)) hNotBefore {} s₀
  cases hBeforeRun : (Internal.sweepEntries fs root dirPrefix maxAgeSec nowSec {} before).run s₀ with | mk repBefore sBefore =>
    rw [hBeforeRun] at hBeforePres; dsimp only at hBeforePres
    refine ⟨before, after, repBefore, sBefore, hBeforePres.1, fun h => by simpa using hBeforePres.2.rm.mp h, fun h => by simpa using hBeforePres.2.kl.mp h,
      fun h => by simpa using hBeforePres.2.kf.mp h, fun h => by simpa using hBeforePres.2.sk.mp h, fun repMid sMid hMid => ?_⟩
    have hAfterPres := sweepEntries_other_preserves fs hOps root dirPrefix childName maxAgeSec nowSec hrNe hcV after (fun nm hnm => hListValid nm (hSplit ▸ List.mem_append_right _ (List.mem_cons_of_mem childName hnm))) hNotAfter repMid sMid
    cases hAfterRun : (Internal.sweepEntries fs root dirPrefix maxAgeSec nowSec repMid after).run sMid with | mk repAfter sFinal =>
      rw [hAfterRun] at hAfterPres; dsimp only at hAfterPres
      have hRunClean : ((Internal.mkApiM fs mockTime mockUuid mockEnv).cleanupStaleTempDirs (some root) dirPrefix maxAgeSec).run s₀ =
          (.ok ⟨(Internal.sortStrings repAfter.removed.toList).toArray, (Internal.sortStrings repAfter.keptLocked.toList).toArray,
                (Internal.sortStrings repAfter.keptFresh.toList).toArray, (Internal.sortStrings repAfter.skipped.toList).toArray, repAfter.failed⟩, sFinal) := by
        rw [mkApiM_cleanupStaleTempDirs_eq]; dsimp only [Internal.cleanupStaleTempDirsM, Internal.validPrefix]
        have hResRoot : (Internal.resolveRoot fs mockEnv (some root)).run s₀ = (.ok root, s₀) := by
          dsimp only [Internal.resolveRoot, Internal.validRoot]; rw [stateM_bind_run, stateM_pure_run]; dsimp only
          simp only [show (!root.isEmpty && !(Char.ofNat 0 ∈ root.toList)) = true from hvr, Bool.not_true, Bool.false_eq_true, ↓reduceIte, stateM_bind_run, hOps.hStat, mockFs_stat_run, hRoot, hRwx.1, show (EntryKind.dir != EntryKind.dir) = false from rfl, Bool.false_eq_true, stateM_pure_run]
        simp only [show (!dirPrefix.isEmpty && dirPrefix.toList.head? != some '.' && !('/' ∈ dirPrefix.toList) && !(Char.ofNat 0 ∈ dirPrefix.toList)) = true from hvp, Bool.not_true, Bool.false_eq_true, ↓reduceIte, stateM_bind_run, hResRoot]
        rw [show (mockTime.nowTimestamp.run s₀).2 = s₀ from rfl, hOps.hListDir, hListRun]; dsimp only; dsimp only [nowSec] at hBeforeRun hMid hAfterRun
        rw [stateM_bind_run, hSplit, sweepEntries_append, hBeforeRun]; dsimp only [Internal.sweepEntries]; rw [stateM_bind_run, hMid]; dsimp only; rw [hAfterRun]; dsimp only; exact stateM_pure_run _ _
      exact ⟨hRunClean, hAfterPres.1, by simpa [hasPath_toArray_mem, mem_sortStrings] using hAfterPres.2.rm, by simpa [hasPath_toArray_mem, mem_sortStrings] using hAfterPres.2.kl,
        by simpa [hasPath_toArray_mem, mem_sortStrings] using hAfterPres.2.kf, by simpa [hasPath_toArray_mem, mem_sortStrings] using hAfterPres.2.sk, hAfterPres.2.failNe, hAfterPres.2.failMem⟩
end LeanSwe.TempDir.Proofs
