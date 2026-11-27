import LeanSwe.Fs.Interface
import LeanSwe.Fs.SpecTests
import LeanSwe.Fs.Proofs.PurePathBase

open Core
open Core.NondetTest
open LeanSwe.Fs

namespace LeanSwe.Fs.Proofs

open LeanSwe.Fs.ProofsInternal

private theorem nonEmptyMsg_ne_empty (fallback msg : String) (hf : fallback ≠ "") :
    Model.nonEmptyMsg fallback msg ≠ "" := by
  unfold Model.nonEmptyMsg
  split
  · exact hf
  · next h =>
    intro hem
    subst hem
    simp [String.isEmpty] at h

private theorem append_head_ne_empty (pre rest : String) (hp : pre ≠ "") :
    pre ++ rest ≠ "" := by
  simp [String.append_eq_empty_iff, hp]

/-- Proof of `test_fs_mapRawError_returnsNonEmptyMessage` for `defaultApi`. -/
theorem proof_fs_mapRawError_returnsNonEmptyMessage :
    AllPass (test_fs_mapRawError_returnsNonEmptyMessage defaultApi) := by
  intro raw
  simp only [defaultApi, Internal.mkApiFromCapsM, Internal.mkApiFromScopedRawRetryM, Internal.mkApiFromScopedRawM,
    Internal.toScopedRawFsOpsM, SysBridge.mkRawFsOpsM, SysBridge.mapRawError, assert]
  refine ⟨?_, trivial⟩
  cases raw with
  | noFileOrDirectory p _ _ =>
    exact nonEmptyMsg_ne_empty _ _ (append_head_ne_empty "no such file or directory: " p (by decide))
  | alreadyExists _ _ _ => exact nonEmptyMsg_ne_empty _ _ (by decide)
  | permissionDenied _ _ _ => exact nonEmptyMsg_ne_empty _ _ (by decide)
  | inappropriateType _ _ _ => exact nonEmptyMsg_ne_empty _ _ (by decide)
  | invalidArgument _ _ _ => exact nonEmptyMsg_ne_empty _ _ (by decide)
  | unsupportedOperation _ _ => exact nonEmptyMsg_ne_empty _ _ (by decide)
  | otherError code _ =>
    exact nonEmptyMsg_ne_empty _ _ (append_head_ne_empty "os error " (toString code) (by decide))
  | wouldBlock _ _ _ => exact nonEmptyMsg_ne_empty _ _ (by decide)
  | userError _ => exact nonEmptyMsg_ne_empty _ _ (by decide)

/-- Proof of `test_fsraw_mapRawError_wouldBlock` for `defaultApi`. -/
theorem proof_fsraw_mapRawError_wouldBlock :
    AllPass (test_fsraw_mapRawError_wouldBlock defaultApi) := by
  intro path? errno detail
  simp only [defaultApi, Internal.mkApiFromCapsM, Internal.mkApiFromScopedRawRetryM, Internal.mkApiFromScopedRawM,
    Internal.toScopedRawFsOpsM, SysBridge.mkRawFsOpsM, SysBridge.mapRawError, assert]
  refine ⟨⟨trivial, trivial, trivial, nonEmptyMsg_ne_empty _ _ (by decide)⟩, trivial⟩

/-- Non-vacuity `CanReach` witness for `test_fsraw_mapRawError_wouldBlock`. -/
theorem reach_fsraw_mapRawError_wouldBlock :
    CanReach (test_fsraw_mapRawError_wouldBlock defaultApi) :=
  ⟨some "/tmp/a.lock", 11, "", proof_fsraw_mapRawError_wouldBlock (some "/tmp/a.lock") 11 ""⟩

private theorem parseRelSegments_err_of_mem_invalid (rawPath : String) :
    ∀ segs : List (List Char),
      (∃ seg ∈ segs, validSeg (String.ofList seg) = false) →
      ∃ e, parseRelSegments rawPath segs = .error e ∧ e.kind = .invalidInput ∧ e.message ≠ ""
  | [], ⟨_, hMem, _⟩ => nomatch hMem
  | s :: rest, ⟨t, hMem, hBad⟩ => by
    unfold parseRelSegments
    by_cases hv : validSeg (String.ofList s) = true
    · simp only [hv, ↓reduceDIte]
      rcases List.mem_cons.mp hMem with rfl | hTail
      · simp [hv] at hBad
      · rcases parseRelSegments_err_of_mem_invalid rawPath rest ⟨t, hTail, hBad⟩ with ⟨e, he, hk, hm⟩
        exact ⟨e, by simp [he], hk, hm⟩
    · simp only [hv]
      refine ⟨_, rfl, rfl, ?_⟩
      intro hem
      simp only [String.append_eq_empty_iff] at hem
      exact absurd hem.1.1.1.1 (by decide)

private theorem splitSlashRaw_append_slash :
    ∀ xs : List Char, ∃ a rest, splitSlashRaw (xs ++ ['/']) = a :: rest ∧ [] ∈ rest
  | [] => ⟨[], [[]], rfl, List.Mem.head _⟩
  | c :: cs => by
    rcases splitSlashRaw_append_slash cs with ⟨a, rest, hEq, hMem⟩
    by_cases hc : c = '/'
    · subst hc
      refine ⟨[], a :: rest, ?_, List.Mem.tail _ hMem⟩
      simp [splitSlashRaw, hEq]
    · have hBeq : (c == '/') = false := beq_false_of_ne hc
      refine ⟨c :: a, rest, ?_, hMem⟩
      simp [splitSlashRaw, hBeq, hEq]

private theorem parse_leadingSlash_invalid (seg : String) :
    ∃ e, RelPath.parse ("/" ++ seg) = .error e ∧ e.kind = .invalidInput ∧ e.message ≠ "" := by
  unfold RelPath.parse
  have hList : ("/" ++ seg).toList = '/' :: seg.toList := by simp
  rw [hList]
  have hSplit : splitSlashRaw ('/' :: seg.toList) = [] :: splitSlashRaw seg.toList := by
    simp [splitSlashRaw]
  rw [hSplit]
  rcases parseRelSegments_err_of_mem_invalid ("/" ++ seg) ([] :: splitSlashRaw seg.toList)
      ⟨[], List.Mem.head _, by decide⟩ with ⟨e, he, hk, hm⟩
  exact ⟨e, by simp [he], hk, hm⟩

private theorem parse_trailingSlash_invalid (seg : String) :
    ∃ e, RelPath.parse (seg ++ "/") = .error e ∧ e.kind = .invalidInput ∧ e.message ≠ "" := by
  unfold RelPath.parse
  have hList : (seg ++ "/").toList = seg.toList ++ ['/'] := by simp
  rw [hList]
  rcases splitSlashRaw_append_slash seg.toList with ⟨a, rest, hEq, hMem⟩
  rw [hEq]
  rcases parseRelSegments_err_of_mem_invalid (seg ++ "/") (a :: rest)
      ⟨[], List.Mem.tail _ hMem, by decide⟩ with ⟨e, he, hk, hm⟩
  exact ⟨e, by simp [he], hk, hm⟩

/-- Proof of `test_fsraw_entryName_parse_acceptsValidAndRejectsUnsafe`. -/
theorem proof_fsraw_entryName_parse_acceptsValidAndRejectsUnsafe :
    AllPass (test_fsraw_entryName_parse_acceptsValidAndRejectsUnsafe EntryName.parse) := by
  intro s
  dsimp only [test_fsraw_entryName_parse_acceptsValidAndRejectsUnsafe, EntryName.parse]
  by_cases h : validSeg s = true
  · simp [h, assert]
  · simp only [h, assert]
    refine ⟨⟨trivial, rfl, ?_⟩, trivial⟩
    intro hem
    simp only [String.append_eq_empty_iff] at hem
    exact absurd hem.1.1 (by decide)

/-- Non-vacuity `CanReach` witness for `test_fsraw_entryName_parse_acceptsValidAndRejectsUnsafe`. -/
theorem reach_fsraw_entryName_parse_acceptsValidAndRejectsUnsafe :
    CanReach (test_fsraw_entryName_parse_acceptsValidAndRejectsUnsafe EntryName.parse) :=
  ⟨"file.txt", proof_fsraw_entryName_parse_acceptsValidAndRejectsUnsafe "file.txt"⟩

/-- Proof of `test_fsraw_relPath_parse_rejectsUnsafeAndParseRootMapsDot`. -/
theorem proof_fsraw_relPath_parse_rejectsUnsafeAndParseRootMapsDot :
    AllPass (test_fsraw_relPath_parse_rejectsUnsafeAndParseRootMapsDot RelPath.parse RelPath.parseRoot) := by
  intro seg
  dsimp only [test_fsraw_relPath_parse_rejectsUnsafeAndParseRootMapsDot, assert]
  refine ⟨?_, ⟨?_, ⟨?_, ⟨?_, trivial⟩⟩⟩⟩
  · rcases parse_leadingSlash_invalid seg with ⟨e1, he1, hk1, hm1⟩
    rcases parse_trailingSlash_invalid seg with ⟨e2, he2, hk2, hm2⟩
    have hm1b : (e1.message != "") = true := by simp [hm1]
    have hm2b : (e2.message != "") = true := by simp [hm2]
    simp only [List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true, he1, hk1, hm1b, he2, hk2, hm2b]
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  · rfl
  · rfl
  · unfold RelPath.parseRoot
    by_cases hs : seg = "."
    · left; exact hs
    · right; simp [hs]

/-- Non-vacuity `CanReach` witness for `test_fsraw_relPath_parse_rejectsUnsafeAndParseRootMapsDot`. -/
theorem reach_fsraw_relPath_parse_rejectsUnsafeAndParseRootMapsDot :
    CanReach (test_fsraw_relPath_parse_rejectsUnsafeAndParseRootMapsDot RelPath.parse RelPath.parseRoot) :=
  ⟨"foo", proof_fsraw_relPath_parse_rejectsUnsafeAndParseRootMapsDot "foo"⟩

private theorem splitCharList_append_tail_no_slash (a b : List Char) (hno : '/' ∉ b) :
    Internal.splitCharList '/' (a ++ '/' :: b) = Internal.splitCharList '/' a ++ [b] := by
  induction a with
  | nil =>
    simp only [List.nil_append, Internal.splitCharList, beq_self_eq_true, ↓reduceIte,
      splitCharList_of_no_sep '/' b hno, List.singleton_append]
  | cons c rest ih =>
    simp only [List.cons_append, Internal.splitCharList]
    split
    · simp [ih]
    · rw [ih]
      cases hsp : Internal.splitCharList '/' rest with
      | nil => exact absurd hsp (splitCharList_ne_nil '/' rest)
      | cons hd tl => simp

private theorem joinSlashChars_ne_nil {s : List Char} {tl : List (List Char)} (hs : s ≠ []) :
    Internal.joinSlashChars (s :: tl) ≠ [] := by
  cases tl with
  | nil => simp [Internal.joinSlashChars, hs]
  | cons _ _ =>
    simp only [Internal.joinSlashChars]
    cases s with
    | nil => exact absurd rfl hs
    | cons _ _ => simp

/-- Proof of `test_fs_normPath_neverEmpty` for `defaultApi`. -/
theorem proof_fs_normPath_neverEmpty :
    AllPass (test_fs_normPath_neverEmpty defaultApi) := by
  intro path
  simp only [defaultApi, Internal.mkApiFromCapsM, Internal.mkApiFromScopedRawRetryM, Internal.mkApiFromScopedRawM, assert]
  refine ⟨?_, trivial⟩
  unfold Internal.normPath
  cases hAbs : Internal.isAbsChars path.toList
  · simp only [hAbs, Bool.false_eq_true, ↓reduceIte]
    cases hCol : Internal.collapseChars false (Internal.splitCharList '/' path.toList) [] with
    | nil =>
      simp only [List.isEmpty_nil, ↓reduceIte]
      decide
    | cons hd tl =>
      have hVal := collapseChars_elems_valid false (Internal.splitCharList '/' path.toList) []
        (fun _ h => by simp at h) (splitCharList_no_sep '/' path.toList) hd (by rw [hCol]; simp)
      have hhdNe : hd ≠ [] := by cases hd <;> simp_all
      have hjNe := joinSlashChars_ne_nil (tl := tl) hhdNe
      simp only [List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte]
      intro h
      have hlen := congrArg String.toList h
      simp only [String.toList_ofList, show ("" : String).toList = [] from rfl] at hlen
      exact hjNe hlen
  · simp only [hAbs, ↓reduceIte]
    intro h
    have hlen := congrArg String.toList h
    simp [show ("" : String).toList = [] from rfl] at hlen

/-- Proof of `test_fs_normPath_idempotent` for `defaultApi`. -/
theorem proof_fs_normPath_idempotent :
    AllPass (test_fs_normPath_idempotent defaultApi) := by
  intro path
  simp only [defaultApi, Internal.mkApiFromCapsM, Internal.mkApiFromScopedRawRetryM, Internal.mkApiFromScopedRawM, assert]
  refine ⟨?_, trivial⟩
  conv => rhs; unfold Internal.normPath
  cases hAbs : Internal.isAbsChars path.toList
  · have hElem : ∀ s ∈ Internal.collapseChars false (Internal.splitCharList '/' path.toList) [],
        !s.isEmpty ∧ s != ['.'] ∧ '/' ∉ s :=
      collapseChars_elems_valid false (Internal.splitCharList '/' path.toList) []
        (fun _ h => by simp at h) (splitCharList_no_sep '/' path.toList)
    have hStack : ValidStack false
        (Internal.collapseChars false (Internal.splitCharList '/' path.toList) []).reverse :=
      collapseChars_validStack false (Internal.splitCharList '/' path.toList) []
        trivial (splitCharList_no_sep '/' path.toList)
    have hOrd : ValidOrder false (Internal.collapseChars false (Internal.splitCharList '/' path.toList) []) := by
      simpa using validStack_to_validOrder false _ hStack
    simp only [Internal.normPath, hAbs, Bool.false_eq_true, ↓reduceIte]
    cases hParts : Internal.collapseChars false (Internal.splitCharList '/' path.toList) [] with
    | nil =>
      have hDot : ".".toList = ['.'] := by decide
      simp [hDot, Internal.isAbsChars, Internal.splitCharList, Internal.collapseChars]
    | cons hd tl =>
      have hHd := hElem hd (by rw [hParts]; simp)
      have hHdNe : hd ≠ [] := by cases hd <;> simp_all
      have hNotAbs : Internal.isAbsChars (Internal.joinSlashChars (hd :: tl)) = false :=
        isAbsChars_joinSlashChars_head hHdNe hHd.2.2
      have hSplit : Internal.splitCharList '/' (Internal.joinSlashChars (hd :: tl)) = hd :: tl :=
        splitCharList_joinSlashChars (hd :: tl) (by simp) (fun s hs => (hElem s (by rw [hParts]; exact hs)).2.2)
      have hOrd' : ValidOrder false (hd :: tl) := hParts ▸ hOrd
      have hNoop := collapseChars_noop false (hd :: tl) []
        (fun s hs => ⟨(hElem s (by rw [hParts]; exact hs)).1, (hElem s (by rw [hParts]; exact hs)).2.1⟩)
        (Or.inr ⟨rfl, hOrd', fun _ h => by simp at h⟩)
      simp only [List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte,
        String.toList_ofList, hNotAbs, hSplit, hNoop, List.reverse_nil, List.nil_append]
  · have hElem : ∀ s ∈ Internal.collapseChars true (Internal.splitCharList '/' path.toList) [],
        !s.isEmpty ∧ s != ['.'] ∧ '/' ∉ s :=
      collapseChars_elems_valid true (Internal.splitCharList '/' path.toList) []
        (fun _ h => by simp at h) (splitCharList_no_sep '/' path.toList)
    have hStack : ValidStack true
        (Internal.collapseChars true (Internal.splitCharList '/' path.toList) []).reverse :=
      collapseChars_validStack true (Internal.splitCharList '/' path.toList) []
        trivial (splitCharList_no_sep '/' path.toList)
    have hOrd : ValidOrder true (Internal.collapseChars true (Internal.splitCharList '/' path.toList) []) := by
      simpa using validStack_to_validOrder true _ hStack
    simp only [Internal.normPath, hAbs, ↓reduceIte]
    have hAbs2 : Internal.isAbsChars ('/' :: Internal.joinSlashChars
        (Internal.collapseChars true (Internal.splitCharList '/' path.toList) [])) = true := rfl
    simp only [String.toList_ofList]
    simp only [hAbs2, ↓reduceIte]
    have hSplit : Internal.splitCharList '/' ('/' :: Internal.joinSlashChars
          (Internal.collapseChars true (Internal.splitCharList '/' path.toList) [])) =
        [] :: Internal.splitCharList '/' (Internal.joinSlashChars
          (Internal.collapseChars true (Internal.splitCharList '/' path.toList) [])) := by
      simp [Internal.splitCharList]
    have hStepNil : Internal.collapseChars true ([] :: Internal.splitCharList '/' (Internal.joinSlashChars
          (Internal.collapseChars true (Internal.splitCharList '/' path.toList) []))) [] =
        Internal.collapseChars true (Internal.splitCharList '/' (Internal.joinSlashChars
          (Internal.collapseChars true (Internal.splitCharList '/' path.toList) []))) [] := by
      simp [Internal.collapseChars]
    rw [hSplit, hStepNil]
    cases hParts : Internal.collapseChars true (Internal.splitCharList '/' path.toList) [] with
    | nil => simp [Internal.joinSlashChars, Internal.splitCharList, Internal.collapseChars]
    | cons hd tl =>
      have hSplitJ : Internal.splitCharList '/' (Internal.joinSlashChars (hd :: tl)) = hd :: tl :=
        splitCharList_joinSlashChars (hd :: tl) (by simp) (fun s hs => (hElem s (by rw [hParts]; exact hs)).2.2)
      have hOrd' : NoDotDot (hd :: tl) := hParts ▸ hOrd
      have hNoop := collapseChars_noop true (hd :: tl) []
        (fun s hs => ⟨(hElem s (by rw [hParts]; exact hs)).1, (hElem s (by rw [hParts]; exact hs)).2.1⟩)
        (Or.inl hOrd')
      rw [hSplitJ, hNoop]
      simp

private theorem join_absOverridesBase (base sub : String) :
    Internal.isAbsolute sub = true → Internal.join base sub = sub := by
  intro h
  simp [Internal.join, h]

/-- Proof of `test_fs_join_absOverridesBase` for `defaultApi`. -/
theorem proof_fs_join_absOverridesBase :
    AllPass (test_fs_join_absOverridesBase defaultApi) := by
  intro base sub
  simp only [defaultApi, Internal.mkApiFromCapsM, Internal.mkApiFromScopedRawRetryM, Internal.mkApiFromScopedRawM, assume, assert]
  intro h
  exact ⟨join_absOverridesBase base sub h, trivial⟩

private theorem cleanCharSegments_joinParentName (par? : Option String) (newName : String)
    (hValid : Internal.validFileName newName = true) :
    ∃ front, (Internal.cleanCharSegments (Internal.joinParentName par? newName)).2 = front ++ [newName.toList] := by
  unfold Internal.validFileName at hValid
  simp only [Bool.and_eq_true, Bool.not_eq_true', bne_iff_ne, ne_eq, decide_eq_false_iff_not] at hValid
  rcases hValid with ⟨⟨⟨hNeEmpty, hNoSlash⟩, hNeDot⟩, _⟩
  have hNotEmptyB : (!newName.toList.isEmpty) = true := by simp [hNeEmpty]
  have hNeDotB : (newName.toList != ['.']) = true := bne_iff_ne.mpr hNeDot
  have hKeep : (fun s => !s.isEmpty && s != ['.']) newName.toList = true := by
    simp [hNotEmptyB, hNeDotB]
  have hSplitNew : Internal.splitCharList '/' newName.toList = [newName.toList] :=
    splitCharList_of_no_sep '/' newName.toList hNoSlash
  cases par? with
  | none =>
    refine ⟨[], ?_⟩
    simp [Internal.joinParentName, Internal.cleanCharSegments, hSplitNew, hKeep]
  | some par =>
    by_cases hRoot : par = "/"
    · subst hRoot
      refine ⟨[], ?_⟩
      have hLst : ("/" ++ newName).toList = '/' :: newName.toList := by
        simp [String.toList_append, show "/".toList = ['/'] by decide]
      have hSp : Internal.splitCharList '/' ('/' :: newName.toList) = [] :: [newName.toList] := by
        simp [Internal.splitCharList, hSplitNew]
      simp [Internal.joinParentName, Internal.cleanCharSegments, hLst, hSp, hKeep]
    · simp only [Internal.joinParentName, Internal.cleanCharSegments]
      have hLst : (par ++ "/" ++ newName).toList = par.toList ++ '/' :: newName.toList := by
        simp [String.toList_append, show "/".toList = ['/'] by decide]
      rw [hLst, splitCharList_append_tail_no_slash par.toList newName.toList hNoSlash, List.filter_append]
      simp [hKeep]

/-- Proof of `test_fs_withName_updatesName` for `defaultApi`. -/
theorem proof_fs_withName_updatesName :
    AllPass (test_fs_withName_updatesName defaultApi) := by
  intro path newName
  simp only [defaultApi, Internal.mkApiFromCapsM, Internal.mkApiFromScopedRawRetryM, Internal.mkApiFromScopedRawM]
  unfold Internal.withName
  split
  · simp [assume]
  · have hValid : Internal.validFileName newName = true := by
      cases hv : Internal.validFileName newName <;> simp_all
    cases hPar : Internal.splitParentName path with
    | none => simp [assume]
    | some pair =>
      rcases pair with ⟨par?, oldName⟩
      simp only [assert]
      obtain ⟨front, hSegs⟩ := cleanCharSegments_joinParentName par? newName hValid
      refine ⟨?_, trivial⟩
      unfold Internal.name Internal.splitParentName
      dsimp only
      rw [hSegs, splitLastAux_append_singleton]
      cases front <;> simp

private theorem splitRevAtDot_append_noDot (revTail revStem : List Char) (hno : '.' ∉ revTail) :
    Internal.splitRevAtDot (revTail ++ '.' :: revStem) = some (revStem, revTail) := by
  induction revTail with
  | nil => simp [Internal.splitRevAtDot]
  | cons c rest ih =>
    have hcne : c ≠ '.' := fun h => hno (by subst h; simp)
    have ih' := ih (fun h => hno (by simp [h]))
    unfold Internal.splitRevAtDot
    split
    · next he => simp at he
    · next he =>
      simp only [List.cons_append, List.cons.injEq] at he
      exact absurd he.1 hcne
    · next _ _ he =>
      simp only [List.cons_append, List.cons.injEq] at he
      rcases he with ⟨rfl, rfl⟩
      rw [ih']

/-- Proof of `test_fs_withSuffix_updatesSuffix` for `defaultApi`. -/
theorem proof_fs_withSuffix_updatesSuffix :
    AllPass (test_fs_withSuffix_updatesSuffix defaultApi) := by
  intro path ext
  simp only [defaultApi, Internal.mkApiFromCapsM, Internal.mkApiFromScopedRawRetryM, Internal.mkApiFromScopedRawM, assume]
  intro hHead hNoDotTail
  cases hSufCall : Internal.withSuffix path ext with
  | error _ => simp
  | ok updated =>
    simp only [assert]
    refine ⟨?_, trivial⟩
    unfold Internal.withSuffix at hSufCall
    have hValidSuf : Internal.validSuffix ext = true := by
      cases hv : Internal.validSuffix ext
      · simp [hv] at hSufCall
      · rfl
    simp only [hValidSuf, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hSufCall
    cases hPar : Internal.splitParentName path with
    | none => simp [hPar] at hSufCall
    | some pair =>
      rcases pair with ⟨par?, oldName⟩
      simp only [hPar] at hSufCall
      let stemPart := (Internal.splitNameSuffix oldName).1
      by_cases hStemBad : (stemPart.isEmpty || stemPart.toList.all (· == '.')) = true
      · simp [stemPart, hStemBad] at hSufCall
      · have hNotBad : (stemPart.isEmpty || stemPart.toList.all (· == '.')) = false :=
          Bool.eq_false_iff.mpr hStemBad
        simp only [stemPart, hNotBad, Bool.false_eq_true, ↓reduceIte] at hSufCall
        change Internal.withName path (stemPart ++ ext) = .ok updated at hSufCall
        have hStemNeEmpty : stemPart.toList ≠ [] := by
          intro h
          have hEmp : stemPart = "" := by rw [← String.ofList_toList (s := stemPart), h]
          have he : stemPart.isEmpty = true := by rw [hEmp]; rfl
          simp [he] at hNotBad
        have hNotAllDots : stemPart.toList.all (· == '.') = false := by
          cases hd : stemPart.toList.all (· == '.') <;> simp_all
        have hNameEq := proof_fs_withName_updatesName path (stemPart ++ ext)
        simp only [defaultApi, Internal.mkApiFromCapsM, Internal.mkApiFromScopedRawRetryM, Internal.mkApiFromScopedRawM, hSufCall, assert] at hNameEq
        unfold Internal.suffix
        rw [hNameEq.1]
        dsimp only
        cases hExt : ext.toList with
        | nil => simp [hExt] at hHead
        | cons d extTail =>
          have hdEq : d = '.' := by simp [hExt] at hHead; exact hHead
          subst hdEq
          have hNoDotTail' : '.' ∉ extTail := by simp [hExt] at hNoDotTail; exact hNoDotTail
          have hExtTailNe : extTail ≠ [] := by
            intro hEmpty
            subst hEmpty
            simp [Internal.validSuffix, hExt] at hValidSuf
          have hNoDotRev : '.' ∉ extTail.reverse := by simpa using hNoDotTail'
          unfold Internal.splitNameSuffix
          have hRev : (stemPart ++ ext).toList.reverse = extTail.reverse ++ '.' :: stemPart.toList.reverse := by
            simp [String.toList_append, hExt, List.reverse_append]
          rw [hRev, splitRevAtDot_append_noDot extTail.reverse stemPart.toList.reverse hNoDotRev]
          have hRevPrefNe : stemPart.toList.reverse.isEmpty = false := by
            cases h : stemPart.toList <;> simp_all
          have hRevSufNe : extTail.reverse.isEmpty = false := by
            cases h : extTail <;> simp_all
          have hRevAllDots : stemPart.toList.reverse.all (· == '.') = false := by
            simpa [List.all_reverse] using hNotAllDots
          simp only [hRevPrefNe, hRevSufNe, hRevAllDots, Bool.or_self, Bool.false_eq_true, ↓reduceIte,
            List.reverse_reverse]
          have hExtEq : ext = String.ofList ('.' :: extTail) := by
            rw [← hExt, String.ofList_toList]
          have hCatEq : "." ++ String.ofList extTail = String.ofList ('.' :: extTail) := by
            rw [← String.ofList_toList (s := "." ++ String.ofList extTail)]
            simp [String.toList_append, show ".".toList = ['.'] from rfl]
          rw [hExtEq, hCatEq]

/-- Non-vacuity `CanReach` witness for `test_fs_mapRawError_returnsNonEmptyMessage`. -/
theorem reach_fs_mapRawError_returnsNonEmptyMessage :
    CanReach (test_fs_mapRawError_returnsNonEmptyMessage defaultApi) :=
  ⟨.userError "", proof_fs_mapRawError_returnsNonEmptyMessage (.userError "")⟩

/-- Non-vacuity `CanReach` witness for `test_fs_normPath_idempotent`. -/
theorem reach_fs_normPath_idempotent :
    CanReach (test_fs_normPath_idempotent defaultApi) :=
  ⟨"/a/b/../c", proof_fs_normPath_idempotent "/a/b/../c"⟩

/-- Non-vacuity `CanReach` witness for `test_fs_normPath_neverEmpty`. -/
theorem reach_fs_normPath_neverEmpty :
    CanReach (test_fs_normPath_neverEmpty defaultApi) :=
  ⟨"", proof_fs_normPath_neverEmpty ""⟩

/-- Non-vacuity `CanReach` witness for `test_fs_join_absOverridesBase`. -/
theorem reach_fs_join_absOverridesBase :
    CanReach (test_fs_join_absOverridesBase defaultApi) :=
  ⟨"/a", "/b", rfl, proof_fs_join_absOverridesBase "/a" "/b" rfl⟩

/-- Non-vacuity `CanReach` witness for `test_fs_withName_updatesName`. -/
theorem reach_fs_withName_updatesName :
    CanReach (test_fs_withName_updatesName defaultApi) := by
  refine ⟨"a/b.txt", "c.lean", ?_⟩
  have h := proof_fs_withName_updatesName "a/b.txt" "c.lean"
  have hw : Internal.withName "a/b.txt" "c.lean" = .ok "a/c.lean" := rfl
  simp [defaultApi, Internal.mkApiFromCapsM, Internal.mkApiFromScopedRawRetryM, Internal.mkApiFromScopedRawM, hw, assert] at h ⊢
  exact h

/-- Non-vacuity `CanReach` witness for `test_fs_withSuffix_updatesSuffix`. -/
theorem reach_fs_withSuffix_updatesSuffix :
    CanReach (test_fs_withSuffix_updatesSuffix defaultApi) := by
  refine ⟨"a/b.txt", ".lean", by decide, by decide, ?_⟩
  have h := proof_fs_withSuffix_updatesSuffix "a/b.txt" ".lean" (by decide) (by decide)
  have hs : Internal.withSuffix "a/b.txt" ".lean" = .ok "a/b.lean" := rfl
  simp [defaultApi, Internal.mkApiFromCapsM, Internal.mkApiFromScopedRawRetryM, Internal.mkApiFromScopedRawM, hs, assert] at h ⊢
  exact h

private theorem splitCharList_dot_concat (bs suf : List Char) (hno : '.' ∉ bs) :
    Internal.splitCharList '.' (bs ++ '.' :: suf) = bs :: Internal.splitCharList '.' suf := by
  induction bs with
  | nil => simp [Internal.splitCharList]
  | cons c rest ih =>
    have hc : c ≠ '.' := fun h => hno (by subst h; simp)
    have ih' := ih (fun h => hno (by simp [h]))
    simp [Internal.splitCharList, hc, ih']

/-- Proof of `test_fs_suffixes_doubleDot` for `defaultApi`. -/
theorem proof_fs_suffixes_doubleDot :
    AllPass (test_fs_suffixes_doubleDot defaultApi) := by
  intro base hNe hNoDot hNoSlash
  simp only [defaultApi, Internal.mkApiFromCapsM, Internal.mkApiFromScopedRawRetryM, Internal.mkApiFromScopedRawM, assert]
  refine ⟨?_, trivial⟩
  cases hBase : base.toList with
  | nil => exact absurd hBase hNe
  | cons c rest =>
    have hcDot : c ≠ '.' := fun h => hNoDot (by simp [hBase, h])
    have hBaseNoDot : '.' ∉ base.toList := hNoDot
    have hBaseNoSlash : '/' ∉ base.toList := hNoSlash
    have hFullNoSlash : '/' ∉ (base ++ "..ext").toList := by
      simp [String.toList_append, hBaseNoSlash, show "..ext".toList = ['.', '.', 'e', 'x', 't'] by decide]
    have hFullNotEmpty : (!(base.toList ++ ['.', '.', 'e', 'x', 't']).isEmpty) = true := by
      simp [hBase]
    have hFullNotDot : ((base.toList ++ ['.', '.', 'e', 'x', 't']) != ['.']) = true := by
      refine bne_iff_ne.mpr fun heq => ?_
      have hLen := congrArg List.length heq
      simp at hLen
    have hName : Internal.name (base ++ "..ext") = some (base ++ "..ext") := by
      unfold Internal.name Internal.splitParentName Internal.cleanCharSegments
      dsimp only
      rw [splitCharList_of_no_sep '/' (base ++ "..ext").toList hFullNoSlash]
      rw [String.toList_append, show "..ext".toList = ['.', '.', 'e', 'x', 't'] by decide]
      simp [hFullNotEmpty, hFullNotDot, Internal.splitLastAux]
    unfold Internal.suffixes
    rw [hName]
    dsimp only
    have hRev : (base ++ "..ext").toList.reverse =
        ['t', 'x', 'e', '.', '.'] ++ base.toList.reverse := by
      simp [String.toList_append, show "..ext".toList = ['.', '.', 'e', 'x', 't'] by decide]
    rw [hRev]
    have hDrop : (base ++ "..ext").toList.dropWhile (· == '.') = base.toList ++ ['.', '.', 'e', 'x', 't'] := by
      have hList : (base ++ "..ext").toList = c :: (rest ++ ['.', '.', 'e', 'x', 't']) := by
        simp [String.toList_append, hBase, show "..ext".toList = ['.', '.', 'e', 'x', 't'] by decide]
      rw [hList]
      simp [hcDot, hBase]
    rw [hDrop]
    have hDotEq : base.toList ++ ['.', '.', 'e', 'x', 't'] = base.toList ++ '.' :: ['.', 'e', 'x', 't'] := rfl
    rw [hDotEq, splitCharList_dot_concat base.toList ['.', 'e', 'x', 't'] hBaseNoDot]
    simp [Internal.splitCharList, show String.ofList [] = "" from rfl,
      show String.ofList ['e', 'x', 't'] = "ext" from rfl]

/-- Non-vacuity `CanReach` witness for `test_fs_suffixes_doubleDot`. -/
theorem reach_fs_suffixes_doubleDot :
    CanReach (test_fs_suffixes_doubleDot defaultApi) :=
  ⟨"a", by decide, by decide, by decide,
    proof_fs_suffixes_doubleDot "a" (by decide) (by decide) (by decide)⟩

end LeanSwe.Fs.Proofs
