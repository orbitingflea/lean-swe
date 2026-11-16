import LeanSwe.Fs.Raw.Types
import LeanSwe.Fs.Raw.Interface
import LeanSwe.Fs.Raw.Impl
import LeanSwe.Fs.Raw.SpecTests

namespace LeanSwe.Fs.Raw.Proofs

open Core
open Core.NondetTest

private theorem nonEmptyMsg_ne_empty (fallback msg : String) (hf : fallback ≠ "") :
    Internal.nonEmptyMsg fallback msg ≠ "" := by
  unfold Internal.nonEmptyMsg
  split
  · exact hf
  · next h =>
    intro hem
    subst hem
    simp [String.isEmpty] at h

private theorem append_head_ne_empty (pre rest : String) (hp : pre ≠ "") :
    pre ++ rest ≠ "" := by
  simp [String.append_eq_empty_iff, hp]

/-- Proof of `test_fsraw_mapRawError_returnsNonEmptyMessage` for `defaultOps`. -/
theorem proof_fsraw_mapRawError_returnsNonEmptyMessage :
    AllPass (test_fsraw_mapRawError_returnsNonEmptyMessage defaultOps) := by
  intro raw
  simp only [defaultOps, Internal.mkRawOps, Internal.mapRawError, assert]
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

/-- Non-vacuity `CanReach` witness for `test_fsraw_mapRawError_returnsNonEmptyMessage`. -/
theorem reach_fsraw_mapRawError_returnsNonEmptyMessage :
    CanReach (test_fsraw_mapRawError_returnsNonEmptyMessage defaultOps) :=
  ⟨.userError "", proof_fsraw_mapRawError_returnsNonEmptyMessage (.userError "")⟩

/-- Proof of `test_fsraw_mapRawError_wouldBlock` for `defaultOps`. -/
theorem proof_fsraw_mapRawError_wouldBlock :
    AllPass (test_fsraw_mapRawError_wouldBlock defaultOps) := by
  intro path? errno detail
  simp only [defaultOps, Internal.mkRawOps, Internal.mapRawError, assert]
  refine ⟨⟨trivial, trivial, trivial, nonEmptyMsg_ne_empty _ _ (by decide)⟩, trivial⟩

/-- Non-vacuity `CanReach` witness for `test_fsraw_mapRawError_wouldBlock`. -/
theorem reach_fsraw_mapRawError_wouldBlock :
    CanReach (test_fsraw_mapRawError_wouldBlock defaultOps) :=
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

/-- Proof of `test_fsraw_isValidDirHandleId_bounds`. -/
theorem proof_fsraw_isValidDirHandleId_bounds :
    AllPass (test_fsraw_isValidDirHandleId_bounds isValidDirHandleId) := by
  intro id
  dsimp only [test_fsraw_isValidDirHandleId_bounds, assert]
  refine ⟨⟨rfl, rfl⟩, ?_⟩
  by_cases h1 : 0 < id <;> by_cases h2 : id < UInt64.size <;>
    simp [isValidDirHandleId, h1, h2]

/-- Non-vacuity `CanReach` witness for `test_fsraw_isValidDirHandleId_bounds`. -/
theorem reach_fsraw_isValidDirHandleId_bounds :
    CanReach (test_fsraw_isValidDirHandleId_bounds isValidDirHandleId) :=
  ⟨1, proof_fsraw_isValidDirHandleId_bounds 1⟩

end LeanSwe.Fs.Raw.Proofs
