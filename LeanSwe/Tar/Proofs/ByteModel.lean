import LeanSwe.Tar.Model
import LeanSwe.Tar.Impl

namespace LeanSwe.Tar.Proofs

open LeanSwe.Tar
open LeanSwe.Tar.Model
open LeanSwe.Tar.Impl

/-- Loop invariant for `ByteArray.toList.loop`. -/
theorem byteArray_toList_loop (bs : ByteArray) (i : Nat) (r : List UInt8) :
    ByteArray.toList.loop bs i r = r.reverse ++ bs.data.toList.drop i := by
  fun_induction ByteArray.toList.loop with
  | case1 i r hi ih =>
    have hi_d : i < bs.data.size := hi
    have hi_l : i < bs.data.toList.length := by simpa [Array.length_toList] using hi_d
    have hget : bs.get! i = bs.data.toList[i]'hi_l := by
      rw [Array.getElem_toList]; exact getElem!_pos bs.data i hi_d
    rw [ih, hget, List.drop_eq_getElem_cons hi_l, List.reverse_cons, List.append_assoc, List.singleton_append]
  | case2 i r hi =>
    rw [List.drop_eq_nil_of_le (by rw [Array.length_toList]; exact Nat.le_of_not_lt hi), List.append_nil]

/-- `bs.toList` equals `bs.data.toList`. -/
theorem byteArray_toList_eq (bs : ByteArray) : bs.toList = bs.data.toList := by
  simpa [ByteArray.toList] using byteArray_toList_loop bs 0 []

/-- Unified indexing lemma for `a ++ b`. -/
theorem byteArray_getElem_append {a b : ByteArray} {i : Nat} (hi : i < (a ++ b).size) :
    (a ++ b)[i]'hi = if h : i < a.size then a[i]'h else b[i - a.size]'(by rw [ByteArray.size_append] at hi; omega) := by
  by_cases h : i < a.size <;> simp [h, ByteArray.getElem_append_left, ByteArray.getElem_append_right, Nat.le_of_not_lt]

/-- `(b.set! k v).size = b.size`. -/
@[simp] theorem byteArray_size_set! (b : ByteArray) (k : Nat) (v : UInt8) : (b.set! k v).size = b.size :=
  Array.size_setIfInBounds

/-- Indexing into `b.set! k v` when `k < b.size` and `i < b.size`. -/
theorem byteArray_getElem_set! {b : ByteArray} {k i : Nat} {v : UInt8} (hk : k < b.size) (hi : i < b.size) :
    (b.set! k v)[i]'(by rw [byteArray_size_set!]; exact hi) = if k = i then v else b[i]'hi := by
  let _ := hk; exact Array.getElem_setIfInBounds ..

/-- Congruence of `ByteArray` indexing across an equality `a = b`. -/
theorem byteArray_getElem_of_eq {a b : ByteArray} (h : a = b) {i : Nat} (ha : i < a.size) (hb : i < b.size) :
    a[i]'ha = b[i]'hb := by subst h; rfl

/-- `pad512 n` is a multiple of `512`. -/
@[simp] theorem pad512_mod (n : Nat) : pad512 n % 512 = 0 := by unfold pad512; simp [Nat.mul_mod_left]

/-- `padRightBytes width bs` always has size `width`. -/
@[simp] theorem padRightBytes_size (width : Nat) (bs : ByteArray) :
    (padRightBytes width bs).size = width := by
  unfold padRightBytes
  split
  · rw [ByteArray.size_extract]; omega
  · rw [ByteArray.size_append]
    have hr : (ByteArray.mk (Array.replicate (width - bs.size) 0)).size = width - bs.size := Array.size_replicate
    rw [hr]; omega

/-- Indexing into `padRightBytes width bs`. -/
theorem padRightBytes_getElem (width : Nat) (bs : ByteArray) {i : Nat} (hi : i < width) :
    (padRightBytes width bs)[i]'(by simp [hi]) =
      if h : i < bs.size then bs[i]'h else 0 := by
  unfold padRightBytes
  by_cases hge : bs.size ≥ width
  · simp [hge, show i < bs.size by omega, ByteArray.getElem_extract]
  · simp only [hge, ↓reduceIte]
    by_cases hilt : i < bs.size
    · simp [hilt, ByteArray.getElem_append_left]
    · simp only [hilt, ↓reduceDIte, ByteArray.getElem_append_right (Nat.le_of_not_lt hilt)]
      exact Array.getElem_replicate ..

private theorem blitFixed_go_size (offset width : Nat) (src : ByteArray) (i : Nat) (buf : ByteArray) :
    (blitFixed.go offset width src i buf).size = buf.size := by
  fun_induction blitFixed.go offset width src i buf <;> simp_all

/-- `(blitFixed dst offset width src).size = dst.size`. -/
@[simp] theorem blitFixed_size (dst : ByteArray) (offset width : Nat) (src : ByteArray) :
    (blitFixed dst offset width src).size = dst.size :=
  blitFixed_go_size offset width src 0 dst

private theorem blitFixed_go_getElem (off w : Nat) (src : ByteArray) (j : Nat) (buf : ByteArray)
    (hbd : off + min w src.size ≤ buf.size) {k : Nat} (hk : k < buf.size) :
    (blitFixed.go off w src j buf)[k]'(by rw [blitFixed_go_size]; exact hk) =
      if h : off + j ≤ k ∧ k < off + min w src.size then src[k - off]'(by omega) else buf[k]'hk := by
  fun_induction blitFixed.go off w src j buf with
  | case1 j buf hj =>
    split
    · omega
    · exact byteArray_getElem_of_eq (by rw [blitFixed.go.eq_1]; simp [hj]) _ hk
  | case2 j buf hj hsrc idx hidx ih =>
    have hstep : blitFixed.go off w src j buf =
        blitFixed.go off w src (j + 1) (buf.set! idx (src[j]'hsrc)) := by
      conv => lhs; rw [blitFixed.go.eq_1]; simp [hj, hsrc, show off + j < buf.size from hidx, idx]
    rw [byteArray_getElem_of_eq hstep _ (by rw [blitFixed_go_size, byteArray_size_set!]; exact hk),
      ih (by rw [byteArray_size_set!]; exact hbd) (by rw [byteArray_size_set!]; exact hk)]
    split <;> split
    · rfl
    · omega
    · rw [byteArray_getElem_set! hidx hk, ite_eq_left (by omega)]; congr 1; omega
    · rw [byteArray_getElem_set! hidx hk, ite_eq_right (by omega)]
  | case3 => exfalso; omega
  | case4 j buf hj hsrc =>
    split
    · omega
    · exact byteArray_getElem_of_eq (by rw [blitFixed.go.eq_1]; simp [hj, hsrc]) _ hk

/-- Indexing into `blitFixed dst off w src` when `off + min w src.size ≤ dst.size`. -/
theorem blitFixed_getElem {dst src : ByteArray} {off w i : Nat}
    (hbd : off + min w src.size ≤ dst.size) (hi : i < dst.size) :
    (blitFixed dst off w src)[i]'(by rw [blitFixed_size]; exact hi) =
      if h : off ≤ i ∧ i < off + min w src.size then src[i - off]'(by omega) else dst[i]'hi := by
  unfold blitFixed; simpa using blitFixed_go_getElem off w src 0 dst hbd hi

/-- Blitting `src` over a contiguous slice `M` of exact size `src.size` replaces `M` with `src`. -/
theorem blitFixed_mid_exact (L M R src : ByteArray) (hM : M.size = src.size) :
    blitFixed (L ++ M ++ R) L.size M.size src = L ++ src ++ R := by
  apply ByteArray.ext_getElem (by simp [ByteArray.size_append, hM])
  intro i hi1 _
  rw [blitFixed_getElem (by simp [ByteArray.size_append]; omega) (by simpa using hi1)]
  simp only [hM, Nat.min_self]
  split
  · rename_i hm
    rw [ByteArray.getElem_append_left (by rw [ByteArray.size_append]; omega), ByteArray.getElem_append_right hm.1]
  · by_cases hL : i < L.size
    · rw [ByteArray.getElem_append_left (by rw [ByteArray.size_append]; omega), ByteArray.getElem_append_left hL,
        ByteArray.getElem_append_left (by rw [ByteArray.size_append]; omega), ByteArray.getElem_append_left hL]
    · rw [ByteArray.getElem_append_right (by rw [ByteArray.size_append]; omega),
        ByteArray.getElem_append_right (by rw [ByteArray.size_append]; omega)]
      congr 1; simp [ByteArray.size_append, hM]

/-- Blitting `src` over a zero-filled slice of width `w` replaces it with `padRightBytes w src`. -/
theorem blitFixed_mid_zeros (L R src : ByteArray) (w : Nat) :
    blitFixed (L ++ ByteArray.mk (Array.replicate w 0) ++ R) L.size w src =
      L ++ padRightBytes w src ++ R := by
  have hrep : (ByteArray.mk (Array.replicate w 0)).size = w := Array.size_replicate
  apply ByteArray.ext_getElem (by simp [ByteArray.size_append, hrep])
  intro i hi1 _
  rw [blitFixed_getElem (by simp [ByteArray.size_append, hrep]; omega) (by simpa using hi1)]
  split
  · rename_i hm
    rw [ByteArray.getElem_append_left (by rw [ByteArray.size_append, padRightBytes_size]; omega),
      ByteArray.getElem_append_right hm.1, padRightBytes_getElem w src (by omega), dite_eq_left (by omega)]
  · by_cases hL : i < L.size
    · rw [ByteArray.getElem_append_left (by rw [ByteArray.size_append]; omega), ByteArray.getElem_append_left hL,
        ByteArray.getElem_append_left (by rw [ByteArray.size_append]; omega), ByteArray.getElem_append_left hL]
    · by_cases hZ : i < L.size + w
      · rw [ByteArray.getElem_append_left (by rw [ByteArray.size_append, hrep]; omega),
          ByteArray.getElem_append_right (by omega),
          ByteArray.getElem_append_left (by rw [ByteArray.size_append, padRightBytes_size]; omega),
          ByteArray.getElem_append_right (by omega),
          padRightBytes_getElem w src (by omega), dite_eq_right (by omega)]
        exact Array.getElem_replicate ..
      · rw [ByteArray.getElem_append_right (by rw [ByteArray.size_append, hrep]; omega),
          ByteArray.getElem_append_right (by rw [ByteArray.size_append, padRightBytes_size]; omega)]
        congr 1; simp [ByteArray.size_append, hrep]

/-- Inversion lemma for `Except` monadic bind failing with `.error e`. -/
@[simp] theorem except_bind_eq_error {ε α β} {m : Except ε α} {f : α → Except ε β} {e : ε} :
    (m >>= f) = .error e ↔ m = .error e ∨ ∃ a, m = .ok a ∧ f a = .error e := by
  cases m <;> simp [Bind.bind, Except.bind, eq_comm]

/-- Appending any suffix to a non-empty string yields a non-empty string. -/
theorem nonEmpty_append_left {a b : String} (ha : (!a.isEmpty) = true) :
    (!(a ++ b).isEmpty) = true := by
  cases hEmp : (a ++ b).isEmpty
  · rfl
  · have hs := congrArg String.utf8ByteSize (String.isEmpty_iff.mp hEmp)
    rw [String.utf8ByteSize_append] at hs
    change a.utf8ByteSize + b.utf8ByteSize = 0 at hs
    have ha0 : a.isEmpty = true := by simp [String.isEmpty, show a.utf8ByteSize = 0 by omega]
    rw [ha0] at ha; contradiction

theorem u64LimitImpl_eq : u64LimitImpl = u64Limit := rfl
theorem u32LimitImpl_eq : u32LimitImpl = u32Limit := rfl
theorem ustarOctal7LimitImpl_eq : ustarOctal7LimitImpl = ustarOctal7Limit := rfl
theorem ustarOctal11LimitImpl_eq : ustarOctal11LimitImpl = ustarOctal11Limit := rfl
theorem pad512Impl_eq (n : Nat) : pad512Impl n = pad512 n := rfl
theorem zeroDeterministicMetaImpl_eq (e : TarEntry) : zeroDeterministicMetaImpl e = zeroDeterministicMeta e := rfl
theorem zeroBlockImpl_eq : zeroBlockImpl = zeroBlock := rfl
theorem padBlock512Impl_eq (bs : ByteArray) : padBlock512Impl bs = padBlock512 bs := rfl
theorem isAsciiStringImpl_eq (s : String) : isAsciiStringImpl s = isAsciiString s := rfl
theorem wirePathOfImpl_eq (k : EntryKind) (p : String) : wirePathOfImpl k p = wirePathOf k p := rfl
theorem stripTrailingSlashesCharsImpl_eq (cs : List Char) : stripTrailingSlashesCharsImpl cs = stripTrailingSlashesChars cs := rfl
theorem decDigitsLenImpl_eq (n : Nat) : decDigitsLenImpl n = decDigitsLen n := rfl

theorem hasNulCharsImpl_eq : ∀ cs, hasNulCharsImpl cs = hasNulChars cs
  | [] => rfl
  | c :: cs => by simp [hasNulCharsImpl, hasNulChars, hasNulCharsImpl_eq cs]

theorem hasNulStringImpl_eq (s : String) : hasNulStringImpl s = hasNulString s :=
  hasNulCharsImpl_eq s.toList

private theorem splitSlashCharsImpl_go_eq : ∀ acc cs, splitSlashCharsImpl.go acc cs = splitSlashChars.go acc cs
  | _, [] => rfl
  | acc, c :: rest => by
    by_cases hc : c = '/'
    · subst hc; exact congrArg _ (splitSlashCharsImpl_go_eq [] rest)
    · simp only [splitSlashCharsImpl.go, splitSlashChars.go, splitSlashCharsImpl_go_eq (c :: acc) rest]

theorem splitSlashCharsImpl_eq : ∀ cs, splitSlashCharsImpl cs = splitSlashChars cs
  | [] => rfl
  | c :: cs => splitSlashCharsImpl_go_eq [] (c :: cs)

private theorem checkSegmentsImpl_go_eq (allowPar : Bool) : ∀ segs, checkSegmentsImpl.go allowPar segs = checkSegments.go allowPar segs
  | [] => rfl
  | seg :: rest => by
    unfold checkSegmentsImpl.go checkSegments.go
    repeat (split; · rfl)
    exact checkSegmentsImpl_go_eq allowPar rest

theorem checkSegmentsImpl_eq (allowPar : Bool) : ∀ segs, checkSegmentsImpl allowPar segs = checkSegments allowPar segs
  | [] => rfl
  | seg :: rest => checkSegmentsImpl_go_eq allowPar (seg :: rest)

theorem validateEntryPathImpl_eq (allowAbs allowPar : Bool) (kind : EntryKind) (path : String) :
    validateEntryPathImpl allowAbs allowPar kind path = validateEntryPath allowAbs allowPar kind path := by
  unfold validateEntryPathImpl validateEntryPath
  simp only [hasNulCharsImpl_eq, stripTrailingSlashesCharsImpl_eq, splitSlashCharsImpl_eq, checkSegmentsImpl_eq]
  rfl

private theorem validateSymlinkTargetImpl_walkDepth_eq (entryPath : String) :
    ∀ depth segs, validateSymlinkTargetImpl.walkDepth entryPath depth segs = validateSymlinkTarget.walkDepth entryPath depth segs
  | _, [] => rfl
  | depth, seg :: rest => by
    unfold validateSymlinkTargetImpl.walkDepth validateSymlinkTarget.walkDepth
    split
    · exact validateSymlinkTargetImpl_walkDepth_eq entryPath depth rest
    · split
      · split
        · rfl
        · exact validateSymlinkTargetImpl_walkDepth_eq entryPath (depth - 1) rest
      · exact validateSymlinkTargetImpl_walkDepth_eq entryPath (depth + 1) rest

theorem validateSymlinkTargetImpl_eq (allowAbs allowPar : Bool) (entryPath linkTarget : String) :
    validateSymlinkTargetImpl allowAbs allowPar entryPath linkTarget =
      validateSymlinkTarget allowAbs allowPar entryPath linkTarget := by
  unfold validateSymlinkTargetImpl validateSymlinkTarget
  simp only [hasNulCharsImpl_eq, splitSlashCharsImpl_eq, validateSymlinkTargetImpl_walkDepth_eq]
  rfl

private theorem findUstarSplitImpl_go_eq : ∀ rev cs, findUstarSplitImpl.go rev cs = findUstarSplit.go rev cs
  | _, [] => rfl
  | rev, c :: rest => by
    by_cases hc : c = '/'
    · subst hc
      rw [findUstarSplitImpl.go.eq_2, findUstarSplit.go.eq_2]
      split
      · rfl
      · exact findUstarSplitImpl_go_eq ('/' :: rev) rest
    · simp only [findUstarSplitImpl.go, findUstarSplit.go, findUstarSplitImpl_go_eq (c :: rev) rest]

theorem findUstarSplitImpl_eq (wp : String) : findUstarSplitImpl wp = findUstarSplit wp :=
  findUstarSplitImpl_go_eq [] wp.toList

theorem pathFitsUstarImpl_eq (wp : String) : pathFitsUstarImpl wp = pathFitsUstar wp := by
  unfold pathFitsUstarImpl pathFitsUstar
  rw [isAsciiStringImpl_eq, findUstarSplitImpl_eq]

theorem needsPaxImpl_eq (e : TarEntry) (wp : String) : needsPaxImpl e wp = needsPax e wp := by
  unfold needsPaxImpl needsPax
  simp only [pathFitsUstarImpl_eq, isAsciiStringImpl_eq, ustarOctal7LimitImpl_eq, ustarOctal11LimitImpl_eq]
  rfl

private theorem paxRecordTotalLenImpl_go_eq (kvBodyLen : Nat) :
    ∀ digits fuel, paxRecordTotalLenImpl.go kvBodyLen digits fuel = paxRecordTotalLen.go kvBodyLen digits fuel
  | _, 0 => rfl
  | digits, fuel + 1 => by
    unfold paxRecordTotalLenImpl.go paxRecordTotalLen.go
    dsimp only
    rw [decDigitsLenImpl_eq]
    split
    · rfl
    · exact paxRecordTotalLenImpl_go_eq kvBodyLen _ fuel

theorem paxRecordTotalLenImpl_eq (kvBodyLen : Nat) : paxRecordTotalLenImpl kvBodyLen = paxRecordTotalLen kvBodyLen :=
  paxRecordTotalLenImpl_go_eq kvBodyLen 1 20

theorem encodePaxRecordImpl_eq (key value : String) : encodePaxRecordImpl key value = encodePaxRecord key value := by
  unfold encodePaxRecordImpl encodePaxRecord
  dsimp only
  rw [paxRecordTotalLenImpl_eq]

theorem buildPaxPayloadImpl_eq (e : TarEntry) (wp : String) : buildPaxPayloadImpl e wp = buildPaxPayload e wp := by
  unfold buildPaxPayloadImpl buildPaxPayload
  simp only [pathFitsUstarImpl_eq, encodePaxRecordImpl_eq, isAsciiStringImpl_eq, ustarOctal11LimitImpl_eq, ustarOctal7LimitImpl_eq]

end LeanSwe.Tar.Proofs
