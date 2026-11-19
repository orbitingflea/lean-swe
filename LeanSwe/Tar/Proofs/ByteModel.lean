import LeanSwe.Tar.Model
import LeanSwe.Tar.Impl
import LeanSwe.Tar.SpecTests

namespace LeanSwe.Tar.Proofs

open Core
open Core.NondetTest
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

/-- `ByteArray.extract` across a matching prefix returns the exact left array. -/
theorem extract_append_exact_left (a b : ByteArray) : (a ++ b).extract 0 a.size = a :=
  ByteArray.extract_append_eq_left rfl

/-- `ByteArray.extract` on `(a ++ b) ++ c` at `[a.size .. a.size + b.size)` yields `b`. -/
theorem byteArray_extract_mid (a b c : ByteArray) : ((a ++ b) ++ c).extract a.size (a.size + b.size) = b := by
  rw [ByteArray.extract_append,
    show a.size - (a ++ b).size = 0 by rw [ByteArray.size_append]; omega,
    show a.size + b.size - (a ++ b).size = 0 by rw [ByteArray.size_append]; omega]
  simp [ByteArray.extract_append_eq_right rfl rfl]

/-- `ByteArray.extract` starting at `a.size` on `(a ++ b)` extracts prefix `k` of `b`. -/
theorem byteArray_extract_append_right (a b : ByteArray) (k : Nat) : (a ++ b).extract a.size (a.size + k) = b.extract 0 k := by
  rw [ByteArray.extract_append, ByteArray.extract_eq_empty_iff.mpr (by omega),
    Nat.sub_self, Nat.add_sub_cancel_left, ByteArray.empty_append]

/-- `ByteArray.extract` suffix `[a.size .. (a ++ b).size)` of `a ++ b` equals `b`. -/
theorem byteArray_extract_suffix (a b : ByteArray) : (a ++ b).extract a.size (a ++ b).size = b := by
  rw [ByteArray.size_append, byteArray_extract_append_right, ByteArray.extract_zero_size]

/-- Extract a contiguous subslice from `bytes.extract offset (offset + e) = L ++ (M ++ R)`. -/
theorem byteArray_extract_sub {bytes L M R : ByteArray} {offset e a w : Nat}
    (he : bytes.extract offset (offset + e) = L ++ (M ++ R)) (ha : L.size = a) (hw : M.size = w) (hb : a + w ≤ e) :
    bytes.extract (offset + a) (offset + a + w) = M := by
  have hsub : bytes.extract (offset + a) (offset + a + w) = (bytes.extract offset (offset + e)).extract a (a + w) := by
    rw [ByteArray.extract_extract]; exact congrArg (bytes.extract (offset + a)) (by omega)
  rw [hsub, he, ← ByteArray.append_assoc, ← ha, ← hw]; exact byteArray_extract_mid L M R

/-- Indexing into `a ++ b` in the left range yields `a[i]`. -/
theorem getElem_append_left {a b : ByteArray} {i : Nat} (hi : i < a.size)
    (hab : i < (a ++ b).size := by rw [ByteArray.size_append]; omega) : (a ++ b)[i]'hab = a[i]'hi :=
  ByteArray.getElem_append_left hi

/-- Indexing into `a ++ b` in the right range yields `b[i - a.size]`. -/
theorem getElem_append_right {a b : ByteArray} {i : Nat} (hle : a.size ≤ i) (hab : i < (a ++ b).size) :
    (a ++ b)[i]'hab = b[i - a.size]'(by rw [ByteArray.size_append] at hab; omega) :=
  ByteArray.getElem_append_right hle

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

/-- `(a ++ b).toUTF8 = a.toUTF8 ++ b.toUTF8`. -/
@[simp] theorem toUTF8_append (a b : String) : (a ++ b).toUTF8 = a.toUTF8 ++ b.toUTF8 := String.toByteArray_append

/-- `(a ++ b).toUTF8.size = a.toUTF8.size + b.toUTF8.size`. -/
@[simp] theorem toUTF8_size_append (a b : String) : (a ++ b).toUTF8.size = a.toUTF8.size + b.toUTF8.size := by
  rw [toUTF8_append, ByteArray.size_append]

/-- `String.fromUTF8?` inverts `String.toUTF8` for every `String`. -/
@[simp] theorem fromUTF8?_toUTF8 (s : String) : String.fromUTF8? s.toUTF8 = some s := by
  simp [String.fromUTF8?, String.toUTF8, s.isValidUTF8, String.fromUTF8]

/-- `zeroBlock` has size `512`. -/
@[simp] theorem zeroBlock_size : zeroBlock.size = 512 := by simp [zeroBlock, ByteArray.size]

/-- Every byte in `zeroBlock` is `0`. -/
@[simp] theorem zeroBlock_getElem {i : Nat} (hi : i < zeroBlock.size) : zeroBlock[i]'hi = 0 := by
  change (Array.replicate 512 (0 : UInt8))[i]'(by simpa [zeroBlock, ByteArray.size] using hi) = 0
  exact Array.getElem_replicate ..

/-- `twoZeroBlocks` has size `1024`. -/
@[simp] theorem twoZeroBlocks_size : twoZeroBlocks.size = 1024 := by simp [twoZeroBlocks, ByteArray.size_append]

/-- `pad512 n` is always `≥ n`. -/
theorem le_pad512 (n : Nat) : n ≤ pad512 n := by unfold pad512; omega

/-- `pad512 n` is a multiple of `512`. -/
@[simp] theorem pad512_mod (n : Nat) : pad512 n % 512 = 0 := by unfold pad512; simp [Nat.mul_mod_left]

/-- `pad512 0 = 0`. -/
@[simp] theorem pad512_zero : pad512 0 = 0 := rfl

/-- `(padBlock512 bs).size = pad512 bs.size`. -/
@[simp] theorem padBlock512_size (bs : ByteArray) : (padBlock512 bs).size = pad512 bs.size := by
  unfold padBlock512 pad512
  by_cases h0 : bs.size % 512 = 0
  · simp only [beq_iff_eq.mpr h0, ↓reduceIte]; omega
  · simp only [beq_false_of_ne h0, Bool.false_eq_true, ↓reduceIte, ByteArray.size_append]
    have hr : (ByteArray.mk (Array.replicate (512 - bs.size % 512) 0)).size = 512 - bs.size % 512 := Array.size_replicate
    rw [hr]; omega

/-- `(padBlock512 bs).extract 0 bs.size = bs`. -/
@[simp] theorem padBlock512_extract_prefix (bs : ByteArray) : (padBlock512 bs).extract 0 bs.size = bs := by
  unfold padBlock512; dsimp only; split <;> simp [ByteArray.extract_zero_size, extract_append_exact_left]

/-- `padRightBytes width bs` always has size `width`. -/
@[simp] theorem padRightBytes_size (width : Nat) (bs : ByteArray) :
    (padRightBytes width bs).size = width := by
  unfold padRightBytes
  split
  · rw [ByteArray.size_extract]; omega
  · rw [ByteArray.size_append]
    have hr : (ByteArray.mk (Array.replicate (width - bs.size) 0)).size = width - bs.size := Array.size_replicate
    rw [hr]; omega

/-- If `bs.size ≤ width`, `(padRightBytes width bs).extract 0 bs.size = bs`. -/
theorem padRightBytes_extract_prefix {width : Nat} {bs : ByteArray} (h : bs.size ≤ width) :
    (padRightBytes width bs).extract 0 bs.size = bs := by
  unfold padRightBytes
  by_cases hge : bs.size ≥ width
  · simp only [hge, ↓reduceIte]
    rw [← Nat.le_antisymm h hge, ByteArray.extract_zero_size, ByteArray.extract_zero_size]
  · simp only [hge, ↓reduceIte, extract_append_exact_left]

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

/-- Inversion lemma for `Except` monadic bind succeeding with `.ok b`. -/
@[simp] theorem except_bind_eq_ok {ε α β} {m : Except ε α} {f : α → Except ε β} {b : β} :
    (m >>= f) = .ok b ↔ ∃ a, m = .ok a ∧ f a = .ok b := by
  cases m <;> simp [Bind.bind, Except.bind]

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

/-- Split `Core.AllPass (assert p >>= k)` into `p` and `Core.AllPass (k ())`. -/
theorem allPass_assert_bind (p : Prop) (k : Unit → Core.AllPassRun Unit) :
    Core.AllPass (Bind.bind (Core.NondetTest.assert p) k) ↔ p ∧ Core.AllPass (k ()) :=
  Iff.rfl

/-- Split `Core.AllPass (checkUnpackError ... >>= k)` into error verification and continuation. -/
theorem allPass_checkUnpackError_bind {api : TarApi} {opts : UnpackOptions}
    {bytes : ByteArray} {expectedKind : TarErrorKind} {e : TarError}
    (herr : api.unpackWith opts bytes = .error e)
    (hk : e.kind = expectedKind) (hm : (!e.message.isEmpty) = true)
    {k : Unit → Core.AllPassRun Unit} (hkRest : Core.AllPass (k ())) :
    Core.AllPass (Bind.bind (checkUnpackError api opts bytes expectedKind) k) := by
  dsimp only [checkUnpackError]; rw [herr]; exact ⟨⟨hk, hm⟩, hkRest⟩

end LeanSwe.Tar.Proofs
