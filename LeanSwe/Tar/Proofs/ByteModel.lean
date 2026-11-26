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

end LeanSwe.Tar.Proofs
