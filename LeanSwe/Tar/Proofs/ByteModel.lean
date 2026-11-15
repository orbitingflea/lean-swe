import LeanSwe.Tar.Model
import LeanSwe.Tar.Impl

namespace LeanSwe.Tar.Proofs

open LeanSwe.Tar
open LeanSwe.Tar.Model
open LeanSwe.Tar.Impl

/-- `ByteArray.extract` across a matching prefix returns the exact left array. -/
theorem extract_append_exact_left (a b : ByteArray) :
    (a ++ b).extract 0 a.size = a :=
  ByteArray.extract_append_eq_left rfl

/-- `ByteArray.extract` on `a ++ b ++ c` at `[a.size .. a.size + b.size)` yields `b`. -/
theorem extract_append_mid (a b c : ByteArray) :
    ((a ++ b) ++ c).extract a.size (a.size + b.size) = b := by
  rw [ByteArray.extract_append]
  have hzero : a.size + b.size - (a ++ b).size = 0 := by
    rw [ByteArray.size_append]; omega
  have hzero2 : a.size - (a ++ b).size = 0 := by
    rw [ByteArray.size_append]; omega
  rw [hzero2, hzero]
  simp [ByteArray.extract_append_eq_right rfl rfl]

/-- `ByteArray.extract` starting at `a.size` on `(a ++ b)` extracts prefix `k` of `b`. -/
theorem extract_append_right (a b : ByteArray) (k : Nat) :
    (a ++ b).extract a.size (a.size + k) = b.extract 0 k := by
  rw [ByteArray.extract_append]
  have h1 : a.extract a.size (a.size + k) = ByteArray.empty := by
    apply ByteArray.extract_eq_empty_iff.mpr
    omega
  rw [h1]
  have he : a.size + k - a.size = k := by omega
  have he2 : a.size - a.size = 0 := Nat.sub_self a.size
  rw [he2, he]
  simp

/-- Indexing into `a ++ b` in the left range yields `a[i]`. -/
theorem getElem_append_left {a b : ByteArray} {i : Nat} (hi : i < a.size)
    (hab : i < (a ++ b).size := by rw [ByteArray.size_append]; omega) :
    (a ++ b)[i]'hab = a[i]'hi :=
  ByteArray.getElem_append_left hi

/-- Indexing into `a ++ b` in the right range yields `b[i - a.size]`. -/
theorem getElem_append_right {a b : ByteArray} {i : Nat} (hle : a.size ≤ i)
    (hab : i < (a ++ b).size) :
    (a ++ b)[i]'hab = b[i - a.size]'(by rw [ByteArray.size_append] at hab; omega) :=
  ByteArray.getElem_append_right hle

/-- `String.fromUTF8?` inverts `String.toUTF8` for every `String`. -/
theorem fromUTF8?_toUTF8 (s : String) : String.fromUTF8? s.toUTF8 = some s := by
  simp [String.fromUTF8?, String.toUTF8, s.isValidUTF8, String.fromUTF8]

/-- `zeroBlock` has size `512`. -/
theorem zeroBlock_size : zeroBlock.size = 512 := by
  simp [zeroBlock, ByteArray.size]

/-- Every byte in `zeroBlock` is `0`. -/
theorem zeroBlock_getElem {i : Nat} (hi : i < zeroBlock.size) : zeroBlock[i]'hi = 0 := by
  change (Array.replicate 512 (0 : UInt8))[i]'(by simpa [zeroBlock, ByteArray.size] using hi) = 0
  exact Array.getElem_replicate ..

/-- `pad512 n` is always `≥ n`. -/
theorem le_pad512 (n : Nat) : n ≤ pad512 n := by
  unfold pad512
  have hdiv := Nat.div_add_mod (n + 511) 512
  have hmod := Nat.mod_lt (n + 511) (by omega : 0 < 512)
  omega

/-- `pad512 n` is a multiple of `512`. -/
theorem pad512_mod (n : Nat) : pad512 n % 512 = 0 := by
  unfold pad512
  simp [Nat.mul_mod_left]

/-- `pad512 0 = 0`. -/
theorem pad512_zero : pad512 0 = 0 := by
  decide

/-- `(padBlock512 bs).size = pad512 bs.size`. -/
theorem padBlock512_size (bs : ByteArray) : (padBlock512 bs).size = pad512 bs.size := by
  unfold padBlock512 pad512
  by_cases h0 : bs.size % 512 = 0
  · have hbe : (bs.size % 512 == 0) = true := beq_iff_eq.mpr h0
    simp only [hbe, ↓reduceIte]
    have hdiv := Nat.div_add_mod bs.size 512
    have h1 : (bs.size + 511) / 512 = bs.size / 512 := by
      have hk : bs.size = 512 * (bs.size / 512) := by omega
      rw [hk]
      omega
    rw [h1]
    omega
  · have hbe : (bs.size % 512 == 0) = false := beq_false_of_ne h0
    simp only [hbe, Bool.false_eq_true, ↓reduceIte]
    rw [ByteArray.size_append]
    have hrep : (ByteArray.mk (Array.replicate (512 - bs.size % 512) 0)).size = 512 - bs.size % 512 := by
      change (Array.replicate (512 - bs.size % 512) (0 : UInt8)).size = 512 - bs.size % 512
      exact Array.size_replicate
    rw [hrep]
    have hmod : 0 < bs.size % 512 := Nat.pos_of_ne_zero h0
    have hlt : bs.size % 512 < 512 := Nat.mod_lt bs.size (by omega)
    have hdiv := Nat.div_add_mod bs.size 512
    have h1 : (bs.size + 511) / 512 = bs.size / 512 + 1 := by omega
    rw [h1]
    omega

/-- `(padBlock512 bs).extract 0 bs.size = bs`. -/
theorem padBlock512_extract_prefix (bs : ByteArray) :
    (padBlock512 bs).extract 0 bs.size = bs := by
  unfold padBlock512
  by_cases h0 : bs.size % 512 = 0
  · have hbe : (bs.size % 512 == 0) = true := beq_iff_eq.mpr h0
    simp only [hbe, ↓reduceIte]
    exact ByteArray.extract_zero_size
  · have hbe : (bs.size % 512 == 0) = false := beq_false_of_ne h0
    simp only [hbe, Bool.false_eq_true, ↓reduceIte]
    exact extract_append_exact_left bs _

/-- `padRightBytes width bs` always has size `width`. -/
theorem padRightBytes_size (width : Nat) (bs : ByteArray) :
    (padRightBytes width bs).size = width := by
  unfold padRightBytes
  by_cases h : bs.size ≥ width
  · simp only [h, ↓reduceIte]
    rw [ByteArray.size_extract]
    omega
  · simp only [h, ↓reduceIte]
    rw [ByteArray.size_append]
    have hrep : (ByteArray.mk (Array.replicate (width - bs.size) 0)).size = width - bs.size := by
      change (Array.replicate (width - bs.size) (0 : UInt8)).size = width - bs.size
      exact Array.size_replicate
    rw [hrep]
    omega

/-- If `bs.size ≤ width`, `(padRightBytes width bs).extract 0 bs.size = bs`. -/
theorem padRightBytes_extract_prefix {width : Nat} {bs : ByteArray} (h : bs.size ≤ width) :
    (padRightBytes width bs).extract 0 bs.size = bs := by
  unfold padRightBytes
  by_cases hge : bs.size ≥ width
  · have heq : bs.size = width := Nat.le_antisymm h hge
    simp only [hge, ↓reduceIte]
    rw [← heq, ByteArray.extract_zero_size, ByteArray.extract_zero_size]
  · simp only [hge, ↓reduceIte]
    exact extract_append_exact_left bs _

/-- Indexing into `padRightBytes width bs` when `bs.size ≤ width`. -/
theorem padRightBytes_getElem {width : Nat} {bs : ByteArray} (hle : bs.size ≤ width)
    {i : Nat} (hi : i < width) :
    (padRightBytes width bs)[i]'(by rw [padRightBytes_size]; exact hi) =
      if h : i < bs.size then bs[i]'h else 0 := by
  unfold padRightBytes
  by_cases hge : bs.size ≥ width
  · have heq : bs.size = width := Nat.le_antisymm hle hge
    have hilt : i < bs.size := by omega
    simp only [hge, ↓reduceIte, hilt, ↓reduceDIte]
    rw [ByteArray.getElem_extract]
    simp
  · simp only [hge, ↓reduceIte]
    by_cases hilt : i < bs.size
    · simp only [hilt, ↓reduceDIte]
      exact ByteArray.getElem_append_left hilt
    · simp only [hilt, ↓reduceDIte]
      have hgei : bs.size ≤ i := Nat.le_of_not_lt hilt
      rw [ByteArray.getElem_append_right hgei]
      change (Array.replicate (width - bs.size) (0 : UInt8))[i - bs.size]'(by rw [Array.size_replicate]; omega) = 0
      exact Array.getElem_replicate ..

private theorem byteArray_size_set! (b : ByteArray) (k : Nat) (v : UInt8) :
    (b.set! k v).size = b.size :=
  Array.size_setIfInBounds

/-- `(blitFixed dst offset width src).size = dst.size`. -/
theorem blitFixed_size (dst : ByteArray) (offset width : Nat) (src : ByteArray) :
    (blitFixed dst offset width src).size = dst.size := by
  unfold blitFixed
  suffices ∀ i buf, buf.size = dst.size → (blitFixed.go offset width src i buf).size = dst.size
    from this 0 dst rfl
  intro i buf hsz
  fun_induction blitFixed.go offset width src i buf with
  | case1 => exact hsz
  | case2 =>
    rename_i ih
    apply ih
    rw [byteArray_size_set!, hsz]
  | case3 => exact hsz
  | case4 => exact hsz

end LeanSwe.Tar.Proofs
