import LeanSwe.Tar.Proofs.ByteModel

namespace LeanSwe.Tar.Proofs

open LeanSwe.Tar
open LeanSwe.Tar.Model
open LeanSwe.Tar.Impl

/-- `(l.toByteArray).toList` equals `l`. -/
theorem toByteArray_toList (l : List UInt8) : l.toByteArray.toList = l := by
  rw [byteArray_toList_eq]
  apply List.ext_getElem (by rw [Array.length_toList, ← ByteArray.size, List.size_toByteArray])
  intro i hi1 _
  have hi : i < l.toByteArray.size := by rw [ByteArray.size]; exact hi1
  rw [Array.getElem_toList, ← ByteArray.getElem_eq_getElem_data (h := hi), List.getElem_toByteArray]

/-- `(a ++ b).data.toList = a.data.toList ++ b.data.toList`. -/
theorem byteArray_data_toList_append (a b : ByteArray) :
    (a ++ b).data.toList = a.data.toList ++ b.data.toList := by
  apply List.ext_getElem (by simp only [List.length_append, Array.length_toList]; exact ByteArray.size_append)
  intro i hi1 _
  have h1 : i < (a ++ b).size := by simpa [Array.length_toList] using hi1
  rw [Array.getElem_toList, ← ByteArray.getElem_eq_getElem_data (h := h1), byteArray_getElem_append h1]
  by_cases hlt : i < a.size
  · have hlt' : i < a.data.toList.length := by simpa [Array.length_toList] using hlt
    simp [hlt, List.getElem_append_left hlt', Array.getElem_toList, ← ByteArray.getElem_eq_getElem_data]
  · have hge : a.size ≤ i := Nat.le_of_not_lt hlt
    have hge' : a.data.toList.length ≤ i := by simpa [Array.length_toList] using hge
    simp only [hlt, ↓reduceDIte, List.getElem_append_right hge', Array.getElem_toList,
      ← ByteArray.getElem_eq_getElem_data]
    congr 1

/-- `s.toUTF8` equals `(s.toList.flatMap String.utf8EncodeChar).toByteArray`. -/
theorem toUTF8_eq_toByteArray (s : String) :
    s.toUTF8 = (s.toList.flatMap String.utf8EncodeChar).toByteArray := by
  conv => lhs; rw [← String.ofList_toList (s := s), String.toUTF8, String.toByteArray_ofList]
  rfl

/-- `s.toUTF8.toList` equals `s.toList.flatMap String.utf8EncodeChar`. -/
theorem toUTF8_toList (s : String) :
    s.toUTF8.toList = s.toList.flatMap String.utf8EncodeChar := by
  rw [toUTF8_eq_toByteArray, toByteArray_toList]

/-- `String.utf8EncodeChar c` never contains `0` when `c ≠ Char.ofNat 0`. -/
theorem zero_not_mem_utf8EncodeChar {c : Char} (hc : c ≠ Char.ofNat 0) :
    (0 : UInt8) ∉ String.utf8EncodeChar c := by
  have hne : c.val.toNat ≠ 0 := fun h0 => hc (by rw [Char.ext_iff, ← UInt32.toNat_inj]; exact h0)
  unfold String.utf8EncodeChar; dsimp only
  split
  · simp only [List.mem_singleton]; intro h
    have hn := congrArg UInt8.toNat h.symm
    rw [UInt8.toNat_ofNat', Nat.mod_eq_of_lt (by omega)] at hn; change c.val.toNat = 0 at hn; omega
  · split
    · simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro (h | h) <;> (have hn := congrArg UInt8.toNat h; rw [UInt8.toNat_ofNat'] at hn; change 0 = _ at hn; omega)
    · split
      · simp only [List.mem_cons, List.not_mem_nil, or_false]
        rintro (h | h | h) <;> (have hn := congrArg UInt8.toNat h; rw [UInt8.toNat_ofNat'] at hn; change 0 = _ at hn; omega)
      · simp only [List.mem_cons, List.not_mem_nil, or_false]
        rintro (h | h | h | h) <;> (have hn := congrArg UInt8.toNat h; rw [UInt8.toNat_ofNat'] at hn; change 0 = _ at hn; omega)

/-- `hasNulChars cs = false` iff `Char.ofNat 0 ∉ cs`. -/
theorem hasNulChars_false_iff (cs : List Char) :
    hasNulChars cs = false ↔ Char.ofNat 0 ∉ cs := by
  induction cs with
  | nil => simp [hasNulChars]
  | cons c rest ih =>
    simp only [hasNulChars, Bool.or_eq_false_iff, beq_eq_false_iff_ne, ne_eq, List.mem_cons, not_or, ih]
    exact ⟨fun ⟨h1, h2⟩ => ⟨Ne.symm h1, h2⟩, fun ⟨h1, h2⟩ => ⟨Ne.symm h1, h2⟩⟩

/-- If `!hasNulString s = true`, then `(0 : UInt8) ∉ s.toUTF8.toList`. -/
theorem zero_not_mem_toUTF8_of_not_hasNulString {s : String} (h : !hasNulString s = true) :
    (0 : UInt8) ∉ s.toUTF8.toList := by
  have hnc : Char.ofNat 0 ∉ s.toList := (hasNulChars_false_iff s.toList).mp (Bool.not_eq_true' _ |>.mp h)
  rw [toUTF8_toList, List.mem_flatMap]
  rintro ⟨c, hcin, hc0⟩
  exact zero_not_mem_utf8EncodeChar (fun heq => hnc (heq ▸ hcin)) hc0

/-- Indexing into `s.toUTF8` never yields `0` when `!hasNulString s = true`. -/
theorem toUTF8_getElem_ne_zero {s : String} (h : !hasNulString s = true)
    {i : Nat} (hi : i < s.toUTF8.size) : s.toUTF8[i]'hi ≠ 0 := by
  intro h0
  apply zero_not_mem_toUTF8_of_not_hasNulString h
  rw [byteArray_toList_eq, ← h0, ByteArray.getElem_eq_getElem_data, ← Array.getElem_toList]
  exact List.getElem_mem _

/-- `hasNulChars (a ++ b) = hasNulChars a || hasNulChars b`. -/
theorem hasNulChars_append (a b : List Char) :
    hasNulChars (a ++ b) = (hasNulChars a || hasNulChars b) := by
  induction a with
  | nil => simp [hasNulChars]
  | cons _ _ ih => simp [hasNulChars, ih, Bool.or_assoc]

/-- `!hasNulString (a ++ b) = (!hasNulString a && !hasNulString b)`. -/
theorem not_hasNulString_append (a b : String) :
    (!hasNulString (a ++ b)) = (!hasNulString a && !hasNulString b) := by
  simp [hasNulString, String.toList_append, hasNulChars_append]

/-- `findUstarSplit` returns a valid split `(pfx, nm)` reconstructing `wp`. -/
theorem findUstarSplit_spec {wp pfx nm : String} (h : findUstarSplit wp = some (pfx, nm)) :
    pfx ++ "/" ++ nm = wp ∧ !pfx.isEmpty = true ∧ !nm.isEmpty = true ∧
      pfx.toUTF8.size ≤ 155 ∧ nm.toUTF8.size ≤ 100 := by
  suffices ∀ revPfx rest, revPfx.reverse ++ rest = wp.toList →
      findUstarSplit.go revPfx rest = some (pfx, nm) →
      pfx ++ "/" ++ nm = wp ∧ !pfx.isEmpty = true ∧ !nm.isEmpty = true ∧
        pfx.toUTF8.size ≤ 155 ∧ nm.toUTF8.size ≤ 100 from
    this [] wp.toList (by simp) h
  intro revPfx rest hrec hgo
  induction rest generalizing revPfx with
  | nil => simp [findUstarSplit.go] at hgo
  | cons c tl ih =>
    by_cases hs : c = '/'
    · subst hs; rw [findUstarSplit.go.eq_2] at hgo
      split at hgo
      · rename_i hcond; cases hgo
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hcond
        rcases hcond with ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩
        refine ⟨?_, h1, h2, h3, h4⟩
        rw [← String.ofList_toList (s := wp), ← hrec,
          show revPfx.reverse ++ '/' :: tl = revPfx.reverse ++ (['/'] ++ tl) from rfl,
          String.ofList_append, String.ofList_append, show String.ofList ['/'] = "/" from rfl, String.append_assoc]
      · exact ih ('/' :: revPfx) (by simpa [List.append_assoc] using hrec) hgo
    · rw [findUstarSplit.go.eq_3 _ c tl hs] at hgo
      exact ih (c :: revPfx) (by simpa [List.append_assoc] using hrec) hgo

/-- `encodeOctalField.loop k v acc` prepends `k` octal digit bytes `[0x30..0x37]` to `acc`. -/
theorem encodeOctalField_loop_spec (k v : Nat) (acc : List UInt8) :
    ∃ ds : List UInt8,
      encodeOctalField.loop k v acc = ds ++ acc ∧
      ds.length = k ∧
      (∀ d ∈ ds, 0x30 ≤ d ∧ d ≤ 0x37) ∧
      ds.foldl (fun a b => a * 8 + (b.toNat - 0x30)) 0 = v % 8 ^ k := by
  induction k generalizing v acc with
  | zero =>
    refine ⟨[], rfl, rfl, ?_, by simp [Nat.mod_one]⟩
    intro _ h; nomatch h
  | succ k' ih =>
    unfold encodeOctalField.loop
    let d : UInt8 := UInt8.ofNat (0x30 + v % 8)
    have hd : d.toNat = 0x30 + v % 8 := by
      change (UInt8.ofNat (0x30 + v % 8)).toNat = _; rw [UInt8.toNat_ofNat', Nat.mod_eq_of_lt (by omega)]
    rcases ih (v / 8) (d :: acc) with ⟨ds', heq, hlen, hdig, hval⟩
    refine ⟨ds' ++ [d], by rw [heq, List.append_assoc, List.singleton_append], by simp [hlen], ?_, ?_⟩
    · intro b hb; rcases List.mem_append.mp hb with hb | hb
      · exact hdig b hb
      · rcases List.mem_singleton.mp hb with rfl
        exact ⟨by change 48 ≤ d.toNat; omega, by change d.toNat ≤ 55; omega⟩
    · rw [List.foldl_append, hval, List.foldl_cons, List.foldl_nil, hd, show 0x30 + v % 8 - 0x30 = v % 8 by omega]
      have hk : (v / 8) % 8 ^ k' < 8 ^ k' := Nat.mod_lt _ (Nat.pow_pos (by omega))
      have hv : v = (8 * 8 ^ k') * (v / 8 / 8 ^ k') + ((v / 8 % 8 ^ k') * 8 + v % 8) := by
        calc v = 8 * (v / 8) + v % 8 := (Nat.div_add_mod v 8).symm
          _ = 8 * (8 ^ k' * (v / 8 / 8 ^ k') + v / 8 % 8 ^ k') + v % 8 := by rw [Nat.div_add_mod (v / 8) (8 ^ k')]
          _ = _ := by rw [Nat.mul_add, Nat.mul_assoc, Nat.mul_comm 8 (v / 8 % 8 ^ k'), Nat.add_assoc]
      conv => rhs; rw [Nat.pow_succ, Nat.mul_comm _ 8, hv, Nat.mul_add_mod, Nat.mod_eq_of_lt (by omega)]

/-- Size of `encodeOctalField val digits` is `digits + 1`. -/
@[simp] theorem encodeOctalField_size (val digits : Nat) :
    (encodeOctalField val digits).size = digits + 1 := by
  unfold encodeOctalField
  rcases encodeOctalField_loop_spec digits val [0] with ⟨ds, heq, hlen, _, _⟩
  rw [heq]; change (ds ++ [0]).toArray.size = digits + 1; simp [hlen]

/-- `List.takeWhile p xs = xs` whenever `∀ x ∈ xs, p x = true`. -/
theorem list_takeWhile_eq_self {α : Type} (p : α → Bool) (xs : List α)
    (h : ∀ x ∈ xs, p x = true) : xs.takeWhile p = xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [h x (by simp), ih (fun y hy => h y (by simp [hy]))]

/-- For `b.toNat < 64`, `b &&& 0x80 = 0`. -/
theorem uint8_and_0x80_eq_zero {b : UInt8} (hb : b.toNat < 64) : (b &&& 0x80) = 0 := by
  have : b.toBitVec < 64#8 := by simp [BitVec.lt_def, hb]
  apply UInt8.toBitVec_inj.mp; grind

/-- `parseChecksumOctal` decodes `encodeOctalField chk 6 ++ #[0x20]` when `chk < 8 ^ 6`. -/
theorem parseChecksumOctal_encodeOctalField {bytes : ByteArray} {start errOff chk : Nat}
    (hchk : chk < 8 ^ 6)
    (hext : bytes.extract start (start + 8) = encodeOctalField chk 6 ++ ByteArray.mk #[0x20]) :
    parseChecksumOctal bytes start (start + 8) errOff = .ok chk := by
  unfold parseChecksumOctal
  rw [hext, byteArray_data_toList_append]
  rcases encodeOctalField_loop_spec 6 chk [0] with ⟨ds, heq, hlen, hdig, hval⟩
  have hraw : (encodeOctalField chk 6).data.toList = ds ++ [0] := by unfold encodeOctalField; rw [heq]
  dsimp only; rw [hraw, List.append_assoc, show ([0] : List UInt8) ++ [0x20] = [0, 0x20] from rfl]
  cases hds : ds with
  | nil => simp [hds] at hlen
  | cons d0 ds' =>
    have hd0 : 0x30 ≤ d0 ∧ d0 ≤ 0x37 := hdig d0 (by simp [hds])
    have hne20 : (d0 == 0x20) = false := beq_false_of_ne (by intro h; subst h; simp at hd0)
    have hd_all : ∀ d ∈ (d0 :: ds'), (0x30 ≤ d && d ≤ 0x37) = true := fun d hd => by
      have ⟨h1, h2⟩ := hdig d (by simpa [hds] using hd); simp [h1, h2]
    have hdrop : ((d0 :: ds') ++ [0, 0x20]).dropWhile (· == 0x20) = (d0 :: ds') ++ [0, 0x20] := by simp [hne20]
    have htake : ((d0 :: ds') ++ [0, 0x20]).takeWhile (fun b => 0x30 ≤ b && b ≤ 0x37) = d0 :: ds' := by
      rw [List.takeWhile_append, list_takeWhile_eq_self _ _ hd_all]; simp
    rw [hdrop, htake]
    simp only [List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte]
    simp [← hds, hval, Nat.mod_eq_of_lt hchk]

/-- `parseUstarNumeric` decodes `encodeOctalField val digits` when `val < 8 ^ digits` and `val < limit`. -/
theorem parseUstarNumeric_encodeOctalField {bytes : ByteArray} {start val digits limit offset : Nat}
    {allowAllEmpty : Bool} {fieldName : String}
    (hdig : 1 ≤ digits) (hval : val < 8 ^ digits) (hlim : val < limit)
    (hext : bytes.extract start (start + (digits + 1)) = encodeOctalField val digits) :
    parseUstarNumeric bytes start (start + (digits + 1)) offset allowAllEmpty limit fieldName = .ok val := by
  let _ := hdig
  unfold parseUstarNumeric; rw [hext]
  rcases encodeOctalField_loop_spec digits val [0] with ⟨ds, heq, hlen, hdigs, hfold⟩
  have hraw : (encodeOctalField val digits).data.toList = ds ++ [0] := by unfold encodeOctalField; rw [heq]
  dsimp only; rw [hraw]
  cases hds : ds with
  | nil => simp [hds] at hlen; omega
  | cons d0 ds' =>
    have hd0 : 0x30 ≤ d0 ∧ d0 ≤ 0x37 := hdigs d0 (by simp [hds])
    have hb0_hi : (d0 &&& 0x80) = 0 := uint8_and_0x80_eq_zero (by have : d0.toNat ≤ 55 := hd0.2; omega)
    have hne0 : (d0 == 0x00) = false := beq_false_of_ne (by intro h; subst h; simp at hd0)
    have hne32 : (d0 == 0x20) = false := beq_false_of_ne (by intro h; subst h; simp at hd0)
    have hd_all : ∀ b ∈ (d0 :: ds'), (0x30 ≤ b && b ≤ 0x37) = true := fun b hb => by
      have ⟨h1, h2⟩ := hdigs b (by simpa [hds] using hb); simp [h1, h2]
    have hdrop : (d0 :: (ds' ++ [0])).dropWhile (· == 0x20) = (d0 :: ds') ++ [0] := by simp [hne32]
    have htake : ((d0 :: ds') ++ [0]).takeWhile (fun b => 0x30 ≤ b && b ≤ 0x37) = d0 :: ds' := by
      rw [List.takeWhile_append, list_takeWhile_eq_self _ _ hd_all]; simp
    have hdrop2 : ((d0 :: ds') ++ [0]).drop (d0 :: ds').length = [0] := by simp
    rw [List.cons_append]; dsimp only
    simp only [hb0_hi, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, List.all_cons, hne0, hne32,
      Bool.or_self, Bool.false_and]
    rw [hdrop, htake]
    simp only [List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte, hdrop2, List.all_cons, List.all_nil, Bool.and_true]
    rw [← hds, hfold, Nat.mod_eq_of_lt hval]
    simp [Nat.not_le_of_lt hlim]

/-- `findNul` stops at `start + s.toUTF8.size` when `bytes.extract start (start + w) = padRightBytes w s.toUTF8`. -/
theorem extractCStringBytes_padRightBytes {bytes : ByteArray} {start w : Nat} {s : String}
    (hs : !hasNulString s = true) (hsz : s.toUTF8.size ≤ w) (hbd : start + w ≤ bytes.size)
    (hext : bytes.extract start (start + w) = padRightBytes w s.toUTF8) :
    extractCStringBytes bytes start (start + w) = s.toUTF8 := by
  have hbyte : ∀ k (hk : k < w), bytes[start + k]'(by omega) =
      if h : k < s.toUTF8.size then s.toUTF8[k]'h else 0 := by
    intro k hk
    have hk_e : k < (bytes.extract start (start + w)).size := by rw [hext, padRightBytes_size]; exact hk
    have hk_p : k < (padRightBytes w s.toUTF8).size := by rw [padRightBytes_size]; exact hk
    rw [← ByteArray.getElem_extract hk_e, byteArray_getElem_of_eq hext hk_e hk_p, padRightBytes_getElem w s.toUTF8 hk]
  unfold extractCStringBytes
  have hfind : ∀ i, i ≤ s.toUTF8.size →
      extractCStringBytes.findNul bytes (start + w) (w - i) (start + i) = start + s.toUTF8.size := by
    intro i hi
    induction hdiff : s.toUTF8.size - i generalizing i with
    | zero =>
      obtain rfl : i = s.toUTF8.size := by omega
      by_cases hfull : s.toUTF8.size = w
      · rw [show w - s.toUTF8.size = 0 by omega, extractCStringBytes.findNul.eq_1]; omega
      · have hlt : s.toUTF8.size < w := by omega
        have hlt_b : start + s.toUTF8.size < bytes.size := by omega
        rw [show w - s.toUTF8.size = (w - s.toUTF8.size - 1) + 1 by omega, extractCStringBytes.findNul.eq_2]
        simp only [hlt_b, ↓reduceDIte, hbyte s.toUTF8.size hlt, dite_eq_right (Nat.lt_irrefl _), beq_self_eq_true, ↓reduceIte]
    | succ d ih =>
      have hlt_s : i < s.toUTF8.size := by omega
      have hlt_w : i < w := by omega
      rw [show w - i = (w - (i + 1)) + 1 by omega, extractCStringBytes.findNul.eq_2]
      have hne0 : bytes[start + i]'(by omega) ≠ 0 := by
        rw [hbyte i hlt_w, dite_eq_left hlt_s]; exact toUTF8_getElem_ne_zero hs hlt_s
      simp only [show start + i < bytes.size by omega, ↓reduceDIte, beq_false_of_ne hne0, Bool.false_eq_true, ↓reduceIte]
      simpa [Nat.add_assoc] using ih (i + 1) (by omega) (by omega)
  have hpos := hfind 0 (Nat.zero_le _)
  simp only [Nat.add_zero, Nat.sub_zero] at hpos
  rw [show start + w - start = w by omega, hpos,
    show bytes.extract start (start + s.toUTF8.size) = (bytes.extract start (start + w)).extract 0 s.toUTF8.size by
      rw [ByteArray.extract_extract]; exact congrArg (bytes.extract start) (by omega),
    hext, padRightBytes_extract_prefix hsz]

/-- `decodeCStringUtf8` decodes a padded `!hasNulString` UTF-8 field back to `.ok s`. -/
theorem decodeCStringUtf8_padRightBytes {bytes : ByteArray} {start w offset : Nat}
    {s : String} {fieldName : String}
    (hs : !hasNulString s = true) (hsz : s.toUTF8.size ≤ w) (hbd : start + w ≤ bytes.size)
    (hext : bytes.extract start (start + w) = padRightBytes w s.toUTF8) :
    decodeCStringUtf8 bytes start (start + w) offset fieldName = .ok s := by
  unfold decodeCStringUtf8; dsimp only
  rw [extractCStringBytes_padRightBytes hs hsz hbd hext, fromUTF8?_toUTF8]

/-- Base-10 foldl shift helper. -/
theorem list_foldl_dec_shift (xs : List Nat) (x y : Nat) :
    xs.foldl (fun s d => s * 10 + d) (x + y) =
      x * 10 ^ xs.length + xs.foldl (fun s d => s * 10 + d) y := by
  induction xs generalizing x y with
  | nil => simp
  | cons z zs ih =>
    simp only [List.foldl_cons, List.length_cons, Nat.pow_succ]
    rw [show (x + y) * 10 + z = x * 10 + (y * 10 + z) by omega, ih (x * 10) (y * 10 + z),
      Nat.mul_assoc, Nat.mul_comm 10 (10 ^ zs.length)]

/-- Base-10 `Nat.toDigitsCore` produces exact decimal digits. -/
theorem toDigitsCore_10_spec (fuel n : Nat) (acc : List Nat)
    (hn : n < fuel) (hacc : ∀ d ∈ acc, d < 10) :
    ∃ ds : List Nat,
      (∀ d ∈ ds, d < 10) ∧
      ds.length ≥ 1 + acc.length ∧
      (n > 0 → ∃ hd tl, ds = hd :: tl ++ acc ∧ 0 < hd ∧
        10 ^ (ds.length - 1 - acc.length) ≤ n ∧ n < 10 ^ (ds.length - acc.length)) ∧
      Nat.toDigitsCore 10 fuel n (acc.map Nat.digitChar) = ds.map Nat.digitChar ∧
      ds.foldl (fun a d => a * 10 + d) 0 =
        n * 10 ^ acc.length + acc.foldl (fun a d => a * 10 + d) 0 := by
  induction fuel generalizing n acc with
  | zero => omega
  | succ f ih =>
    rw [Nat.toDigitsCore.eq_2]
    split
    · have hn10 : n < 10 := by omega
      refine ⟨n :: acc, ?_, by simp; omega, ?_, by simp [Nat.mod_eq_of_lt hn10],
        by simpa using list_foldl_dec_shift acc n 0⟩
      · intro d hd; rcases List.mem_cons.mp hd with rfl | hd
        · exact hn10
        · exact hacc d hd
      · intro hpos; exact ⟨n, [], rfl, hpos, by simp; omega, by simp [hn10]⟩
    · have hacc' : ∀ d ∈ (n % 10 :: acc), d < 10 := fun d hd => by
        rcases List.mem_cons.mp hd with rfl | hd
        · exact Nat.mod_lt _ (by omega)
        · exact hacc d hd
      rcases ih (n / 10) (n % 10 :: acc) (by omega) hacc' with ⟨ds, hdigs, hlen, hbounds, hmap, hfold⟩
      rcases hbounds (by omega) with ⟨hd, tl, hds_eq, hhd_pos, hlo, hhi⟩
      have hlen_ds : ds.length = tl.length + acc.length + 2 := by simp [hds_eq, List.length_append]; omega
      refine ⟨ds, hdigs, by simp at hlen; omega, ?_, by simpa [List.map_cons] using hmap, ?_⟩
      · intro _
        refine ⟨hd, tl ++ [n % 10], by simp [hds_eq, List.append_assoc], hhd_pos, ?_, ?_⟩
        · rw [show ds.length - 1 - acc.length = (ds.length - 1 - (n % 10 :: acc).length) + 1 by rw [hlen_ds]; simp; omega, Nat.pow_succ]; omega
        · rw [show ds.length - acc.length = (ds.length - (n % 10 :: acc).length) + 1 by rw [hlen_ds]; simp; omega, Nat.pow_succ]; omega
      · rw [hfold]; simp only [List.length_cons, List.foldl_cons, Nat.zero_mul, Nat.zero_add]
        have hsh := list_foldl_dec_shift acc (n % 10) 0; rw [Nat.add_zero] at hsh; rw [hsh]
        have heq_sum : n / 10 * 10 ^ (acc.length + 1) + n % 10 * 10 ^ acc.length = n * 10 ^ acc.length := by
          rw [Nat.pow_succ, ← Nat.mul_assoc, Nat.mul_right_comm (n / 10) (10 ^ acc.length) 10,
            ← Nat.add_mul, Nat.mul_comm (n / 10) 10, Nat.div_add_mod]
        omega

/-- `decDigitsLen n` equals the number of decimal digits of `n` (at least 1). -/
theorem decDigitsLen_eq_digits_length (n : Nat) :
    ∃ ds : List Nat, (∀ d ∈ ds, d < 10) ∧
      (n > 0 → ∃ hd tl, ds = hd :: tl ∧ 0 < hd ∧ 10 ^ (ds.length - 1) ≤ n ∧ n < 10 ^ ds.length) ∧
      (toString n).toList = ds.map Nat.digitChar ∧ ds.foldl (fun a d => a * 10 + d) 0 = n ∧
      decDigitsLen n = ds.length ∧ 1 ≤ decDigitsLen n := by
  rcases toDigitsCore_10_spec (n + 1) n [] (Nat.lt_succ_self n) (fun _ h => nomatch h) with
    ⟨ds, hdigs, hlen, hbounds, hmap, hfold⟩
  have hstr : (toString n).toList = ds.map Nat.digitChar := by
    change (Nat.repr n).toList = ds.map Nat.digitChar; rw [Nat.repr, Nat.toDigits, String.toList_ofList]; simpa using hmap
  have hflat : ∀ l : List Nat, (∀ d ∈ l, d < 10) →
      ((l.map Nat.digitChar).flatMap String.utf8EncodeChar).length = l.length := by
    intro l hl; induction l with
    | nil => rfl
    | cons d ds ih =>
      have hlen1 : (String.utf8EncodeChar (Nat.digitChar d)).length = 1 := by
        have := hl d (by simp); match d with | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 => rfl | _ + 10 => omega
      simp only [List.map_cons, List.flatMap_cons, List.length_append, List.length_cons,
        hlen1, ih (fun x hx => hl x (by simp [hx])), Nat.add_comm 1 _]
  have hdec : decDigitsLen n = ds.length := by
    unfold decDigitsLen; rw [toUTF8_eq_toByteArray, List.size_toByteArray, hstr, hflat ds hdigs]
  refine ⟨ds, hdigs, fun hpos => ?_, hstr, by simpa using hfold, hdec, by simpa [hdec] using hlen⟩
  rcases hbounds hpos with ⟨hd, tl, heq, hhd, hlo, hhi⟩
  exact ⟨hd, tl, by simpa using heq, hhd, by simpa using hlo, by simpa using hhi⟩

/-- `decDigitsLen` is bounded above by `7` for `n < 10 ^ 7`. -/
theorem decDigitsLen_le_7 {n : Nat} (hn : n < 10 ^ 7) : decDigitsLen n ≤ 7 := by
  rcases decDigitsLen_eq_digits_length n with ⟨ds, _, hbounds, _, _, hdec, _⟩
  rw [hdec]
  by_cases hn0 : n = 0
  · subst hn0; have : decDigitsLen 0 = 1 := rfl; omega
  · rcases hbounds (Nat.pos_of_ne_zero hn0) with ⟨_, _, _, _, hlo, _⟩
    rcases Nat.lt_or_ge ds.length 8 with hlt | hge8
    · omega
    · have := Nat.pow_le_pow_right (n := 10) (by omega) (show 7 ≤ ds.length - 1 by omega); omega

/-- `decDigitsLen` is monotone. -/
theorem decDigitsLen_mono {m n : Nat} (hmn : m ≤ n) : decDigitsLen m ≤ decDigitsLen n := by
  rcases decDigitsLen_eq_digits_length m with ⟨ds1, _, hb1, _, _, hdec1, _⟩
  rcases decDigitsLen_eq_digits_length n with ⟨ds2, _, hb2, _, _, hdec2, _⟩
  rw [hdec1, hdec2]
  by_cases hm0 : m = 0
  · subst hm0; have : decDigitsLen 0 = 1 := rfl; omega
  · rcases hb1 (Nat.pos_of_ne_zero hm0) with ⟨_, _, _, _, _, _⟩
    rcases hb2 (by omega) with ⟨_, _, _, _, _, _⟩
    rcases Nat.lt_or_ge ds2.length ds1.length with hlt | hle
    · have := Nat.pow_le_pow_right (n := 10) (by omega) (show ds2.length ≤ ds1.length - 1 by omega); omega
    · exact hle

/-- Fixed point lemma for `paxRecordTotalLen` when `4 ≤ kvBodyLen ≤ maxPaxHeaderBytes`. -/
theorem paxRecordTotalLen_fixed_point {kvBodyLen : Nat}
    (hmin : 4 ≤ kvBodyLen) (hmax : kvBodyLen ≤ maxPaxHeaderBytes) :
    paxRecordTotalLen kvBodyLen = decDigitsLen (paxRecordTotalLen kvBodyLen) + kvBodyLen ∧
      paxRecordTotalLen kvBodyLen ≥ 5 := by
  have hmax_num : maxPaxHeaderBytes = 1048576 := rfl
  have hgo : ∀ fuel d : Nat, 1 ≤ d → d ≤ 7 → d ≤ decDigitsLen (d + kvBodyLen) → 8 - d ≤ fuel →
      paxRecordTotalLen.go kvBodyLen d fuel = decDigitsLen (paxRecordTotalLen.go kvBodyLen d fuel) + kvBodyLen ∧
      paxRecordTotalLen.go kvBodyLen d fuel ≥ 5 := by
    intro fuel; induction fuel with
    | zero => intro d _ hd7 _ hle; omega
    | succ f ih =>
      intro d hd1 hd7 hle hf; rw [paxRecordTotalLen.go.eq_2]
      by_cases heq : (decDigitsLen (d + kvBodyLen) == d) = true
      · rw [ite_eq_left heq, beq_iff_eq.mp heq]; exact ⟨rfl, by omega⟩
      · rw [ite_eq_right heq]
        have hne : decDigitsLen (d + kvBodyLen) ≠ d := fun h => heq (beq_iff_eq.mpr h)
        exact ih (decDigitsLen (d + kvBodyLen)) (by omega) (decDigitsLen_le_7 (by omega))
          (decDigitsLen_mono (by omega)) (by omega)
  rcases decDigitsLen_eq_digits_length (1 + kvBodyLen) with ⟨_, _, _, _, _, _, h1⟩
  exact hgo 20 1 (Nat.le_refl 1) (by omega) h1 (by omega)

/-- UTF-8 encoding of a single digit `d < 10` is `[UInt8.ofNat (0x30 + d)]`. -/
theorem digitChar_utf8EncodeChar_eq {d : Nat} (hd : d < 10) :
    String.utf8EncodeChar (Nat.digitChar d) = [UInt8.ofNat (0x30 + d)] := by
  match d with
  | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 => rfl
  | _ + 10 => omega

/-- Properties of `Nat.digitChar d` for `d < 10`. -/
theorem digitChar_props {d : Nat} (hd : d < 10) :
    ('0' ≤ Nat.digitChar d ∧ Nat.digitChar d ≤ '9') ∧
    (Nat.digitChar d).toNat - '0'.toNat = d ∧
    Nat.digitChar d ≠ '-' := by
  match d with
  | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 => decide
  | _ + 10 => omega

/-- UTF-8 byte list of `toString n` equals `ds.map (fun d => UInt8.ofNat (0x30 + d))`. -/
theorem toString_toUTF8_bytes_eq {n : Nat} :
    ∃ ds : List Nat,
      (∀ d ∈ ds, d < 10) ∧
      ds ≠ [] ∧
      (n > 0 → ∃ hd tl, ds = hd :: tl ∧ 0 < hd) ∧
      (toString n).toList = ds.map Nat.digitChar ∧
      ds.foldl (fun a d => a * 10 + d) 0 = n ∧
      (toString n).toUTF8 = (ds.map (fun d => UInt8.ofNat (0x30 + d))).toByteArray ∧
      (toString n).toUTF8.size = ds.length := by
  rcases decDigitsLen_eq_digits_length n with ⟨ds, hdigs, hbounds, hstr, hfold, hdec, hpos⟩
  have hne : ds ≠ [] := by intro h; subst h; simp at hdec; omega
  have hbytes : (ds.map Nat.digitChar).flatMap String.utf8EncodeChar = ds.map (fun d => UInt8.ofNat (0x30 + d)) := by
    clear hbounds hstr hfold hdec hpos hne
    induction ds with
    | nil => rfl
    | cons d ds ih =>
      simp only [List.map_cons, List.flatMap_cons, List.singleton_append, digitChar_utf8EncodeChar_eq (hdigs d (by simp))]
      rw [ih (fun x hx => hdigs x (by simp [hx]))]
  refine ⟨ds, hdigs, hne, fun hn0 => ?_, hstr, hfold, by rw [toUTF8_eq_toByteArray, hstr, hbytes], by rw [← hdec]; rfl⟩
  rcases hbounds hn0 with ⟨hd, tl, heq, hhd, _⟩; exact ⟨hd, tl, heq, hhd⟩

/-- Helper: folding `(ds.map Nat.digitChar)` agrees with folding `ds`. -/
theorem foldl_digitChar_eq (ds : List Nat) (hdigs : ∀ d ∈ ds, d < 10) (init : Nat) :
    (ds.map Nat.digitChar).foldl (fun acc c => acc * 10 + (c.toNat - '0'.toNat)) init =
      ds.foldl (fun a d => a * 10 + d) init := by
  induction ds generalizing init with
  | nil => rfl
  | cons d ds ih =>
    simp only [List.map_cons, List.foldl_cons, (digitChar_props (hdigs d (by simp))).2.1]
    exact ih (fun x hx => hdigs x (by simp [hx])) _

private theorem toString_dec_props (n : Nat) :
    ((toString n).toList.isEmpty = false) ∧ (((toString n).toList.head? == some '-') = false) ∧
    (∀ c ∈ (toString n).toList, ('0' ≤ c && c ≤ '9') = true) ∧
    (toString n).toList.foldl (fun acc c => acc * 10 + (c.toNat - '0'.toNat)) 0 = n := by
  rcases toString_toUTF8_bytes_eq (n := n) with ⟨ds, hdigs, hne, _, hstr, hfold, _, _⟩
  rw [hstr]; refine ⟨?_, ?_, ?_, by rw [foldl_digitChar_eq ds hdigs 0, hfold]⟩
  · cases ds with | nil => exact absurd rfl hne | cons _ _ => rfl
  · cases ds with | nil => exact absurd rfl hne | cons d _ => simp [beq_false_of_ne (digitChar_props (hdigs d (by simp))).2.2]
  · rintro c hm; rcases List.mem_map.mp hm with ⟨d, hd, rfl⟩
    have ⟨h1, h2⟩ := (digitChar_props (hdigs d hd)).1; simp [h1, h2]

/-- `parsePaxNat (toString n) offset key` returns `.ok n` when `n < u64Limit`. -/
theorem parsePaxNat_toString {n offset : Nat} {key : String} (hn : n < u64Limit) :
    parsePaxNat (toString n) offset key = .ok n := by
  have ⟨hne_e, hdash, hall, hfc⟩ := toString_dec_props n
  unfold parsePaxNat
  simp only [hne_e, hdash, List.all_eq_true.mpr hall, Bool.false_eq_true, Bool.not_true, ↓reduceIte, hfc, Nat.not_le_of_lt hn]

/-- `parsePaxMtime (toString n) offset` returns `.ok n` when `n < u64Limit`. -/
theorem parsePaxMtime_toString {n offset : Nat} (hn : n < u64Limit) :
    parsePaxMtime (toString n) offset = .ok n := by
  have ⟨hne_e, hdash, hall, hfc⟩ := toString_dec_props n
  have htake := list_takeWhile_eq_self (fun c => '0' ≤ c && c ≤ '9') _ hall
  unfold parsePaxMtime
  simp only [hne_e, hdash, htake, Bool.false_eq_true, ↓reduceIte, List.drop_length, hfc, Nat.not_le_of_lt hn]; rfl

/-- `findByteIn bs target idx stop` returns `some pos` when bytes `[idx..pos)` avoid `target` and `bs[pos] = target`. -/
theorem findByteIn_eq {bs : ByteArray} {target : UInt8} {idx pos stop : Nat}
    (hle : idx ≤ pos) (hlt : pos < stop) (hbd : stop ≤ bs.size)
    (havoid : ∀ j, idx ≤ j → j < pos → ∀ hj : j < bs.size, bs[j]'hj ≠ target)
    (hhit : bs[pos]'(by omega) = target) :
    findByteIn bs target idx stop = some pos := by
  unfold findByteIn
  have hgo : ∀ d i, pos - i = d → i ≤ pos →
      (∀ j, i ≤ j → j < pos → ∀ hj : j < bs.size, bs[j]'hj ≠ target) →
      findByteIn.go bs target (stop - i) i = some pos := by
    intro d; induction d with
    | zero =>
      intro i hdiff hle_i _; obtain rfl : i = pos := by omega
      rw [show stop - i = (stop - (i + 1)) + 1 by omega, findByteIn.go.eq_2]
      simp [show i < bs.size by omega, hhit]
    | succ d ih =>
      intro i hdiff hle_i havoid_i
      have hlt_b : i < bs.size := by omega
      rw [show stop - i = (stop - (i + 1)) + 1 by omega, findByteIn.go.eq_2]
      simp only [hlt_b, ↓reduceDIte, beq_false_of_ne (havoid_i i (Nat.le_refl _) (by omega) hlt_b), Bool.false_eq_true, ↓reduceIte]
      exact ih (i + 1) (by omega) (by omega) (fun j hj1 hj2 hj => havoid_i j (by omega) hj2 hj)
  exact hgo (pos - idx) idx rfl hle havoid

/-- `parsePaxLen` decodes `(toString n).toUTF8` stored at `[pos .. pos + (toString n).toUTF8.size)` when `n > 0`. -/
theorem parsePaxLen_toString {bs : ByteArray} {pos n : Nat} (hn : 0 < n)
    (_hbd : pos + (toString n).toUTF8.size ≤ bs.size)
    (hext : bs.extract pos (pos + (toString n).toUTF8.size) = (toString n).toUTF8) :
    parsePaxLen bs pos (pos + (toString n).toUTF8.size) = some n := by
  rcases toString_toUTF8_bytes_eq (n := n) with ⟨ds, hdigs, hne, hpos, _, hfold, hbytes, hsz⟩
  have hsz_pos : 0 < (toString n).toUTF8.size := by
    rw [hsz]; cases ds with | nil => exact absurd rfl hne | cons _ _ => simp
  unfold parsePaxLen
  simp only [show ¬(pos ≥ pos + (toString n).toUTF8.size) by omega, ↓reduceIte]
  have hlist : (bs.extract pos (pos + (toString n).toUTF8.size)).data.toList = ds.map (fun d => UInt8.ofNat (0x30 + d)) := by
    rw [hext, hbytes]; simp
  rw [hlist]
  rcases hpos hn with ⟨hd, tl, rfl, hhd_pos⟩
  have hhd_lt := hdigs hd (by simp)
  have hbeq : (UInt8.ofNat (0x30 + hd) == 0x30) = false := beq_false_of_ne fun h => by
    have hn := congrArg UInt8.toNat h; rw [UInt8.toNat_ofNat', Nat.mod_eq_of_lt (by omega)] at hn
    change 48 + hd = 48 at hn; omega
  have hall : ((hd :: tl).map (fun d => UInt8.ofNat (0x30 + d))).all (fun b => 0x30 ≤ b && b ≤ 0x39) = true := by
    rw [List.all_eq_true]; rintro b hm; rcases List.mem_map.mp hm with ⟨d, hd_m, rfl⟩
    have hd_l := hdigs d hd_m
    have hlo : (0x30 : UInt8) ≤ UInt8.ofNat (0x30 + d) := by
      change 48 ≤ (UInt8.ofNat (48 + d)).toNat; rw [UInt8.toNat_ofNat', Nat.mod_eq_of_lt (by omega)]; omega
    have hhi : UInt8.ofNat (0x30 + d) ≤ 0x39 := by
      change (UInt8.ofNat (48 + d)).toNat ≤ 57; rw [UInt8.toNat_ofNat', Nat.mod_eq_of_lt (by omega)]; omega
    simp only [hlo, hhi, decide_true, Bool.and_self]
  have hgen : ∀ (l : List Nat) (_ : ∀ d ∈ l, d < 10) (init : Nat),
      (l.map (fun d => UInt8.ofNat (0x30 + d))).foldl (fun acc b => acc * 10 + (b.toNat - 0x30)) init =
        l.foldl (fun a d => a * 10 + d) init := by
    intro l; induction l with
    | nil => intros; rfl
    | cons d ds ih =>
      intro hl init; have hd_l := hl d (by simp)
      have hsub : (UInt8.ofNat (0x30 + d)).toNat - 0x30 = d := by
        rw [UInt8.toNat_ofNat', Nat.mod_eq_of_lt (by omega)]; omega
      simp only [List.map_cons, List.foldl_cons, hsub]
      exact ih (fun x hx => hl x (by simp [hx])) _
  have hfb : ((hd :: tl).map (fun d => UInt8.ofNat (0x30 + d))).foldl (fun acc b => acc * 10 + (b.toNat - 0x30)) 0 = n := by
    rw [hgen (hd :: tl) hdigs 0, hfold]
  rw [List.map_cons] at hall hfb
  simp only [List.map_cons, hbeq, Bool.false_eq_true, ↓reduceIte, hall, Bool.not_true, hfb]

/-- Decompose `encodePaxRecord key value` into an opaque total length and its UTF-8 bytes. -/
theorem encodePaxRecord_parts {key value : String}
    (hkvMin : 4 ≤ (" " ++ key ++ "=" ++ value ++ "\n").toUTF8.size)
    (hkvMax : (" " ++ key ++ "=" ++ value ++ "\n").toUTF8.size ≤ maxPaxHeaderBytes) :
    ∃ recLen : Nat,
      recLen = (toString recLen).toUTF8.size + 1 + key.toUTF8.size + 1 + value.toUTF8.size + 1 ∧
      recLen ≥ 5 ∧
      encodePaxRecord key value = (toString recLen ++ (" " ++ key ++ "=" ++ value ++ "\n")).toUTF8 ∧
      (encodePaxRecord key value).size = recLen := by
  have ⟨hfix, hge5⟩ := paxRecordTotalLen_fixed_point hkvMin hkvMax
  refine ⟨paxRecordTotalLen (" " ++ key ++ "=" ++ value ++ "\n").toUTF8.size, ?_, hge5, rfl, ?_⟩
  · have hsuf_sz : (" " ++ key ++ "=" ++ value ++ "\n").toUTF8.size = 1 + key.toUTF8.size + 1 + value.toUTF8.size + 1 := by
      simp only [toUTF8_size_append, show " ".toUTF8.size = 1 from rfl,
        show "=".toUTF8.size = 1 from rfl, show "\n".toUTF8.size = 1 from rfl, Nat.add_assoc]
    change _ = decDigitsLen _ + 1 + _ + 1 + _ + 1; omega
  · rw [encodePaxRecord, toUTF8_size_append]; exact hfix.symm

/-- Execute one `parsePaxPayload.go` step on a prefixed `encodePaxRecord key value`. -/
theorem parsePaxPayload_go_step {bs rest : ByteArray} {offset fuel pos : Nat}
    {seenKeys : List String} {ov nextOv : PaxOverrides} {key value : String}
    (hfuel : bs.size - pos < fuel)
    (hkvMin : 4 ≤ (" " ++ key ++ "=" ++ value ++ "\n").toUTF8.size)
    (hkvMax : (" " ++ key ++ "=" ++ value ++ "\n").toUTF8.size ≤ maxPaxHeaderBytes)
    (hkey_ne : !key.isEmpty = true) (hkey_nul : !hasNulString key = true)
    (hkey_nl : !key.toList.contains '\n' = true)
    (hkey_eq : (0x3d : UInt8) ∉ key.toUTF8.toList)
    (hnot_seen : !seenKeys.contains key = true)
    (hnot_sparse : !startsWithStr key "GNU.sparse." = true)
    (happly : applyPaxKey ov key value offset = .ok nextOv)
    (hsuf : bs.extract pos bs.size = encodePaxRecord key value ++ rest) :
    parsePaxPayload.go bs offset fuel pos seenKeys ov =
      parsePaxPayload.go bs offset (fuel - 1) (pos + (encodePaxRecord key value).size) (key :: seenKeys) nextOv := by
  rcases encodePaxRecord_parts hkvMin hkvMax with ⟨recLen, hrecLen_eq, hge5, hrec_eq, hrec_sz⟩
  have hpos_le : pos ≤ bs.size := by
    rcases Nat.lt_or_ge bs.size pos with hlt | hle
    · have h0 : (bs.extract pos bs.size).size = 0 := by rw [ByteArray.size_extract]; omega
      rw [hsuf, ByteArray.size_append, hrec_sz] at h0; omega
    · exact hle
  have hbd_rec : pos + recLen ≤ bs.size := by
    have h1 := congrArg ByteArray.size hsuf
    rw [ByteArray.size_extract, ByteArray.size_append, hrec_sz] at h1; omega
  let d := (toString recLen).toUTF8.size
  have hsp1 : " ".toUTF8.size = 1 := rfl; have heq1 : "=".toUTF8.size = 1 := rfl; have hnl1 : "\n".toUTF8.size = 1 := rfl
  have hsuf_eq : bs.extract pos (pos + (bs.size - pos)) =
      (toString recLen).toUTF8 ++ (" ".toUTF8 ++ (key.toUTF8 ++ ("=".toUTF8 ++ (value.toUTF8 ++ ("\n".toUTF8 ++ rest))))) := by
    rw [show pos + (bs.size - pos) = bs.size by omega, hsuf, hrec_eq]; simp only [toUTF8_append, ByteArray.append_assoc]
  have hext_len : bs.extract pos (pos + d) = (toString recLen).toUTF8 := by
    simpa using byteArray_extract_sub (L := ByteArray.empty) (M := (toString recLen).toUTF8) (a := 0) (w := d) (by rw [ByteArray.empty_append]; exact hsuf_eq) rfl rfl (by omega)
  have hext_sp : bs.extract (pos + d) (pos + d + 1) = " ".toUTF8 := byteArray_extract_sub (a := d) (w := 1) hsuf_eq rfl hsp1 (by omega)
  have hext_key : bs.extract (pos + d + 1) (pos + d + 1 + key.toUTF8.size) = key.toUTF8 := by
    simpa [Nat.add_assoc] using byteArray_extract_sub (L := (toString recLen).toUTF8 ++ " ".toUTF8) (M := key.toUTF8)
      (a := d + 1) (w := key.toUTF8.size) (by rw [hsuf_eq]; simp only [ByteArray.append_assoc]; rfl) (by rw [ByteArray.size_append, hsp1]) rfl (by omega)
  have hext_eq : bs.extract (pos + d + 1 + key.toUTF8.size) (pos + d + 1 + key.toUTF8.size + 1) = "=".toUTF8 := by
    simpa [Nat.add_assoc] using byteArray_extract_sub (L := (toString recLen).toUTF8 ++ " ".toUTF8 ++ key.toUTF8) (M := "=".toUTF8)
      (a := d + 1 + key.toUTF8.size) (w := 1) (by rw [hsuf_eq]; simp only [ByteArray.append_assoc]; rfl) (by simp only [ByteArray.size_append, hsp1]; rfl) heq1 (by omega)
  have hext_val : bs.extract (pos + d + 1 + key.toUTF8.size + 1) (pos + recLen - 1) = value.toUTF8 := by
    have h1 := byteArray_extract_sub (L := (toString recLen).toUTF8 ++ " ".toUTF8 ++ key.toUTF8 ++ "=".toUTF8)
      (M := value.toUTF8) (a := d + 1 + key.toUTF8.size + 1) (w := value.toUTF8.size)
      (by rw [hsuf_eq]; simp only [ByteArray.append_assoc]; rfl) (by simp only [ByteArray.size_append, hsp1, heq1]; rfl) rfl (by omega)
    rw [show pos + (d + 1 + key.toUTF8.size + 1) = pos + d + 1 + key.toUTF8.size + 1 by omega,
      show pos + d + 1 + key.toUTF8.size + 1 + value.toUTF8.size = pos + recLen - 1 by omega] at h1; exact h1
  have hext_nl : bs.extract (pos + recLen - 1) (pos + recLen) = "\n".toUTF8 := by
    have h1 := byteArray_extract_sub (L := (toString recLen).toUTF8 ++ " ".toUTF8 ++ key.toUTF8 ++ "=".toUTF8 ++ value.toUTF8)
      (M := "\n".toUTF8) (a := d + 1 + key.toUTF8.size + 1 + value.toUTF8.size) (w := 1)
      (by rw [hsuf_eq]; simp only [ByteArray.append_assoc]; rfl) (by simp only [ByteArray.size_append, hsp1, heq1]; rfl) hnl1 (by omega)
    rw [show pos + (d + 1 + key.toUTF8.size + 1 + value.toUTF8.size) = pos + recLen - 1 by omega,
      show pos + recLen - 1 + 1 = pos + recLen by omega] at h1; exact h1
  have hget_slice : ∀ {off len k : Nat} {sl : ByteArray} (he : bs.extract off (off + len) = sl)
      (hk : k < sl.size) (hj : off + k < bs.size), bs[off + k]'hj = sl[k]'hk := by
    intro off len k sl he hk hj
    have hk_e : k < (bs.extract off (off + len)).size := by rw [he]; exact hk
    rw [← ByteArray.getElem_extract hk_e, byteArray_getElem_of_eq he hk_e hk]
  rcases toString_toUTF8_bytes_eq (n := recLen) with ⟨ds, hdigs, _, _, _, _, hbytes_rec, _⟩
  have havoid_sp : ∀ j, pos ≤ j → j < pos + d → ∀ hj : j < bs.size, bs[j]'hj ≠ 0x20 := by
    intro j hj1 hj2 hj
    have hk_lt : j - pos < d := by omega
    have hbsj : bs[j]'hj = (toString recLen).toUTF8[j - pos]'hk_lt := by
      simpa [show pos + (j - pos) = j by omega] using hget_slice hext_len hk_lt (by omega)
    have hk_ba : j - pos < (ds.map (fun d => UInt8.ofNat (0x30 + d))).toByteArray.size := by rw [← hbytes_rec]; exact hk_lt
    rw [hbsj, byteArray_getElem_of_eq hbytes_rec hk_lt hk_ba, List.getElem_toByteArray]
    rcases List.mem_map.mp (List.getElem_mem (by rw [← List.size_toByteArray]; exact hk_ba)) with ⟨dig, hdm, hde⟩
    have := hdigs dig hdm
    intro heq20
    have hn := congrArg UInt8.toNat (hde.trans heq20)
    rw [UInt8.toNat_ofNat', Nat.mod_eq_of_lt (by omega)] at hn; change 48 + dig = 32 at hn; omega
  have hget_1 : ∀ {off : Nat} {c : UInt8} (hoff : off < bs.size),
      bs.extract off (off + 1) = ByteArray.mk #[c] → bs[off]'hoff = c := fun {off c} hoff he => by
    have h0 := hget_slice (sl := ByteArray.mk #[c]) (k := 0) he (by simp [ByteArray.size]) hoff
    simpa [Nat.add_zero, ByteArray.getElem_eq_getElem_data] using h0
  have hsp_idx : bs[pos + d]'(by omega) = 0x20 := hget_1 (by omega) hext_sp
  have hfind_sp : findByteIn bs 0x20 pos bs.size = some (pos + d) :=
    findByteIn_eq (by omega) (by omega) (Nat.le_refl _) havoid_sp hsp_idx
  have hparse_len : parsePaxLen bs pos (pos + d) = some recLen :=
    parsePaxLen_toString (by omega) (by omega) hext_len
  have hnl_idx : bs[pos + recLen - 1]'(by omega) = 0x0a :=
    hget_1 (by omega) (by rw [show pos + recLen - 1 + 1 = pos + recLen by omega]; exact hext_nl)
  let eqPos := pos + d + 1 + key.toUTF8.size
  have havoid_eq : ∀ j, pos + d + 1 ≤ j → j < eqPos → ∀ hj : j < bs.size, bs[j]'hj ≠ 0x3d := by
    intro j hj1 hj2 hj
    have hk_k : j - (pos + d + 1) < key.toUTF8.size := by omega
    have hbsj : bs[j]'hj = key.toUTF8[j - (pos + d + 1)]'hk_k := by
      simpa [show pos + d + 1 + (j - (pos + d + 1)) = j by omega] using hget_slice hext_key hk_k (by omega)
    rw [hbsj]; intro heq3d; apply hkey_eq
    have hi_ba : j - (pos + d + 1) < (key.toList.flatMap String.utf8EncodeChar).toByteArray.size := by
      rw [← toUTF8_eq_toByteArray]; exact hk_k
    rw [toUTF8_toList, ← heq3d, byteArray_getElem_of_eq (toUTF8_eq_toByteArray key) hk_k hi_ba, List.getElem_toByteArray]
    exact List.getElem_mem _
  have heq_idx : bs[eqPos]'(by omega) = 0x3d := hget_1 (by omega) hext_eq
  have hfind_eq : findByteIn bs 0x3d (pos + d + 1) (pos + recLen - 1) = some eqPos :=
    findByteIn_eq (by omega) (by omega) (by omega) havoid_eq heq_idx
  have hk_inv : (key.isEmpty || hasNulString key || key.toList.contains '\n') = false := by
    rw [show key.isEmpty = false by simpa using hkey_ne, show hasNulString key = false by simpa using hkey_nul,
      show key.toList.contains '\n' = false by simpa using hkey_nl]; rfl
  have hseen_f : seenKeys.contains key = false := by simpa using hnot_seen
  have hsp_f : startsWithStr key "GNU.sparse." = false := by simpa using hnot_sparse
  conv => lhs; rw [show fuel = (fuel - 1) + 1 by omega, parsePaxPayload.go.eq_2]
  simp only [show ¬(pos ≥ bs.size) by omega, ↓reduceIte, hfind_sp, hparse_len,
    show ¬(recLen < 5) by omega, show ¬(pos + recLen > bs.size) by omega,
    show pos + recLen - 1 < bs.size by omega, ↓reduceDIte, hnl_idx, beq_self_eq_true,
    Bool.not_true, Bool.false_eq_true, hfind_eq, eqPos, hext_key, hext_val, fromUTF8?_toUTF8,
    hk_inv, hseen_f, hsp_f, happly, hrec_sz]

end LeanSwe.Tar.Proofs
