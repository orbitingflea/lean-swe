import LeanSwe.Tar.Proofs.ByteModel

namespace LeanSwe.Tar.Proofs

open LeanSwe.Tar
open LeanSwe.Tar.Model
open LeanSwe.Tar.Impl

/-- Loop invariant for `ByteArray.toList.loop`. -/
theorem byteArray_toList_loop (bs : ByteArray) (i : Nat) (r : List UInt8) :
    ByteArray.toList.loop bs i r = r.reverse ++ bs.data.toList.drop i := by
  fun_induction ByteArray.toList.loop with
  | case1 i r hi ih =>
    rw [ih]
    have hi_data : i < bs.data.size := by rw [← ByteArray.size]; exact hi
    have hget : bs.get! i = bs.data[i]'hi_data := by
      change bs.data[i]! = bs.data[i]'hi_data
      exact getElem!_pos bs.data i hi_data
    rw [hget]
    have hi_list : i < bs.data.toList.length := by rw [Array.length_toList]; exact hi_data
    have hdrop := List.drop_eq_getElem_cons hi_list
    have helem : bs.data.toList[i]'hi_list = bs.data[i]'hi_data := Array.getElem_toList hi_list
    rw [helem] at hdrop
    rw [hdrop, List.reverse_cons, List.append_assoc, List.singleton_append]
  | case2 i r hi =>
    have hge : bs.data.toList.length ≤ i := by
      rw [Array.length_toList, ← ByteArray.size]
      exact Nat.le_of_not_lt hi
    rw [List.drop_eq_nil_of_le hge, List.append_nil]

/-- `bs.toList` equals `bs.data.toList`. -/
theorem byteArray_toList_eq (bs : ByteArray) : bs.toList = bs.data.toList := by
  simpa [ByteArray.toList] using byteArray_toList_loop bs 0 []

/-- `(l.toByteArray).toList` equals `l`. -/
theorem toByteArray_toList (l : List UInt8) : l.toByteArray.toList = l := by
  rw [byteArray_toList_eq]
  apply List.ext_getElem
  · rw [Array.length_toList, ← ByteArray.size, List.size_toByteArray]
  · intro i hi1 _
    have hi : i < l.toByteArray.size := by rw [ByteArray.size]; exact hi1
    rw [Array.getElem_toList, ← ByteArray.getElem_eq_getElem_data (h := hi), List.getElem_toByteArray]

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
  have hne : c.toNat ≠ 0 := by
    intro h0
    apply hc
    rw [Char.ext_iff, ← UInt32.toNat_inj]
    exact h0
  unfold String.utf8EncodeChar
  dsimp only
  split
  · simp only [List.mem_singleton]
    intro heq
    have hnat : (UInt8.ofNat c.val.toNat).toNat = (0 : UInt8).toNat := congrArg UInt8.toNat heq.symm
    have hlt : c.val.toNat ≤ 127 := ‹_›
    rw [UInt8.toNat_ofNat', Nat.mod_eq_of_lt (by omega)] at hnat
    change c.val.toNat = 0 at hnat
    have hcnat : c.toNat = c.val.toNat := rfl
    omega
  · split
    · simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro (h | h) <;>
        (have hn := congrArg UInt8.toNat h; rw [UInt8.toNat_ofNat'] at hn; change (0 : Nat) = _ at hn; omega)
    · split
      · simp only [List.mem_cons, List.not_mem_nil, or_false]
        rintro (h | h | h) <;>
          (have hn := congrArg UInt8.toNat h; rw [UInt8.toNat_ofNat'] at hn; change (0 : Nat) = _ at hn; omega)
      · simp only [List.mem_cons, List.not_mem_nil, or_false]
        rintro (h | h | h | h) <;>
          (have hn := congrArg UInt8.toNat h; rw [UInt8.toNat_ofNat'] at hn; change (0 : Nat) = _ at hn; omega)

/-- `hasNulChars cs = false` iff `Char.ofNat 0 ∉ cs`. -/
theorem hasNulChars_false_iff (cs : List Char) :
    hasNulChars cs = false ↔ Char.ofNat 0 ∉ cs := by
  induction cs with
  | nil => simp [hasNulChars]
  | cons c rest ih =>
    simp only [hasNulChars, Bool.or_eq_false_iff, beq_eq_false_iff_ne, ne_eq,
      List.mem_cons, not_or]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨fun heq => h1 heq.symm, ih.mp h2⟩
    · rintro ⟨h1, h2⟩
      exact ⟨fun heq => h1 heq.symm, ih.mpr h2⟩

/-- If `!hasNulString s = true`, then `(0 : UInt8) ∉ s.toUTF8.toList`. -/
theorem zero_not_mem_toUTF8_of_not_hasNulString {s : String} (h : !hasNulString s = true) :
    (0 : UInt8) ∉ s.toUTF8.toList := by
  have hf : hasNulChars s.toList = false := by
    rw [hasNulString] at h
    exact Bool.eq_false_iff.mpr (by simpa using h)
  have hnc : Char.ofNat 0 ∉ s.toList := (hasNulChars_false_iff s.toList).mp hf
  rw [toUTF8_toList]
  intro hmem
  rw [List.mem_flatMap] at hmem
  rcases hmem with ⟨c, hcin, hc0⟩
  have hcne : c ≠ Char.ofNat 0 := fun heq => hnc (heq ▸ hcin)
  exact zero_not_mem_utf8EncodeChar hcne hc0

/-- Indexing into `s.toUTF8` never yields `0` when `!hasNulString s = true`. -/
theorem toUTF8_getElem_ne_zero {s : String} (h : !hasNulString s = true)
    {i : Nat} (hi : i < s.toUTF8.size) : s.toUTF8[i]'hi ≠ 0 := by
  intro h0
  have hsz : s.toUTF8.size = (s.toList.flatMap String.utf8EncodeChar).length := by
    rw [toUTF8_eq_toByteArray, List.size_toByteArray]
  have hi' : i < (s.toList.flatMap String.utf8EncodeChar).length := hsz ▸ hi
  have hba_sz : i < (s.toList.flatMap String.utf8EncodeChar).toByteArray.size := by
    rw [List.size_toByteArray]; exact hi'
  have hg_ba : s.toUTF8[i]'hi = (s.toList.flatMap String.utf8EncodeChar).toByteArray[i]'hba_sz := by
    have hfun := congrArg (fun ba : ByteArray => if hlt : i < ba.size then ba[i]'hlt else 0)
      (toUTF8_eq_toByteArray s)
    simp only [hi, hba_sz, ↓reduceDIte] at hfun
    exact hfun
  have hget : (s.toList.flatMap String.utf8EncodeChar)[i]'hi' = 0 := by
    rw [← List.getElem_toByteArray (h := hba_sz), ← hg_ba, h0]
  have hmem : (0 : UInt8) ∈ s.toUTF8.toList := by
    rw [toUTF8_toList, ← hget]
    exact List.getElem_mem hi'
  exact zero_not_mem_toUTF8_of_not_hasNulString h hmem

/-- `hasNulChars (a ++ b) = hasNulChars a || hasNulChars b`. -/
theorem hasNulChars_append (a b : List Char) :
    hasNulChars (a ++ b) = (hasNulChars a || hasNulChars b) := by
  induction a with
  | nil => simp [hasNulChars]
  | cons c cs ih => simp [hasNulChars, ih, Bool.or_assoc]

/-- `!hasNulString (a ++ b) = (!hasNulString a && !hasNulString b)`. -/
theorem not_hasNulString_append (a b : String) :
    (!hasNulString (a ++ b)) = (!hasNulString a && !hasNulString b) := by
  simp [hasNulString, String.toList_append, hasNulChars_append]

/-- Every byte in `asciiFallback s maxChars` is `< 0x80`. -/
theorem asciiFallback_isAscii (s : String) (maxChars : Nat) :
    isAsciiString (asciiFallback s maxChars) = true := by
  unfold isAsciiString asciiFallback
  rw [toUTF8_toList]
  simp only [String.toList_ofList, List.all_eq_true, List.mem_flatMap, List.mem_map]
  rintro b ⟨c, ⟨x, _, rfl⟩, hb⟩
  by_cases hx : x.toNat < 0x80
  · simp only [hx, ↓reduceIte] at hb
    unfold String.utf8EncodeChar at hb
    dsimp only at hb
    have hxle : x.val.toNat ≤ 127 := by
      have : x.val.toNat = x.toNat := rfl
      omega
    split at hb
    · simp only [List.mem_singleton] at hb
      subst hb
      have h128 : (UInt8.ofNat x.val.toNat).toNat < 128 := by
        rw [UInt8.toNat_ofNat', Nat.mod_eq_of_lt (by omega)]
        omega
      exact decide_eq_true h128
    · omega
  · simp only [hx, ↓reduceIte] at hb
    change b ∈ String.utf8EncodeChar '?' at hb
    have hq : b = 0x3f := by
      simpa [String.utf8EncodeChar] using hb
    subst hq
    decide

/-- `asciiFallback s maxChars` has UTF-8 byte length `≤ maxChars`. -/
theorem asciiFallback_utf8_size_le (s : String) (maxChars : Nat) :
    (asciiFallback s maxChars).toUTF8.size ≤ maxChars := by
  have h1 : ∀ l : List Char, (∀ c ∈ l, c.val.toNat ≤ 127) →
      (l.flatMap String.utf8EncodeChar).length = l.length := by
    intro l hl
    induction l with
    | nil => simp
    | cons hd tl ih =>
      have hhd : hd.val.toNat ≤ 127 := hl hd (by simp)
      have hlen : (String.utf8EncodeChar hd).length = 1 := by
        unfold String.utf8EncodeChar
        dsimp only
        have hhd' : hd.val.toNat ≤ 127 := hhd
        split
        · simp
        · omega
      simp [hlen, ih (fun c hc => hl c (by simp [hc])), Nat.add_comm]
  unfold asciiFallback
  rw [toUTF8_eq_toByteArray, List.size_toByteArray, String.toList_ofList, h1]
  · simp [List.length_take]
    omega
  · intro c hc
    rw [List.mem_map] at hc
    rcases hc with ⟨x, _, rfl⟩
    split
    · rename_i hlt
      have : x.val.toNat = x.toNat := rfl
      omega
    · decide

/-- `asciiFallback` preserves `!hasNulString`. -/
theorem asciiFallback_not_hasNul {s : String} (maxChars : Nat) (h : !hasNulString s = true) :
    !hasNulString (asciiFallback s maxChars) = true := by
  have hf : hasNulChars s.toList = false := by
    rw [hasNulString] at h
    exact Bool.eq_false_iff.mpr (by simpa using h)
  have hnc : Char.ofNat 0 ∉ s.toList := (hasNulChars_false_iff s.toList).mp hf
  unfold asciiFallback hasNulString
  rw [String.toList_ofList]
  have hf2 : hasNulChars ((s.toList.take maxChars).map
      fun c => if c.toNat < 0x80 then c else '?') = false := by
    apply (hasNulChars_false_iff _).mpr
    intro hmem
    rw [List.mem_map] at hmem
    rcases hmem with ⟨x, hx, h0⟩
    have hxtake := List.mem_of_mem_take hx
    by_cases hlt : x.toNat < 0x80
    · simp only [hlt, ↓reduceIte] at h0
      exact hnc (h0 ▸ hxtake)
    · simp only [hlt, ↓reduceIte] at h0
      have hq : ('?').toNat = 0 := by rw [h0]; rfl
      contradiction
  rw [hf2]
  decide

/-- `findUstarSplit` returns a valid split `(pfx, nm)` reconstructing `wp`. -/
theorem findUstarSplit_spec {wp pfx nm : String} (h : findUstarSplit wp = some (pfx, nm)) :
    pfx ++ "/" ++ nm = wp ∧ !pfx.isEmpty = true ∧ !nm.isEmpty = true ∧
      pfx.toUTF8.size ≤ 155 ∧ nm.toUTF8.size ≤ 100 := by
  unfold findUstarSplit at h
  suffices ∀ revPfx rest,
      revPfx.reverse ++ rest = wp.toList →
      findUstarSplit.go revPfx rest = some (pfx, nm) →
      pfx ++ "/" ++ nm = wp ∧ !pfx.isEmpty = true ∧ !nm.isEmpty = true ∧
        pfx.toUTF8.size ≤ 155 ∧ nm.toUTF8.size ≤ 100 from
    this [] wp.toList (by simp) h
  intro revPfx rest hrec hgo
  induction rest generalizing revPfx with
  | nil => simp [findUstarSplit.go] at hgo
  | cons c tl ih =>
    by_cases hslash : c = '/'
    · subst hslash
      rw [findUstarSplit.go.eq_2] at hgo
      split at hgo
      · rename_i hcond
        cases hgo
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hcond
        rcases hcond with ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩
        refine ⟨?_, h1, h2, h3, h4⟩
        rw [← String.ofList_toList (s := wp), ← hrec]
        have hlist : revPfx.reverse ++ '/' :: tl = revPfx.reverse ++ (['/'] ++ tl) := rfl
        rw [hlist, String.ofList_append, String.ofList_append]
        have hslash_str : String.ofList ['/'] = "/" := rfl
        rw [hslash_str, String.append_assoc]
      · apply ih ('/' :: revPfx)
        · simpa [List.append_assoc] using hrec
        · exact hgo
    · rw [findUstarSplit.go.eq_3 _ c tl hslash] at hgo
      apply ih (c :: revPfx)
      · simpa [List.append_assoc] using hrec
      · exact hgo

/-- `encodeOctalField.loop k v acc` prepends `k` octal digit bytes `[0x30..0x37]` to `acc`. -/
theorem encodeOctalField_loop_spec (k v : Nat) (acc : List UInt8) :
    ∃ ds : List UInt8,
      encodeOctalField.loop k v acc = ds ++ acc ∧
      ds.length = k ∧
      (∀ d ∈ ds, 0x30 ≤ d ∧ d ≤ 0x37) ∧
      ds.foldl (fun a b => a * 8 + (b.toNat - 0x30)) 0 = v % 8 ^ k := by
  induction k generalizing v acc with
  | zero =>
    refine ⟨[], rfl, rfl, ?_, ?_⟩
    · intro d hd; cases hd
    · simp [Nat.mod_one]
  | succ k' ih =>
    unfold encodeOctalField.loop
    let d : UInt8 := UInt8.ofNat (0x30 + v % 8)
    rcases ih (v / 8) (d :: acc) with ⟨ds', heq, hlen, hdig, hval⟩
    refine ⟨ds' ++ [d], ?_, ?_, ?_, ?_⟩
    · rw [heq, List.append_assoc, List.singleton_append]
    · simp [hlen]
    · intro b hb
      simp only [List.mem_append, List.mem_singleton] at hb
      rcases hb with hb | rfl
      · exact hdig b hb
      · have hm : v % 8 < 8 := Nat.mod_lt _ (by omega)
        constructor
        · change (48 : Nat) ≤ (UInt8.ofNat (0x30 + v % 8)).toNat
          rw [UInt8.toNat_ofNat', Nat.mod_eq_of_lt (by omega)]
          omega
        · change (UInt8.ofNat (0x30 + v % 8)).toNat ≤ 55
          rw [UInt8.toNat_ofNat', Nat.mod_eq_of_lt (by omega)]
          omega
    · rw [List.foldl_append, hval, List.foldl_cons, List.foldl_nil]
      have hd : d.toNat = 0x30 + v % 8 := by
        change (UInt8.ofNat (0x30 + v % 8)).toNat = 0x30 + v % 8
        rw [UInt8.toNat_ofNat', Nat.mod_eq_of_lt (by have := Nat.mod_lt v (by omega : 0 < 8); omega)]
      rw [hd]
      have hsub : 0x30 + v % 8 - 0x30 = v % 8 := by omega
      rw [hsub]
      have hmod_div : v % 8 ^ (k' + 1) = (v / 8 % 8 ^ k') * 8 + v % 8 := by
        have hr : v % 8 < 8 := Nat.mod_lt v (by omega)
        have hk : (v / 8) % 8 ^ k' < 8 ^ k' := Nat.mod_lt _ (Nat.pow_pos (by omega))
        have hv : v = (8 * 8 ^ k') * (v / 8 / 8 ^ k') + ((v / 8 % 8 ^ k') * 8 + v % 8) := by
          calc v = 8 * (v / 8) + v % 8 := (Nat.div_add_mod v 8).symm
            _ = 8 * (8 ^ k' * (v / 8 / 8 ^ k') + v / 8 % 8 ^ k') + v % 8 := by
                rw [Nat.div_add_mod (v / 8) (8 ^ k')]
            _ = (8 * 8 ^ k') * (v / 8 / 8 ^ k') + ((v / 8 % 8 ^ k') * 8 + v % 8) := by
                rw [Nat.mul_add, Nat.mul_assoc, Nat.mul_comm 8 (v / 8 % 8 ^ k'), Nat.add_assoc]
        have hlt : (v / 8 % 8 ^ k') * 8 + v % 8 < 8 * 8 ^ k' := by omega
        have hp : 8 ^ (k' + 1) = 8 * 8 ^ k' := by rw [Nat.pow_succ, Nat.mul_comm]
        conv => lhs; rw [hp, hv, Nat.mul_add_mod, Nat.mod_eq_of_lt hlt]
      exact hmod_div.symm

/-- Size of `encodeOctalField val digits` is `digits + 1`. -/
theorem encodeOctalField_size (val digits : Nat) :
    (encodeOctalField val digits).size = digits + 1 := by
  unfold encodeOctalField
  rcases encodeOctalField_loop_spec digits val [0] with ⟨ds, heq, hlen, _, _⟩
  rw [heq]
  change (ds ++ [0]).toArray.size = digits + 1
  simp [hlen]

/-- `encodeOctalField val digits` has `0x00` as its final byte. -/
theorem encodeOctalField_last_zero (val digits : Nat) :
    (encodeOctalField val digits)[digits]'(by rw [encodeOctalField_size]; omega) = 0 := by
  unfold encodeOctalField
  rcases encodeOctalField_loop_spec digits val [0] with ⟨ds, heq, hlen, _, _⟩
  rw [ByteArray.getElem_eq_getElem_data]
  simp only [heq]
  change (ds ++ [0]).toArray[digits]'(by simp [hlen]) = 0
  rw [List.getElem_toArray]
  rw [List.getElem_append_right (by omega)]
  simp [hlen]

/-- `List.takeWhile p xs = xs` whenever `∀ x ∈ xs, p x = true`. -/
theorem list_takeWhile_eq_self {α : Type} (p : α → Bool) (xs : List α)
    (h : ∀ x ∈ xs, p x = true) : xs.takeWhile p = xs := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    have hx : p x = true := h x (by simp)
    simp [hx, ih (fun y hy => h y (by simp [hy]))]

/-- For `b.toNat < 64`, `b &&& 0x80 = 0`. -/
theorem uint8_and_0x80_eq_zero {b : UInt8} (hb : b.toNat < 64) : (b &&& 0x80) = 0 := by
  have hnat : b.toNat &&& 128 = 0 := by
    apply Nat.eq_of_testBit_eq
    intro i
    rw [Nat.testBit_and, Nat.zero_testBit]
    rcases Nat.lt_or_ge i 7 with hi7 | hi7
    · have h128 : (128 : Nat).testBit i = false := by
        match i with
        | 0 => rfl | 1 => rfl | 2 => rfl | 3 => rfl
        | 4 => rfl | 5 => rfl | 6 => rfl | _ + 7 => omega
      simp [h128]
    · have hb7 : b.toNat < 2 ^ 7 := by omega
      have hbi := Nat.testBit_lt_two_pow (x := b.toNat) (i := i)
        (Nat.lt_of_lt_of_le hb7 (Nat.pow_le_pow_right (by omega) hi7))
      simp [hbi]
  rcases b with ⟨bv⟩
  exact congrArg UInt8.ofBitVec (BitVec.eq_of_toNat_eq (by simpa [UInt8.toNat_and] using hnat))

/-- `parseChecksumOctal` decodes `encodeOctalField chk 6 ++ #[0x20]` when `chk < 8 ^ 6`. -/
theorem parseChecksumOctal_encodeOctalField {bytes : ByteArray} {start chk : Nat}
    (hchk : chk < 8 ^ 6)
    (hext : bytes.extract start (start + 8) =
      encodeOctalField chk 6 ++ ByteArray.mk #[0x20]) :
    parseChecksumOctal bytes start (start + 8) start = .ok chk := by
  unfold parseChecksumOctal
  rw [hext]
  rcases encodeOctalField_loop_spec 6 chk [0] with ⟨ds, heq, hlen, hdig, hval⟩
  have hraw : (encodeOctalField chk 6 ++ ByteArray.mk #[0x20]).toList = ds ++ [0, 0x20] := by
    unfold encodeOctalField
    rw [heq]
    have hconcat : ByteArray.mk (ds ++ [0]).toArray ++ ByteArray.mk #[0x20] =
        (ds ++ [0, 0x20]).toByteArray := by
      apply ByteArray.ext
      apply Array.ext
      · rw [← ByteArray.size, ByteArray.size_append, ← ByteArray.size, List.size_toByteArray]
        change (ds ++ [0]).toArray.size + (#[0x20] : Array UInt8).size = (ds ++ [0, 0x20]).length
        simp
      · intro i hi1 hi2
        have hi' : i < (ds ++ [0, 0x20]).toByteArray.size := by
          rw [ByteArray.size]; exact hi2
        have hi1' : i < (ByteArray.mk (ds ++ [0]).toArray ++ ByteArray.mk #[0x20]).size := by
          rw [ByteArray.size]; exact hi1
        rw [← ByteArray.getElem_eq_getElem_data (h := hi1'),
          ← ByteArray.getElem_eq_getElem_data (h := hi'), List.getElem_toByteArray]
        by_cases hlt : i < (ByteArray.mk (ds ++ [0]).toArray).size
        · rw [getElem_append_left hlt]
          have hlt' : i < (ds ++ [0]).length := by
            change i < (ds ++ [0]).toArray.size at hlt
            simpa using hlt
          have hba_eq : (ByteArray.mk (ds ++ [0]).toArray)[i]'hlt = (ds ++ [0])[i]'hlt' := by
            rw [ByteArray.getElem_eq_getElem_data]
            exact List.getElem_toArray _
          rw [hba_eq]
          have h2 : ds ++ [0, 0x20] = (ds ++ [0]) ++ [0x20] := by simp [List.append_assoc]
          have hlt2 : i < ((ds ++ [0]) ++ [0x20]).length := by
            rw [← h2]; rw [List.size_toByteArray] at hi'; exact hi'
          have h3 : ((ds ++ [0]) ++ [0x20])[i]'hlt2 = (ds ++ [0])[i]'hlt' :=
            List.getElem_append_left hlt'
          have h3' := h3.symm
          have hcongr : ((ds ++ [0]) ++ [0x20])[i]'hlt2 =
              (ds ++ [0, 0x20])[i]'(by rw [h2]; exact hlt2) := by
            congr 1
            exact h2.symm
          rw [← hcongr]
          exact h3'
        · have hge : (ByteArray.mk (ds ++ [0]).toArray).size ≤ i := Nat.le_of_not_lt hlt
          rw [getElem_append_right hge hi1']
          have hlen1 : (ByteArray.mk (ds ++ [0]).toArray).size = ds.length + 1 := by
            change (ds ++ [0]).toArray.size = ds.length + 1; simp
          have hi_eq : i = ds.length + 1 := by
            have hlt2 : i < (ds ++ [0, 0x20]).length := by
              rw [List.size_toByteArray] at hi'; exact hi'
            have hge1 : ds.length + 1 ≤ i := hlen1 ▸ hge
            simp only [List.length_append, List.length_cons, List.length_nil] at hlt2
            omega
          subst hi_eq
          have hsub : ds.length + 1 - (ByteArray.mk (ds ++ [0]).toArray).size = 0 := by
            rw [hlen1]; omega
          have h0 : (ByteArray.mk #[0x20])[ds.length + 1 - (ByteArray.mk (ds ++ [0]).toArray).size]'(by
              rw [hsub]; decide) = 0x20 := by
            simp only [hsub]
            rfl
          rw [h0]
          have h2 : ds ++ [0, 0x20] = (ds ++ [0]) ++ [0x20] := by simp [List.append_assoc]
          have hlen0 : (ds ++ [0]).length = ds.length + 1 := by simp
          simp only [h2]
          rw [List.getElem_append_right (by omega)]
          have hsub0 : ds.length + 1 - (ds ++ [0]).length = 0 := by omega
          simp only [hsub0]
          rfl
    rw [hconcat, toByteArray_toList]
  dsimp only
  rw [hraw]
  have hne0x20 : ∀ d ∈ ds, (d == 0x20) = false := by
    intro d hd
    have ⟨hlo, _⟩ := hdig d hd
    exact beq_false_of_ne (by intro h; subst h; simp at hlo)
  have hdrop : (ds ++ [0, 0x20]).dropWhile (· == 0x20) = ds ++ [0, 0x20] := by
    cases ds with
    | nil => simp at hlen
    | cons d0 ds' =>
      have hd0 := hne0x20 d0 (by simp)
      simp [hd0]
  have hdigBool : ∀ d ∈ ds, (0x30 ≤ d && d ≤ 0x37) = true := by
    intro d hd
    have ⟨hlo, hhi⟩ := hdig d hd
    simp [hlo, hhi]
  have htake : (ds ++ [0, 0x20]).takeWhile (fun b => 0x30 ≤ b && b ≤ 0x37) = ds := by
    rw [List.takeWhile_append]
    have h1 := list_takeWhile_eq_self (fun b => 0x30 ≤ b && b ≤ 0x37) ds hdigBool
    rw [h1]
    simp
  have hdrop2 : (ds ++ [0, 0x20]).drop ds.length = [0, 0x20] := by
    simp
  rw [hdrop, htake]
  have hnot_empty : ds.isEmpty = false := by cases ds <;> simp_all
  have htail : ((ds ++ [0, 0x20]).drop ds.length).all (fun b => b == 0x20 || b == 0x00) = true := by
    rw [hdrop2]
    decide
  simp [hnot_empty, hval, Nat.mod_eq_of_lt hchk]

/-- `parseUstarNumeric` decodes `encodeOctalField val digits` when `val < 8 ^ digits` and `val < limit`. -/
theorem parseUstarNumeric_encodeOctalField {bytes : ByteArray} {start val digits limit offset : Nat}
    {allowAllEmpty : Bool} {fieldName : String}
    (hdig : 1 ≤ digits) (hval : val < 8 ^ digits) (hlim : val < limit)
    (hext : bytes.extract start (start + (digits + 1)) = encodeOctalField val digits) :
    parseUstarNumeric bytes start (start + (digits + 1)) offset allowAllEmpty limit fieldName = .ok val := by
  unfold parseUstarNumeric
  rw [hext]
  rcases encodeOctalField_loop_spec digits val [0] with ⟨ds, heq, hlen, hdigs, hfold⟩
  have hraw : (encodeOctalField val digits).toList = ds ++ [0] := by
    unfold encodeOctalField
    rw [heq, byteArray_toList_eq]
  dsimp only
  rw [hraw]
  cases hds : ds with
  | nil => simp [hds] at hlen; omega
  | cons d0 ds' =>
    have hd0_range : 0x30 ≤ d0 ∧ d0 ≤ 0x37 := hdigs d0 (by simp [hds])
    have hb0_hi : (d0 &&& 0x80) = 0 := uint8_and_0x80_eq_zero (by
      have ⟨_, hhi⟩ := hd0_range
      have hu : d0.toNat ≤ 55 := hhi
      omega)
    have hnot_all : ((d0 :: (ds' ++ [0])).all fun b => b == 0x00 || b == 0x20) = false := by
      have hne0 : (d0 == 0x00) = false := beq_false_of_ne (by
        intro h; subst h; have ⟨hlo, _⟩ := hd0_range; simp at hlo)
      have hne32 : (d0 == 0x20) = false := beq_false_of_ne (by
        intro h; subst h; have ⟨hlo, _⟩ := hd0_range; simp at hlo)
      simp [hne0, hne32]
    have hd_all : ∀ b ∈ (d0 :: ds'), (0x30 ≤ b && b ≤ 0x37) = true := by
      intro b hb
      have ⟨hlo, hhi⟩ := hdigs b (by simpa [hds] using hb)
      simp [hlo, hhi]
    have hne0x20 : (d0 == 0x20) = false := by
      have ⟨hlo, _⟩ := hd0_range
      exact beq_false_of_ne (by intro h; subst h; simp at hlo)
    have hdrop : (d0 :: (ds' ++ [0])).dropWhile (· == 0x20) = d0 :: (ds' ++ [0]) := by
      simp [hne0x20]
    have htake : (d0 :: (ds' ++ [0])).takeWhile (fun b => 0x30 ≤ b && b ≤ 0x37) = d0 :: ds' := by
      change ((d0 :: ds') ++ [0]).takeWhile (fun b => 0x30 ≤ b && b ≤ 0x37) = d0 :: ds'
      rw [List.takeWhile_append]
      have h1 := list_takeWhile_eq_self (fun b => 0x30 ≤ b && b ≤ 0x37) (d0 :: ds') hd_all
      simp [h1]
    have hdrop2 : (d0 :: (ds' ++ [0])).drop (d0 :: ds').length = [0] := by
      change ((d0 :: ds') ++ [0]).drop (d0 :: ds').length = [0]
      simp
    rw [List.cons_append]
    dsimp only
    simp only [hb0_hi, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
    rw [ite_eq_right_iff.mpr (by intro h; simp [hnot_all] at h)]
    rw [hdrop, htake]
    simp only [List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte, hdrop2, List.all_cons,
      List.all_nil, Bool.and_true]
    have hfold' : (d0 :: ds').foldl (fun acc b => acc * 8 + (b.toNat - 0x30)) 0 = val := by
      rw [← hds, hfold, Nat.mod_eq_of_lt hval]
    rw [hfold']
    have hnot_ge : ¬(val ≥ limit) := Nat.not_le_of_lt hlim
    simp [hnot_ge]

/-- `findNul` stops at `start + s.toUTF8.size` when `bytes.extract start (start + w) = padRightBytes w s.toUTF8`. -/
theorem extractCStringBytes_padRightBytes {bytes : ByteArray} {start w : Nat} {s : String}
    (hs : !hasNulString s = true) (hsz : s.toUTF8.size ≤ w) (hbd : start + w ≤ bytes.size)
    (hext : bytes.extract start (start + w) = padRightBytes w s.toUTF8) :
    extractCStringBytes bytes start (start + w) = s.toUTF8 := by
  have hext_sz : (bytes.extract start (start + w)).size = w := by
    rw [hext, padRightBytes_size]
  unfold extractCStringBytes
  have hfind : ∀ i, i ≤ s.toUTF8.size →
      extractCStringBytes.findNul bytes (start + w) (start + i) = start + s.toUTF8.size := by
    intro i hi
    induction hdiff : s.toUTF8.size - i generalizing i with
    | zero =>
      have heq : i = s.toUTF8.size := by omega
      subst heq
      unfold extractCStringBytes.findNul
      by_cases hfull : s.toUTF8.size = w
      · have hge : start + s.toUTF8.size ≥ start + w := by omega
        rw [ite_eq_left_iff.mpr (by intro h; exact absurd hge h)]
        exact congrArg (start + ·) hfull.symm
      · have hlt : s.toUTF8.size < w := by omega
        have hlt_b : start + s.toUTF8.size < bytes.size := by omega
        have hnotge : ¬(start + s.toUTF8.size ≥ start + w) := by omega
        simp only [hnotge, ↓reduceIte, hlt_b, ↓reduceDIte]
        have hsz_e : s.toUTF8.size < (bytes.extract start (start + w)).size := by
          rw [hext_sz]; exact hlt
        have hs0 : (bytes.extract start (start + w))[s.toUTF8.size]'hsz_e =
            bytes[start + s.toUTF8.size]'hlt_b := ByteArray.getElem_extract hsz_e
        have hsz_p : s.toUTF8.size < (padRightBytes w s.toUTF8).size := by
          rw [padRightBytes_size]; exact hlt
        have hpad_idx : (bytes.extract start (start + w))[s.toUTF8.size]'hsz_e =
            (padRightBytes w s.toUTF8)[s.toUTF8.size]'hsz_p := by
          have hfun := congrArg (fun ba : ByteArray =>
            if h : s.toUTF8.size < ba.size then ba[s.toUTF8.size]'h else 0) hext
          simp only [hsz_e, hsz_p, ↓reduceDIte] at hfun
          exact hfun
        have hpad0 : (padRightBytes w s.toUTF8)[s.toUTF8.size]'hsz_p = 0 := by
          rw [padRightBytes_getElem hsz hlt]
          simp [Nat.not_lt_of_ge (Nat.le_refl _)]
        have hb0 : bytes[start + s.toUTF8.size]'hlt_b = 0 := by
          rw [← hs0, hpad_idx, hpad0]
        simp only [hb0, beq_self_eq_true, ↓reduceIte]
    | succ d ih =>
      have hlt_s : i < s.toUTF8.size := by omega
      have hlt_w : i < w := by omega
      have hlt_b : start + i < bytes.size := by omega
      unfold extractCStringBytes.findNul
      have hnotge : ¬(start + i ≥ start + w) := by omega
      simp only [hnotge, ↓reduceIte, hlt_b, ↓reduceDIte]
      have hi_e : i < (bytes.extract start (start + w)).size := by
        rw [hext_sz]; exact hlt_w
      have hs_i : (bytes.extract start (start + w))[i]'hi_e =
          bytes[start + i]'hlt_b := ByteArray.getElem_extract hi_e
      have hi_p : i < (padRightBytes w s.toUTF8).size := by
        rw [padRightBytes_size]; exact hlt_w
      have hpad_idx : (bytes.extract start (start + w))[i]'hi_e =
          (padRightBytes w s.toUTF8)[i]'hi_p := by
        have hfun := congrArg (fun ba : ByteArray =>
          if h : i < ba.size then ba[i]'h else 0) hext
        simp only [hi_e, hi_p, ↓reduceDIte] at hfun
        exact hfun
      have hpad_i : (padRightBytes w s.toUTF8)[i]'hi_p = s.toUTF8[i]'hlt_s := by
        rw [padRightBytes_getElem hsz hlt_w]
        simp only [hlt_s, ↓reduceDIte]
      have hne0 : bytes[start + i]'hlt_b ≠ 0 := by
        rw [← hs_i, hpad_idx, hpad_i]
        exact toUTF8_getElem_ne_zero hs hlt_s
      have hbeq0 : (bytes[start + i]'hlt_b == 0) = false := beq_false_of_ne hne0
      simp only [hbeq0, Bool.false_eq_true, ↓reduceIte]
      have hstep := ih (i + 1) (by omega) (by omega)
      simpa [Nat.add_assoc] using hstep
  have hpos := hfind 0 (Nat.zero_le _)
  simp only [Nat.add_zero] at hpos
  dsimp only
  rw [hpos]
  have hext' : bytes.extract start (start + s.toUTF8.size) =
      (bytes.extract start (start + w)).extract 0 s.toUTF8.size := by
    rw [ByteArray.extract_extract]
    exact congrArg (bytes.extract start) (by omega)
  rw [hext', hext, padRightBytes_extract_prefix hsz]

/-- `decodeCStringUtf8` decodes a padded `!hasNulString` UTF-8 field back to `.ok s`. -/
theorem decodeCStringUtf8_padRightBytes {bytes : ByteArray} {start w offset : Nat}
    {s : String} {fieldName : String}
    (hs : !hasNulString s = true) (hsz : s.toUTF8.size ≤ w) (hbd : start + w ≤ bytes.size)
    (hext : bytes.extract start (start + w) = padRightBytes w s.toUTF8) :
    decodeCStringUtf8 bytes start (start + w) offset fieldName = .ok s := by
  unfold decodeCStringUtf8
  dsimp only
  rw [extractCStringBytes_padRightBytes hs hsz hbd hext, fromUTF8?_toUTF8]

/-- Base-10 foldl shift helper. -/
theorem list_foldl_dec_shift (xs : List Nat) (x y : Nat) :
    xs.foldl (fun s d => s * 10 + d) (x + y) =
      x * 10 ^ xs.length + xs.foldl (fun s d => s * 10 + d) y := by
  induction xs generalizing x y with
  | nil => simp
  | cons z zs ih =>
    simp only [List.foldl_cons, List.length_cons, Nat.pow_succ]
    have harg : (x + y) * 10 + z = x * 10 + (y * 10 + z) := by omega
    rw [harg, ih (x * 10) (y * 10 + z)]
    have hmul : x * 10 * 10 ^ zs.length = x * (10 ^ zs.length * 10) := by
      rw [Nat.mul_assoc, Nat.mul_comm 10 (10 ^ zs.length)]
    rw [hmul]

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
    · rename_i hdiv
      have hn10 : n < 10 := by omega
      refine ⟨n :: acc, ?_, ?_, ?_, ?_, ?_⟩
      · intro d hd
        simp only [List.mem_cons] at hd
        rcases hd with rfl | hd
        · exact hn10
        · exact hacc d hd
      · simp only [List.length_cons]
        omega
      · intro hpos
        refine ⟨n, [], rfl, hpos, ?_, ?_⟩
        · simp; omega
        · simp [hn10]
      · simp [Nat.mod_eq_of_lt hn10]
      · simp only [List.foldl_cons, Nat.zero_mul, Nat.zero_add]
        have hsh := list_foldl_dec_shift acc n 0
        simpa using hsh
    · rename_i hdiv
      have hn10 : 10 ≤ n := by omega
      have hdiv_lt : n / 10 < f := by omega
      have hdiv_pos : 0 < n / 10 := by omega
      have hacc' : ∀ d ∈ (n % 10 :: acc), d < 10 := by
        intro d hd
        simp only [List.mem_cons] at hd
        rcases hd with rfl | hd
        · exact Nat.mod_lt _ (by omega)
        · exact hacc d hd
      rcases ih (n / 10) (n % 10 :: acc) hdiv_lt hacc' with
        ⟨ds, hdigs, hlen, hbounds, hmap, hfold⟩
      rcases hbounds hdiv_pos with ⟨hd, tl, hds_eq, hhd_pos, hlo, hhi⟩
      refine ⟨ds, hdigs, by simp at hlen; omega, ?_, ?_, ?_⟩
      · intro _
        refine ⟨hd, tl ++ [n % 10], ?_, hhd_pos, ?_, ?_⟩
        · simp [hds_eq, List.append_assoc]
        · have hlen_ds : ds.length = tl.length + acc.length + 2 := by
            simp [hds_eq, List.length_append]
            omega
          have he1 : ds.length - 1 - acc.length = (ds.length - 1 - (n % 10 :: acc).length) + 1 := by
            rw [hlen_ds]; simp; omega
          rw [he1, Nat.pow_succ]
          omega
        · have hlen_ds : ds.length = tl.length + acc.length + 2 := by
            simp [hds_eq, List.length_append]
            omega
          have he2 : ds.length - acc.length = (ds.length - (n % 10 :: acc).length) + 1 := by
            rw [hlen_ds]; simp; omega
          rw [he2, Nat.pow_succ]
          omega
      · simpa [List.map_cons] using hmap
      · rw [hfold]
        simp only [List.length_cons, List.foldl_cons, Nat.zero_mul, Nat.zero_add]
        have hsh := list_foldl_dec_shift acc (n % 10) 0
        rw [Nat.add_zero] at hsh
        rw [hsh]
        have heq_sum : n / 10 * 10 ^ (acc.length + 1) + n % 10 * 10 ^ acc.length =
            n * 10 ^ acc.length := by
          rw [Nat.pow_succ, ← Nat.mul_assoc, Nat.mul_right_comm (n / 10) (10 ^ acc.length) 10,
            ← Nat.add_mul, Nat.mul_comm (n / 10) 10, Nat.div_add_mod]
        omega

/-- Spec for `(toString n).toList` as base-10 digits. -/
theorem toString_digits_spec (n : Nat) :
    ∃ ds : List Nat,
      (∀ d ∈ ds, d < 10) ∧
      ds.length ≥ 1 ∧
      (n > 0 → ∃ hd tl, ds = hd :: tl ∧ 0 < hd ∧
        10 ^ (ds.length - 1) ≤ n ∧ n < 10 ^ ds.length) ∧
      (toString n).toList = ds.map Nat.digitChar ∧
      ds.foldl (fun a d => a * 10 + d) 0 = n := by
  rcases toDigitsCore_10_spec (n + 1) n [] (Nat.lt_succ_self n) (fun _ h => by cases h) with
    ⟨ds, hdigs, hlen, hbounds, hmap, hfold⟩
  refine ⟨ds, hdigs, by simpa using hlen, ?_, ?_, ?_⟩
  · intro hpos
    rcases hbounds hpos with ⟨hd, tl, heq, hhd, hlo, hhi⟩
    refine ⟨hd, tl, by simpa using heq, hhd, by simpa using hlo, by simpa using hhi⟩
  · change (Nat.repr n).toList = ds.map Nat.digitChar
    rw [Nat.repr, Nat.toDigits, String.toList_ofList]
    simpa using hmap
  · simpa using hfold

/-- Every decimal digit char `'0'..'9'` has UTF-8 length `1`. -/
theorem digitChar_utf8EncodeChar_len {d : Nat} (hd : d < 10) :
    (String.utf8EncodeChar (Nat.digitChar d)).length = 1 := by
  match d with
  | 0 => rfl | 1 => rfl | 2 => rfl | 3 => rfl | 4 => rfl
  | 5 => rfl | 6 => rfl | 7 => rfl | 8 => rfl | 9 => rfl
  | _ + 10 => omega

/-- `decDigitsLen n` equals the number of decimal digits of `n` (at least 1). -/
theorem decDigitsLen_eq_digits_length (n : Nat) :
    ∃ ds : List Nat,
      (∀ d ∈ ds, d < 10) ∧
      (n > 0 → ∃ hd tl, ds = hd :: tl ∧ 0 < hd ∧
        10 ^ (ds.length - 1) ≤ n ∧ n < 10 ^ ds.length) ∧
      (toString n).toList = ds.map Nat.digitChar ∧
      ds.foldl (fun a d => a * 10 + d) 0 = n ∧
      decDigitsLen n = ds.length ∧
      1 ≤ decDigitsLen n := by
  rcases toString_digits_spec n with ⟨ds, hdigs, hlen, hbounds, hstr, hfold⟩
  have hflat : ∀ l : List Nat, (∀ d ∈ l, d < 10) →
      ((l.map Nat.digitChar).flatMap String.utf8EncodeChar).length = l.length := by
    intro l hl
    induction l with
    | nil => simp
    | cons d ds ih =>
      have hd : d < 10 := hl d (by simp)
      simp only [List.map_cons, List.flatMap_cons, List.length_append, List.length_cons,
        digitChar_utf8EncodeChar_len hd, ih (fun x hx => hl x (by simp [hx])), Nat.add_comm 1 _]
  have hdec : decDigitsLen n = ds.length := by
    unfold decDigitsLen
    rw [toUTF8_eq_toByteArray, List.size_toByteArray, hstr, hflat ds hdigs]
  exact ⟨ds, hdigs, hbounds, hstr, hfold, hdec, hdec ▸ hlen⟩

/-- `decDigitsLen` is bounded above by `7` for `n < 10 ^ 7`. -/
theorem decDigitsLen_le_7 {n : Nat} (hn : n < 10 ^ 7) : decDigitsLen n ≤ 7 := by
  rcases decDigitsLen_eq_digits_length n with ⟨ds, _, hbounds, _, _, hdec, _⟩
  rw [hdec]
  by_cases hn0 : n = 0
  · subst hn0
    have h0 : decDigitsLen 0 = 1 := by decide
    omega
  · rcases hbounds (Nat.pos_of_ne_zero hn0) with ⟨_, _, _, _, hlo, _⟩
    rcases Nat.lt_or_ge ds.length 8 with hlt | hge8
    · omega
    · have hpow : 10 ^ 7 ≤ 10 ^ (ds.length - 1) :=
        Nat.pow_le_pow_right (by omega) (by omega)
      omega

/-- `decDigitsLen` is monotone. -/
theorem decDigitsLen_mono {m n : Nat} (hmn : m ≤ n) : decDigitsLen m ≤ decDigitsLen n := by
  rcases decDigitsLen_eq_digits_length m with ⟨ds1, _, hb1, _, _, hdec1, hpos1⟩
  rcases decDigitsLen_eq_digits_length n with ⟨ds2, _, hb2, _, _, hdec2, hpos2⟩
  rw [hdec1, hdec2]
  by_cases hm0 : m = 0
  · subst hm0
    have hm1 : decDigitsLen 0 = 1 := by decide
    omega
  · rcases hb1 (Nat.pos_of_ne_zero hm0) with ⟨_, _, _, _, hlo1, _⟩
    rcases hb2 (by omega) with ⟨_, _, _, _, _, hhi2⟩
    rcases Nat.lt_or_ge ds2.length ds1.length with hlt | hle
    · have hpow : 10 ^ ds2.length ≤ 10 ^ (ds1.length - 1) :=
        Nat.pow_le_pow_right (by omega) (by omega)
      omega
    · exact hle

/-- Fixed point lemma for `paxRecordTotalLen` when `4 ≤ kvBodyLen ≤ maxPaxHeaderBytes`. -/
theorem paxRecordTotalLen_fixed_point {kvBodyLen : Nat}
    (hmin : 4 ≤ kvBodyLen) (hmax : kvBodyLen ≤ maxPaxHeaderBytes) :
    paxRecordTotalLen kvBodyLen = decDigitsLen (paxRecordTotalLen kvBodyLen) + kvBodyLen ∧
      paxRecordTotalLen kvBodyLen ≥ 5 := by
  have hmax_num : maxPaxHeaderBytes = 1048576 := rfl
  have hgo : ∀ fuel d : Nat, 1 ≤ d → d ≤ 7 → d ≤ decDigitsLen (d + kvBodyLen) →
      8 - d ≤ fuel →
      paxRecordTotalLen.go kvBodyLen d fuel =
        decDigitsLen (paxRecordTotalLen.go kvBodyLen d fuel) + kvBodyLen ∧
      paxRecordTotalLen.go kvBodyLen d fuel ≥ 5 := by
    intro fuel
    induction fuel with
    | zero => intro d _ hd7 _ hle; omega
    | succ f ih =>
      intro d hd1 hd7 hle hf
      rw [paxRecordTotalLen.go.eq_2]
      by_cases heq : (decDigitsLen (d + kvBodyLen) == d) = true
      · rw [ite_eq_left_iff.mpr (by intro h; exact absurd heq h)]
        have hact : decDigitsLen (d + kvBodyLen) = d := beq_iff_eq.mp heq
        refine ⟨?_, ?_⟩
        · rw [hact]
        · omega
      · rw [ite_eq_right_iff.mpr (by intro h; exact absurd h heq)]
        have hne : decDigitsLen (d + kvBodyLen) ≠ d := by
          intro h; exact heq (beq_iff_eq.mpr h)
        have hgt : d < decDigitsLen (d + kvBodyLen) := by omega
        have hcand_lt : d + kvBodyLen < 10 ^ 7 := by omega
        have hact7 : decDigitsLen (d + kvBodyLen) ≤ 7 := decDigitsLen_le_7 hcand_lt
        have hmono : decDigitsLen (d + kvBodyLen) ≤
            decDigitsLen (decDigitsLen (d + kvBodyLen) + kvBodyLen) := by
          exact decDigitsLen_mono (by omega)
        exact ih (decDigitsLen (d + kvBodyLen)) (by omega) hact7 hmono (by omega)
  rw [paxRecordTotalLen]
  rcases decDigitsLen_eq_digits_length (1 + kvBodyLen) with ⟨_, _, _, _, _, _, h1⟩
  exact hgo 20 1 (Nat.le_refl 1) (by omega) h1 (by omega)

/-- `(a ++ b).toUTF8 = a.toUTF8 ++ b.toUTF8`. -/
theorem toUTF8_append (a b : String) : (a ++ b).toUTF8 = a.toUTF8 ++ b.toUTF8 := by
  rw [toUTF8_eq_toByteArray, toUTF8_eq_toByteArray, toUTF8_eq_toByteArray,
    String.toList_append, List.flatMap_append, List.toByteArray_append]

/-- `(a ++ b).toUTF8.size = a.toUTF8.size + b.toUTF8.size`. -/
theorem toUTF8_size_append (a b : String) : (a ++ b).toUTF8.size = a.toUTF8.size + b.toUTF8.size := by
  rw [toUTF8_append, ByteArray.size_append]

/-- UTF-8 encoding of a single digit `d < 10` is `[UInt8.ofNat (0x30 + d)]`. -/
theorem digitChar_utf8EncodeChar_eq {d : Nat} (hd : d < 10) :
    String.utf8EncodeChar (Nat.digitChar d) = [UInt8.ofNat (0x30 + d)] := by
  match d with
  | 0 => rfl | 1 => rfl | 2 => rfl | 3 => rfl | 4 => rfl
  | 5 => rfl | 6 => rfl | 7 => rfl | 8 => rfl | 9 => rfl
  | _ + 10 => omega

/-- Properties of `Nat.digitChar d` for `d < 10`. -/
theorem digitChar_props {d : Nat} (hd : d < 10) :
    ('0' ≤ Nat.digitChar d ∧ Nat.digitChar d ≤ '9') ∧
    (Nat.digitChar d).toNat - '0'.toNat = d ∧
    Nat.digitChar d ≠ '-' := by
  match d with
  | 0 => decide | 1 => decide | 2 => decide | 3 => decide | 4 => decide
  | 5 => decide | 6 => decide | 7 => decide | 8 => decide | 9 => decide
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
  have hne : ds ≠ [] := by
    intro h; subst h; simp at hdec; omega
  have hbytes : (ds.map Nat.digitChar).flatMap String.utf8EncodeChar =
      ds.map (fun d => UInt8.ofNat (0x30 + d)) := by
    clear hbounds hstr hfold hdec hpos hne
    induction ds with
    | nil => simp
    | cons d ds ih =>
      have hd : d < 10 := hdigs d (by simp)
      simp [List.map_cons, List.flatMap_cons, digitChar_utf8EncodeChar_eq hd,
        ih (fun x hx => hdigs x (by simp [hx]))]
  refine ⟨ds, hdigs, hne, ?_, hstr, hfold, ?_, ?_⟩
  · intro hn0
    rcases hbounds hn0 with ⟨hd, tl, heq, hhd, _⟩
    exact ⟨hd, tl, heq, hhd⟩
  · rw [toUTF8_eq_toByteArray, hstr, hbytes]
  · change (toString n).toUTF8.size = ds.length
    rw [← hdec, decDigitsLen]

/-- Helper: folding `(ds.map Nat.digitChar)` agrees with folding `ds`. -/
theorem foldl_digitChar_eq (ds : List Nat) (hdigs : ∀ d ∈ ds, d < 10) (init : Nat) :
    (ds.map Nat.digitChar).foldl (fun acc c => acc * 10 + (c.toNat - '0'.toNat)) init =
      ds.foldl (fun a d => a * 10 + d) init := by
  induction ds generalizing init with
  | nil => simp
  | cons d ds ih =>
    have hd : d < 10 := hdigs d (by simp)
    have hsub := (digitChar_props hd).2.1
    simp only [List.map_cons, List.foldl_cons, hsub]
    exact ih (fun x hx => hdigs x (by simp [hx])) _

/-- `parsePaxNat (toString n) offset key` returns `.ok n` when `n < u64Limit`. -/
theorem parsePaxNat_toString {n offset : Nat} {key : String} (hn : n < u64Limit) :
    parsePaxNat (toString n) offset key = .ok n := by
  rcases toString_toUTF8_bytes_eq (n := n) with ⟨ds, hdigs, hne, _, hstr, hfold, _, _⟩
  unfold parsePaxNat
  rw [hstr]
  have hnot_empty : (ds.map Nat.digitChar).isEmpty = false := by
    cases ds with
    | nil => exact absurd rfl hne
    | cons _ _ => rfl
  have hnot_dash : ((ds.map Nat.digitChar).head? == some '-') = false := by
    cases ds with
    | nil => exact absurd rfl hne
    | cons d _ =>
      have hd : d < 10 := hdigs d (by simp)
      have hne_dash := (digitChar_props hd).2.2
      have hbeq : (Nat.digitChar d == '-') = false := beq_false_of_ne hne_dash
      simp [hbeq]
  have hall_dig : (ds.map Nat.digitChar).all (fun c => '0' ≤ c && c ≤ '9') = true := by
    rw [List.all_eq_true]
    intro c hc
    rw [List.mem_map] at hc
    rcases hc with ⟨d, hd, rfl⟩
    have ⟨hlo, hhi⟩ := (digitChar_props (hdigs d hd)).1
    simp [hlo, hhi]
  have hfold_chars : (ds.map Nat.digitChar).foldl (fun acc c => acc * 10 + (c.toNat - '0'.toNat)) 0 = n := by
    rw [foldl_digitChar_eq ds hdigs 0, hfold]
  simp only [hnot_empty, hnot_dash, hall_dig, Bool.false_eq_true, Bool.not_true, ↓reduceIte,
    hfold_chars, Nat.not_le_of_lt hn]

/-- `parsePaxMtime (toString n) offset` returns `.ok n` when `n < u64Limit`. -/
theorem parsePaxMtime_toString {n offset : Nat} (hn : n < u64Limit) :
    parsePaxMtime (toString n) offset = .ok n := by
  rcases toString_toUTF8_bytes_eq (n := n) with ⟨ds, hdigs, hne, _, hstr, hfold, _, _⟩
  unfold parsePaxMtime
  rw [hstr]
  have hnot_empty : (ds.map Nat.digitChar).isEmpty = false := by
    cases ds with | nil => exact absurd rfl hne | cons _ _ => rfl
  have hnot_dash : ((ds.map Nat.digitChar).head? == some '-') = false := by
    cases ds with
    | nil => exact absurd rfl hne
    | cons d _ =>
      have hne_dash := (digitChar_props (hdigs d (by simp))).2.2
      have hbeq : (Nat.digitChar d == '-') = false := beq_false_of_ne hne_dash
      simp [hbeq]
  have hall_dig : ∀ c ∈ ds.map Nat.digitChar, ('0' ≤ c && c ≤ '9') = true := by
    intro c hc
    rw [List.mem_map] at hc
    rcases hc with ⟨d, hd, rfl⟩
    have ⟨hlo, hhi⟩ := (digitChar_props (hdigs d hd)).1
    simp [hlo, hhi]
  have htake : (ds.map Nat.digitChar).takeWhile (fun c => '0' ≤ c && c ≤ '9') = ds.map Nat.digitChar :=
    list_takeWhile_eq_self _ _ hall_dig
  have hdrop : (ds.map Nat.digitChar).drop ds.length = [] := by simp
  have hfold_chars : (ds.map Nat.digitChar).foldl (fun acc c => acc * 10 + (c.toNat - '0'.toNat)) 0 = n := by
    rw [foldl_digitChar_eq ds hdigs 0, hfold]
  simp only [hnot_empty, hnot_dash, htake, Bool.false_eq_true, ↓reduceIte,
    hdrop, List.length_map, hfold_chars, Nat.not_le_of_lt hn]
  rfl

/-- `findByteIn bs target idx stop` returns `some pos` when bytes `[idx..pos)` avoid `target` and `bs[pos] = target`. -/
theorem findByteIn_eq {bs : ByteArray} {target : UInt8} {idx pos stop : Nat}
    (hle : idx ≤ pos) (hlt : pos < stop) (hbd : stop ≤ bs.size)
    (havoid : ∀ j, idx ≤ j → j < pos → ∀ hj : j < bs.size, bs[j]'hj ≠ target)
    (hhit : bs[pos]'(by omega) = target) :
    findByteIn bs target idx stop = some pos := by
  induction hdiff : pos - idx generalizing idx with
  | zero =>
    have heq : idx = pos := by omega
    subst heq
    rw [findByteIn.eq_1]
    have hnotge : ¬(idx ≥ stop) := by omega
    have hlt_b : idx < bs.size := by omega
    simp [hnotge, hlt_b, hhit]
  | succ d ih =>
    have hlt_pos : idx < pos := by omega
    have hnotge : ¬(idx ≥ stop) := by omega
    have hlt_b : idx < bs.size := by omega
    rw [findByteIn.eq_1]
    have hne : bs[idx]'hlt_b ≠ target := havoid idx (Nat.le_refl _) hlt_pos hlt_b
    have hbeq : (bs[idx]'hlt_b == target) = false := beq_false_of_ne hne
    simp only [hnotge, ↓reduceIte, hlt_b, ↓reduceDIte, hbeq, Bool.false_eq_true]
    exact ih (by omega) (fun j hj1 hj2 hj => havoid j (by omega) hj2 hj) hhit (by omega)

/-- `parsePaxLen` decodes `(toString n).toUTF8` stored at `[pos .. pos + (toString n).toUTF8.size)` when `n > 0`. -/
theorem parsePaxLen_toString {bs : ByteArray} {pos n : Nat} (hn : 0 < n)
    (_hbd : pos + (toString n).toUTF8.size ≤ bs.size)
    (hext : bs.extract pos (pos + (toString n).toUTF8.size) = (toString n).toUTF8) :
    parsePaxLen bs pos (pos + (toString n).toUTF8.size) = some n := by
  rcases toString_toUTF8_bytes_eq (n := n) with ⟨ds, hdigs, hne, hpos, _, hfold, hbytes, hsz⟩
  have hsz_pos : 0 < (toString n).toUTF8.size := by rw [hsz]; cases ds with | nil => exact absurd rfl hne | cons _ _ => simp
  unfold parsePaxLen
  have hnotge : ¬(pos ≥ pos + (toString n).toUTF8.size) := by omega
  simp only [hnotge, ↓reduceIte]
  have hlist : (bs.extract pos (pos + (toString n).toUTF8.size)).toList =
      ds.map (fun d => UInt8.ofNat (0x30 + d)) := by
    rw [hext, hbytes, toByteArray_toList]
  rw [hlist]
  rcases hpos hn with ⟨hd, tl, rfl, hhd_pos⟩
  have hhd_lt : hd < 10 := hdigs hd (by simp)
  have hhd_ne0 : UInt8.ofNat (0x30 + hd) ≠ 0x30 := by
    intro h
    have hn := congrArg UInt8.toNat h
    rw [UInt8.toNat_ofNat', Nat.mod_eq_of_lt (by omega)] at hn
    change 48 + hd = 48 at hn
    omega
  have hall_dig : ((hd :: tl).map (fun d => UInt8.ofNat (0x30 + d))).all
      (fun b => 0x30 ≤ b && b ≤ 0x39) = true := by
    rw [List.all_eq_true]
    intro b hb
    rw [List.mem_map] at hb
    rcases hb with ⟨d, hd_mem, rfl⟩
    have hd_lt := hdigs d hd_mem
    have hlo : (0x30 : UInt8) ≤ UInt8.ofNat (0x30 + d) := by
      change 48 ≤ (UInt8.ofNat (48 + d)).toNat
      rw [UInt8.toNat_ofNat', Nat.mod_eq_of_lt (by omega)]; omega
    have hhi : UInt8.ofNat (0x30 + d) ≤ 0x39 := by
      change (UInt8.ofNat (48 + d)).toNat ≤ 57
      rw [UInt8.toNat_ofNat', Nat.mod_eq_of_lt (by omega)]; omega
    simp only [hlo, hhi, decide_true, Bool.and_self]
  have hfold_bytes : ((hd :: tl).map (fun d => UInt8.ofNat (0x30 + d))).foldl
      (fun acc b => acc * 10 + (b.toNat - 0x30)) 0 = n := by
    rw [← hfold]
    clear hne hpos hfold hbytes hsz hsz_pos hnotge hlist hhd_ne0 hall_dig hext _hbd
    have hgen : ∀ (l : List Nat) (hl : ∀ d ∈ l, d < 10) (init : Nat),
        (l.map (fun d => UInt8.ofNat (0x30 + d))).foldl (fun acc b => acc * 10 + (b.toNat - 0x30)) init =
          l.foldl (fun a d => a * 10 + d) init := by
      intro l
      induction l with
      | nil => intro _ init; simp
      | cons d ds ih =>
        intro hl init
        have hd_lt := hl d (by simp)
        have hsub : (UInt8.ofNat (0x30 + d)).toNat - 0x30 = d := by
          rw [UInt8.toNat_ofNat', Nat.mod_eq_of_lt (by omega)]; omega
        simp only [List.map_cons, List.foldl_cons, hsub]
        exact ih (fun x hx => hl x (by simp [hx])) _
    exact hgen (hd :: tl) hdigs 0
  have hbeq : (UInt8.ofNat (0x30 + hd) == 0x30) = false := beq_false_of_ne hhd_ne0
  rw [List.map_cons] at hall_dig hfold_bytes
  simp only [List.map_cons, hbeq, Bool.false_eq_true, ↓reduceIte, hall_dig, Bool.not_true, hfold_bytes]

private theorem byteArray_getElem_of_eq {a b : ByteArray} (h : a = b) {i : Nat}
    (ha : i < a.size) (hb : i < b.size) : a[i]'ha = b[i]'hb := by
  subst h; rfl

private theorem byteArray_getElem_of_idx {a b : ByteArray} {i j : Nat}
    (ha : a = b) (hij : i = j) (hi : i < a.size) (hj : j < b.size) :
    a[i]'hi = b[j]'hj := by
  subst ha hij; rfl

private theorem byteArray_append_getElem_left {a b : ByteArray} {i : Nat}
    (hi : i < a.size) {hab : i < (a ++ b).size} :
    (a ++ b)[i]'hab = a[i]'hi := getElem_append_left hi

private theorem byteArray_append_getElem_right {a b : ByteArray} {i k : Nat}
    (hk : i = a.size + k) (hkb : k < b.size) {hab : i < (a ++ b).size} :
    (a ++ b)[i]'hab = b[k]'hkb := by
  subst hk
  rw [getElem_append_right (Nat.le_add_right _ _)]
  exact byteArray_getElem_of_idx rfl (Nat.add_sub_cancel_left _ _) _ hkb

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
  · have hsp1 : " ".toUTF8.size = 1 := rfl
    have heq1 : "=".toUTF8.size = 1 := rfl
    have hnl1 : "\n".toUTF8.size = 1 := rfl
    have hsuf_sz : (" " ++ key ++ "=" ++ value ++ "\n").toUTF8.size =
        1 + key.toUTF8.size + 1 + value.toUTF8.size + 1 := by
      simp only [toUTF8_size_append, hsp1, heq1, hnl1, Nat.add_assoc]
    have hlen_digits : decDigitsLen (paxRecordTotalLen (" " ++ key ++ "=" ++ value ++ "\n").toUTF8.size) =
        (toString (paxRecordTotalLen (" " ++ key ++ "=" ++ value ++ "\n").toUTF8.size)).toUTF8.size := rfl
    omega
  · rw [encodePaxRecord, toUTF8_size_append]
    exact hfix.symm

/-- Execute one `parsePaxPayload.go` step on a prefixed `encodePaxRecord key value`. -/
theorem parsePaxPayload_go_step {bs rest : ByteArray} {offset pos : Nat}
    {seenKeys : List String} {ov nextOv : PaxOverrides} {key value : String}
    (hkvMin : 4 ≤ (" " ++ key ++ "=" ++ value ++ "\n").toUTF8.size)
    (hkvMax : (" " ++ key ++ "=" ++ value ++ "\n").toUTF8.size ≤ maxPaxHeaderBytes)
    (hkey_ne : !key.isEmpty = true) (hkey_nul : !hasNulString key = true)
    (hkey_nl : !key.toList.contains '\n' = true)
    (hkey_eq : (0x3d : UInt8) ∉ key.toUTF8.toList)
    (hnot_seen : !seenKeys.contains key = true)
    (hnot_sparse : !startsWithStr key "GNU.sparse." = true)
    (happly : applyPaxKey ov key value offset = .ok nextOv)
    (hsuf : bs.extract pos bs.size = encodePaxRecord key value ++ rest) :
    parsePaxPayload.go bs offset pos seenKeys ov =
      parsePaxPayload.go bs offset (pos + (encodePaxRecord key value).size) (key :: seenKeys) nextOv := by
  rcases encodePaxRecord_parts hkvMin hkvMax with ⟨recLen, hrecLen_eq, hge5, hrec_eq, hrec_sz⟩
  have hpos_le : pos ≤ bs.size := by
    rcases Nat.lt_or_ge bs.size pos with hlt | hle
    · have h0 : (bs.extract pos bs.size).size = 0 := by rw [ByteArray.size_extract]; omega
      rw [hsuf, ByteArray.size_append, hrec_sz] at h0
      omega
    · exact hle
  have hsz_suf : (bs.extract pos bs.size).size = bs.size - pos := by
    rw [ByteArray.size_extract]; omega
  have hbd_rec : pos + recLen ≤ bs.size := by
    have h1 := congrArg ByteArray.size hsuf
    rw [hsz_suf, ByteArray.size_append, hrec_sz] at h1
    omega
  have hnotge_pos : ¬(pos ≥ bs.size) := by omega
  have hget_bs : ∀ (j : Nat) (hj : j < recLen),
      bs[pos + j]'(by omega) = (encodePaxRecord key value)[j]'(by rw [hrec_sz]; exact hj) := by
    intro j hj
    have hidx_e : j < (bs.extract pos bs.size).size := by rw [hsz_suf]; omega
    have h1 := ByteArray.getElem_extract hidx_e
    have hidx_app : j < (encodePaxRecord key value ++ rest).size := by
      rw [ByteArray.size_append, hrec_sz]; omega
    have hfun := congrArg (fun ba : ByteArray => if h : j < ba.size then ba[j]'h else 0) hsuf
    simp only [hidx_e, hidx_app, ↓reduceDIte] at hfun
    rw [← h1, hfun, getElem_append_left (by rw [hrec_sz]; exact hj)]
  let d := (toString recLen).toUTF8.size
  rcases toString_toUTF8_bytes_eq (n := recLen) with ⟨ds, hdigs, _, _, _, _, hbytes_rec, _⟩
  have hrec_utf8_eq : encodePaxRecord key value =
      (toString recLen).toUTF8 ++ (" " ++ key ++ "=" ++ value ++ "\n").toUTF8 := by
    rw [hrec_eq, toUTF8_append]
  have hrec_utf8_sz : ((toString recLen).toUTF8 ++ (" " ++ key ++ "=" ++ value ++ "\n").toUTF8).size = recLen := by
    rw [← hrec_utf8_eq, hrec_sz]
  have havoid_sp : ∀ j, pos ≤ j → j < pos + d → ∀ hj : j < bs.size, bs[j]'hj ≠ 0x20 := by
    intro j hj1 hj2 hj
    let k := j - pos
    have hk_lt : k < d := by omega
    have hj_eq : j = pos + k := by omega
    have hk_rec : k < recLen := by rw [hrecLen_eq]; omega
    have hbsj : bs[j]'hj = (encodePaxRecord key value)[k]'(by rw [hrec_sz]; exact hk_rec) := by
      simpa [hj_eq] using hget_bs k hk_rec
    rw [hbsj, byteArray_getElem_of_eq hrec_utf8_eq _ (by rw [hrec_utf8_sz]; exact hk_rec),
      getElem_append_left hk_lt]
    have hk_ba : k < (ds.map (fun d => UInt8.ofNat (0x30 + d))).toByteArray.size := by
      rw [← hbytes_rec]; exact hk_lt
    rw [byteArray_getElem_of_eq hbytes_rec hk_lt hk_ba, List.getElem_toByteArray]
    have hmem : (ds.map (fun d => UInt8.ofNat (0x30 + d)))[k]'(by
        rw [← List.size_toByteArray]; exact hk_ba) ∈ ds.map (fun d => UInt8.ofNat (0x30 + d)) :=
      List.getElem_mem _
    rw [List.mem_map] at hmem
    rcases hmem with ⟨dig, hdig_mem, hdig_eq⟩
    have hdig_lt := hdigs dig hdig_mem
    intro heq20
    have hn := congrArg UInt8.toNat (hdig_eq.trans heq20)
    rw [UInt8.toNat_ofNat', Nat.mod_eq_of_lt (by omega)] at hn
    change 48 + dig = 32 at hn
    omega
  have hsp_idx : bs[pos + d]'(by omega) = 0x20 := by
    have hd_rec : d < recLen := by omega
    rw [hget_bs d hd_rec, byteArray_getElem_of_eq hrec_utf8_eq _ (by rw [hrec_utf8_sz]; exact hd_rec)]
    have hsp_eq : (" " ++ key ++ "=" ++ value ++ "\n").toUTF8 =
        " ".toUTF8 ++ (key ++ "=" ++ value ++ "\n").toUTF8 := by
      simp only [toUTF8_append, ByteArray.append_assoc]
    have hrem_sz : (" " ++ key ++ "=" ++ value ++ "\n").toUTF8.size =
        1 + key.toUTF8.size + 1 + value.toUTF8.size + 1 := by
      have hsp1 : " ".toUTF8.size = 1 := rfl
      have heq1 : "=".toUTF8.size = 1 := rfl
      have hnl1 : "\n".toUTF8.size = 1 := rfl
      simp only [toUTF8_size_append, hsp1, heq1, hnl1, Nat.add_assoc]
    have hidx0 : d = (toString recLen).toUTF8.size + 0 := (Nat.add_zero d).symm
    rw [byteArray_append_getElem_right hidx0 (by rw [hrem_sz]; omega)]
    rw [byteArray_getElem_of_eq hsp_eq _ (by rw [← hsp_eq, hrem_sz]; omega),
      byteArray_append_getElem_left (by decide : 0 < " ".toUTF8.size)]
    rfl
  have hfind_sp : findByteIn bs 0x20 pos bs.size = some (pos + d) :=
    findByteIn_eq (by omega) (by omega) (Nat.le_refl _) havoid_sp hsp_idx
  have hext_len : bs.extract pos (pos + d) = (toString recLen).toUTF8 := by
    apply ByteArray.ext
    · apply Array.ext
      · show (bs.extract pos (pos + d)).size = (toString recLen).toUTF8.size
        rw [ByteArray.size_extract]; omega
      · intro i hi1 hi2
        have hi1' : i < (bs.extract pos (pos + d)).size := hi1
        have hi2' : i < d := hi2
        rw [← ByteArray.getElem_eq_getElem_data (h := hi1'),
          ← ByteArray.getElem_eq_getElem_data (h := hi2'), ByteArray.getElem_extract]
        have hi_rec : i < recLen := by omega
        rw [hget_bs i hi_rec, byteArray_getElem_of_eq hrec_utf8_eq _ (by rw [hrec_utf8_sz]; exact hi_rec),
          getElem_append_left hi2']
  have hparse_len : parsePaxLen bs pos (pos + d) = some recLen :=
    parsePaxLen_toString (by omega) (by omega) hext_len
  have hnl_idx : bs[pos + recLen - 1]'(by omega) = 0x0a := by
    have hlt_rec : recLen - 1 < recLen := by omega
    have hpref_sz : (" " ++ key ++ "=" ++ value).toUTF8.size = 1 + key.toUTF8.size + 1 + value.toUTF8.size := by
      have hsp1 : " ".toUTF8.size = 1 := rfl
      have heq1 : "=".toUTF8.size = 1 := rfl
      simp only [toUTF8_size_append, hsp1, heq1]
    have hsuf_nl : (" " ++ key ++ "=" ++ value ++ "\n").toUTF8 =
        (" " ++ key ++ "=" ++ value).toUTF8 ++ "\n".toUTF8 := by
      simp only [toUTF8_append, ByteArray.append_assoc]
    have hnl1 : "\n".toUTF8.size = 1 := rfl
    have hrem_sz : (" " ++ key ++ "=" ++ value ++ "\n").toUTF8.size =
        (" " ++ key ++ "=" ++ value).toUTF8.size + "\n".toUTF8.size := by
      rw [hsuf_nl, ByteArray.size_append]
    rw [byteArray_getElem_of_idx rfl (by omega : pos + recLen - 1 = pos + (recLen - 1)) _ (by omega)]
    rw [hget_bs (recLen - 1) hlt_rec,
      byteArray_getElem_of_eq hrec_utf8_eq _ (by rw [hrec_utf8_sz]; exact hlt_rec),
      byteArray_append_getElem_right (by omega : recLen - 1 = (toString recLen).toUTF8.size + (" " ++ key ++ "=" ++ value).toUTF8.size)
        (by rw [hrem_sz, hnl1]; omega)]
    have hidx0 : (" " ++ key ++ "=" ++ value).toUTF8.size = (" " ++ key ++ "=" ++ value).toUTF8.size + 0 :=
      (Nat.add_zero _).symm
    rw [byteArray_getElem_of_eq hsuf_nl _ (by rw [ByteArray.size_append, hnl1]; omega),
      byteArray_append_getElem_right hidx0 (by decide : 0 < "\n".toUTF8.size)]
    rfl
  let eqPos := pos + d + 1 + key.toUTF8.size
  have havoid_eq : ∀ j, pos + d + 1 ≤ j → j < eqPos → ∀ hj : j < bs.size, bs[j]'hj ≠ 0x3d := by
    intro j hj1 hj2 hj
    let k := j - (pos + d + 1)
    have hk_key : k < key.toUTF8.size := by omega
    have hj_rec : j - pos < recLen := by omega
    have hbsj : bs[j]'hj = (encodePaxRecord key value)[j - pos]'(by rw [hrec_sz]; exact hj_rec) := by
      rw [byteArray_getElem_of_idx rfl (by omega : j = pos + (j - pos)) hj (by omega)]
      exact hget_bs (j - pos) hj_rec
    have hsuf_k : (" " ++ key ++ "=" ++ value ++ "\n").toUTF8 =
        " ".toUTF8 ++ (key.toUTF8 ++ ("=".toUTF8 ++ (value ++ "\n").toUTF8)) := by
      simp only [toUTF8_append, ByteArray.append_assoc]
    have hsp1 : " ".toUTF8.size = 1 := rfl
    have hrem_sz : (" " ++ key ++ "=" ++ value ++ "\n").toUTF8.size =
        1 + (key.toUTF8.size + (1 + value.toUTF8.size + 1)) := by
      have heq1 : "=".toUTF8.size = 1 := rfl
      have hnl1 : "\n".toUTF8.size = 1 := rfl
      simp only [toUTF8_size_append, hsp1, heq1, hnl1, Nat.add_assoc]
    rw [hbsj, byteArray_getElem_of_eq hrec_utf8_eq _ (by rw [hrec_utf8_sz]; exact hj_rec),
      byteArray_append_getElem_right (by omega : j - pos = (toString recLen).toUTF8.size + (1 + k)) (by rw [hrem_sz]; omega)]
    rw [byteArray_getElem_of_eq hsuf_k _ (by rw [← hsuf_k, hrem_sz]; omega)]
    have htail_sz : (key.toUTF8 ++ ("=".toUTF8 ++ (value ++ "\n").toUTF8)).size =
        key.toUTF8.size + (1 + value.toUTF8.size + 1) := by
      have heq1 : "=".toUTF8.size = 1 := rfl
      have hnl1 : "\n".toUTF8.size = 1 := rfl
      simp only [ByteArray.size_append, toUTF8_size_append, heq1, hnl1, Nat.add_assoc]
    rw [byteArray_append_getElem_right (by rw [hsp1] : 1 + k = " ".toUTF8.size + k) (by rw [htail_sz]; omega),
      getElem_append_left hk_key]
    intro heq3d
    apply hkey_eq
    have hi_ba : k < (key.toList.flatMap String.utf8EncodeChar).toByteArray.size := by
      rw [← toUTF8_eq_toByteArray]; exact hk_key
    rw [toUTF8_toList, ← heq3d, byteArray_getElem_of_eq (toUTF8_eq_toByteArray key) hk_key hi_ba,
      List.getElem_toByteArray]
    exact List.getElem_mem _
  have heq_idx : bs[eqPos]'(by omega) = 0x3d := by
    have heq_rec : eqPos - pos < recLen := by omega
    rw [byteArray_getElem_of_idx rfl (by omega : eqPos = pos + (eqPos - pos)) (by omega) (by omega),
      hget_bs (eqPos - pos) heq_rec,
      byteArray_getElem_of_eq hrec_utf8_eq _ (by rw [hrec_utf8_sz]; exact heq_rec)]
    have hsuf_k : (" " ++ key ++ "=" ++ value ++ "\n").toUTF8 =
        (" " ++ key).toUTF8 ++ ("=".toUTF8 ++ (value ++ "\n").toUTF8) := by
      simp only [toUTF8_append, ByteArray.append_assoc]
    have hsp_key : (" " ++ key).toUTF8.size = 1 + key.toUTF8.size := by
      rw [toUTF8_size_append]; rfl
    have heq_tail_sz : ("=".toUTF8 ++ (value ++ "\n").toUTF8).size = 1 + value.toUTF8.size + 1 := by
      have heq1 : "=".toUTF8.size = 1 := rfl
      have hnl1 : "\n".toUTF8.size = 1 := rfl
      simp only [ByteArray.size_append, toUTF8_size_append, heq1, hnl1, Nat.add_assoc]
    have hrem_sz : (" " ++ key ++ "=" ++ value ++ "\n").toUTF8.size =
        (" " ++ key).toUTF8.size + ("=".toUTF8 ++ (value ++ "\n").toUTF8).size := by
      rw [hsuf_k, ByteArray.size_append]
    rw [byteArray_append_getElem_right (by omega : eqPos - pos = (toString recLen).toUTF8.size + (" " ++ key).toUTF8.size)
      (by rw [hrem_sz, heq_tail_sz]; omega)]
    have hidx0 : (" " ++ key).toUTF8.size = (" " ++ key).toUTF8.size + 0 := (Nat.add_zero _).symm
    rw [byteArray_getElem_of_eq hsuf_k _ (by rw [ByteArray.size_append, heq_tail_sz]; omega),
      byteArray_append_getElem_right hidx0 (by rw [heq_tail_sz]; omega),
      byteArray_append_getElem_left (by decide : 0 < "=".toUTF8.size)]
    rfl
  have hfind_eq : findByteIn bs 0x3d (pos + d + 1) (pos + recLen - 1) = some eqPos :=
    findByteIn_eq (by omega) (by omega) (by omega) havoid_eq heq_idx
  have hext_key : bs.extract (pos + d + 1) eqPos = key.toUTF8 := by
    apply ByteArray.ext; apply Array.ext
    · show (bs.extract (pos + d + 1) eqPos).size = key.toUTF8.size
      rw [ByteArray.size_extract]; omega
    · intro i hi1 hi2
      have hi1' : i < (bs.extract (pos + d + 1) eqPos).size := hi1
      have hi2' : i < key.toUTF8.size := hi2
      rw [← ByteArray.getElem_eq_getElem_data (h := hi1'),
        ← ByteArray.getElem_eq_getElem_data (h := hi2'), ByteArray.getElem_extract]
      have hj_rec : d + 1 + i < recLen := by omega
      rw [byteArray_getElem_of_idx rfl (by omega : pos + d + 1 + i = pos + (d + 1 + i)) _ (by omega),
        hget_bs (d + 1 + i) hj_rec,
        byteArray_getElem_of_eq hrec_utf8_eq _ (by rw [hrec_utf8_sz]; exact hj_rec)]
      have hsuf_k : (" " ++ key ++ "=" ++ value ++ "\n").toUTF8 =
          " ".toUTF8 ++ (key.toUTF8 ++ ("=".toUTF8 ++ (value ++ "\n").toUTF8)) := by
        simp only [toUTF8_append, ByteArray.append_assoc]
      have hsp1 : " ".toUTF8.size = 1 := rfl
      have hrem_sz : (" " ++ key ++ "=" ++ value ++ "\n").toUTF8.size =
          1 + (key.toUTF8.size + (1 + value.toUTF8.size + 1)) := by
        have heq1 : "=".toUTF8.size = 1 := rfl
        have hnl1 : "\n".toUTF8.size = 1 := rfl
        simp only [toUTF8_size_append, hsp1, heq1, hnl1, Nat.add_assoc]
      rw [byteArray_append_getElem_right (by omega : d + 1 + i = (toString recLen).toUTF8.size + (1 + i))
        (by rw [hrem_sz]; omega),
        byteArray_getElem_of_eq hsuf_k _ (by rw [← hsuf_k, hrem_sz]; omega)]
      have htail_sz : (key.toUTF8 ++ ("=".toUTF8 ++ (value ++ "\n").toUTF8)).size =
          key.toUTF8.size + (1 + value.toUTF8.size + 1) := by
        have heq1 : "=".toUTF8.size = 1 := rfl
        have hnl1 : "\n".toUTF8.size = 1 := rfl
        simp only [ByteArray.size_append, toUTF8_size_append, heq1, hnl1, Nat.add_assoc]
      rw [byteArray_append_getElem_right (by rw [hsp1] : 1 + i = " ".toUTF8.size + i) (by rw [htail_sz]; omega),
        getElem_append_left hi2']
  have hext_val : bs.extract (eqPos + 1) (pos + recLen - 1) = value.toUTF8 := by
    apply ByteArray.ext; apply Array.ext
    · show (bs.extract (eqPos + 1) (pos + recLen - 1)).size = value.toUTF8.size
      rw [ByteArray.size_extract]; omega
    · intro i hi1 hi2
      have hi1' : i < (bs.extract (eqPos + 1) (pos + recLen - 1)).size := hi1
      have hi2' : i < value.toUTF8.size := hi2
      rw [← ByteArray.getElem_eq_getElem_data (h := hi1'),
        ← ByteArray.getElem_eq_getElem_data (h := hi2'), ByteArray.getElem_extract]
      have hj_rec : d + 1 + key.toUTF8.size + 1 + i < recLen := by omega
      rw [byteArray_getElem_of_idx rfl (by omega : eqPos + 1 + i = pos + (d + 1 + key.toUTF8.size + 1 + i)) _ (by omega),
        hget_bs (d + 1 + key.toUTF8.size + 1 + i) hj_rec,
        byteArray_getElem_of_eq hrec_utf8_eq _ (by rw [hrec_utf8_sz]; exact hj_rec)]
      have hsuf_k : (" " ++ key ++ "=" ++ value ++ "\n").toUTF8 =
          (" " ++ key ++ "=").toUTF8 ++ (value.toUTF8 ++ "\n".toUTF8) := by
        simp only [toUTF8_append, ByteArray.append_assoc]
      have hpre_sz : (" " ++ key ++ "=").toUTF8.size = 1 + key.toUTF8.size + 1 := by
        rw [toUTF8_size_append, toUTF8_size_append]; rfl
      have hrem_sz : (" " ++ key ++ "=" ++ value ++ "\n").toUTF8.size =
          (" " ++ key ++ "=").toUTF8.size + (value.toUTF8.size + 1) := by
        have hnl1 : "\n".toUTF8.size = 1 := rfl
        rw [hsuf_k, ByteArray.size_append, ByteArray.size_append, hnl1]
      have hvalnl_sz : (value.toUTF8 ++ "\n".toUTF8).size = value.toUTF8.size + 1 := by
        have hnl1 : "\n".toUTF8.size = 1 := rfl
        rw [ByteArray.size_append, hnl1]
      rw [byteArray_append_getElem_right (by omega : d + 1 + key.toUTF8.size + 1 + i =
        (toString recLen).toUTF8.size + ((" " ++ key ++ "=").toUTF8.size + i))
        (by rw [hrem_sz, hpre_sz]; omega),
        byteArray_getElem_of_eq hsuf_k _ (by rw [← hsuf_k, hrem_sz]; omega),
        byteArray_append_getElem_right (by omega : (" " ++ key ++ "=").toUTF8.size + i =
          (" " ++ key ++ "=").toUTF8.size + i) (by rw [hvalnl_sz]; omega),
        getElem_append_left hi2']
  have hnl_bd : pos + recLen - 1 < bs.size := by omega
  rw [parsePaxPayload.go.eq_1]
  simp only [hnotge_pos, ↓reduceIte, hfind_sp, hparse_len, Nat.not_lt_of_ge hge5,
    Nat.not_lt_of_ge hbd_rec, hnl_bd, ↓reduceDIte, Bool.not_true, Bool.false_eq_true,
    hnl_idx, beq_self_eq_true, hfind_eq, hext_key, hext_val, fromUTF8?_toUTF8]
  have hkey_invalid : (key.isEmpty || hasNulString key || key.toList.contains '\n') = false := by
    have h1 : key.isEmpty = false := Bool.eq_false_iff.mpr (by simpa using hkey_ne)
    have h2 : hasNulString key = false := Bool.eq_false_iff.mpr (by simpa using hkey_nul)
    have h3 : key.toList.contains '\n' = false := Bool.eq_false_iff.mpr (by simpa using hkey_nl)
    rw [h1, h2, h3]
    rfl
  have hseen_false : seenKeys.contains key = false :=
    Bool.eq_false_iff.mpr (by simpa using hnot_seen)
  have hsparse_false : startsWithStr key "GNU.sparse." = false :=
    Bool.eq_false_iff.mpr (by simpa using hnot_sparse)
  simp only [hkey_invalid, hseen_false, hsparse_false, Bool.false_eq_true, ↓reduceIte, happly]
  rw [hrec_sz]

end LeanSwe.Tar.Proofs
