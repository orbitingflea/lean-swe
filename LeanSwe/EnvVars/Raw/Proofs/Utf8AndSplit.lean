import LeanSwe.EnvVars.Raw.Types
import LeanSwe.EnvVars.Raw.Model
import LeanSwe.EnvVars.Raw.Interface
import LeanSwe.EnvVars.Raw.Impl
import LeanSwe.EnvVars.Raw.SpecTests

namespace LeanSwe.EnvVars.Raw.Proofs

open Core
open Core.NondetTest

/-- Non-empty fallback guarantees a non-empty `Internal.nonEmptyMsg` result. -/
theorem nonEmptyMsg_ne_empty (fallback msg : String) (hf : fallback ≠ "") :
    Internal.nonEmptyMsg fallback msg ≠ "" := by
  unfold Internal.nonEmptyMsg
  split
  · exact hf
  · next h =>
    intro hem
    subst hem
    simp [String.isEmpty] at h

/-- Appending onto a non-empty string prefix yields a non-empty string. -/
theorem append_head_ne_empty (pre rest : String) (hp : pre ≠ "") :
    pre ++ rest ≠ "" := by
  simp [String.append_eq_empty_iff, hp]

private theorem hasInvalidKeyChar_iff (cs : List Char) :
    Internal.hasInvalidKeyChar cs = true ↔ '=' ∈ cs ∨ Char.ofNat 0 ∈ cs := by
  induction cs with
  | nil => simp [Internal.hasInvalidKeyChar]
  | cons c rest ih =>
    simp only [Internal.hasInvalidKeyChar, Bool.or_eq_true, beq_iff_eq, List.mem_cons, ih]
    constructor
    · intro h
      rcases h with (h1 | h2) | h3 | h4
      · exact Or.inl (Or.inl h1.symm)
      · exact Or.inr (Or.inl h2.symm)
      · exact Or.inl (Or.inr h3)
      · exact Or.inr (Or.inr h4)
    · intro h
      rcases h with (h1 | h2) | (h3 | h4)
      · exact Or.inl (Or.inl h1.symm)
      · exact Or.inr (Or.inl h2)
      · exact Or.inl (Or.inr h3.symm)
      · exact Or.inr (Or.inr h4)

/-- Characterization of `Internal.isValidPosixKey key = true`. -/
theorem isValidPosixKey_true_iff (key : String) :
    Internal.isValidPosixKey key = true ↔ key ≠ "" ∧ '=' ∉ key.toList ∧ Char.ofNat 0 ∉ key.toList := by
  unfold Internal.isValidPosixKey
  rw [Bool.and_eq_true, Bool.not_eq_true', Bool.not_eq_true']
  have hne : key.isEmpty = false ↔ key ≠ "" := by
    constructor
    · intro hf heq
      subst heq
      simp [String.isEmpty] at hf
    · intro hne
      cases hk : key.isEmpty with
      | false => rfl
      | true =>
        exfalso
        apply hne
        exact String.isEmpty_iff.mp hk
  have hmem : Internal.hasInvalidKeyChar key.toList = false ↔
      '=' ∉ key.toList ∧ Char.ofNat 0 ∉ key.toList := by
    constructor
    · intro hf
      refine ⟨?_, ?_⟩
      · intro heq
        have ht := (hasInvalidKeyChar_iff key.toList).mpr (Or.inl heq)
        rw [hf] at ht
        cases ht
      · intro hnul
        have ht := (hasInvalidKeyChar_iff key.toList).mpr (Or.inr hnul)
        rw [hf] at ht
        cases ht
    · intro ⟨h1, h2⟩
      cases h : Internal.hasInvalidKeyChar key.toList with
      | false => rfl
      | true =>
        rcases (hasInvalidKeyChar_iff key.toList).mp h with heq | hnul
        · exact absurd heq h1
        · exact absurd hnul h2
  rw [hne, hmem]

/-- Characterization of `Internal.isValidPosixKey key = false`. -/
theorem isValidPosixKey_false_iff (key : String) :
    Internal.isValidPosixKey key = false ↔ key = "" ∨ '=' ∈ key.toList ∨ Char.ofNat 0 ∈ key.toList := by
  cases hk : Internal.isValidPosixKey key with
  | true =>
    have ht := (isValidPosixKey_true_iff key).mp hk
    constructor
    · intro h; cases h
    · intro h
      rcases h with h1 | h2 | h3
      · exact absurd h1 ht.1
      · exact absurd h2 ht.2.1
      · exact absurd h3 ht.2.2
  | false =>
    constructor
    · intro _
      by_cases h1 : key = ""
      · exact Or.inl h1
      · by_cases h2 : '=' ∈ key.toList
        · exact Or.inr (Or.inl h2)
        · by_cases h3 : Char.ofNat 0 ∈ key.toList
          · exact Or.inr (Or.inr h3)
          · have ht := (isValidPosixKey_true_iff key).mpr ⟨h1, h2, h3⟩
            rw [hk] at ht
            cases ht
    · intro _; rfl

/-- Round-trip UTF-8 decoding of `s.toUTF8`. -/
theorem fromUTF8?_toUTF8 (s : String) : String.fromUTF8? s.toUTF8 = some s := by
  simp [String.fromUTF8?, String.toUTF8, s.isValidUTF8]

/-- `String.fromUTF8? bs = some s` holds iff `bs = s.toUTF8`. -/
theorem fromUTF8?_eq_some_iff (bs : ByteArray) (s : String) :
    String.fromUTF8? bs = some s ↔ bs = s.toUTF8 := by
  constructor
  · intro h
    unfold String.fromUTF8? at h
    split at h
    · injection h with hs
      subst hs
      rfl
    · cases h
  · intro h
    subst h
    exact fromUTF8?_toUTF8 s

private theorem toUTF8_eq_toByteArray (s : String) :
    s.toUTF8 = (s.toList.flatMap String.utf8EncodeChar).toByteArray := by
  conv => lhs; rw [← String.ofList_toList (s := s), String.toUTF8, String.toByteArray_ofList]
  rfl

private theorem data_toList_toByteArray (l : List UInt8) :
    l.toByteArray.data.toList = l := by
  apply List.ext_getElem
  · rw [Array.length_toList, ← ByteArray.size, List.size_toByteArray]
  · intro i hi1 _
    have hi : i < l.toByteArray.size := by rw [ByteArray.size]; exact hi1
    rw [Array.getElem_toList, ← ByteArray.getElem_eq_getElem_data (h := hi), List.getElem_toByteArray]

private theorem toUTF8_data_toList (s : String) :
    s.toUTF8.data.toList = s.toList.flatMap String.utf8EncodeChar := by
  rw [toUTF8_eq_toByteArray, data_toList_toByteArray]

private theorem zero_not_mem_utf8EncodeChar {c : Char} (hc : c ≠ Char.ofNat 0) :
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

private theorem eqByte_not_mem_utf8EncodeChar {c : Char} (hc : c ≠ '=') :
    (0x3D : UInt8) ∉ String.utf8EncodeChar c := by
  have hne : c.toNat ≠ 0x3D := by
    intro h0
    apply hc
    rw [Char.ext_iff, ← UInt32.toNat_inj]
    exact h0
  unfold String.utf8EncodeChar
  dsimp only
  split
  · simp only [List.mem_singleton]
    intro heq
    have hnat : (UInt8.ofNat c.val.toNat).toNat = (0x3D : UInt8).toNat := congrArg UInt8.toNat heq.symm
    have hlt : c.val.toNat ≤ 127 := ‹_›
    rw [UInt8.toNat_ofNat', Nat.mod_eq_of_lt (by omega)] at hnat
    change c.val.toNat = 0x3D at hnat
    have hcnat : c.toNat = c.val.toNat := rfl
    omega
  · split
    · simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro (h | h) <;>
        (have hn := congrArg UInt8.toNat h; rw [UInt8.toNat_ofNat'] at hn; change (0x3D : Nat) = _ at hn; omega)
    · split
      · simp only [List.mem_cons, List.not_mem_nil, or_false]
        rintro (h | h | h) <;>
          (have hn := congrArg UInt8.toNat h; rw [UInt8.toNat_ofNat'] at hn; change (0x3D : Nat) = _ at hn; omega)
      · simp only [List.mem_cons, List.not_mem_nil, or_false]
        rintro (h | h | h | h) <;>
          (have hn := congrArg UInt8.toNat h; rw [UInt8.toNat_ofNat'] at hn; change (0x3D : Nat) = _ at hn; omega)

/-- Byte `0x3D` (`'='`) occurs in `s.toUTF8` iff `'=' ∈ s.toList`. -/
theorem eqByte_mem_toUTF8_iff (s : String) :
    (0x3D : UInt8) ∈ s.toUTF8.data.toList ↔ '=' ∈ s.toList := by
  rw [toUTF8_data_toList, List.mem_flatMap]
  constructor
  · rintro ⟨c, hc, hmem⟩
    by_cases hce : c = '='
    · exact hce ▸ hc
    · exact False.elim (eqByte_not_mem_utf8EncodeChar hce hmem)
  · intro hmem
    refine ⟨'=', hmem, ?_⟩
    show (0x3D : UInt8) ∈ String.utf8EncodeChar '='
    decide

/-- Byte `0x00` occurs in `s.toUTF8` iff `Char.ofNat 0 ∈ s.toList`. -/
theorem zeroByte_mem_toUTF8_iff (s : String) :
    (0 : UInt8) ∈ s.toUTF8.data.toList ↔ Char.ofNat 0 ∈ s.toList := by
  rw [toUTF8_data_toList, List.mem_flatMap]
  constructor
  · rintro ⟨c, hc, hmem⟩
    by_cases hce : c = Char.ofNat 0
    · exact hce ▸ hc
    · exact False.elim (zero_not_mem_utf8EncodeChar hce hmem)
  · intro hmem
    refine ⟨Char.ofNat 0, hmem, ?_⟩
    show (0 : UInt8) ∈ String.utf8EncodeChar (Char.ofNat 0)
    decide

/-- `s.toUTF8` is non-empty iff `s ≠ ""`. -/
theorem toUTF8_data_ne_nil_iff (s : String) :
    s.toUTF8.data.toList ≠ [] ↔ s ≠ "" := by
  constructor
  · intro hne heq
    subst heq
    exact hne rfl
  · intro hne hl
    apply hne
    have hsz : s.utf8ByteSize = 0 := by
      change s.toByteArray.size = 0
      change s.toUTF8.data.size = 0
      rw [← Array.length_toList, hl]
      rfl
    exact String.utf8ByteSize_eq_zero_iff.mp hsz

private theorem splitFirstEqList_append_eq (revPre ks vs : List UInt8)
    (hno : (0x3D : UInt8) ∉ ks) (hne : revPre ≠ [] ∨ ks ≠ []) :
    Internal.splitFirstEqList revPre (ks ++ (0x3D : UInt8) :: vs) =
      some (ByteArray.mk (revPre.reverse ++ ks).toArray, ByteArray.mk vs.toArray) := by
  induction ks generalizing revPre with
  | nil =>
    have hrev : revPre ≠ [] := by rcases hne with h | h; exact h; exact absurd rfl h
    have hem : revPre.isEmpty = false := by
      cases revPre with
      | nil => contradiction
      | cons _ _ => rfl
    simp [Internal.splitFirstEqList, hem]
  | cons b rest ih =>
    have hbne : b ≠ (0x3D : UInt8) := fun heq => hno (heq ▸ List.mem_cons_self)
    have hno' : (0x3D : UInt8) ∉ rest := fun hm => hno (List.mem_cons_of_mem b hm)
    have hbeq : (b == (0x3D : UInt8)) = false := beq_false_of_ne hbne
    have ih' := ih (b :: revPre) hno' (Or.inl (by simp))
    simp only [List.cons_append, Internal.splitFirstEqList, hbeq, Bool.false_eq_true, ↓reduceIte]
    rw [ih']
    simp [List.reverse_cons, List.append_assoc]

private theorem splitFirstEqList_of_no_eq (revPre bs : List UInt8) (hno : (0x3D : UInt8) ∉ bs) :
    Internal.splitFirstEqList revPre bs = none := by
  induction bs generalizing revPre with
  | nil => simp [Internal.splitFirstEqList]
  | cons b rest ih =>
    have hbne : b ≠ (0x3D : UInt8) := fun heq => hno (heq ▸ List.mem_cons_self)
    have hno' : (0x3D : UInt8) ∉ rest := fun hm => hno (List.mem_cons_of_mem b hm)
    have hbeq : (b == (0x3D : UInt8)) = false := beq_false_of_ne hbne
    simp [Internal.splitFirstEqList, hbeq, ih (b :: revPre) hno']

private theorem splitFirstEqBytes_mal (mal : ByteArray)
    (h : !(mal.data.toList.contains (0x3D : UInt8)) = true ∨ mal.data.toList.head? == some (0x3D : UInt8)) :
    Internal.splitFirstEqBytes mal = none := by
  unfold Internal.splitFirstEqBytes
  rcases h with hno | hhead
  · have hno' : (0x3D : UInt8) ∉ mal.data.toList := by
      intro hm
      have hc : mal.data.toList.contains (0x3D : UInt8) = true := List.contains_iff_mem.mpr hm
      rw [hc] at hno
      cases hno
    exact splitFirstEqList_of_no_eq [] mal.data.toList hno'
  · cases hdl : mal.data.toList with
    | nil => simp [Internal.splitFirstEqList]
    | cons b rest =>
      rw [hdl] at hhead
      have hb : b = 0x3D := by
        simp only [List.head?_cons, beq_iff_eq, Option.some.injEq] at hhead
        exact hhead
      subst hb
      simp [Internal.splitFirstEqList]

private theorem splitFirstEqBytes_pair (k v : String)
    (hne : k ≠ "") (hno : '=' ∉ k.toList) :
    Internal.splitFirstEqBytes (k ++ "=" ++ v).toUTF8 = some (k.toUTF8, v.toUTF8) := by
  unfold Internal.splitFirstEqBytes
  have hdata : (k ++ "=" ++ v).toUTF8.data.toList =
      k.toUTF8.data.toList ++ (0x3D : UInt8) :: v.toUTF8.data.toList := by
    have ha : (k ++ "=" ++ v).toUTF8 = k.toUTF8 ++ "=".toUTF8 ++ v.toUTF8 := by
      simp [String.toUTF8_eq_toByteArray, String.toByteArray_append]
    rw [ha]
    have hdt : (k.toUTF8 ++ "=".toUTF8 ++ v.toUTF8).data.toList =
        k.toUTF8.data.toList ++ ("=".toUTF8).data.toList ++ v.toUTF8.data.toList := by
      simp [ByteArray.data_append]
    rw [hdt]
    have heq : ("=".toUTF8).data.toList = [0x3D] := rfl
    rw [heq, List.append_assoc, List.singleton_append]
  rw [hdata]
  have hnoBytes : (0x3D : UInt8) ∉ k.toUTF8.data.toList := fun hm =>
    hno ((eqByte_mem_toUTF8_iff k).mp hm)
  have hneBytes : k.toUTF8.data.toList ≠ [] := (toUTF8_data_ne_nil_iff k).mpr hne
  rw [splitFirstEqList_append_eq [] k.toUTF8.data.toList v.toUTF8.data.toList hnoBytes (Or.inr hneBytes)]
  simp only [List.reverse_nil, List.nil_append]

/-- Splitting `kBytes ++ "=" ++ vBytes` yields `some (kBytes, vBytes)` when `kBytes` is non-empty and `'='`-free. -/
theorem splitFirstEqBytes_rawConcat (kBytes vBytes : ByteArray)
    (hne : kBytes.size > 0) (hno : (0x3D : UInt8) ∉ kBytes.data.toList) :
    Internal.splitFirstEqBytes (kBytes ++ ByteArray.mk #[0x3D] ++ vBytes) = some (kBytes, vBytes) := by
  unfold Internal.splitFirstEqBytes
  have hdata : (kBytes ++ ByteArray.mk #[0x3D] ++ vBytes).data.toList =
      kBytes.data.toList ++ (0x3D : UInt8) :: vBytes.data.toList := by
    simp [ByteArray.data_append]
  rw [hdata]
  have hneList : kBytes.data.toList ≠ [] := by
    intro hl
    have hsz : kBytes.size = 0 := by
      change kBytes.data.size = 0
      rw [← Array.length_toList, hl]
      rfl
    omega
  rw [splitFirstEqList_append_eq [] kBytes.data.toList vBytes.data.toList hno (Or.inr hneList)]
  simp only [List.reverse_nil, List.nil_append]

/-- Structural invariant of `Internal.splitFirstEqList`. -/
theorem splitFirstEqList_spec (kBytes vBytes : ByteArray) :
    ∀ (rp bl : List UInt8),
      Internal.splitFirstEqList rp bl = some (kBytes, vBytes) →
      (0x3D : UInt8) ∉ rp →
      kBytes.data.toList ≠ [] ∧
      (0x3D : UInt8) ∉ kBytes.data.toList ∧
      (∀ b ∈ kBytes.data.toList, b ∈ rp ∨ b ∈ bl) ∧
      (∀ b ∈ vBytes.data.toList, b ∈ bl) := by
  intro rp bl hsp hnr
  induction bl generalizing rp with
  | nil => simp [Internal.splitFirstEqList] at hsp
  | cons x xs ih =>
    unfold Internal.splitFirstEqList at hsp
    by_cases hx : x = 0x3D
    · subst hx
      simp only [beq_self_eq_true, ↓reduceIte] at hsp
      by_cases hrp : rp.isEmpty
      · simp [hrp] at hsp
      · simp only [hrp, Bool.false_eq_true, ↓reduceIte, Option.some.injEq] at hsp
        have hk : kBytes = ByteArray.mk rp.reverse.toArray := congrArg Prod.fst hsp |>.symm
        have hv : vBytes = ByteArray.mk xs.toArray := congrArg Prod.snd hsp |>.symm
        rw [hk, hv]
        refine ⟨?_, ?_, ?_, ?_⟩
        · intro hl
          have hrev : rp.reverse = [] := by simpa using hl
          have hrnil : rp = [] := List.reverse_eq_nil_iff.mp hrev
          subst hrnil
          simp at hrp
        · simp only [List.mem_reverse]
          exact hnr
        · intro b hb
          simp only [List.mem_reverse] at hb
          exact Or.inl hb
        · intro b hb
          exact List.mem_cons_of_mem _ hb
    · have hbeq : (x == (0x3D : UInt8)) = false := beq_false_of_ne hx
      simp only [hbeq, Bool.false_eq_true, ↓reduceIte] at hsp
      have hnr' : (0x3D : UInt8) ∉ x :: rp := by
        intro hm
        rcases List.mem_cons.mp hm with h1 | h2
        · exact hx h1.symm
        · exact hnr h2
      rcases ih (x :: rp) hsp hnr' with ⟨hne, hno, hkmem, hvmem⟩
      refine ⟨hne, hno, ?_, ?_⟩
      · intro b hb
        rcases hkmem b hb with hm1 | hm2
        · rcases List.mem_cons.mp hm1 with h1 | h2
          · exact Or.inr (h1 ▸ List.mem_cons_self)
          · exact Or.inl h2
        · exact Or.inr (List.mem_cons_of_mem _ hm2)
      · intro b hb
        exact List.mem_cons_of_mem _ (hvmem b hb)

/-- Direct structural list decoder equivalent to `Internal.decodeEnvironAcc []`. -/
def decodeEnvironList : List ByteArray → Except EnvVars.Raw.EnvVarsRawError (List (String × String))
  | [] => .ok []
  | entry :: rest =>
    match Internal.splitFirstEqBytes entry with
    | none => decodeEnvironList rest
    | some (kBytes, vBytes) =>
      match String.fromUTF8? kBytes with
      | none => .error (.invalidEncoding none "invalid UTF-8 in environment key")
      | some k =>
        match String.fromUTF8? vBytes with
        | none => .error (.invalidEncoding (some k) "invalid UTF-8 in environment value")
        | some v =>
          match decodeEnvironList rest with
          | .error err => .error err
          | .ok tail => .ok ((k, v) :: tail)

/-- Decoding mixed malformed and valid `k=v` entries skips malformed slices and preserves valid pairs. -/
theorem decodeEnvironList_of_items (items : List (ByteArray ⊕ (String × String)))
    (hall : items.all (fun
      | .inl mal => !(mal.data.toList.contains (0x3D : UInt8)) || mal.data.toList.head? == some (0x3D : UInt8)
      | .inr (k, _) => !k.isEmpty && !('=' ∈ k.toList)) = true) :
    decodeEnvironList (items.map fun
      | .inl mal => mal
      | .inr (k, v) => (k ++ "=" ++ v).toUTF8) =
      .ok (items.filterMap fun
        | .inl _ => none
        | .inr kv => some kv) := by
  induction items with
  | nil => simp [decodeEnvironList]
  | cons item rest ih =>
    simp only [List.all_cons, Bool.and_eq_true] at hall
    rcases hall with ⟨hitem, hrest⟩
    have ih' := ih hrest
    cases item with
    | inl mal =>
      dsimp only at hitem
      have hmal : !(mal.data.toList.contains (0x3D : UInt8)) = true ∨
          mal.data.toList.head? == some (0x3D : UInt8) := by
        simpa [Bool.or_eq_true] using hitem
      simp only [List.map_cons, List.filterMap_cons, decodeEnvironList,
        splitFirstEqBytes_mal mal hmal]
      exact ih'
    | inr kv =>
      rcases kv with ⟨k, v⟩
      simp only [Bool.and_eq_true, Bool.not_eq_true'] at hitem
      rcases hitem with ⟨hkne, hkno⟩
      have hne : k ≠ "" := fun heq => by subst heq; simp [String.isEmpty] at hkne
      have hno : '=' ∉ k.toList := by
        intro hm
        have hd : decide ('=' ∈ k.toList) = true := decide_eq_true hm
        rw [hkno] at hd
        cases hd
      simp only [List.map_cons, List.filterMap_cons, decodeEnvironList,
        splitFirstEqBytes_pair k v hne hno, fromUTF8?_toUTF8, ih']

/-- Proof of `test_envvarsraw_getEnv_nonPosixKeyReturnsNoneWithoutLookup` for `Internal.mkRawOps`. -/
theorem proof_envvarsraw_getEnv_nonPosixKeyReturnsNoneWithoutLookup :
    AllPass (test_envvarsraw_getEnv_nonPosixKeyReturnsNoneWithoutLookup (Internal.mkRawOps (m := Id))) := by
  intro key leaked envSnap hbad
  have hk : Internal.isValidPosixKey key = false := (isValidPosixKey_false_iff key).mpr hbad
  simp [Internal.mkRawOps, hk, pure, assert]

/-- Non-vacuity `CanReach` witness for `test_envvarsraw_getEnv_nonPosixKeyReturnsNoneWithoutLookup`. -/
theorem reach_envvarsraw_getEnv_nonPosixKeyReturnsNoneWithoutLookup :
    CanReach (test_envvarsraw_getEnv_nonPosixKeyReturnsNoneWithoutLookup (Internal.mkRawOps (m := Id))) :=
  ⟨"", none, #[], Or.inl rfl,
    proof_envvarsraw_getEnv_nonPosixKeyReturnsNoneWithoutLookup "" none #[] (Or.inl rfl)⟩

/-- Proof of `test_envvarsraw_getEnv_unsetReturnsNone` for `Internal.mkRawOps`. -/
theorem proof_envvarsraw_getEnv_unsetReturnsNone :
    AllPass (test_envvarsraw_getEnv_unsetReturnsNone (Internal.mkRawOps (m := Id))) := by
  intro key envSnap hvalid
  have hk : Internal.isValidPosixKey key = true := (isValidPosixKey_true_iff key).mpr hvalid
  simp [Internal.mkRawOps, bind, pure, assert]

/-- Non-vacuity `CanReach` witness for `test_envvarsraw_getEnv_unsetReturnsNone`. -/
theorem reach_envvarsraw_getEnv_unsetReturnsNone :
    CanReach (test_envvarsraw_getEnv_unsetReturnsNone (Internal.mkRawOps (m := Id))) :=
  ⟨"PATH", #[], ⟨by decide, by decide, by decide⟩,
    proof_envvarsraw_getEnv_unsetReturnsNone "PATH" #[] ⟨by decide, by decide, by decide⟩⟩

/-- Proof of `test_envvarsraw_getEnv_validUtf8DecodesExactValue` for `Internal.mkRawOps`. -/
theorem proof_envvarsraw_getEnv_validUtf8DecodesExactValue :
    AllPass (test_envvarsraw_getEnv_validUtf8DecodesExactValue (Internal.mkRawOps (m := Id))) := by
  intro key val envSnap hvalid
  have hk : Internal.isValidPosixKey key = true := (isValidPosixKey_true_iff key).mpr hvalid
  simp only [Internal.mkRawOps, hk, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
    beq_self_eq_true, bind, pure, assert]
  rw [fromUTF8?_toUTF8]
  exact ⟨rfl, trivial⟩

/-- Non-vacuity `CanReach` witness for `test_envvarsraw_getEnv_validUtf8DecodesExactValue`. -/
theorem reach_envvarsraw_getEnv_validUtf8DecodesExactValue :
    CanReach (test_envvarsraw_getEnv_validUtf8DecodesExactValue (Internal.mkRawOps (m := Id))) :=
  ⟨"PATH", "/bin", #[], ⟨by decide, by decide, by decide⟩,
    proof_envvarsraw_getEnv_validUtf8DecodesExactValue "PATH" "/bin" #[] ⟨by decide, by decide, by decide⟩⟩

/-- Proof of `test_envvarsraw_getEnv_invalidUtf8ReturnsInvalidEncoding` for `Internal.mkRawOps`. -/
theorem proof_envvarsraw_getEnv_invalidUtf8ReturnsInvalidEncoding :
    AllPass (test_envvarsraw_getEnv_invalidUtf8ReturnsInvalidEncoding (Internal.mkRawOps (m := Id))) := by
  intro key rawVal envSnap hvalid hbad
  have hk : Internal.isValidPosixKey key = true := (isValidPosixKey_true_iff key).mpr hvalid
  simp only [Internal.mkRawOps, hk, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
    beq_self_eq_true, bind, pure, assert, hbad]
  exact ⟨⟨"invalid UTF-8 in environment value", rfl, by decide⟩, trivial⟩

/-- Non-vacuity `CanReach` witness for `test_envvarsraw_getEnv_invalidUtf8ReturnsInvalidEncoding`. -/
theorem reach_envvarsraw_getEnv_invalidUtf8ReturnsInvalidEncoding :
    CanReach (test_envvarsraw_getEnv_invalidUtf8ReturnsInvalidEncoding (Internal.mkRawOps (m := Id))) :=
  ⟨"BAD_VAL", ByteArray.mk #[0xFF], #[], ⟨by decide, by decide, by decide⟩, rfl,
    proof_envvarsraw_getEnv_invalidUtf8ReturnsInvalidEncoding "BAD_VAL" (ByteArray.mk #[0xFF]) #[]
      ⟨by decide, by decide, by decide⟩ rfl⟩

end LeanSwe.EnvVars.Raw.Proofs
