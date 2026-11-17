import LeanSwe.EnvVars.Raw.Types
import LeanSwe.EnvVars.Raw.Interface
import LeanSwe.EnvVars.Raw.Impl
import LeanSwe.EnvVars.Raw.SpecTests

namespace LeanSwe.EnvVars.Raw.Proofs

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

private theorem isValidPosixKey_true_iff (key : String) :
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

private theorem isValidPosixKey_false_iff (key : String) :
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

private theorem fromUTF8?_toUTF8 (s : String) : String.fromUTF8? s.toUTF8 = some s := by
  simp [String.fromUTF8?, String.toUTF8, s.isValidUTF8]

private theorem fromUTF8?_eq_some_iff (bs : ByteArray) (s : String) :
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

private theorem byteArray_mk_eq_of_data_toList_eq {a b : ByteArray}
    (h : a.data.toList = b.data.toList) : a = b := by
  cases a with | mk ad =>
  cases b with | mk bd =>
  congr 1
  exact Array.ext' h

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

private theorem eqByte_mem_toUTF8_iff (s : String) :
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

private theorem zeroByte_mem_toUTF8_iff (s : String) :
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

private theorem toUTF8_data_ne_nil_iff (s : String) :
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

private theorem splitFirstEqBytes_rawConcat (kBytes vBytes : ByteArray)
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

private theorem splitFirstEqList_spec (kBytes vBytes : ByteArray) :
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

private theorem decodeEnvironList_of_items (items : List (ByteArray ⊕ (String × String)))
    (hall : items.all (fun
      | .inl mal => !(mal.data.toList.contains (0x3D : UInt8)) || mal.data.toList.head? == some (0x3D : UInt8)
      | .inr (k, _) => !k.isEmpty && !('=' ∈ k.toList)) = true) :
    Internal.decodeEnvironList (items.map fun
      | .inl mal => mal
      | .inr (k, v) => (k ++ "=" ++ v).toUTF8) =
      .ok (items.filterMap fun
        | .inl _ => none
        | .inr kv => some kv) := by
  induction items with
  | nil => simp [Internal.decodeEnvironList]
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
      simp only [List.map_cons, List.filterMap_cons, Internal.decodeEnvironList,
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
      simp only [List.map_cons, List.filterMap_cons, Internal.decodeEnvironList,
        splitFirstEqBytes_pair k v hne hno, fromUTF8?_toUTF8, ih']

/-- Proof of `test_envvarsraw_mapRawError_returnsNonEmptyMessage` for `defaultOps`. -/
theorem proof_envvarsraw_mapRawError_returnsNonEmptyMessage :
    AllPass (test_envvarsraw_mapRawError_returnsNonEmptyMessage defaultOps) := by
  intro raw
  simp only [defaultOps, Internal.mkRawOps, Internal.mapRawError, assert]
  refine ⟨?_, trivial⟩
  cases raw with
  | invalidEncoding _ _ => exact nonEmptyMsg_ne_empty _ _ (by decide)
  | invalidArgument _ _ _ => exact nonEmptyMsg_ne_empty _ _ (by decide)
  | otherError code _ =>
    exact nonEmptyMsg_ne_empty _ _ (append_head_ne_empty "os error " (toString code) (by decide))
  | userError _ => exact nonEmptyMsg_ne_empty _ _ (by decide)

/-- Non-vacuity `CanReach` witness for `test_envvarsraw_mapRawError_returnsNonEmptyMessage`. -/
theorem reach_envvarsraw_mapRawError_returnsNonEmptyMessage :
    CanReach (test_envvarsraw_mapRawError_returnsNonEmptyMessage defaultOps) :=
  ⟨.userError "", proof_envvarsraw_mapRawError_returnsNonEmptyMessage (.userError "")⟩

/-- Proof of `test_envvarsraw_mapRawError_preservesKindAndMetadata` for `defaultOps`. -/
theorem proof_envvarsraw_mapRawError_preservesKindAndMetadata :
    AllPass (test_envvarsraw_mapRawError_preservesKindAndMetadata defaultOps) := by
  intro raw
  cases raw <;> simp [defaultOps, Internal.mkRawOps, Internal.mapRawError, assert]

/-- Non-vacuity `CanReach` witness for `test_envvarsraw_mapRawError_preservesKindAndMetadata`. -/
theorem reach_envvarsraw_mapRawError_preservesKindAndMetadata :
    CanReach (test_envvarsraw_mapRawError_preservesKindAndMetadata defaultOps) :=
  ⟨.invalidEncoding (some "PATH") "bad",
    proof_envvarsraw_mapRawError_preservesKindAndMetadata (.invalidEncoding (some "PATH") "bad")⟩

/-- Proof of `test_envvarsraw_mapRawError_consistentAcrossBackends` for `defaultOps` and `Internal.mkRawOps`. -/
theorem proof_envvarsraw_mapRawError_consistentAcrossBackends :
    AllPass (test_envvarsraw_mapRawError_consistentAcrossBackends defaultOps (Internal.mkRawOps (m := Id))) := by
  intro _ _
  simp [defaultOps, Internal.mkRawOps, assert]

/-- Non-vacuity `CanReach` witness for `test_envvarsraw_mapRawError_consistentAcrossBackends`. -/
theorem reach_envvarsraw_mapRawError_consistentAcrossBackends :
    CanReach (test_envvarsraw_mapRawError_consistentAcrossBackends defaultOps (Internal.mkRawOps (m := Id))) :=
  ⟨{ getEnvBytes := fun _ => none, listEnvironBytes := #[] }, .userError "",
    proof_envvarsraw_mapRawError_consistentAcrossBackends
      { getEnvBytes := fun _ => none, listEnvironBytes := #[] } (.userError "")⟩

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

/-- Proof of `test_envvarsraw_listEnv_splitsFirstEqualsAndPreservesOrder` for `Internal.mkRawOps`. -/
theorem proof_envvarsraw_listEnv_splitsFirstEqualsAndPreservesOrder :
    AllPass (test_envvarsraw_listEnv_splitsFirstEqualsAndPreservesOrder (Internal.mkRawOps (m := Id))) := by
  intro getSnap pairs hall
  have hitems : ((pairs.map Sum.inr : List (Sum ByteArray (String × String))).all (fun
      | .inl mal => !(mal.data.toList.contains (0x3D : UInt8)) || mal.data.toList.head? == some (0x3D : UInt8)
      | .inr (k, _) => !k.isEmpty && !('=' ∈ k.toList))) = true := by
    rw [List.all_map]
    exact hall
  have hdec := decodeEnvironList_of_items (pairs.map Sum.inr) hitems
  rw [List.map_map] at hdec
  have hleft : (pairs.map (Function.comp (fun
      | .inl mal => mal
      | .inr (k, v) => (k ++ "=" ++ v).toUTF8) Sum.inr)) =
      pairs.map (fun x => (x.1 ++ "=" ++ x.2).toUTF8) := rfl
  have hright : ((pairs.map Sum.inr).filterMap fun
      | .inl (_ : ByteArray) => (none : Option (String × String))
      | .inr kv => some kv) = pairs := by
    rw [List.filterMap_map]
    change pairs.filterMap some = pairs
    exact List.filterMap_some
  rw [hleft, hright] at hdec
  simp only [Internal.mkRawOps, bind, pure, assert]
  change (Internal.decodeEnvironList (pairs.map (fun x => (x.1 ++ "=" ++ x.2).toUTF8))).map List.toArray =
    .ok pairs.toArray ∧ True
  rw [hdec]
  exact ⟨rfl, trivial⟩

/-- Non-vacuity `CanReach` witness for `test_envvarsraw_listEnv_splitsFirstEqualsAndPreservesOrder`. -/
theorem reach_envvarsraw_listEnv_splitsFirstEqualsAndPreservesOrder :
    CanReach (test_envvarsraw_listEnv_splitsFirstEqualsAndPreservesOrder (Internal.mkRawOps (m := Id))) :=
  ⟨fun _ => none, [("A", "1")], by decide,
    proof_envvarsraw_listEnv_splitsFirstEqualsAndPreservesOrder (fun _ => none) [("A", "1")] (by decide)⟩

/-- Proof of `test_envvarsraw_listEnv_skipsMissingEqualsAndEmptyKey` for `Internal.mkRawOps`. -/
theorem proof_envvarsraw_listEnv_skipsMissingEqualsAndEmptyKey :
    AllPass (test_envvarsraw_listEnv_skipsMissingEqualsAndEmptyKey (Internal.mkRawOps (m := Id))) := by
  intro getSnap items hall
  simp only [Internal.mkRawOps, bind, pure, assert]
  change (Internal.decodeEnvironList (items.map fun
    | .inl mal => mal
    | .inr (k, v) => (k ++ "=" ++ v).toUTF8)).map List.toArray =
    .ok (items.filterMap fun
      | .inl _ => none
      | .inr kv => some kv).toArray ∧ True
  rw [decodeEnvironList_of_items items hall]
  exact ⟨rfl, trivial⟩

/-- Non-vacuity `CanReach` witness for `test_envvarsraw_listEnv_skipsMissingEqualsAndEmptyKey`. -/
theorem reach_envvarsraw_listEnv_skipsMissingEqualsAndEmptyKey :
    CanReach (test_envvarsraw_listEnv_skipsMissingEqualsAndEmptyKey (Internal.mkRawOps (m := Id))) :=
  ⟨fun _ => none, [], rfl,
    proof_envvarsraw_listEnv_skipsMissingEqualsAndEmptyKey (fun _ => none) [] rfl⟩

private theorem decodeEnvironList_append_error (xs ys : List ByteArray) (out : List (String × String))
    (hxs : Internal.decodeEnvironList xs = .ok out)
    (err : EnvVarsRawError) (hys : Internal.decodeEnvironList ys = .error err) :
    Internal.decodeEnvironList (xs ++ ys) = .error err := by
  induction xs generalizing out with
  | nil => exact hys
  | cons x rest ih =>
    change Internal.decodeEnvironList (x :: (rest ++ ys)) = .error err
    unfold Internal.decodeEnvironList at hxs ⊢
    cases hsx : Internal.splitFirstEqBytes x with
    | none => rw [hsx] at hxs; exact ih out hxs
    | some p =>
      rw [hsx] at hxs
      dsimp only at hxs ⊢
      cases hkx : String.fromUTF8? p.1 with
      | none => rw [hkx] at hxs; cases hxs
      | some kx =>
        rw [hkx] at hxs
        cases hvx : String.fromUTF8? p.2 with
        | none => rw [hvx] at hxs; cases hxs
        | some vx =>
          rw [hvx] at hxs
          cases htail : Internal.decodeEnvironList rest with
          | error e => rw [htail] at hxs; cases hxs
          | ok tl =>
            rw [htail] at hxs
            rw [ih tl htail]

/-- Proof of `test_envvarsraw_listEnv_invalidUtf8KeyReturnsNoneKeyError` for `Internal.mkRawOps`. -/
theorem proof_envvarsraw_listEnv_invalidUtf8KeyReturnsNoneKeyError :
    AllPass (test_envvarsraw_listEnv_invalidUtf8KeyReturnsNoneKeyError (Internal.mkRawOps (m := Id))) := by
  intro getSnap pre badKey valBytes tail hpre ⟨hsz, hno, hbad⟩
  have hno' : (0x3D : UInt8) ∉ badKey.data.toList := by
    intro hm
    have hc : badKey.data.toList.contains (0x3D : UInt8) = true := List.contains_iff_mem.mpr hm
    rw [hc] at hno
    cases hno
  have hsp : Internal.splitFirstEqBytes (badKey ++ ByteArray.mk #[0x3D] ++ valBytes) = some (badKey, valBytes) :=
    splitFirstEqBytes_rawConcat badKey valBytes hsz hno'
  have hpreDec := decodeEnvironList_of_items pre hpre
  have hbadEntry : Internal.decodeEnvironList ((badKey ++ ByteArray.mk #[0x3D] ++ valBytes) :: tail) =
      .error (.invalidEncoding none "invalid UTF-8 in environment key") := by
    unfold Internal.decodeEnvironList
    rw [hsp]
    dsimp only
    rw [hbad]
  have hfull := decodeEnvironList_append_error _ ((badKey ++ ByteArray.mk #[0x3D] ++ valBytes) :: tail) _
    hpreDec _ hbadEntry
  simp only [Internal.mkRawOps, bind, pure, assert]
  change (∃ detail, (Internal.decodeEnvironList _).map List.toArray =
    .error (.invalidEncoding none detail) ∧ detail ≠ "") ∧ True
  have hmap : (Internal.decodeEnvironList ((pre.map fun
      | .inl mal => mal
      | .inr (k, v) => (k ++ "=" ++ v).toUTF8) ++ ((badKey ++ ByteArray.mk #[0x3D] ++ valBytes) :: tail))).map
      List.toArray = .error (.invalidEncoding none "invalid UTF-8 in environment key") := by
    rw [hfull]
    rfl
  exact ⟨⟨"invalid UTF-8 in environment key", hmap, by decide⟩, trivial⟩

/-- Non-vacuity `CanReach` witness for `test_envvarsraw_listEnv_invalidUtf8KeyReturnsNoneKeyError`. -/
theorem reach_envvarsraw_listEnv_invalidUtf8KeyReturnsNoneKeyError :
    CanReach (test_envvarsraw_listEnv_invalidUtf8KeyReturnsNoneKeyError (Internal.mkRawOps (m := Id))) :=
  ⟨fun _ => none, [], ByteArray.mk #[0xFF], ByteArray.empty, [], rfl, ⟨by decide, rfl, rfl⟩,
    proof_envvarsraw_listEnv_invalidUtf8KeyReturnsNoneKeyError
      (fun _ => none) [] (ByteArray.mk #[0xFF]) ByteArray.empty [] rfl ⟨by decide, rfl, rfl⟩⟩

/-- Proof of `test_envvarsraw_listEnv_invalidUtf8ValueReturnsSomeKeyError` for `Internal.mkRawOps`. -/
theorem proof_envvarsraw_listEnv_invalidUtf8ValueReturnsSomeKeyError :
    AllPass (test_envvarsraw_listEnv_invalidUtf8ValueReturnsSomeKeyError (Internal.mkRawOps (m := Id))) := by
  intro getSnap pre key badVal tail hpre ⟨hkne, hkno⟩ hbad
  have hsz : key.toUTF8.size > 0 := by
    have hne : key.toUTF8.data.toList ≠ [] := (toUTF8_data_ne_nil_iff key).mpr hkne
    cases hdl : key.toUTF8.data.toList with
    | nil => exact absurd hdl hne
    | cons _ _ =>
      have hlen : key.toUTF8.size = key.toUTF8.data.toList.length := by
        change key.toUTF8.data.size = key.toUTF8.data.toList.length
        exact (Array.length_toList).symm
      rw [hlen, hdl]
      simp
  have hno' : (0x3D : UInt8) ∉ key.toUTF8.data.toList := fun hm =>
    hkno ((eqByte_mem_toUTF8_iff key).mp hm)
  have hsp : Internal.splitFirstEqBytes (key.toUTF8 ++ ByteArray.mk #[0x3D] ++ badVal) = some (key.toUTF8, badVal) :=
    splitFirstEqBytes_rawConcat key.toUTF8 badVal hsz hno'
  have hpreDec := decodeEnvironList_of_items pre hpre
  have hbadEntry : Internal.decodeEnvironList ((key.toUTF8 ++ ByteArray.mk #[0x3D] ++ badVal) :: tail) =
      .error (.invalidEncoding (some key) "invalid UTF-8 in environment value") := by
    unfold Internal.decodeEnvironList
    rw [hsp]
    dsimp only
    rw [fromUTF8?_toUTF8]
    dsimp only
    rw [hbad]
  have hfull := decodeEnvironList_append_error _ ((key.toUTF8 ++ ByteArray.mk #[0x3D] ++ badVal) :: tail) _
    hpreDec _ hbadEntry
  simp only [Internal.mkRawOps, bind, pure, assert]
  change (∃ detail, (Internal.decodeEnvironList _).map List.toArray =
    .error (.invalidEncoding (some key) detail) ∧ detail ≠ "") ∧ True
  have hmap : (Internal.decodeEnvironList ((pre.map fun
      | .inl mal => mal
      | .inr (k, v) => (k ++ "=" ++ v).toUTF8) ++ ((key.toUTF8 ++ ByteArray.mk #[0x3D] ++ badVal) :: tail))).map
      List.toArray = .error (.invalidEncoding (some key) "invalid UTF-8 in environment value") := by
    rw [hfull]
    rfl
  exact ⟨⟨"invalid UTF-8 in environment value", hmap, by decide⟩, trivial⟩

/-- Non-vacuity `CanReach` witness for `test_envvarsraw_listEnv_invalidUtf8ValueReturnsSomeKeyError`. -/
theorem reach_envvarsraw_listEnv_invalidUtf8ValueReturnsSomeKeyError :
    CanReach (test_envvarsraw_listEnv_invalidUtf8ValueReturnsSomeKeyError (Internal.mkRawOps (m := Id))) :=
  ⟨fun _ => none, [], "BAD_VAL", ByteArray.mk #[0xFF], [], rfl, ⟨by decide, by decide⟩, rfl,
    proof_envvarsraw_listEnv_invalidUtf8ValueReturnsSomeKeyError
      (fun _ => none) [] "BAD_VAL" (ByteArray.mk #[0xFF]) [] rfl ⟨by decide, by decide⟩ rfl⟩

private theorem decodeEnvironList_keys_wellFormed (entries : List ByteArray)
    (out : List (String × String))
    (hdec : Internal.decodeEnvironList entries = .ok out) :
    ∀ p ∈ out, !p.1.isEmpty && !('=' ∈ p.1.toList) := by
  induction entries generalizing out with
  | nil =>
    simp [Internal.decodeEnvironList] at hdec
    subst hdec
    intro p hp
    cases hp
  | cons e rest ih =>
    unfold Internal.decodeEnvironList at hdec
    cases hsp : Internal.splitFirstEqBytes e with
    | none =>
      rw [hsp] at hdec
      exact ih out hdec
    | some kv =>
      rcases kv with ⟨kBytes, vBytes⟩
      rw [hsp] at hdec
      dsimp only at hdec
      cases hk : String.fromUTF8? kBytes with
      | none => rw [hk] at hdec; cases hdec
      | some k =>
        rw [hk] at hdec
        cases hv : String.fromUTF8? vBytes with
        | none => rw [hv] at hdec; cases hdec
        | some v =>
          rw [hv] at hdec
          cases htail : Internal.decodeEnvironList rest with
          | error err => rw [htail] at hdec; cases hdec
          | ok tail =>
            rw [htail] at hdec
            injection hdec with hEq
            subst hEq
            intro p hp
            rcases List.mem_cons.mp hp with rfl | hmem
            · have hsp' : Internal.splitFirstEqList [] e.data.toList = some (kBytes, vBytes) := hsp
              rcases splitFirstEqList_spec kBytes vBytes [] e.data.toList hsp' (by simp) with
                ⟨hneBytes, hnoEqBytes, _, _⟩
              have hkUtf : kBytes = k.toUTF8 := (fromUTF8?_eq_some_iff kBytes k).mp hk
              rw [hkUtf] at hneBytes hnoEqBytes
              have hkne : k ≠ "" := (toUTF8_data_ne_nil_iff k).mp hneBytes
              have hkno : '=' ∉ k.toList := fun hm => hnoEqBytes ((eqByte_mem_toUTF8_iff k).mpr hm)
              have hkEmpty : k.isEmpty = false := by
                cases hke : k.isEmpty with
                | false => rfl
                | true => exact absurd (String.isEmpty_iff.mp hke) hkne
              simp [hkEmpty, hkno]
            · exact ih tail htail p hmem

private theorem decodeEnvironList_nulFree (entries : List ByteArray)
    (out : List (String × String))
    (hnul : ∀ e ∈ entries, (0 : UInt8) ∉ e.data.toList)
    (hdec : Internal.decodeEnvironList entries = .ok out) :
    ∀ p ∈ out, !(Char.ofNat 0 ∈ p.1.toList) && !(Char.ofNat 0 ∈ p.2.toList) := by
  induction entries generalizing out with
  | nil =>
    simp [Internal.decodeEnvironList] at hdec
    subst hdec
    intro p hp
    cases hp
  | cons e rest ih =>
    have heNul : (0 : UInt8) ∉ e.data.toList := hnul e List.mem_cons_self
    have hrestNul : ∀ x ∈ rest, (0 : UInt8) ∉ x.data.toList := fun x hx =>
      hnul x (List.mem_cons_of_mem e hx)
    unfold Internal.decodeEnvironList at hdec
    cases hsp : Internal.splitFirstEqBytes e with
    | none =>
      rw [hsp] at hdec
      exact ih out hrestNul hdec
    | some kv =>
      rcases kv with ⟨kBytes, vBytes⟩
      rw [hsp] at hdec
      dsimp only at hdec
      cases hk : String.fromUTF8? kBytes with
      | none => rw [hk] at hdec; cases hdec
      | some k =>
        rw [hk] at hdec
        cases hv : String.fromUTF8? vBytes with
        | none => rw [hv] at hdec; cases hdec
        | some v =>
          rw [hv] at hdec
          cases htail : Internal.decodeEnvironList rest with
          | error err => rw [htail] at hdec; cases hdec
          | ok tail =>
            rw [htail] at hdec
            injection hdec with hEq
            subst hEq
            intro p hp
            rcases List.mem_cons.mp hp with rfl | hmem
            · have hsp' : Internal.splitFirstEqList [] e.data.toList = some (kBytes, vBytes) := hsp
              rcases splitFirstEqList_spec kBytes vBytes [] e.data.toList hsp' (by simp) with
                ⟨_, _, hkmem, hvmem⟩
              have hkUtf : kBytes = k.toUTF8 := (fromUTF8?_eq_some_iff kBytes k).mp hk
              have hvUtf : vBytes = v.toUTF8 := (fromUTF8?_eq_some_iff vBytes v).mp hv
              have h0k : (0 : UInt8) ∉ k.toUTF8.data.toList := by
                intro hm
                rw [← hkUtf] at hm
                rcases hkmem 0 hm with hnil | hmemE
                · cases hnil
                · exact heNul hmemE
              have h0v : (0 : UInt8) ∉ v.toUTF8.data.toList := by
                intro hm
                rw [← hvUtf] at hm
                exact heNul (hvmem 0 hm)
              have hkNul : Char.ofNat 0 ∉ k.toList := fun hm => h0k ((zeroByte_mem_toUTF8_iff k).mpr hm)
              have hvNul : Char.ofNat 0 ∉ v.toList := fun hm => h0v ((zeroByte_mem_toUTF8_iff v).mpr hm)
              simp [hkNul, hvNul]
            · exact ih tail hrestNul htail p hmem

/-- Proof of `test_envvarsraw_listEnv_outputKeysWellFormed` for `Internal.mkRawOps`. -/
theorem proof_envvarsraw_listEnv_outputKeysWellFormed :
    AllPass (test_envvarsraw_listEnv_outputKeysWellFormed (Internal.mkRawOps (m := Id))) := by
  intro getSnap entries pairs hok
  simp only [Internal.mkRawOps, bind, pure] at hok
  change (Internal.decodeEnvironList entries.toList).map List.toArray = .ok pairs at hok
  cases hdec : Internal.decodeEnvironList entries.toList with
  | error err => rw [hdec] at hok; cases hok
  | ok out =>
    rw [hdec] at hok
    injection hok with hEq
    subst hEq
    simp only [assert]
    exact ⟨List.all_eq_true.mpr (decodeEnvironList_keys_wellFormed entries.toList out hdec), trivial⟩

/-- Non-vacuity `CanReach` witness for `test_envvarsraw_listEnv_outputKeysWellFormed`. -/
theorem reach_envvarsraw_listEnv_outputKeysWellFormed :
    CanReach (test_envvarsraw_listEnv_outputKeysWellFormed (Internal.mkRawOps (m := Id))) :=
  ⟨fun _ => none, #[], #[], rfl,
    proof_envvarsraw_listEnv_outputKeysWellFormed (fun _ => none) #[] #[] rfl⟩

/-- Proof of `test_envvarsraw_listEnv_nulFreeInputsPreserveNulFreedom` for `Internal.mkRawOps`. -/
theorem proof_envvarsraw_listEnv_nulFreeInputsPreserveNulFreedom :
    AllPass (test_envvarsraw_listEnv_nulFreeInputsPreserveNulFreedom (Internal.mkRawOps (m := Id))) := by
  intro getSnap entries pairs hnul hok
  simp only [Internal.mkRawOps, bind, pure] at hok
  change (Internal.decodeEnvironList entries.toList).map List.toArray = .ok pairs at hok
  cases hdec : Internal.decodeEnvironList entries.toList with
  | error err => rw [hdec] at hok; cases hok
  | ok out =>
    rw [hdec] at hok
    injection hok with hEq
    subst hEq
    have hnulList : ∀ e ∈ entries.toList, (0 : UInt8) ∉ e.data.toList := by
      intro e he hm
      have hAll := List.all_eq_true.mp hnul e he
      have hc : e.data.toList.contains (0 : UInt8) = true := List.contains_iff_mem.mpr hm
      rw [hc] at hAll
      cases hAll
    have hwf := decodeEnvironList_keys_wellFormed entries.toList out hdec
    have hnf := decodeEnvironList_nulFree entries.toList out hnulList hdec
    simp only [assert]
    refine ⟨List.all_eq_true.mpr fun p hp => ?_, trivial⟩
    have h12 := hwf p hp
    have h34 := hnf p hp
    simp only [Bool.and_eq_true] at h12 h34 ⊢
    exact ⟨⟨⟨h12.1, h12.2⟩, h34.1⟩, h34.2⟩

/-- Non-vacuity `CanReach` witness for `test_envvarsraw_listEnv_nulFreeInputsPreserveNulFreedom`. -/
theorem reach_envvarsraw_listEnv_nulFreeInputsPreserveNulFreedom :
    CanReach (test_envvarsraw_listEnv_nulFreeInputsPreserveNulFreedom (Internal.mkRawOps (m := Id))) :=
  ⟨fun _ => none, #[], #[], rfl, rfl,
    proof_envvarsraw_listEnv_nulFreeInputsPreserveNulFreedom (fun _ => none) #[] #[] rfl rfl⟩

/-- Satisfiability `CanReach` witness for `assume_envvarsraw_listEnv_consistentWithGetEnv`. -/
theorem reach_assume_envvarsraw_listEnv_consistentWithGetEnv :
    CanReach (assume_envvarsraw_listEnv_consistentWithGetEnv
      (Internal.mkRawOps { getEnvBytes := fun _ => none, listEnvironBytes := #[] })) := by
  refine ⟨#[], "PATH", rfl, ⟨by decide, by decide, by decide⟩, ?_⟩
  simp [Internal.mkRawOps, Internal.isValidPosixKey, bind, pure, assert]

private theorem baseIO_liftM_never_throws {α : Type} (act : BaseIO α) (w : Void IO.RealWorld) :
    ∃ a w', (liftM act : IO α) w = .ok a w' := by
  simp only [liftM, monadLift, MonadLiftT.monadLift, MonadLift.monadLift, BaseIO.toEIO]
  cases act w with
  | mk a s => exact ⟨a, s, rfl⟩

private theorem decodeEnvironList_only_invalidEncoding (xs : List ByteArray) {err : EnvVarsRawError}
    (herr : Internal.decodeEnvironList xs = .error err) : err.kind = .invalidEncoding := by
  induction xs with
  | nil => simp [Internal.decodeEnvironList] at herr
  | cons x rest ih =>
    unfold Internal.decodeEnvironList at herr
    cases hs : Internal.splitFirstEqBytes x with
    | none => rw [hs] at herr; exact ih herr
    | some kv =>
      rw [hs] at herr
      dsimp only at herr
      rcases kv with ⟨kBytes, vBytes⟩
      cases hkf : String.fromUTF8? kBytes with
      | none => rw [hkf] at herr; injection herr with he; subst he; rfl
      | some k =>
        rw [hkf] at herr
        dsimp only at herr
        cases hvf : String.fromUTF8? vBytes with
        | none => rw [hvf] at herr; injection herr with he; subst he; rfl
        | some v =>
          rw [hvf] at herr
          dsimp only at herr
          cases hr : Internal.decodeEnvironList rest with
          | error e => rw [hr] at herr; injection herr with he; subst he; exact ih hr
          | ok tl => rw [hr] at herr; cases herr

private theorem io_pure_eq {α : Type} (a : α) (w : Void IO.RealWorld) :
    (pure a : IO α) w = EST.Out.ok a w := rfl

private theorem io_bind_baseIO {α β : Type} (act : BaseIO α) (k : α → IO β) (w : Void IO.RealWorld) :
    ((liftM act : IO α) >>= k) w = k (act w).val (act w).state := by
  rcases baseIO_liftM_never_throws act w with ⟨v, w', hv⟩
  have hst : act w = .mk v w' := by
    simp only [liftM, monadLift, MonadLiftT.monadLift, MonadLift.monadLift, BaseIO.toEIO] at hv
    cases h : act w with
    | mk a s =>
      rw [h] at hv
      have ha : a = v := by injection hv
      have hs : s = w' := by injection hv
      subst ha hs
      rfl
  rw [hst]
  have hbind : ((liftM act : IO α) >>= k) w =
      match (liftM act : IO α) w with
      | EST.Out.ok a s => k a s
      | EST.Out.error e s => EST.Out.error e s := rfl
  rw [hbind, hv]

private theorem mkRawOps_getEnv_never
    (f : EnvVarsRawErrorKind) (hf : f ≠ .invalidEncoding)
    (g : String → BaseIO (Option ByteArray))
    (l : BaseIO (Array ByteArray))
    (key : String) (w : Void IO.RealWorld) :
    Core.NeverErrorKindIO EnvVarsRawError.kind f
      ((Internal.mkRawOps (m := IO) {
        getEnvBytes := fun k => liftM (g k)
        listEnvironBytes := liftM l
      }).getEnv key) w := by
  unfold Core.NeverErrorKindIO
  simp only [Internal.mkRawOps]
  by_cases hk : Internal.isValidPosixKey key
  · simp only [hk, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    rw [io_bind_baseIO]
    cases (g key w).val with
    | none => dsimp only; rw [io_pure_eq]; trivial
    | some bs =>
      dsimp only
      cases hutf : String.fromUTF8? bs with
      | some _ => dsimp only; rw [io_pure_eq]; trivial
      | none => dsimp only; rw [io_pure_eq]; simp only [EnvVarsRawError.kind]; exact hf.symm
  · simp only [hk, Bool.not_false, ↓reduceIte]
    rw [io_pure_eq]
    trivial

private theorem mkRawOps_listEnv_never
    (f : EnvVarsRawErrorKind) (hf : f ≠ .invalidEncoding)
    (g : String → BaseIO (Option ByteArray))
    (l : BaseIO (Array ByteArray))
    (w : Void IO.RealWorld) :
    Core.NeverErrorKindIO EnvVarsRawError.kind f
      ((Internal.mkRawOps (m := IO) {
        getEnvBytes := fun k => liftM (g k)
        listEnvironBytes := liftM l
      }).listEnv) w := by
  unfold Core.NeverErrorKindIO
  simp only [Internal.mkRawOps]
  rw [io_bind_baseIO]
  cases hd : Internal.decodeEnvironList (l w).val.toList with
  | ok _ => simp only [Except.map]; rw [io_pure_eq]; trivial
  | error err =>
    simp only [Except.map]
    rw [io_pure_eq]
    intro heq
    exact hf (heq ▸ decodeEnvironList_only_invalidEncoding (l w).val.toList hd)

/-- Proof that `Raw.getEnv` never returns `.invalidArgument`. -/
theorem raw_getEnv_never_invalidArgument (key : String) (w : Void IO.RealWorld) :
    Core.NeverErrorKindIO EnvVarsRawError.kind .invalidArgument (Raw.getEnv key) w := by
  apply mkRawOps_getEnv_never .invalidArgument (by decide)

/-- Proof that `Raw.getEnv` never returns `.otherError`. -/
theorem raw_getEnv_never_otherError (key : String) (w : Void IO.RealWorld) :
    Core.NeverErrorKindIO EnvVarsRawError.kind .otherError (Raw.getEnv key) w := by
  apply mkRawOps_getEnv_never .otherError (by decide)

/-- Proof that `Raw.getEnv` never returns `.userError`. -/
theorem raw_getEnv_never_userError (key : String) (w : Void IO.RealWorld) :
    Core.NeverErrorKindIO EnvVarsRawError.kind .userError (Raw.getEnv key) w := by
  apply mkRawOps_getEnv_never .userError (by decide)

/-- Proof that `Raw.listEnv` never returns `.invalidArgument`. -/
theorem raw_listEnv_never_invalidArgument (w : Void IO.RealWorld) :
    Core.NeverErrorKindIO EnvVarsRawError.kind .invalidArgument Raw.listEnv w := by
  apply mkRawOps_listEnv_never .invalidArgument (by decide)

/-- Proof that `Raw.listEnv` never returns `.otherError`. -/
theorem raw_listEnv_never_otherError (w : Void IO.RealWorld) :
    Core.NeverErrorKindIO EnvVarsRawError.kind .otherError Raw.listEnv w := by
  apply mkRawOps_listEnv_never .otherError (by decide)

/-- Proof that `Raw.listEnv` never returns `.userError`. -/
theorem raw_listEnv_never_userError (w : Void IO.RealWorld) :
    Core.NeverErrorKindIO EnvVarsRawError.kind .userError Raw.listEnv w := by
  apply mkRawOps_listEnv_never .userError (by decide)

end LeanSwe.EnvVars.Raw.Proofs
