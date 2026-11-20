import LeanSwe.LinuxSyscall.Sandbox.SpecTests
import LeanSwe.LinuxSyscall.Sandbox.Impl

namespace LeanSwe.LinuxSyscall.Sandbox

open Core (NondetTest AllPass CanReach CanReachRun)
open Core.NondetTest
open LeanSwe.LinuxSyscall

private theorem ui32_or_and_distrib (x y m : UInt32) :
    (x ||| y) &&& m = (x &&& m) ||| (y &&& m) := by
  apply UInt32.toNat_inj.mp
  rw [UInt32.toNat_and, UInt32.toNat_or, UInt32.toNat_or, UInt32.toNat_and, UInt32.toNat_and]
  exact Nat.and_or_distrib_right x.toNat y.toNat m.toNat

private theorem ui32_bit_and_mask (b : Bool) (shift mask : UInt32)
    (h0 : ((1 : UInt32) <<< shift) &&& mask = 0) :
    (if b then (1 : UInt32) <<< shift else 0) &&& mask = 0 := by
  cases b
  · simp
  · exact h0

private theorem ui32_bit_and_self (b : Bool) (shift : UInt32)
    (h1 : ((1 : UInt32) <<< shift) &&& ((1 : UInt32) <<< shift) = (1 : UInt32) <<< shift) :
    (if b then (1 : UInt32) <<< shift else 0) &&& ((1 : UInt32) <<< shift) =
      if b then (1 : UInt32) <<< shift else 0 := by
  cases b
  · simp
  · exact h1

private theorem ui32_or_zero (x : UInt32) : x ||| 0 = x := by
  apply UInt32.toNat_inj.mp
  simp

private theorem ui32_zero_or (x : UInt32) : 0 ||| x = x := by
  apply UInt32.toNat_inj.mp
  simp

private theorem bool_of_ui32_bit_eq {b1 b2 : Bool} {shift : UInt32}
    (hne : ((1 : UInt32) <<< shift) ≠ 0)
    (h : (if b1 then (1 : UInt32) <<< shift else 0) =
         (if b2 then (1 : UInt32) <<< shift else 0)) : b1 = b2 := by
  cases b1 <;> cases b2
  · rfl
  · exact absurd h.symm hne
  · exact absurd h hne
  · rfl

private theorem seccompFlags_toBits_inj {f1 f2 : SeccompFlags}
    (h : f1.toBits = f2.toBits) : f1 = f2 := by
  have hb0 : f1.toBits &&& ((1 : UInt32) <<< 0) = f2.toBits &&& ((1 : UInt32) <<< 0) :=
    congrArg (· &&& ((1 : UInt32) <<< 0)) h
  have hb1 : f1.toBits &&& ((1 : UInt32) <<< 1) = f2.toBits &&& ((1 : UInt32) <<< 1) :=
    congrArg (· &&& ((1 : UInt32) <<< 1)) h
  have hb2 : f1.toBits &&& ((1 : UInt32) <<< 2) = f2.toBits &&& ((1 : UInt32) <<< 2) :=
    congrArg (· &&& ((1 : UInt32) <<< 2)) h
  have hb4 : f1.toBits &&& ((1 : UInt32) <<< 4) = f2.toBits &&& ((1 : UInt32) <<< 4) :=
    congrArg (· &&& ((1 : UInt32) <<< 4)) h
  have hb5 : f1.toBits &&& ((1 : UInt32) <<< 5) = f2.toBits &&& ((1 : UInt32) <<< 5) :=
    congrArg (· &&& ((1 : UInt32) <<< 5)) h
  have m0 : ∀ f : SeccompFlags, f.toBits &&& ((1 : UInt32) <<< 0) =
      if f.tsync then (1 : UInt32) <<< 0 else 0 := fun f => by
    unfold SeccompFlags.toBits
    dsimp only
    repeat rw [ui32_or_and_distrib]
    rw [ui32_bit_and_self f.tsync 0 (by decide),
      ui32_bit_and_mask f.log 1 ((1 : UInt32) <<< 0) (by decide),
      ui32_bit_and_mask f.specAllow 2 ((1 : UInt32) <<< 0) (by decide),
      ui32_bit_and_mask f.tsyncEsrch 4 ((1 : UInt32) <<< 0) (by decide),
      ui32_bit_and_mask f.waitKillableRecv 5 ((1 : UInt32) <<< 0) (by decide)]
    simp only [ui32_or_zero]
  have m1 : ∀ f : SeccompFlags, f.toBits &&& ((1 : UInt32) <<< 1) =
      if f.log then (1 : UInt32) <<< 1 else 0 := fun f => by
    unfold SeccompFlags.toBits
    dsimp only
    repeat rw [ui32_or_and_distrib]
    rw [ui32_bit_and_mask f.tsync 0 ((1 : UInt32) <<< 1) (by decide),
      ui32_bit_and_self f.log 1 (by decide),
      ui32_bit_and_mask f.specAllow 2 ((1 : UInt32) <<< 1) (by decide),
      ui32_bit_and_mask f.tsyncEsrch 4 ((1 : UInt32) <<< 1) (by decide),
      ui32_bit_and_mask f.waitKillableRecv 5 ((1 : UInt32) <<< 1) (by decide)]
    simp only [ui32_zero_or, ui32_or_zero]
  have m2 : ∀ f : SeccompFlags, f.toBits &&& ((1 : UInt32) <<< 2) =
      if f.specAllow then (1 : UInt32) <<< 2 else 0 := fun f => by
    unfold SeccompFlags.toBits
    dsimp only
    repeat rw [ui32_or_and_distrib]
    rw [ui32_bit_and_mask f.tsync 0 ((1 : UInt32) <<< 2) (by decide),
      ui32_bit_and_mask f.log 1 ((1 : UInt32) <<< 2) (by decide),
      ui32_bit_and_self f.specAllow 2 (by decide),
      ui32_bit_and_mask f.tsyncEsrch 4 ((1 : UInt32) <<< 2) (by decide),
      ui32_bit_and_mask f.waitKillableRecv 5 ((1 : UInt32) <<< 2) (by decide)]
    simp only [ui32_zero_or, ui32_or_zero]
  have m4 : ∀ f : SeccompFlags, f.toBits &&& ((1 : UInt32) <<< 4) =
      if f.tsyncEsrch then (1 : UInt32) <<< 4 else 0 := fun f => by
    unfold SeccompFlags.toBits
    dsimp only
    repeat rw [ui32_or_and_distrib]
    rw [ui32_bit_and_mask f.tsync 0 ((1 : UInt32) <<< 4) (by decide),
      ui32_bit_and_mask f.log 1 ((1 : UInt32) <<< 4) (by decide),
      ui32_bit_and_mask f.specAllow 2 ((1 : UInt32) <<< 4) (by decide),
      ui32_bit_and_self f.tsyncEsrch 4 (by decide),
      ui32_bit_and_mask f.waitKillableRecv 5 ((1 : UInt32) <<< 4) (by decide)]
    simp only [ui32_zero_or, ui32_or_zero]
  have m5 : ∀ f : SeccompFlags, f.toBits &&& ((1 : UInt32) <<< 5) =
      if f.waitKillableRecv then (1 : UInt32) <<< 5 else 0 := fun f => by
    unfold SeccompFlags.toBits
    dsimp only
    repeat rw [ui32_or_and_distrib]
    rw [ui32_bit_and_mask f.tsync 0 ((1 : UInt32) <<< 5) (by decide),
      ui32_bit_and_mask f.log 1 ((1 : UInt32) <<< 5) (by decide),
      ui32_bit_and_mask f.specAllow 2 ((1 : UInt32) <<< 5) (by decide),
      ui32_bit_and_mask f.tsyncEsrch 4 ((1 : UInt32) <<< 5) (by decide),
      ui32_bit_and_self f.waitKillableRecv 5 (by decide)]
    simp only [ui32_zero_or]
  rw [m0 f1, m0 f2] at hb0
  rw [m1 f1, m1 f2] at hb1
  rw [m2 f1, m2 f2] at hb2
  rw [m4 f1, m4 f2] at hb4
  rw [m5 f1, m5 f2] at hb5
  cases f1; cases f2
  dsimp only at hb0 hb1 hb2 hb4 hb5
  congr 1
  · exact bool_of_ui32_bit_eq (by decide) hb0
  · exact bool_of_ui32_bit_eq (by decide) hb1
  · exact bool_of_ui32_bit_eq (by decide) hb2
  · exact bool_of_ui32_bit_eq (by decide) hb4
  · exact bool_of_ui32_bit_eq (by decide) hb5

private theorem memfdFlags_toBits_inj {f1 f2 : MemfdFlags}
    (h : f1.toBits = f2.toBits) : f1 = f2 := by
  have hb0 : f1.toBits &&& ((1 : UInt32) <<< 0) = f2.toBits &&& ((1 : UInt32) <<< 0) :=
    congrArg (· &&& ((1 : UInt32) <<< 0)) h
  have hb1 : f1.toBits &&& ((1 : UInt32) <<< 1) = f2.toBits &&& ((1 : UInt32) <<< 1) :=
    congrArg (· &&& ((1 : UInt32) <<< 1)) h
  have hb3 : f1.toBits &&& ((1 : UInt32) <<< 3) = f2.toBits &&& ((1 : UInt32) <<< 3) :=
    congrArg (· &&& ((1 : UInt32) <<< 3)) h
  have hb4 : f1.toBits &&& ((1 : UInt32) <<< 4) = f2.toBits &&& ((1 : UInt32) <<< 4) :=
    congrArg (· &&& ((1 : UInt32) <<< 4)) h
  have m0 : ∀ f : MemfdFlags, f.toBits &&& ((1 : UInt32) <<< 0) =
      if f.cloexec then (1 : UInt32) <<< 0 else 0 := fun f => by
    unfold MemfdFlags.toBits
    dsimp only
    repeat rw [ui32_or_and_distrib]
    rw [ui32_bit_and_self f.cloexec 0 (by decide),
      ui32_bit_and_mask f.allowSealing 1 ((1 : UInt32) <<< 0) (by decide),
      ui32_bit_and_mask f.noexecSeal 3 ((1 : UInt32) <<< 0) (by decide),
      ui32_bit_and_mask f.exec 4 ((1 : UInt32) <<< 0) (by decide)]
    simp only [ui32_or_zero]
  have m1 : ∀ f : MemfdFlags, f.toBits &&& ((1 : UInt32) <<< 1) =
      if f.allowSealing then (1 : UInt32) <<< 1 else 0 := fun f => by
    unfold MemfdFlags.toBits
    dsimp only
    repeat rw [ui32_or_and_distrib]
    rw [ui32_bit_and_mask f.cloexec 0 ((1 : UInt32) <<< 1) (by decide),
      ui32_bit_and_self f.allowSealing 1 (by decide),
      ui32_bit_and_mask f.noexecSeal 3 ((1 : UInt32) <<< 1) (by decide),
      ui32_bit_and_mask f.exec 4 ((1 : UInt32) <<< 1) (by decide)]
    simp only [ui32_zero_or, ui32_or_zero]
  have m3 : ∀ f : MemfdFlags, f.toBits &&& ((1 : UInt32) <<< 3) =
      if f.noexecSeal then (1 : UInt32) <<< 3 else 0 := fun f => by
    unfold MemfdFlags.toBits
    dsimp only
    repeat rw [ui32_or_and_distrib]
    rw [ui32_bit_and_mask f.cloexec 0 ((1 : UInt32) <<< 3) (by decide),
      ui32_bit_and_mask f.allowSealing 1 ((1 : UInt32) <<< 3) (by decide),
      ui32_bit_and_self f.noexecSeal 3 (by decide),
      ui32_bit_and_mask f.exec 4 ((1 : UInt32) <<< 3) (by decide)]
    simp only [ui32_zero_or, ui32_or_zero]
  have m4 : ∀ f : MemfdFlags, f.toBits &&& ((1 : UInt32) <<< 4) =
      if f.exec then (1 : UInt32) <<< 4 else 0 := fun f => by
    unfold MemfdFlags.toBits
    dsimp only
    repeat rw [ui32_or_and_distrib]
    rw [ui32_bit_and_mask f.cloexec 0 ((1 : UInt32) <<< 4) (by decide),
      ui32_bit_and_mask f.allowSealing 1 ((1 : UInt32) <<< 4) (by decide),
      ui32_bit_and_mask f.noexecSeal 3 ((1 : UInt32) <<< 4) (by decide),
      ui32_bit_and_self f.exec 4 (by decide)]
    simp only [ui32_zero_or]
  rw [m0 f1, m0 f2] at hb0
  rw [m1 f1, m1 f2] at hb1
  rw [m3 f1, m3 f2] at hb3
  rw [m4 f1, m4 f2] at hb4
  cases f1; cases f2
  dsimp only at hb0 hb1 hb3 hb4
  congr 1
  · exact bool_of_ui32_bit_eq (by decide) hb0
  · exact bool_of_ui32_bit_eq (by decide) hb1
  · exact bool_of_ui32_bit_eq (by decide) hb3
  · exact bool_of_ui32_bit_eq (by decide) hb4

private theorem prctlOp_toRaw_inj {p1 p2 : PrctlOp}
    (h : p1.toRaw = p2.toRaw) : p1 = p2 := by
  cases p1 <;> cases p2 <;> simp [PrctlOp.toRaw] at h ⊢
  · rename_i b1 b2; cases b1 <;> cases b2 <;> simp_all
  · exact h

private theorem seccompFlags_beq_iff (a b : SeccompFlags) : (a == b) = true ↔ a = b := by
  cases a; cases b; simp [BEq.beq, instBEqSeccompFlags.beq]

private theorem memfdFlags_beq_iff (a b : MemfdFlags) : (a == b) = true ↔ a = b := by
  cases a; cases b; simp [BEq.beq, instBEqMemfdFlags.beq]

private theorem prctlOp_beq_iff (a b : PrctlOp) : (a == b) = true ↔ a = b := by
  cases a <;> cases b <;> simp [BEq.beq, instBEqPrctlOp.beq]

private theorem hasEmbeddedNul_mkRepBytes_97 :
    ∀ n, (List.replicate n (97 : UInt8)).any (· == (0 : UInt8)) = false
  | 0 => rfl
  | n + 1 => hasEmbeddedNul_mkRepBytes_97 n

private theorem mkRepBytes_size (n : Nat) : (mkRepBytes n).data.size = n := by
  unfold mkRepBytes
  rw [List.size_toArray, List.length_replicate]

private theorem mkRepBytes_noNul (n : Nat) : hasEmbeddedNul (mkRepBytes n) = false := by
  rw [hasEmbeddedNul_eq_toList_any]
  unfold mkRepBytes
  rw [List.toList_toArray]
  exact hasEmbeddedNul_mkRepBytes_97 n

private theorem decode_encodeSockFilterList (prog : List SockFilterInsn) :
    decodeSockFilterList (prog.flatMap encodeSockFilterInsn) = some prog := by
  induction prog with
  | nil => rfl
  | cons insn rest ih =>
    simp only [List.flatMap_cons, encodeSockFilterInsn, List.cons_append, List.nil_append]
    unfold decodeSockFilterList
    rw [ih]
    have hCode : UInt16.ofNat
        ((UInt8.ofNat (insn.code.toNat % 256)).toNat +
          (UInt8.ofNat ((insn.code.toNat / 256) % 256)).toNat * 256) = insn.code := by
      apply UInt16.toNat_inj.mp
      have hc : insn.code.toNat < 65536 := insn.code.toBitVec.isLt
      simp only [UInt16.toNat_ofNat', UInt8.toNat_ofNat']
      omega
    have hk : UInt32.ofNat
        ((UInt8.ofNat (insn.k.toNat % 256)).toNat +
          (UInt8.ofNat ((insn.k.toNat / 256) % 256)).toNat * 256 +
          (UInt8.ofNat ((insn.k.toNat / 65536) % 256)).toNat * 65536 +
          (UInt8.ofNat ((insn.k.toNat / 16777216) % 256)).toNat * 16777216) = insn.k := by
      apply UInt32.toNat_inj.mp
      have hkt : insn.k.toNat < 4294967296 := insn.k.toBitVec.isLt
      simp only [UInt32.toNat_ofNat', UInt8.toNat_ofNat']
      omega
    rw [hCode, hk]

private theorem decodeSockFilterList_len_mod8 :
    ∀ (xs : List UInt8) (prog : List SockFilterInsn),
      decodeSockFilterList xs = some prog → xs.length % 8 = 0
  | [], _, _ => rfl
  | [_], _, h => by simp [decodeSockFilterList] at h
  | [_, _], _, h => by simp [decodeSockFilterList] at h
  | [_, _, _], _, h => by simp [decodeSockFilterList] at h
  | [_, _, _, _], _, h => by simp [decodeSockFilterList] at h
  | [_, _, _, _, _], _, h => by simp [decodeSockFilterList] at h
  | [_, _, _, _, _, _], _, h => by simp [decodeSockFilterList] at h
  | [_, _, _, _, _, _, _], _, h => by simp [decodeSockFilterList] at h
  | _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: rest, prog, h => by
    unfold decodeSockFilterList at h
    cases hRec : decodeSockFilterList rest with
    | none => rw [hRec] at h; contradiction
    | some tail =>
      have ih := decodeSockFilterList_len_mod8 rest tail hRec
      simp only [List.length_cons]
      omega

private theorem byteArray_get!_eq (b : ByteArray) (j : Nat) (hj : j < b.size) :
    b.get! j = b.data[j]'(by exact hj) := by
  have h1 : b.get! j = b.data[j]! := rfl
  rw [h1]
  exact getElem!_pos b.data j hj

private theorem decodeSockFilterBytesAux_eq (b : ByteArray) :
    ∀ (n i : Nat) (acc : List SockFilterInsn),
      i + n * 8 = b.size →
      some (decodeSockFilterBytesAux b i acc n) =
        (decodeSockFilterList (b.data.toList.drop i)).map (acc.reverse ++ ·)
  | 0, i, acc, hEq => by
    have hi : b.data.toList.length ≤ i := by
      have : b.data.toList.length = b.size := Array.length_toList
      omega
    rw [List.drop_of_length_le hi]
    simp [decodeSockFilterBytesAux, decodeSockFilterList]
  | n + 1, i, acc, hEq => by
    have hi8 : i + 8 ≤ b.size := by omega
    have hLen : b.data.toList.length = b.size := Array.length_toList
    have hDrop : ∀ k, k < 8 →
        b.data.toList.drop (i + k) =
          (b.get! (i + k)) :: b.data.toList.drop (i + k + 1) := by
      intro k hk
      have hjk : i + k < b.data.toList.length := by omega
      rw [List.drop_eq_getElem_cons hjk, byteArray_get!_eq b (i + k) (by omega)]
      simp
    have h8 : b.data.toList.drop i =
        b.get! i :: b.get! (i + 1) :: b.get! (i + 2) :: b.get! (i + 3) ::
          b.get! (i + 4) :: b.get! (i + 5) :: b.get! (i + 6) :: b.get! (i + 7) ::
            b.data.toList.drop (i + 8) := by
      rw [show i = i + 0 from rfl, hDrop 0 (by omega),
          hDrop 1 (by omega), hDrop 2 (by omega), hDrop 3 (by omega),
          hDrop 4 (by omega), hDrop 5 (by omega), hDrop 6 (by omega), hDrop 7 (by omega)]
    rw [h8]
    unfold decodeSockFilterList decodeSockFilterBytesAux
    have ih := decodeSockFilterBytesAux_eq b n (i + 8)
      ({ code := UInt16.ofNat ((b.get! i).toNat + (b.get! (i + 1)).toNat * 256),
         jt := b.get! (i + 2), jf := b.get! (i + 3),
         k := UInt32.ofNat ((b.get! (i + 4)).toNat + (b.get! (i + 5)).toNat * 256 +
           (b.get! (i + 6)).toNat * 65536 + (b.get! (i + 7)).toNat * 16777216) } :: acc)
      (by omega)
    cases hRec : decodeSockFilterList (b.data.toList.drop (i + 8)) with
    | none => simp [hRec] at ih
    | some tail =>
      simp only [Option.map_some] at ih ⊢
      rw [hRec, Option.map_some] at ih
      simp only [List.reverse_cons, List.append_assoc, List.singleton_append] at ih
      exact ih

private theorem decodeSockFilters_eq_list (b : ByteArray) :
    decodeSockFilters b = decodeSockFilterList b.data.toList := by
  unfold decodeSockFilters
  by_cases hMod : b.size % 8 = 0
  · have hB : (b.size % 8 != 0) = false := by simp [hMod]
    simp only [hB, Bool.false_eq_true, ↓reduceIte]
    have hEq := decodeSockFilterBytesAux_eq b (b.size / 8) 0 [] (by omega)
    simpa using hEq
  · have hB : (b.size % 8 != 0) = true := bne_iff_ne.mpr hMod
    simp only [hB, ↓reduceIte]
    cases hDec : decodeSockFilterList b.data.toList with
    | none => rfl
    | some p =>
      have hm := decodeSockFilterList_len_mod8 b.data.toList p hDec
      have hLen : b.data.toList.length = b.size := Array.length_toList
      omega

/-- Every `Errno` satisfies the `Sandbox` transient classification and `SandboxErrorKind.ofErrno` bucket mapping. -/
theorem sandbox_errno_classificationAndConstants_allPass :
    AllPass (test_sandbox_errno_classificationAndConstants
      Errno.isTransientOsErrno SandboxErrorKind.ofErrno) := by
  intro e
  dsimp only [AllPass, NondetTest.assert]
  refine ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl⟩, ⟨rfl, ⟨rfl, ⟨rfl, ⟨⟨rfl, rfl⟩, ⟨⟨rfl, rfl⟩, ⟨⟨rfl, rfl⟩,
    ⟨⟨rfl, rfl, rfl, rfl, rfl⟩, ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl⟩, trivial⟩⟩⟩⟩⟩⟩⟩⟩⟩

/-- Every `SeccompFlags`, `PrctlOp`, `RlimitResource`, `MemfdFlags` encoder is injective with exact wire encodings and invertible 8-byte `sock_filter` codec. -/
theorem sandbox_flags_andBpfCodecInjective_allPass :
    AllPass (test_sandbox_flags_andBpfCodecInjective
      SeccompFlags.toBits PrctlOp.toRaw RlimitResource.toTag MemfdFlags.toBits
      encodeSockFilters decodeSockFilters) := by
  intro sf1 sf2
  dsimp only [AllPass, NondetTest.assert]
  refine ⟨?_, ?_, ?_, ?_⟩
  · cases hEq : (sf1 == sf2)
    · have hNe : sf1 ≠ sf2 := fun h => by
        have := (seccompFlags_beq_iff sf1 sf2).mpr h
        rw [this] at hEq; cases hEq
      have hBitsNe : sf1.toBits ≠ sf2.toBits := fun h => hNe (seccompFlags_toBits_inj h)
      simp [beq_eq_false_iff_ne, hBitsNe]
    · rw [(seccompFlags_beq_iff sf1 sf2).mp hEq]; simp
  · exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  · unfold SeccompFlags.toBits; rfl
  · intro p1 p2 sig
    refine ⟨?_, ?_, ?_⟩
    · cases hEq : (p1 == p2)
      · have hNe : p1 ≠ p2 := fun h => by
          have := (prctlOp_beq_iff p1 p2).mpr h
          rw [this] at hEq; cases hEq
        have hRawNe : p1.toRaw ≠ p2.toRaw := fun h => hNe (prctlOp_toRaw_inj h)
        simp [beq_eq_false_iff_ne, hRawNe]
      · rw [(prctlOp_beq_iff p1 p2).mp hEq]; simp
    · exact ⟨rfl, rfl, rfl, rfl, rfl⟩
    · intro r1 r2
      refine ⟨?_, ?_, ?_⟩
      · cases r1 <;> cases r2 <;> decide
      · exact ⟨rfl, rfl, rfl⟩
      · intro m1 m2
        refine ⟨?_, ?_, ?_, ?_⟩
        · cases hEq : (m1 == m2)
          · have hNe : m1 ≠ m2 := fun h => by
              have := (memfdFlags_beq_iff m1 m2).mpr h
              rw [this] at hEq; cases hEq
            have hBitsNe : m1.toBits ≠ m2.toBits := fun h => hNe (memfdFlags_toBits_inj h)
            simp [beq_eq_false_iff_ne, hBitsNe]
          · rw [(memfdFlags_beq_iff m1 m2).mp hEq]; simp
        · exact ⟨rfl, rfl, rfl, rfl, rfl⟩
        · unfold MemfdFlags.toBits; rfl
        · intro insn
          refine ⟨?_, ?_⟩
          · simp [encodeSockFilters, encodeSockFilterInsn]
          · intro prog
            refine ⟨?_, ?_⟩
            · rw [decodeSockFilters_eq_list]; unfold encodeSockFilters
              exact decode_encodeSockFilterList prog
            · intro oddBytes hOdd
              refine ⟨?_, trivial⟩
              cases hDec : decodeSockFilters oddBytes with
              | none => rfl
              | some p =>
                rw [decodeSockFilters_eq_list] at hDec
                have hMod := decodeSockFilterList_len_mod8 oddBytes.data.toList p hDec
                rw [Array.length_toList] at hMod
                exact absurd hMod hOdd

/-- Reachability witness for `test_sandbox_flags_andBpfCodecInjective`. -/
theorem sandbox_flags_andBpfCodecInjective_canReach :
    CanReach (test_sandbox_flags_andBpfCodecInjective
      SeccompFlags.toBits PrctlOp.toRaw RlimitResource.toTag MemfdFlags.toBits
      encodeSockFilters decodeSockFilters) := by
  refine ⟨{}, {}, ?_, ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩, rfl,
    .getNoNewPrivs, .getNoNewPrivs, 0, rfl, ⟨rfl, rfl, rfl, rfl, rfl⟩,
    .core, .core, rfl, ⟨rfl, rfl, rfl⟩,
    {}, {}, rfl, ⟨rfl, rfl, rfl, rfl, rfl⟩, rfl,
    { code := 0x0006, jt := 0, jf := 0, k := SECCOMP_RET_ALLOW }, rfl,
    [], rfl, ByteArray.mk #[1], by decide, rfl, trivial⟩
  decide

/-- `Internal.mkSandboxOps` makes `0` raw hook calls on guarded failures and `1` call forwarding `.ok`/`.error` faithfully. -/
theorem sandbox_impl_wrapperGuards_allPass :
    AllPass (test_sandbox_impl_wrapperGuards Internal.mkSandboxOps) := by
  intro attr qFlags hq nzSecFlags hnz scFlags act prOp rlRes rlCur rlMax mfdFlags rawErr
  intro badNul hNul overName hOver okName ⟨hOkNul, hOkSize⟩
  intro badFilter hBadF okFilter ⟨hOkLen, hOkMod, hOkMax, hOkSafe⟩
  dsimp only [AllPass, test_sandbox_impl_wrapperGuards, NondetTest.assert, Internal.mkSandboxOps,
    StateT.run, Id.run, Pure.pure, Bind.bind, StateT.bind, StateT.pure, modify, modifyGet,
    MonadStateOf.modifyGet, StateT.modifyGet]
  have hqB : (qFlags == 0) = false := beq_false_of_ne hq
  have hqBne : (qFlags != 0) = true := bne_iff_ne.mpr hq
  have hnzB : (nzSecFlags.toBits != 0) = true := bne_iff_ne.mpr hnz
  have hBadFCheck :
      (!isValidSeccompFilterByteLen badFilter.data.size || !hasSafeSeccompRetBytes badFilter) = true := by
    unfold isValidSeccompFilterByteLen
    rcases hBadF with h0 | h8 | hMax | hSafe
    · simp only [h0, Nat.lt_irrefl, decide_false, Bool.false_and, Bool.not_false, Bool.true_or]
    · have : (badFilter.data.size % 8 == 0) = false := beq_false_of_ne h8
      simp only [this, Bool.and_false, Bool.false_and, Bool.not_false, Bool.true_or]
    · have : decide (badFilter.data.size ≤ SECCOMP_MAX_FILTER_INSNS * 8) = false :=
        decide_eq_false (Nat.not_le_of_gt hMax)
      simp only [this, Bool.and_false, Bool.not_false, Bool.true_or]
    · simp only [hSafe, Bool.not_false, Bool.or_true]
  have hOkFCheck :
      (!isValidSeccompFilterByteLen okFilter.data.size || !hasSafeSeccompRetBytes okFilter) = false := by
    unfold isValidSeccompFilterByteLen
    have hGt : decide (0 < okFilter.data.size) = true := decide_eq_true hOkLen
    have hModB : (okFilter.data.size % 8 == 0) = true := beq_iff_eq.mpr hOkMod
    have hLe : decide (okFilter.data.size ≤ SECCOMP_MAX_FILTER_INSNS * 8) = true := decide_eq_true hOkMax
    simp only [hGt, hModB, hLe, Bool.and_true, Bool.not_true, hOkSafe, Bool.or_self]
  have hOverB : decide (MFD_NAME_MAX < overName.data.size) = true := decide_eq_true hOver
  have hOkSizeB : decide (MFD_NAME_MAX < okName.data.size) = false :=
    decide_eq_false (Nat.not_lt_of_ge hOkSize)
  have hEmptySecBits : ({ } : SeccompFlags).toBits = 0 := rfl
  simp only [StateT.pure, StateT.bind, StateT.modifyGet, Pure.pure, Bind.bind,
    hqB, hqBne, hnzB, hBadFCheck, hOkFCheck, hNul, hOverB, hOkNul, hOkSizeB,
    hEmptySecBits, ByteArray.size, Bool.true_or, Bool.or_true, Bool.false_or, Bool.false_eq_true, ↓reduceIte,
    bne_self_eq_false, beq_self_eq_true, Bool.and_self, Nat.zero_add]
  repeat first | exact trivial | exact rfl | refine ⟨?_, ?_⟩

/-- Reachability witness for `test_sandbox_impl_wrapperGuards`. -/
theorem sandbox_impl_wrapperGuards_canReach :
    CanReach (test_sandbox_impl_wrapperGuards Internal.mkSandboxOps) := by
  refine ⟨{}, 1, by decide, { tsync := true }, by decide, {}, SECCOMP_RET_ALLOW,
    .getNoNewPrivs, .core, 0, 0, {}, Errno.EIO,
    ByteArray.mk #[0], by decide,
    mkRepBytes 250, ?_,
    ByteArray.mk #[97], ⟨by decide, by decide⟩,
    ByteArray.empty, Or.inl rfl,
    allowAllSeccompFilterBytes, ⟨by decide, by decide, by decide, by decide⟩, ?_⟩
  · rw [mkRepBytes_size]; decide
  · have h250Sz : decide (MFD_NAME_MAX < (mkRepBytes 250).data.size) = true := by
      rw [mkRepBytes_size]; decide
    dsimp only [test_sandbox_impl_wrapperGuards, CanReachRun, NondetTest.assert,
      Internal.mkSandboxOps, StateT.run, Id.run, Pure.pure, Bind.bind, StateT.bind, StateT.pure,
      modify, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet]
    simp only [h250Sz, ByteArray.size, Bool.true_or, ↓reduceIte]
    repeat first | exact trivial | exact rfl | refine ⟨?_, ?_⟩

/-- `Internal.mkSandboxOps` rejects all unsafe seccomp instructions and forwards all safe actions. -/
theorem sandbox_impl_seccompSafetyGuards_allPass :
    AllPass (test_sandbox_impl_seccompSafetyGuards Internal.mkSandboxOps) := by
  intro scFlags
  dsimp only [AllPass, test_sandbox_impl_seccompSafetyGuards, NondetTest.assert,
    Internal.mkSandboxOps, StateT.run, Pure.pure, Bind.bind, StateT.bind, StateT.pure,
    modify, modifyGet, MonadStateOf.modifyGet]
  have hBad1 : (!isValidSeccompFilterByteLen (encodeSockFilters [{ code := 0x0006, jt := 0, jf := 0, k := SECCOMP_RET_ERRNO }]).data.size ||
      !hasSafeSeccompRetBytes (encodeSockFilters [{ code := 0x0006, jt := 0, jf := 0, k := SECCOMP_RET_ERRNO }])) = true := by decide
  have hBad2 : (!isValidSeccompFilterByteLen (encodeSockFilters [{ code := 0x0006, jt := 0, jf := 0, k := SECCOMP_RET_ERRNO ||| Errno.EFAULT }]).data.size ||
      !hasSafeSeccompRetBytes (encodeSockFilters [{ code := 0x0006, jt := 0, jf := 0, k := SECCOMP_RET_ERRNO ||| Errno.EFAULT }])) = true := by decide
  have hBad3 : (!isValidSeccompFilterByteLen (encodeSockFilters [{ code := 0x0006, jt := 0, jf := 0, k := SECCOMP_RET_KILL_PROCESS }]).data.size ||
      !hasSafeSeccompRetBytes (encodeSockFilters [{ code := 0x0006, jt := 0, jf := 0, k := SECCOMP_RET_KILL_PROCESS }])) = true := by decide
  have hBad4 : (!isValidSeccompFilterByteLen (encodeSockFilters [{ code := 0x0006, jt := 0, jf := 0, k := SECCOMP_RET_KILL_THREAD }]).data.size ||
      !hasSafeSeccompRetBytes (encodeSockFilters [{ code := 0x0006, jt := 0, jf := 0, k := SECCOMP_RET_KILL_THREAD }])) = true := by decide
  have hBad5 : (!isValidSeccompFilterByteLen (encodeSockFilters [{ code := 0x0006, jt := 0, jf := 0, k := SECCOMP_RET_TRAP }]).data.size ||
      !hasSafeSeccompRetBytes (encodeSockFilters [{ code := 0x0006, jt := 0, jf := 0, k := SECCOMP_RET_TRAP }])) = true := by decide
  have hBad6 : (!isValidSeccompFilterByteLen (encodeSockFilters [{ code := 0x0006, jt := 0, jf := 0, k := 0x12340000 }]).data.size ||
      !hasSafeSeccompRetBytes (encodeSockFilters [{ code := 0x0006, jt := 0, jf := 0, k := 0x12340000 }])) = true := by decide
  have hBad7 : (!isValidSeccompFilterByteLen (encodeSockFilters [{ code := 0x0016, jt := 0, jf := 0, k := SECCOMP_RET_ALLOW }]).data.size ||
      !hasSafeSeccompRetBytes (encodeSockFilters [{ code := 0x0016, jt := 0, jf := 0, k := SECCOMP_RET_ALLOW }])) = true := by decide
  have hBad8 : (!isValidSeccompFilterByteLen (encodeSockFilters [{ code := 0x000e, jt := 0, jf := 0, k := SECCOMP_RET_ALLOW }]).data.size ||
      !hasSafeSeccompRetBytes (encodeSockFilters [{ code := 0x000e, jt := 0, jf := 0, k := SECCOMP_RET_ALLOW }])) = true := by decide
  have hBad9 : (!isValidSeccompFilterByteLen (encodeSockFilters [{ code := 0x003c, jt := 0, jf := 0, k := 0 }, { code := 0x0006, jt := 0, jf := 0, k := SECCOMP_RET_ALLOW }]).data.size ||
      !hasSafeSeccompRetBytes (encodeSockFilters [{ code := 0x003c, jt := 0, jf := 0, k := 0 }, { code := 0x0006, jt := 0, jf := 0, k := SECCOMP_RET_ALLOW }])) = true := by decide
  have hBad10 : (!isValidSeccompFilterByteLen (encodeSockFilters [{ code := 0x0006, jt := 0, jf := 0, k := SECCOMP_RET_TRACE ||| 7 }]).data.size ||
      !hasSafeSeccompRetBytes (encodeSockFilters [{ code := 0x0006, jt := 0, jf := 0, k := SECCOMP_RET_TRACE ||| 7 }])) = true := by decide
  have hBad11 : (!isValidSeccompFilterByteLen (encodeSockFilters [{ code := 0x0006, jt := 0, jf := 0, k := SECCOMP_RET_USER_NOTIF }]).data.size ||
      !hasSafeSeccompRetBytes (encodeSockFilters [{ code := 0x0006, jt := 0, jf := 0, k := SECCOMP_RET_USER_NOTIF }])) = true := by decide
  have hOk1 : (!isValidSeccompFilterByteLen (encodeSockFilters [{ code := 0x0006, jt := 0, jf := 0, k := SECCOMP_RET_ALLOW }]).data.size ||
      !hasSafeSeccompRetBytes (encodeSockFilters [{ code := 0x0006, jt := 0, jf := 0, k := SECCOMP_RET_ALLOW }])) = false := by decide
  have hOk2 : (!isValidSeccompFilterByteLen (encodeSockFilters [{ code := 0x0006, jt := 0, jf := 0, k := SECCOMP_RET_LOG }]).data.size ||
      !hasSafeSeccompRetBytes (encodeSockFilters [{ code := 0x0006, jt := 0, jf := 0, k := SECCOMP_RET_LOG }])) = false := by decide
  have hOk5 : (!isValidSeccompFilterByteLen (encodeSockFilters [{ code := 0x0006, jt := 0, jf := 0, k := SECCOMP_RET_ERRNO ||| Errno.EPERM }]).data.size ||
      !hasSafeSeccompRetBytes (encodeSockFilters [{ code := 0x0006, jt := 0, jf := 0, k := SECCOMP_RET_ERRNO ||| Errno.EPERM }])) = false := by decide
  have hOk6 : (!isValidSeccompFilterByteLen (encodeSockFilters [{ code := 0x0006, jt := 0, jf := 0, k := SECCOMP_RET_ERRNO ||| 4095 }]).data.size ||
      !hasSafeSeccompRetBytes (encodeSockFilters [{ code := 0x0006, jt := 0, jf := 0, k := SECCOMP_RET_ERRNO ||| 4095 }])) = false := by decide
  simp only [ByteArray.size, hBad1, hBad2, hBad3, hBad4, hBad5, hBad6, hBad7, hBad8, hBad9,
    hBad10, hBad11, hOk1, hOk2, hOk5, hOk6, ↓reduceIte, Bool.false_eq_true]
  repeat first | exact trivial | exact rfl | refine ⟨?_, ?_⟩

end LeanSwe.LinuxSyscall.Sandbox
