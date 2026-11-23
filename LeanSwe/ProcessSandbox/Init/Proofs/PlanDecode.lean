import LeanSwe.ProcessSandbox.Init.Proofs.PlanPrimitives

/-!
# ProcessSandbox Init `LSWP0002` Full Plan Decoder Agreement Proofs

Machine-checked agreement and rejection theorems for `psandbox_init::plan` and
`psandbox_init::ops::install_seccomp`:
- Fixed header parsers (`parse_header_part1`, `parse_header_part2`, `parse_header_limits`,
  `parse_header`) agreeing with `encodePlanPrefix`,
- Single-entry readers (`read_sys_entry`, `read_mount_entry`) and section loop scanners
  (`scan_str_list`, `scan_env_list`, `scan_sys_entries`, `scan_mounts`),
- End-to-end `parse_plan_agrees_with_encodePlan`: whenever host
  `LeanSwe.ProcessSandbox.Raw.Internal.encodePlan` succeeds within the wire section-count caps,
  `psandbox_init::plan::parse_plan` succeeds and recovers the exact header fields, `program` and
  `cwd` UTF-8 spans, section counts, `seccomp` instruction count (`1..160`), and `seccomp` filter
  trailer slice,
- `install_seccomp_valid_view_spec`: when `s.seccompErr? = none`, `ops.install_seccomp` succeeds
  on any `PlanView` produced by `parse_plan` and appends `(.syscall, view.seccomp_n)` to
  `s.seccompInstalled` (`ENOSYS` `prctl` fallback and `seccompErr?` / `prctlSeccompErr?` error
  branches are proved in `OracleOps.install_seccomp_fallback_spec`),
- Rejection theorems (`parse_plan_rejects_short_magic`, `parse_header_part1_rejects_low_abi`,
  `validate_seccomp_trailer_rejects_zero`, `validate_seccomp_trailer_rejects_over_160`,
  `validate_seccomp_trailer_rejects_trailing_bytes`).
-/

namespace LeanSwe.ProcessSandbox.Init.Proofs

open _root_.Aeneas _root_.Aeneas.Std Result ControlFlow
open psandbox_init
open LeanSwe.ProcessSandbox.Init.World
open LeanSwe.ProcessSandbox.Raw
  (CompiledSandboxPlan PresetSystemEntry SandboxMount PortForward SandboxError SECCOMP_MAX_INSNS)
open LeanSwe.ProcessSandbox.Raw.Internal
  (pushU8 pushU16LE pushU32LE pushU64LE pushStr boolU8 natToUInt64Sat encodePlanPrefix encodePlan)

/-- Associativity of `ByteArray.append`. -/
theorem byteArray_append_assoc (a b c : ByteArray) :
    (a ++ b) ++ c = a ++ (b ++ c) := by
  cases a with
  | mk da =>
    cases b with
    | mk db =>
      cases c with
      | mk dc =>
        apply ByteArray.ext
        apply Array.toList_inj.mp
        simp

/-- Right identity `a ++ ByteArray.empty = a`. -/
theorem byteArray_append_empty (a : ByteArray) :
    a ++ ByteArray.empty = a := by
  cases a with
  | mk da =>
    apply ByteArray.ext
    apply Array.toList_inj.mp
    simp [ByteArray.empty, ByteArray.emptyWithCapacity]
    rfl

/-- Left identity `ByteArray.empty ++ a = a`. -/
theorem empty_append_byteArray (a : ByteArray) :
    ByteArray.empty ++ a = a := by
  cases a with
  | mk da =>
    apply ByteArray.ext
    apply Array.toList_inj.mp
    simp [ByteArray.empty, ByteArray.emptyWithCapacity]
    rfl

/-- Concatenate a list of `ByteArray` chunks left-to-right. -/
def concatByteArrays : List ByteArray → ByteArray
  | [] => ByteArray.empty
  | b :: bs => b ++ concatByteArrays bs

/-- `byteArrayToBytes` over `concatByteArrays` equals flattening the mapped chunk lists. -/
theorem byteArrayToBytes_concatByteArrays (bss : List ByteArray) :
    byteArrayToBytes (concatByteArrays bss) = (bss.map byteArrayToBytes).flatten := by
  induction bss with
  | nil => rfl
  | cons b bs ih =>
    unfold concatByteArrays
    rw [byteArrayToBytes_append, ih]
    rfl

/-- Encode each element of `xs` independently into a `ByteArray` chunk. -/
def encodeList {α : Type} (f : α → Except SandboxError ByteArray) :
    List α → Except SandboxError (List ByteArray)
  | [] => .ok []
  | x :: xs => do
    let b ← f x
    let bs ← encodeList f xs
    return b :: bs

/-- Length preservation for `encodeList`. -/
theorem encodeList_length {α : Type} {f : α → Except SandboxError ByteArray}
    {xs : List α} {bss : List ByteArray} (h : encodeList f xs = .ok bss) :
    bss.length = xs.length := by
  induction xs generalizing bss with
  | nil =>
    cases h
    rfl
  | cons x xs ih =>
    unfold encodeList at h
    cases hfx : f x with
    | error e =>
      rw [hfx] at h
      cases h
    | ok b =>
      rw [hfx] at h
      cases hRest : encodeList f xs with
      | error e =>
        rw [hRest] at h
        cases h
      | ok bs =>
        rw [hRest] at h
        cases h
        simp [ih hRest]

/-- Membership witness extraction for `encodeList`. -/
theorem encodeList_mem {α : Type} {f : α → Except SandboxError ByteArray}
    {xs : List α} {bss : List ByteArray} (h : encodeList f xs = .ok bss)
    {b : ByteArray} (hb : b ∈ bss) :
    ∃ x ∈ xs, f x = .ok b := by
  induction xs generalizing bss with
  | nil =>
    cases h
    cases hb
  | cons x xs ih =>
    unfold encodeList at h
    cases hfx : f x with
    | error e =>
      rw [hfx] at h
      cases h
    | ok b0 =>
      rw [hfx] at h
      cases hRest : encodeList f xs with
      | error e =>
        rw [hRest] at h
        cases h
      | ok bs =>
        rw [hRest] at h
        cases h
        rcases List.mem_cons.mp hb with rfl | hTail
        · exact ⟨x, List.Mem.head _, hfx⟩
        · obtain ⟨y, hy, hfy⟩ := ih hRest hTail
          exact ⟨y, List.Mem.tail _ hy, hfy⟩

/-- Accumulator-splitting theorem for `forIn` over `List` in `Except SandboxError ByteArray`. -/
theorem list_forIn_encodeList {α : Type}
    (f : α → Except SandboxError ByteArray)
    (step : α → ByteArray → Except SandboxError (ForInStep ByteArray))
    (hStep : ∀ (x : α) (ba : ByteArray),
      step x ba = (f x).map (fun b => ForInStep.yield (ba ++ b)))
    (xs : List α) (init : ByteArray) :
    forIn xs init step = (encodeList f xs).map (fun bss => init ++ concatByteArrays bss) := by
  induction xs generalizing init with
  | nil =>
    change Except.ok init = Except.ok (init ++ ByteArray.empty)
    rw [byteArray_append_empty]
  | cons x xs ih =>
    rw [List.forIn_cons, hStep x init]
    unfold encodeList
    cases hfx : f x with
    | error e => rfl
    | ok b =>
      change forIn xs (init ++ b) step =
        (do let bs ← encodeList f xs; pure (b :: bs)).map (fun bss => init ++ concatByteArrays bss)
      rw [ih (init ++ b)]
      cases encodeList f xs with
      | error e => rfl
      | ok bs =>
        change Except.ok ((init ++ b) ++ concatByteArrays bs) =
          Except.ok (init ++ (b ++ concatByteArrays bs))
        rw [byteArray_append_assoc]

/-- Accumulator-splitting theorem for `forIn` over `Array` in `Except SandboxError ByteArray`. -/
theorem array_forIn_encodeList {α : Type}
    (f : α → Except SandboxError ByteArray)
    (step : α → ByteArray → Except SandboxError (ForInStep ByteArray))
    (hStep : ∀ (x : α) (ba : ByteArray),
      step x ba = (f x).map (fun b => ForInStep.yield (ba ++ b)))
    (arr : _root_.Array α) (init : ByteArray) :
    forIn arr init step =
      (encodeList f arr.toList).map (fun bss => init ++ concatByteArrays bss) := by
  rw [← Array.forIn_toList]
  exact list_forIn_encodeList f step hStep arr.toList init

private theorem u8_boolU8_ne_zero (b : Bool) :
    (u8OfUInt8 (boolU8 b) != 0#u8) = b := by
  cases b <;> decide

/-- `plan.parse_header_part1` accepts valid mandatory flags and `landlockMinAbi ≥ 4`. -/
theorem parse_header_part1_atOffset (data : Slice U8) (pos : Usize)
    (llAbi : Nat) (tail : Bytes)
    (hAbi : 4 ≤ llAbi)
    (h : AtOffset data pos
      (byteArrayToBytes
        (pushU32LE
          (pushU8 (pushU8 (pushU8 (pushU8 (pushU8 ByteArray.empty 1) 1) 1) 1) 1)
          (UInt32.ofNat (Nat.min llAbi (UInt32.size - 1)))))
      tail) :
    ∃ (abiU32 : U32) (pos9 : Usize),
      plan.parse_header_part1 data pos = Result.ok (.Ok (abiU32, pos9)) ∧
      abiU32.val = Nat.min llAbi (UInt32.size - 1) ∧
      4 ≤ abiU32.val ∧
      pos9.val = pos.val + 9 ∧
      AtOffset data pos9 tail [] := by
  let rawU32 := UInt32.ofNat (Nat.min llAbi (UInt32.size - 1))
  have hSeg :
      byteArrayToBytes
        (pushU32LE
          (pushU8 (pushU8 (pushU8 (pushU8 (pushU8 ByteArray.empty 1) 1) 1) 1) 1)
          rawU32) =
      [1#u8] ++ [1#u8] ++ [1#u8] ++ [1#u8] ++ [1#u8] ++
      byteArrayToBytes (pushU32LE ByteArray.empty rawU32) := by
    rw [pushU32LE_eq_append, byteArrayToBytes_append]
    rfl
  have h0 : AtOffset data pos [1#u8]
      ([1#u8] ++ [1#u8] ++ [1#u8] ++ [1#u8] ++ byteArrayToBytes (pushU32LE ByteArray.empty rawU32) ++ tail) := by
    refine ⟨h.1, ?_⟩
    rw [h.2, hSeg]
    simp
  obtain ⟨p1, hr1, hp1, hs1⟩ := read_u8_atOffset data pos 1#u8 _ h0
  have h1 : AtOffset data p1 [1#u8]
      ([1#u8] ++ [1#u8] ++ [1#u8] ++ byteArrayToBytes (pushU32LE ByteArray.empty rawU32) ++ tail) :=
    ⟨hs1.1, by simpa [List.append_assoc] using hs1.2⟩
  obtain ⟨p2, hr2, hp2, hs2⟩ := read_u8_atOffset data p1 1#u8 _ h1
  have h2 : AtOffset data p2 [1#u8]
      ([1#u8] ++ [1#u8] ++ byteArrayToBytes (pushU32LE ByteArray.empty rawU32) ++ tail) :=
    ⟨hs2.1, by simpa [List.append_assoc] using hs2.2⟩
  obtain ⟨p3, hr3, hp3, hs3⟩ := read_u8_atOffset data p2 1#u8 _ h2
  have h3 : AtOffset data p3 [1#u8]
      ([1#u8] ++ byteArrayToBytes (pushU32LE ByteArray.empty rawU32) ++ tail) :=
    ⟨hs3.1, by simpa [List.append_assoc] using hs3.2⟩
  obtain ⟨p4, hr4, hp4, hs4⟩ := read_u8_atOffset data p3 1#u8 _ h3
  have h4 : AtOffset data p4 [1#u8]
      (byteArrayToBytes (pushU32LE ByteArray.empty rawU32) ++ tail) :=
    ⟨hs4.1, by simpa [List.append_assoc] using hs4.2⟩
  obtain ⟨p5, hr5, hp5, hs5⟩ := read_u8_atOffset data p4 1#u8 _ h4
  have h5 : AtOffset data p5 (byteArrayToBytes (pushU32LE ByteArray.empty rawU32)) tail :=
    ⟨hs5.1, by simpa [List.append_nil] using hs5.2⟩
  obtain ⟨p6, hr6, hp6, hs6⟩ := read_u32_le_atOffset data p5 rawU32 tail h5
  have hMinLt : Nat.min llAbi (UInt32.size - 1) < UInt32.size :=
    Nat.lt_of_le_of_lt (Nat.min_le_right _ _) (by decide)
  have hMinGe4 : 4 ≤ Nat.min llAbi (UInt32.size - 1) :=
    Nat.le_min.mpr ⟨hAbi, by decide⟩
  have hAbiVal : (⟨rawU32.toBitVec⟩ : U32).val = Nat.min llAbi (UInt32.size - 1) := by
    change rawU32.toNat = Nat.min llAbi (UInt32.size - 1)
    exact Nat.mod_eq_of_lt hMinLt
  have hGe4 : 4 ≤ (⟨rawU32.toBitVec⟩ : U32).val := by
    rw [hAbiVal]
    exact hMinGe4
  have hGe4Scalar : (⟨rawU32.toBitVec⟩ : U32) ≥ 4#u32 := by
    change (4#u32).val ≤ (⟨rawU32.toBitVec⟩ : U32).val
    exact hGe4
  have hCond :
      ((((((1#u8 != 0#u8) && (1#u8 != 0#u8)) && (1#u8 != 0#u8)) &&
        (1#u8 != 0#u8)) && (1#u8 != 0#u8)) && decide ((⟨rawU32.toBitVec⟩ : U32) ≥ 4#u32)) = true := by
    rw [decide_eq_true hGe4Scalar]
    decide
  refine ⟨⟨rawU32.toBitVec⟩, p6, ?_, hAbiVal, hGe4, by omega, hs6⟩
  rw [plan.parse_header_part1]
  refine eq_ok_of_try_ok hr1 ?_
  refine eq_ok_of_try_ok hr2 ?_
  refine eq_ok_of_try_ok hr3 ?_
  refine eq_ok_of_try_ok hr4 ?_
  refine eq_ok_of_try_ok hr5 ?_
  refine eq_ok_of_try_ok hr6 ?_
  change (if ((((((1#u8 != 0#u8) && (1#u8 != 0#u8)) && (1#u8 != 0#u8)) &&
      (1#u8 != 0#u8)) && (1#u8 != 0#u8)) && decide ((⟨rawU32.toBitVec⟩ : U32) ≥ 4#u32)) = true then
      Result.ok (core.result.Result.Ok ((⟨rawU32.toBitVec⟩ : U32), p6))
    else Result.ok (core.result.Result.Err plan.EINVAL)) = _
  rw [if_true_eq hCond]

/-- `plan.parse_header_part2` decodes `allowBoxLocalhost` and verifies the 8 mandatory flags. -/
theorem parse_header_part2_atOffset (data : Slice U8) (pos : Usize)
    (allowLo : Bool) (tail : Bytes)
    (h : AtOffset data pos
      [u8OfUInt8 (boolU8 allowLo), 1#u8, 1#u8, 1#u8, 1#u8, 1#u8, 1#u8, 1#u8, 1#u8] tail) :
    ∃ pos9 : Usize,
      plan.parse_header_part2 data pos = Result.ok (.Ok (allowLo, pos9)) ∧
      pos9.val = pos.val + 9 ∧
      AtOffset data pos9 tail [] := by
  have h0 : AtOffset data pos [u8OfUInt8 (boolU8 allowLo)]
      ([1#u8] ++ [1#u8] ++ [1#u8] ++ [1#u8] ++ [1#u8] ++ [1#u8] ++ [1#u8] ++ [1#u8] ++ tail) :=
    ⟨h.1, by simpa [List.append_assoc] using h.2⟩
  obtain ⟨p1, hr1, hp1, hs1⟩ := read_u8_atOffset data pos _ _ h0
  have h1 : AtOffset data p1 [1#u8]
      ([1#u8] ++ [1#u8] ++ [1#u8] ++ [1#u8] ++ [1#u8] ++ [1#u8] ++ [1#u8] ++ tail) :=
    ⟨hs1.1, by simpa [List.append_assoc] using hs1.2⟩
  obtain ⟨p2, hr2, hp2, hs2⟩ := read_u8_atOffset data p1 1#u8 _ h1
  have h2 : AtOffset data p2 [1#u8]
      ([1#u8] ++ [1#u8] ++ [1#u8] ++ [1#u8] ++ [1#u8] ++ [1#u8] ++ tail) :=
    ⟨hs2.1, by simpa [List.append_assoc] using hs2.2⟩
  obtain ⟨p3, hr3, hp3, hs3⟩ := read_u8_atOffset data p2 1#u8 _ h2
  have h3 : AtOffset data p3 [1#u8]
      ([1#u8] ++ [1#u8] ++ [1#u8] ++ [1#u8] ++ [1#u8] ++ tail) :=
    ⟨hs3.1, by simpa [List.append_assoc] using hs3.2⟩
  obtain ⟨p4, hr4, hp4, hs4⟩ := read_u8_atOffset data p3 1#u8 _ h3
  have h4 : AtOffset data p4 [1#u8]
      ([1#u8] ++ [1#u8] ++ [1#u8] ++ [1#u8] ++ tail) :=
    ⟨hs4.1, by simpa [List.append_assoc] using hs4.2⟩
  obtain ⟨p5, hr5, hp5, hs5⟩ := read_u8_atOffset data p4 1#u8 _ h4
  have h5 : AtOffset data p5 [1#u8]
      ([1#u8] ++ [1#u8] ++ [1#u8] ++ tail) :=
    ⟨hs5.1, by simpa [List.append_assoc] using hs5.2⟩
  obtain ⟨p6, hr6, hp6, hs6⟩ := read_u8_atOffset data p5 1#u8 _ h5
  have h6 : AtOffset data p6 [1#u8] ([1#u8] ++ [1#u8] ++ tail) :=
    ⟨hs6.1, by simpa [List.append_assoc] using hs6.2⟩
  obtain ⟨p7, hr7, hp7, hs7⟩ := read_u8_atOffset data p6 1#u8 _ h6
  have h7 : AtOffset data p7 [1#u8] ([1#u8] ++ tail) :=
    ⟨hs7.1, by simpa [List.append_assoc] using hs7.2⟩
  obtain ⟨p8, hr8, hp8, hs8⟩ := read_u8_atOffset data p7 1#u8 _ h7
  have h8 : AtOffset data p8 [1#u8] tail :=
    ⟨hs8.1, by simpa [List.append_nil] using hs8.2⟩
  obtain ⟨p9, hr9, hp9, hs9⟩ := read_u8_atOffset data p8 1#u8 tail h8
  have hFlags :
      ((((((((1#u8 != 0#u8) && (1#u8 != 0#u8)) && (1#u8 != 0#u8)) &&
        (1#u8 != 0#u8)) && (1#u8 != 0#u8)) && (1#u8 != 0#u8)) &&
        (1#u8 != 0#u8)) && (1#u8 != 0#u8)) = true := by decide
  refine ⟨p9, ?_, by omega, hs9⟩
  rw [plan.parse_header_part2]
  refine eq_ok_of_try_ok hr1 ?_
  refine eq_ok_of_try_ok hr2 ?_
  refine eq_ok_of_try_ok hr3 ?_
  refine eq_ok_of_try_ok hr4 ?_
  refine eq_ok_of_try_ok hr5 ?_
  refine eq_ok_of_try_ok hr6 ?_
  refine eq_ok_of_try_ok hr7 ?_
  refine eq_ok_of_try_ok hr8 ?_
  refine eq_ok_of_try_ok hr9 ?_
  change (if ((((((((1#u8 != 0#u8) && (1#u8 != 0#u8)) && (1#u8 != 0#u8)) &&
      (1#u8 != 0#u8)) && (1#u8 != 0#u8)) && (1#u8 != 0#u8)) &&
      (1#u8 != 0#u8)) && (1#u8 != 0#u8)) = true then
      Result.ok (core.result.Result.Ok (u8OfUInt8 (boolU8 allowLo) != 0#u8, p9))
    else Result.ok (core.result.Result.Err plan.EINVAL)) = _
  rw [if_true_eq hFlags, u8_boolU8_ne_zero]

/-- `plan.parse_header_limits` decodes the 44-byte resource limits block and extracts `(has_fsize, fsize_max)`. -/
theorem parse_header_limits_atOffset (data : Slice U8) (pos : Usize)
    (tMs : UInt64) (hasMem : UInt8) (memMax : UInt64)
    (hasPids : UInt8) (pidsMax : UInt64)
    (hasFsize : Bool) (fsizeMax : UInt64)
    (hasOut : UInt8) (maxOut : UInt64)
    (tail : Bytes)
    (h : AtOffset data pos
      (byteArrayToBytes (pushU64LE ByteArray.empty tMs) ++
       [u8OfUInt8 hasMem] ++
       byteArrayToBytes (pushU64LE ByteArray.empty memMax) ++
       [u8OfUInt8 hasPids] ++
       byteArrayToBytes (pushU64LE ByteArray.empty pidsMax) ++
       [u8OfUInt8 (boolU8 hasFsize)] ++
       byteArrayToBytes (pushU64LE ByteArray.empty fsizeMax) ++
       [u8OfUInt8 hasOut] ++
       byteArrayToBytes (pushU64LE ByteArray.empty maxOut)) tail) :
    ∃ pos44 : Usize,
      plan.parse_header_limits data pos =
        Result.ok (.Ok ((hasFsize, ⟨fsizeMax.toBitVec⟩), pos44)) ∧
      pos44.val = pos.val + 44 ∧
      AtOffset data pos44 tail [] := by
  have h0 : AtOffset data pos (byteArrayToBytes (pushU64LE ByteArray.empty tMs))
      ([u8OfUInt8 hasMem] ++ byteArrayToBytes (pushU64LE ByteArray.empty memMax) ++
       [u8OfUInt8 hasPids] ++ byteArrayToBytes (pushU64LE ByteArray.empty pidsMax) ++
       [u8OfUInt8 (boolU8 hasFsize)] ++ byteArrayToBytes (pushU64LE ByteArray.empty fsizeMax) ++
       [u8OfUInt8 hasOut] ++ byteArrayToBytes (pushU64LE ByteArray.empty maxOut) ++ tail) :=
    ⟨h.1, by simpa [List.append_assoc] using h.2⟩
  obtain ⟨p1, hr1, hp1, hs1⟩ := read_u64_le_atOffset data pos tMs _ h0
  have h1 : AtOffset data p1 [u8OfUInt8 hasMem]
      (byteArrayToBytes (pushU64LE ByteArray.empty memMax) ++
       [u8OfUInt8 hasPids] ++ byteArrayToBytes (pushU64LE ByteArray.empty pidsMax) ++
       [u8OfUInt8 (boolU8 hasFsize)] ++ byteArrayToBytes (pushU64LE ByteArray.empty fsizeMax) ++
       [u8OfUInt8 hasOut] ++ byteArrayToBytes (pushU64LE ByteArray.empty maxOut) ++ tail) :=
    ⟨hs1.1, by simpa [List.append_assoc] using hs1.2⟩
  obtain ⟨p2, hr2, hp2, hs2⟩ := read_u8_atOffset data p1 _ _ h1
  have h2 : AtOffset data p2 (byteArrayToBytes (pushU64LE ByteArray.empty memMax))
      ([u8OfUInt8 hasPids] ++ byteArrayToBytes (pushU64LE ByteArray.empty pidsMax) ++
       [u8OfUInt8 (boolU8 hasFsize)] ++ byteArrayToBytes (pushU64LE ByteArray.empty fsizeMax) ++
       [u8OfUInt8 hasOut] ++ byteArrayToBytes (pushU64LE ByteArray.empty maxOut) ++ tail) :=
    ⟨hs2.1, by simpa [List.append_assoc] using hs2.2⟩
  obtain ⟨p3, hr3, hp3, hs3⟩ := read_u64_le_atOffset data p2 memMax _ h2
  have h3 : AtOffset data p3 [u8OfUInt8 hasPids]
      (byteArrayToBytes (pushU64LE ByteArray.empty pidsMax) ++
       [u8OfUInt8 (boolU8 hasFsize)] ++ byteArrayToBytes (pushU64LE ByteArray.empty fsizeMax) ++
       [u8OfUInt8 hasOut] ++ byteArrayToBytes (pushU64LE ByteArray.empty maxOut) ++ tail) :=
    ⟨hs3.1, by simpa [List.append_assoc] using hs3.2⟩
  obtain ⟨p4, hr4, hp4, hs4⟩ := read_u8_atOffset data p3 _ _ h3
  have h4 : AtOffset data p4 (byteArrayToBytes (pushU64LE ByteArray.empty pidsMax))
      ([u8OfUInt8 (boolU8 hasFsize)] ++ byteArrayToBytes (pushU64LE ByteArray.empty fsizeMax) ++
       [u8OfUInt8 hasOut] ++ byteArrayToBytes (pushU64LE ByteArray.empty maxOut) ++ tail) :=
    ⟨hs4.1, by simpa [List.append_assoc] using hs4.2⟩
  obtain ⟨p5, hr5, hp5, hs5⟩ := read_u64_le_atOffset data p4 pidsMax _ h4
  have h5 : AtOffset data p5 [u8OfUInt8 (boolU8 hasFsize)]
      (byteArrayToBytes (pushU64LE ByteArray.empty fsizeMax) ++
       [u8OfUInt8 hasOut] ++ byteArrayToBytes (pushU64LE ByteArray.empty maxOut) ++ tail) :=
    ⟨hs5.1, by simpa [List.append_assoc] using hs5.2⟩
  obtain ⟨p6, hr6, hp6, hs6⟩ := read_u8_atOffset data p5 _ _ h5
  have h6 : AtOffset data p6 (byteArrayToBytes (pushU64LE ByteArray.empty fsizeMax))
      ([u8OfUInt8 hasOut] ++ byteArrayToBytes (pushU64LE ByteArray.empty maxOut) ++ tail) :=
    ⟨hs6.1, by simpa [List.append_assoc] using hs6.2⟩
  obtain ⟨p7, hr7, hp7, hs7⟩ := read_u64_le_atOffset data p6 fsizeMax _ h6
  have h7 : AtOffset data p7 [u8OfUInt8 hasOut]
      (byteArrayToBytes (pushU64LE ByteArray.empty maxOut) ++ tail) :=
    ⟨hs7.1, by simpa [List.append_assoc] using hs7.2⟩
  obtain ⟨p8, hr8, hp8, hs8⟩ := read_u8_atOffset data p7 _ _ h7
  have h8 : AtOffset data p8 (byteArrayToBytes (pushU64LE ByteArray.empty maxOut)) tail :=
    ⟨hs8.1, by simpa [List.append_nil] using hs8.2⟩
  obtain ⟨p9, hr9, hp9, hs9⟩ := read_u64_le_atOffset data p8 maxOut tail h8
  refine ⟨p9, ?_, by omega, hs9⟩
  rw [plan.parse_header_limits]
  refine eq_ok_of_try_ok hr1 ?_
  refine eq_ok_of_try_ok hr2 ?_
  refine eq_ok_of_try_ok hr3 ?_
  refine eq_ok_of_try_ok hr4 ?_
  refine eq_ok_of_try_ok hr5 ?_
  refine eq_ok_of_try_ok hr6 ?_
  refine eq_ok_of_try_ok hr7 ?_
  refine eq_ok_of_try_ok hr8 ?_
  refine eq_ok_of_try_ok hr9 ?_
  change Result.ok (core.result.Result.Ok ((u8OfUInt8 (boolU8 hasFsize) != 0#u8,
    (⟨fsizeMax.toBitVec⟩ : U64)), p9)) = _
  rw [u8_boolU8_ne_zero]

/-- Single-item encoder for `PresetSystemEntry` onto `ByteArray.empty`. -/
def encodeSysEntry0 : PresetSystemEntry → Except SandboxError ByteArray
  | .readOnlyDir p => do
    let bp ← pushStr ByteArray.empty p
    return ByteArray.mk #[0] ++ bp
  | .topSymlink lp tgt => do
    let b1 ← pushStr ByteArray.empty lp
    let b2 ← pushStr ByteArray.empty tgt
    return ByteArray.mk #[1] ++ b1 ++ b2

/-- Single-item encoder for `(key, val)` environment pairs onto `ByteArray.empty`. -/
def encodeEnvPair0 (kv : String × String) : Except SandboxError ByteArray := do
  let bk ← pushStr ByteArray.empty kv.1
  let bv ← pushStr ByteArray.empty kv.2
  return bk ++ bv

/-- Single-item encoder for `SandboxMount` onto `ByteArray.empty`. -/
def encodeMount0 : SandboxMount → Except SandboxError ByteArray
  | .readOnly hp bp => do
    let bhp ← pushStr ByteArray.empty hp
    let bbp ← pushStr ByteArray.empty bp
    return ByteArray.mk #[0] ++ bhp ++ bbp
  | .readWrite hp bp => do
    let bhp ← pushStr ByteArray.empty hp
    let bbp ← pushStr ByteArray.empty bp
    return ByteArray.mk #[1] ++ bhp ++ bbp
  | .scratch bp => do
    let bbp ← pushStr ByteArray.empty bp
    return ByteArray.mk #[2] ++ bbp

/-- Single-item encoder for `PortForward` onto `ByteArray.empty`. -/
def encodePortFwd0 (pf : PortForward) : Except SandboxError ByteArray :=
  .ok (pushU16LE ByteArray.empty pf.boxPort ++ pushU16LE ByteArray.empty pf.hostPort)

/-- `plan.read_sys_entry` decodes any `encodeSysEntry0`-encoded entry and advances `pos`. -/
theorem read_sys_entry_atOffset (data : Slice U8) (pos : Usize)
    (e : PresetSystemEntry) (eb : ByteArray) (tail : Bytes)
    (hEnc : encodeSysEntry0 e = .ok eb)
    (h : AtOffset data pos (byteArrayToBytes eb) tail) :
    ∃ (tag : U8) (sp : plan.Span) (pos' : Usize),
      plan.read_sys_entry data pos = Result.ok (.Ok (tag, sp, pos')) ∧
      pos'.val = pos.val + eb.size ∧
      AtOffset data pos' tail [] := by
  cases e with
  | readOnlyDir p =>
    rw [encodeSysEntry0] at hEnc
    cases hp : pushStr ByteArray.empty p with
    | error err =>
      rw [hp] at hEnc
      cases hEnc
    | ok bp =>
      rw [hp] at hEnc
      cases hEnc
      have hSeg : byteArrayToBytes (ByteArray.mk #[0] ++ bp) = [0#u8] ++ byteArrayToBytes bp := by
        rw [byteArrayToBytes_append]
        rfl
      have h0 : AtOffset data pos [0#u8] (byteArrayToBytes bp ++ tail) := by
        refine ⟨h.1, ?_⟩
        rw [h.2, hSeg, List.append_assoc]
      obtain ⟨p1, hrTag, hp1, hs1⟩ := read_u8_atOffset data pos 0#u8 _ h0
      have h1 : AtOffset data p1 (byteArrayToBytes bp) tail :=
        ⟨hs1.1, by simpa [List.append_nil] using hs1.2⟩
      obtain ⟨sp, p2, hrPath, _, _, _, hp2, hs2⟩ := read_str_span_atOffset data p1 p bp tail hp h1
      have hSz : (ByteArray.mk #[0] ++ bp).size = 1 + bp.size := by
        have hL := congrArg List.length hSeg
        rw [length_byteArrayToBytes, List.length_append, length_byteArrayToBytes] at hL
        simpa using hL
      have hNe1 : ¬ ((0#u8 : U8) = 1#u8) := by decide
      refine ⟨0#u8, sp, p2, ?_, by omega, hs2⟩
      rw [plan.read_sys_entry]
      refine eq_ok_of_try_ok hrTag ?_
      refine eq_ok_of_try_ok hrPath ?_
      change (if (0#u8 : U8) = 1#u8 then _ else Result.ok (core.result.Result.Ok (0#u8, sp, p2))) = _
      rw [if_false_eq hNe1]
  | topSymlink lp tgt =>
    rw [encodeSysEntry0] at hEnc
    cases hlp : pushStr ByteArray.empty lp with
    | error err =>
      rw [hlp] at hEnc
      cases hEnc
    | ok b1 =>
      rw [hlp] at hEnc
      cases htgt : pushStr ByteArray.empty tgt with
      | error err =>
        rw [htgt] at hEnc
        cases hEnc
      | ok b2 =>
        rw [htgt] at hEnc
        cases hEnc
        have hSeg : byteArrayToBytes (ByteArray.mk #[1] ++ b1 ++ b2) =
            [1#u8] ++ byteArrayToBytes b1 ++ byteArrayToBytes b2 := by
          rw [byteArrayToBytes_append, byteArrayToBytes_append]
          rfl
        have h0 : AtOffset data pos [1#u8] (byteArrayToBytes b1 ++ byteArrayToBytes b2 ++ tail) := by
          refine ⟨h.1, ?_⟩
          rw [h.2, hSeg]
          simp [List.append_assoc]
        obtain ⟨p1, hrTag, hp1, hs1⟩ := read_u8_atOffset data pos 1#u8 _ h0
        have h1 : AtOffset data p1 (byteArrayToBytes b1) (byteArrayToBytes b2 ++ tail) :=
          ⟨hs1.1, by simpa [List.append_assoc] using hs1.2⟩
        obtain ⟨sp, p2, hrLp, _, _, _, hp2, hs2⟩ := read_str_span_atOffset data p1 lp b1 _ hlp h1
        have h2 : AtOffset data p2 (byteArrayToBytes b2) tail :=
          ⟨hs2.1, by simpa [List.append_nil] using hs2.2⟩
        obtain ⟨spT, p3, hrTgt, _, _, _, hp3, hs3⟩ := read_str_span_atOffset data p2 tgt b2 tail htgt h2
        have hSz : (ByteArray.mk #[1] ++ b1 ++ b2).size = 1 + b1.size + b2.size := by
          have hL := congrArg List.length hSeg
          rw [length_byteArrayToBytes, List.length_append, List.length_append,
            length_byteArrayToBytes, length_byteArrayToBytes] at hL
          simpa using hL
        refine ⟨1#u8, sp, p3, ?_, by omega, hs3⟩
        rw [plan.read_sys_entry]
        refine eq_ok_of_try_ok hrTag ?_
        refine eq_ok_of_try_ok hrLp ?_
        change (if (1#u8 : U8) = 1#u8 then _ else _) = _
        rw [if_true_eq rfl]
        exact eq_ok_of_try_ok hrTgt rfl

/-- `plan.read_mount_entry` decodes any `encodeMount0`-encoded entry and advances `pos`. -/
theorem read_mount_entry_atOffset (data : Slice U8) (pos : Usize)
    (m : SandboxMount) (mb : ByteArray) (tail : Bytes)
    (hEnc : encodeMount0 m = .ok mb)
    (h : AtOffset data pos (byteArrayToBytes mb) tail) :
    ∃ (tag : U8) (sp : plan.Span) (pos' : Usize),
      plan.read_mount_entry data pos = Result.ok (.Ok (tag, sp, pos')) ∧
      pos'.val = pos.val + mb.size ∧
      AtOffset data pos' tail [] := by
  cases m with
  | readOnly hp bp =>
    rw [encodeMount0] at hEnc
    cases hhp : pushStr ByteArray.empty hp with
    | error err => rw [hhp] at hEnc; cases hEnc
    | ok bhp =>
      rw [hhp] at hEnc
      cases hbp : pushStr ByteArray.empty bp with
      | error err => rw [hbp] at hEnc; cases hEnc
      | ok bbp =>
        rw [hbp] at hEnc
        cases hEnc
        have hSeg : byteArrayToBytes (ByteArray.mk #[0] ++ bhp ++ bbp) =
            [0#u8] ++ byteArrayToBytes bhp ++ byteArrayToBytes bbp := by
          rw [byteArrayToBytes_append, byteArrayToBytes_append]; rfl
        have h0 : AtOffset data pos [0#u8] (byteArrayToBytes bhp ++ byteArrayToBytes bbp ++ tail) := by
          refine ⟨h.1, ?_⟩; rw [h.2, hSeg]; simp [List.append_assoc]
        obtain ⟨p1, hrTag, hp1, hs1⟩ := read_u8_atOffset data pos 0#u8 _ h0
        have h1 : AtOffset data p1 (byteArrayToBytes bhp) (byteArrayToBytes bbp ++ tail) :=
          ⟨hs1.1, by simpa [List.append_assoc] using hs1.2⟩
        obtain ⟨_, p2, hrHp, _, _, _, hp2, hs2⟩ := read_str_span_atOffset data p1 hp bhp _ hhp h1
        have h2 : AtOffset data p2 (byteArrayToBytes bbp) tail :=
          ⟨hs2.1, by simpa [List.append_nil] using hs2.2⟩
        obtain ⟨sp, p3, hrBp, _, _, _, hp3, hs3⟩ := read_str_span_atOffset data p2 bp bbp tail hbp h2
        have hSz : (ByteArray.mk #[0] ++ bhp ++ bbp).size = 1 + bhp.size + bbp.size := by
          have hL := congrArg List.length hSeg
          rw [length_byteArrayToBytes, List.length_append, List.length_append,
            length_byteArrayToBytes, length_byteArrayToBytes] at hL
          simpa using hL
        refine ⟨0#u8, sp, p3, ?_, by omega, hs3⟩
        rw [plan.read_mount_entry]
        refine eq_ok_of_try_ok hrTag ?_
        change (if (0#u8 : U8) = 0#u8 then _ else _) = _
        rw [if_true_eq rfl]
        refine eq_ok_of_try_ok hrHp ?_
        exact eq_ok_of_try_ok hrBp rfl
  | readWrite hp bp =>
    rw [encodeMount0] at hEnc
    cases hhp : pushStr ByteArray.empty hp with
    | error err => rw [hhp] at hEnc; cases hEnc
    | ok bhp =>
      rw [hhp] at hEnc
      cases hbp : pushStr ByteArray.empty bp with
      | error err => rw [hbp] at hEnc; cases hEnc
      | ok bbp =>
        rw [hbp] at hEnc
        cases hEnc
        have hSeg : byteArrayToBytes (ByteArray.mk #[1] ++ bhp ++ bbp) =
            [1#u8] ++ byteArrayToBytes bhp ++ byteArrayToBytes bbp := by
          rw [byteArrayToBytes_append, byteArrayToBytes_append]; rfl
        have h0 : AtOffset data pos [1#u8] (byteArrayToBytes bhp ++ byteArrayToBytes bbp ++ tail) := by
          refine ⟨h.1, ?_⟩; rw [h.2, hSeg]; simp [List.append_assoc]
        obtain ⟨p1, hrTag, hp1, hs1⟩ := read_u8_atOffset data pos 1#u8 _ h0
        have h1 : AtOffset data p1 (byteArrayToBytes bhp) (byteArrayToBytes bbp ++ tail) :=
          ⟨hs1.1, by simpa [List.append_assoc] using hs1.2⟩
        obtain ⟨_, p2, hrHp, _, _, _, hp2, hs2⟩ := read_str_span_atOffset data p1 hp bhp _ hhp h1
        have h2 : AtOffset data p2 (byteArrayToBytes bbp) tail :=
          ⟨hs2.1, by simpa [List.append_nil] using hs2.2⟩
        obtain ⟨sp, p3, hrBp, _, _, _, hp3, hs3⟩ := read_str_span_atOffset data p2 bp bbp tail hbp h2
        have hSz : (ByteArray.mk #[1] ++ bhp ++ bbp).size = 1 + bhp.size + bbp.size := by
          have hL := congrArg List.length hSeg
          rw [length_byteArrayToBytes, List.length_append, List.length_append,
            length_byteArrayToBytes, length_byteArrayToBytes] at hL
          simpa using hL
        have hNe0 : ¬ ((1#u8 : U8) = 0#u8) := by decide
        refine ⟨1#u8, sp, p3, ?_, by omega, hs3⟩
        rw [plan.read_mount_entry]
        refine eq_ok_of_try_ok hrTag ?_
        change (if (1#u8 : U8) = 0#u8 then _ else if (1#u8 : U8) = 1#u8 then _ else _) = _
        rw [if_false_eq hNe0, if_true_eq rfl]
        refine eq_ok_of_try_ok hrHp ?_
        exact eq_ok_of_try_ok hrBp rfl
  | scratch bp =>
    rw [encodeMount0] at hEnc
    cases hbp : pushStr ByteArray.empty bp with
    | error err => rw [hbp] at hEnc; cases hEnc
    | ok bbp =>
      rw [hbp] at hEnc
      cases hEnc
      have hSeg : byteArrayToBytes (ByteArray.mk #[2] ++ bbp) = [2#u8] ++ byteArrayToBytes bbp := by
        rw [byteArrayToBytes_append]; rfl
      have h0 : AtOffset data pos [2#u8] (byteArrayToBytes bbp ++ tail) := by
        refine ⟨h.1, ?_⟩; rw [h.2, hSeg, List.append_assoc]
      obtain ⟨p1, hrTag, hp1, hs1⟩ := read_u8_atOffset data pos 2#u8 _ h0
      have h1 : AtOffset data p1 (byteArrayToBytes bbp) tail :=
        ⟨hs1.1, by simpa [List.append_nil] using hs1.2⟩
      obtain ⟨sp, p2, hrBp, _, _, _, hp2, hs2⟩ := read_str_span_atOffset data p1 bp bbp tail hbp h1
      have hSz : (ByteArray.mk #[2] ++ bbp).size = 1 + bbp.size := by
        have hL := congrArg List.length hSeg
        rw [length_byteArrayToBytes, List.length_append, length_byteArrayToBytes] at hL
        simpa using hL
      have hNe0 : ¬ ((2#u8 : U8) = 0#u8) := by decide
      have hNe1 : ¬ ((2#u8 : U8) = 1#u8) := by decide
      refine ⟨2#u8, sp, p2, ?_, by omega, hs2⟩
      rw [plan.read_mount_entry]
      refine eq_ok_of_try_ok hrTag ?_
      change (if (2#u8 : U8) = 0#u8 then _ else if (2#u8 : U8) = 1#u8 then _ else if (2#u8 : U8) = 2#u8 then _ else _) = _
      rw [if_false_eq hNe0, if_false_eq hNe1, if_true_eq rfl]
      exact eq_ok_of_try_ok hrBp rfl

/-- Generic `Aeneas.Std.loop` progress theorem over a pre-validated list of wire chunks. -/
theorem scan_chunks_loop_spec
    (data : Slice U8) (pos : Usize) (count : U32)
    (chunks : List Bytes) (tail : Bytes)
    (body : Usize → U32 → Result (ControlFlow (Usize × U32) (Usize × Bool)))
    (hLen : chunks.length = count.val)
    (hInit : AtOffset data pos chunks.flatten tail)
    (hStep : ∀ (cur : Usize) (i : U32) (seg rest : Bytes),
      i < count →
      AtOffset data cur seg rest →
      seg ∈ chunks →
      ∃ (nextPos : Usize) (i1 : U32),
        body cur i = Result.ok (ControlFlow.cont (nextPos, i1)) ∧
        nextPos.val = cur.val + seg.length ∧
        i1.val = i.val + 1 ∧
        AtOffset data nextPos rest [])
    (hDone : ∀ (cur : Usize) (i : U32),
      ¬ (i < count) →
      body cur i = Result.ok (ControlFlow.done (cur, false))) :
    ∃ endPos : Usize,
      loop (fun (cur1, i1) => body cur1 i1) (pos, 0#u32) = Result.ok (endPos, false) ∧
      endPos.val = pos.val + chunks.flatten.length ∧
      AtOffset data endPos tail [] := by
  have hPost :
      OkPost (loop (fun (cur1, i1) => body cur1 i1) (pos, 0#u32))
        (fun res : Usize × Bool =>
          res.2 = false ∧
          res.1.val = pos.val + chunks.flatten.length ∧
          AtOffset data res.1 tail []) := by
    refine okPost_loop_decr_nat
      (fun st : Usize × U32 => count.val - st.2.val)
      (fun st : Usize × U32 =>
        st.2.val ≤ chunks.length ∧
        st.1.val = pos.val + (chunks.take st.2.val).flatten.length ∧
        AtOffset data st.1 (chunks.drop st.2.val).flatten tail)
      (fun res : Usize × Bool =>
        res.2 = false ∧
        res.1.val = pos.val + chunks.flatten.length ∧
        AtOffset data res.1 tail [])
      (fun (cur1, i1) => body cur1 i1)
      (pos, 0#u32) ?_ ?_
    · rintro ⟨cur, i⟩ ⟨hiLe, hCurEq, hAt⟩
      change i.val ≤ chunks.length at hiLe
      change cur.val = pos.val + (chunks.take i.val).flatten.length at hCurEq
      change AtOffset data cur (chunks.drop i.val).flatten tail at hAt
      by_cases hLt : i < count
      · have hiLt : i.val < chunks.length := by
          have : i.val < count.val := by simpa using hLt
          omega
        have hDrop : chunks.drop i.val = chunks[i.val] :: chunks.drop (i.val + 1) :=
          List.drop_eq_getElem_cons hiLt
        have hFlatDrop :
            (chunks.drop i.val).flatten =
              chunks[i.val] ++ (chunks.drop (i.val + 1)).flatten := by
          rw [hDrop]
          rfl
        have hAtSeg :
            AtOffset data cur chunks[i.val] ((chunks.drop (i.val + 1)).flatten ++ tail) := by
          refine ⟨hAt.1, ?_⟩
          rw [hAt.2, hFlatDrop, List.append_assoc]
        have hMem : chunks[i.val] ∈ chunks := List.getElem_mem hiLt
        obtain ⟨nextPos, i1, hB, hNextVal, hi1Val, hNextAt⟩ :=
          hStep cur i chunks[i.val] ((chunks.drop (i.val + 1)).flatten ++ tail) hLt hAtSeg hMem
        have hTakeSucc :
            (chunks.take (i.val + 1)).flatten.length =
              (chunks.take i.val).flatten.length + chunks[i.val].length := by
          have hTakeEq : chunks.take (i.val + 1) = chunks.take i.val ++ [chunks[i.val]] := by
            rw [List.take_add_one, List.getElem?_eq_getElem hiLt]
            rfl
          rw [hTakeEq, List.flatten_append, List.length_append]
          simp
        refine ⟨ControlFlow.cont (nextPos, i1), hB, ⟨?_, ?_, ?_⟩, ?_⟩
        · change i1.val ≤ chunks.length
          omega
        · change nextPos.val = pos.val + (chunks.take i1.val).flatten.length
          rw [hi1Val, hTakeSucc]
          omega
        · change AtOffset data nextPos (chunks.drop i1.val).flatten tail
          rw [hi1Val]
          exact ⟨hNextAt.1, by simpa [List.append_nil] using hNextAt.2⟩
        · change count.val - i1.val < count.val - i.val
          omega
      · have hiEq : i.val = chunks.length := by
          have : ¬ (i.val < count.val) := by simpa using hLt
          omega
        refine ⟨ControlFlow.done (cur, false), hDone cur i hLt, rfl, ?_, ?_⟩
        · rw [hiEq, List.take_length] at hCurEq
          exact hCurEq
        · rw [hiEq, List.drop_length] at hAt
          exact ⟨hAt.1, by simpa using hAt.2⟩
    · refine ⟨by simp, by simp, ?_⟩
      simpa using hInit
  rcases hPost with ⟨⟨endPos, bad⟩, hRun, hBad, hVal, hAt⟩
  subst hBad
  exact ⟨endPos, hRun, hVal, hAt⟩

private theorem u32_add_1_of_lt (i count : U32) (hLt : i < count) :
    ∃ i1 : U32, i + 1#u32 = Result.ok i1 ∧ i1.val = i.val + 1 := by
  have hiLt : i.val < count.val := by simpa using hLt
  have hcLt : count.val < 4294967296 := count.bv.isLt
  have hMax32 : U32.max = 4294967295 := by
    rw [U32.max_def, U32.numBits_def, UScalarTy.U32_numBits_eq]
    decide
  have h1 : (1#u32).val = 1 := rfl
  exact u32_add_ok i 1#u32 (by omega)

/-- `plan.scan_str_list` accepts `encodeList (pushStr ByteArray.empty) xs` and advances `pos`. -/
theorem scan_str_list_atOffset (data : Slice U8) (pos : Usize) (count : U32)
    (xs : List String) (bss : List ByteArray) (tail : Bytes)
    (hEnc : encodeList (pushStr ByteArray.empty) xs = .ok bss)
    (hCnt : xs.length = count.val)
    (h : AtOffset data pos (byteArrayToBytes (concatByteArrays bss)) tail) :
    ∃ endPos : Usize,
      plan.scan_str_list data pos count = Result.ok (.Ok endPos) ∧
      endPos.val = pos.val + (concatByteArrays bss).size ∧
      AtOffset data endPos tail [] := by
  let chunks := bss.map byteArrayToBytes
  have hChunksLen : chunks.length = count.val := by
    simp [chunks, encodeList_length hEnc, hCnt]
  have hInit : AtOffset data pos chunks.flatten tail := by
    rwa [byteArrayToBytes_concatByteArrays] at h
  obtain ⟨endPos, hLoop, hEndVal, hEndAt⟩ :=
    scan_chunks_loop_spec data pos count chunks tail
      (plan.scan_str_list_loop.body data count)
      hChunksLen hInit
      (fun cur i seg rest hLt hAtSeg hMem => by
        rcases List.mem_map.mp hMem with ⟨b, hbMem, rfl⟩
        obtain ⟨s, _, hsPush⟩ := encodeList_mem hEnc hbMem
        obtain ⟨_, nextPos, hr, _, _, _, hNextVal, hNextAt⟩ :=
          read_str_span_atOffset data cur s b rest hsPush hAtSeg
        obtain ⟨i1, hi1, hi1Val⟩ := u32_add_1_of_lt i count hLt
        refine ⟨nextPos, i1, ?_, ?_, hi1Val, hNextAt⟩
        · rw [plan.scan_str_list_loop.body, if_true_eq hLt]
          refine eq_ok_of_bind hr ?_
          exact eq_ok_of_bind hi1 rfl
        · rw [length_byteArrayToBytes]; exact hNextVal)
      (fun cur i hNotLt => by
        rw [plan.scan_str_list_loop.body, if_false_eq hNotLt])
  have hFlatSz : chunks.flatten.length = (concatByteArrays bss).size := by
    rw [← byteArrayToBytes_concatByteArrays, length_byteArrayToBytes]
  refine ⟨endPos, ?_, by omega, hEndAt⟩
  rw [plan.scan_str_list, plan.scan_str_list_loop]
  refine eq_ok_of_bind hLoop ?_
  exact if_false_eq Bool.false_ne_true

/-- `plan.scan_env_list` accepts `encodeList encodeEnvPair0 xs` and advances `pos`. -/
theorem scan_env_list_atOffset (data : Slice U8) (pos : Usize) (envc : U32)
    (xs : List (String × String)) (bss : List ByteArray) (tail : Bytes)
    (hEnc : encodeList encodeEnvPair0 xs = .ok bss)
    (hCnt : xs.length = envc.val)
    (h : AtOffset data pos (byteArrayToBytes (concatByteArrays bss)) tail) :
    ∃ endPos : Usize,
      plan.scan_env_list data pos envc = Result.ok (.Ok endPos) ∧
      endPos.val = pos.val + (concatByteArrays bss).size ∧
      AtOffset data endPos tail [] := by
  let chunks := bss.map byteArrayToBytes
  have hChunksLen : chunks.length = envc.val := by
    simp [chunks, encodeList_length hEnc, hCnt]
  have hInit : AtOffset data pos chunks.flatten tail := by
    rwa [byteArrayToBytes_concatByteArrays] at h
  obtain ⟨endPos, hLoop, hEndVal, hEndAt⟩ :=
    scan_chunks_loop_spec data pos envc chunks tail
      (plan.scan_env_list_loop.body data envc)
      hChunksLen hInit
      (fun cur i seg rest hLt hAtSeg hMem => by
        rcases List.mem_map.mp hMem with ⟨b, hbMem, rfl⟩
        obtain ⟨⟨k, v⟩, _, hkv⟩ := encodeList_mem hEnc hbMem
        unfold encodeEnvPair0 at hkv
        cases hk : pushStr ByteArray.empty k with
        | error err => rw [hk] at hkv; cases hkv
        | ok bk =>
          rw [hk] at hkv
          cases hv : pushStr ByteArray.empty v with
          | error err => rw [hv] at hkv; cases hkv
          | ok bv =>
            rw [hv] at hkv
            cases hkv
            have hSeg : byteArrayToBytes (bk ++ bv) = byteArrayToBytes bk ++ byteArrayToBytes bv :=
              byteArrayToBytes_append bk bv
            have hAtK : AtOffset data cur (byteArrayToBytes bk) (byteArrayToBytes bv ++ rest) := by
              refine ⟨hAtSeg.1, ?_⟩
              rw [hAtSeg.2, hSeg, List.append_assoc]
            obtain ⟨_, p1, hrK, _, _, _, hp1, hs1⟩ :=
              read_str_span_atOffset data cur k bk _ hk hAtK
            have hAtV : AtOffset data p1 (byteArrayToBytes bv) rest :=
              ⟨hs1.1, by simpa [List.append_nil] using hs1.2⟩
            obtain ⟨_, p2, hrV, _, _, _, hp2, hs2⟩ :=
              read_str_span_atOffset data p1 v bv rest hv hAtV
            obtain ⟨i1, hi1, hi1Val⟩ := u32_add_1_of_lt i envc hLt
            have hLenPair : (byteArrayToBytes (bk ++ bv)).length = bk.size + bv.size := by
              rw [hSeg, List.length_append, length_byteArrayToBytes, length_byteArrayToBytes]
            refine ⟨p2, i1, ?_, by omega, hi1Val, hs2⟩
            rw [plan.scan_env_list_loop.body, if_true_eq hLt]
            refine eq_ok_of_bind hrK ?_
            refine eq_ok_of_bind hrV ?_
            exact eq_ok_of_bind hi1 rfl)
      (fun cur i hNotLt => by
        rw [plan.scan_env_list_loop.body, if_false_eq hNotLt])
  have hFlatSz : chunks.flatten.length = (concatByteArrays bss).size := by
    rw [← byteArrayToBytes_concatByteArrays, length_byteArrayToBytes]
  refine ⟨endPos, ?_, by omega, hEndAt⟩
  rw [plan.scan_env_list, plan.scan_env_list_loop]
  refine eq_ok_of_bind hLoop ?_
  exact if_false_eq Bool.false_ne_true

/-- `plan.scan_sys_entries` accepts `encodeList encodeSysEntry0 xs` and advances `pos`. -/
theorem scan_sys_entries_atOffset (data : Slice U8) (pos : Usize) (nSys : U32)
    (xs : List PresetSystemEntry) (bss : List ByteArray) (tail : Bytes)
    (hEnc : encodeList encodeSysEntry0 xs = .ok bss)
    (hCnt : xs.length = nSys.val)
    (h : AtOffset data pos (byteArrayToBytes (concatByteArrays bss)) tail) :
    ∃ endPos : Usize,
      plan.scan_sys_entries data pos nSys = Result.ok (.Ok endPos) ∧
      endPos.val = pos.val + (concatByteArrays bss).size ∧
      AtOffset data endPos tail [] := by
  let chunks := bss.map byteArrayToBytes
  have hChunksLen : chunks.length = nSys.val := by
    simp [chunks, encodeList_length hEnc, hCnt]
  have hInit : AtOffset data pos chunks.flatten tail := by
    rwa [byteArrayToBytes_concatByteArrays] at h
  obtain ⟨endPos, hLoop, hEndVal, hEndAt⟩ :=
    scan_chunks_loop_spec data pos nSys chunks tail
      (plan.scan_sys_entries_loop.body data nSys)
      hChunksLen hInit
      (fun cur i seg rest hLt hAtSeg hMem => by
        rcases List.mem_map.mp hMem with ⟨b, hbMem, rfl⟩
        obtain ⟨e, _, he⟩ := encodeList_mem hEnc hbMem
        obtain ⟨_, _, nextPos, hr, hNextVal, hNextAt⟩ :=
          read_sys_entry_atOffset data cur e b rest he hAtSeg
        obtain ⟨i1, hi1, hi1Val⟩ := u32_add_1_of_lt i nSys hLt
        refine ⟨nextPos, i1, ?_, ?_, hi1Val, hNextAt⟩
        · rw [plan.scan_sys_entries_loop.body, if_true_eq hLt]
          refine eq_ok_of_bind hr ?_
          exact eq_ok_of_bind hi1 rfl
        · rw [length_byteArrayToBytes]; exact hNextVal)
      (fun cur i hNotLt => by
        rw [plan.scan_sys_entries_loop.body, if_false_eq hNotLt])
  have hFlatSz : chunks.flatten.length = (concatByteArrays bss).size := by
    rw [← byteArrayToBytes_concatByteArrays, length_byteArrayToBytes]
  refine ⟨endPos, ?_, by omega, hEndAt⟩
  rw [plan.scan_sys_entries, plan.scan_sys_entries_loop]
  refine eq_ok_of_bind hLoop ?_
  exact if_false_eq Bool.false_ne_true

/-- `plan.scan_mounts` accepts `encodeList encodeMount0 xs` and advances `pos`. -/
theorem scan_mounts_atOffset (data : Slice U8) (pos : Usize) (nMounts : U32)
    (xs : List SandboxMount) (bss : List ByteArray) (tail : Bytes)
    (hEnc : encodeList encodeMount0 xs = .ok bss)
    (hCnt : xs.length = nMounts.val)
    (h : AtOffset data pos (byteArrayToBytes (concatByteArrays bss)) tail) :
    ∃ endPos : Usize,
      plan.scan_mounts data pos nMounts = Result.ok (.Ok endPos) ∧
      endPos.val = pos.val + (concatByteArrays bss).size ∧
      AtOffset data endPos tail [] := by
  let chunks := bss.map byteArrayToBytes
  have hChunksLen : chunks.length = nMounts.val := by
    simp [chunks, encodeList_length hEnc, hCnt]
  have hInit : AtOffset data pos chunks.flatten tail := by
    rwa [byteArrayToBytes_concatByteArrays] at h
  obtain ⟨endPos, hLoop, hEndVal, hEndAt⟩ :=
    scan_chunks_loop_spec data pos nMounts chunks tail
      (plan.scan_mounts_loop.body data nMounts)
      hChunksLen hInit
      (fun cur i seg rest hLt hAtSeg hMem => by
        rcases List.mem_map.mp hMem with ⟨b, hbMem, rfl⟩
        obtain ⟨m, _, hm⟩ := encodeList_mem hEnc hbMem
        obtain ⟨_, _, nextPos, hr, hNextVal, hNextAt⟩ :=
          read_mount_entry_atOffset data cur m b rest hm hAtSeg
        obtain ⟨i1, hi1, hi1Val⟩ := u32_add_1_of_lt i nMounts hLt
        refine ⟨nextPos, i1, ?_, ?_, hi1Val, hNextAt⟩
        · rw [plan.scan_mounts_loop.body, if_true_eq hLt]
          refine eq_ok_of_bind hr ?_
          exact eq_ok_of_bind hi1 rfl
        · rw [length_byteArrayToBytes]; exact hNextVal)
      (fun cur i hNotLt => by
        rw [plan.scan_mounts_loop.body, if_false_eq hNotLt])
  have hFlatSz : chunks.flatten.length = (concatByteArrays bss).size := by
    rw [← byteArrayToBytes_concatByteArrays, length_byteArrayToBytes]
  refine ⟨endPos, ?_, by omega, hEndAt⟩
  rw [plan.scan_mounts, plan.scan_mounts_loop]
  refine eq_ok_of_bind hLoop ?_
  exact if_false_eq Bool.false_ne_true

private theorem encodePortFwds_size (xs : List PortForward) (bss : List ByteArray)
    (hEnc : encodeList encodePortFwd0 xs = .ok bss) :
    (concatByteArrays bss).size = xs.length * 4 := by
  induction xs generalizing bss with
  | nil =>
    cases hEnc
    rfl
  | cons pf rest ih =>
    rw [encodeList] at hEnc
    rw [encodePortFwd0] at hEnc
    cases hRest : encodeList encodePortFwd0 rest with
    | error err => rw [hRest] at hEnc; cases hEnc
    | ok bs =>
      rw [hRest] at hEnc
      cases hEnc
      have hSub := ih bs hRest
      unfold concatByteArrays
      have hHeadSz :
          (byteArrayToBytes (pushU16LE ByteArray.empty pf.boxPort ++
            pushU16LE ByteArray.empty pf.hostPort)).length = 4 := by
        rw [byteArrayToBytes_append, List.length_append]
        rfl
      have hTot :
          ((pushU16LE ByteArray.empty pf.boxPort ++
            pushU16LE ByteArray.empty pf.hostPort) ++ concatByteArrays bs).size =
          4 + (concatByteArrays bs).size := by
        rw [← length_byteArrayToBytes, byteArrayToBytes_append, List.length_append,
          hHeadSz, length_byteArrayToBytes]
      rw [hTot, hSub, List.length_cons]
      omega

private theorem except_map_ok_bind {ε α β γ : Type} (f : α → β) (v : α) (k : β → Except ε γ) :
    (Except.map f (Except.ok v) >>= k) = k (f v) := rfl

private theorem except_ok_inj {ε α : Type} {a b : α}
    (h : (Except.ok a : Except ε α) = Except.ok b) : a = b := by
  cases h
  rfl

private theorem atOffset_zero_of_eq {d : Slice U8} {a b : Bytes}
    (heq : d.val = a ++ b) : AtOffset d 0#usize a b :=
  ⟨Nat.zero_le _, heq⟩

private theorem atOffset_next {d : Slice U8} {p : Usize} {a b : Bytes}
    (h : AtOffset d p (a ++ b) []) : AtOffset d p a b :=
  ⟨h.1, by simpa using h.2⟩

private theorem step_forIn_encodeList {α : Type} {arr : Array α} {init : ByteArray}
    {step : α → ByteArray → Except SandboxError (ForInStep ByteArray)}
    {k : ByteArray → Except SandboxError ByteArray} {res : Except SandboxError ByteArray}
    (f : α → Except SandboxError ByteArray)
    (h : (forIn arr init step >>= k) = res)
    (hStep : ∀ (x : α) (ba : ByteArray),
      step x ba = (f x).map (fun b => ForInStep.yield (ba ++ b))) :
    ((encodeList f arr.toList).map (fun bss => init ++ concatByteArrays bss) >>= k) = res := by
  rwa [← array_forIn_encodeList f step hStep]

private def u32Bytes (v : UInt32) : Bytes :=
  byteArrayToBytes (pushU32LE ByteArray.empty v)

private def u64Bytes (v : UInt64) : Bytes :=
  byteArrayToBytes (pushU64LE ByteArray.empty v)

private theorem byteArrayToBytes_empty : byteArrayToBytes ByteArray.empty = [] := rfl

private theorem byteArrayToBytes_pushU8_eq (ba : ByteArray) (v : UInt8) :
    byteArrayToBytes (pushU8 ba v) = byteArrayToBytes ba ++ [u8OfUInt8 v] := by
  rw [pushU8_eq_append, byteArrayToBytes_append]
  rfl

private theorem byteArrayToBytes_pushU32LE_u32Bytes (ba : ByteArray) (v : UInt32) :
    byteArrayToBytes (pushU32LE ba v) = byteArrayToBytes ba ++ u32Bytes v := by
  rw [pushU32LE_eq_append, byteArrayToBytes_append, u32Bytes]

private theorem byteArrayToBytes_pushU64LE_u64Bytes (ba : ByteArray) (v : UInt64) :
    byteArrayToBytes (pushU64LE ba v) = byteArrayToBytes ba ++ u64Bytes v := by
  rw [pushU64LE_eq_append, byteArrayToBytes_append, u64Bytes]

/-- Wire-cap predicate matching the section limits enforced by `psandbox_init::plan::parse_plan`. -/
def WithinInitWireCaps (cplan : CompiledSandboxPlan) : Prop :=
  cplan.args.size ≤ 65536 ∧
  cplan.env.size ≤ 65536 ∧
  cplan.presetSystemEntries.size ≤ 1024 ∧
  cplan.presetEtcPaths.size ≤ 1024 ∧
  cplan.maskedPresetPaths.size ≤ 1024 ∧
  cplan.userMounts.size ≤ 4096 ∧
  cplan.portForwards.size ≤ 1024

/-- End-to-end wire protocol agreement: whenever host `encodePlan cplan seccompBytes = .ok bs`
succeeds within `WithinInitWireCaps cplan` and `bs.size ≤ Usize.max`, the extracted Rust parser
`psandbox_init::plan::parse_plan` succeeds on `bs` and recovers the exact header fields,
`program`/`cwd` UTF-8 byte spans, section counts, `seccomp_n` (`1..160`), and `seccomp` trailer. -/
theorem parse_plan_agrees_with_encodePlan
    (cplan : CompiledSandboxPlan) (seccompBytes bs : ByteArray)
    (hCaps : WithinInitWireCaps cplan)
    (hEnc : encodePlan cplan seccompBytes = .ok bs)
    (hMax : (byteArrayToBytes bs).length ≤ Usize.max) :
    ∃ view : plan.PlanView,
      plan.parse_plan (Slice.from (byteArrayToBytes bs) hMax) = Result.ok (.Ok view) ∧
      view.header.allow_box_localhost = cplan.allowBoxLocalhost ∧
      view.header.has_file_size_max = cplan.limits.fileSizeMaxBytes.isSome ∧
      view.header.file_size_max_bytes =
        ⟨(natToUInt64Sat (cplan.limits.fileSizeMaxBytes.getD 0)).toBitVec⟩ ∧
      view.header.landlock_min_abi.val = Nat.min cplan.landlockMinAbi (UInt32.size - 1) ∧
      4 ≤ view.header.landlock_min_abi.val ∧
      ((byteArrayToBytes bs).drop view.program.start.val).take view.program.len.val =
        byteArrayToBytes cplan.program.toUTF8 ∧
      ((byteArrayToBytes bs).drop view.cwd.start.val).take view.cwd.len.val =
        byteArrayToBytes cplan.cwd.toUTF8 ∧
      view.argc.val = cplan.args.size ∧
      view.envc.val = cplan.env.size ∧
      view.n_sys.val = cplan.presetSystemEntries.size ∧
      view.n_etc.val = cplan.presetEtcPaths.size ∧
      view.n_masks.val = cplan.maskedPresetPaths.size ∧
      view.n_mounts.val = cplan.userMounts.size ∧
      view.n_fwds.val = cplan.portForwards.size ∧
      view.seccomp_n.val = seccompBytes.size / 8 ∧
      1 ≤ view.seccomp_n.val ∧
      view.seccomp_n.val ≤ 160 ∧
      (byteArrayToBytes bs).drop view.seccomp_pos.val = byteArrayToBytes seccompBytes := by
  rcases hCaps with ⟨hCapArgs, hCapEnv, hCapSys, hCapEtc, hCapMasks, hCapMnts, hCapFwds⟩
  unfold encodePlan at hEnc
  split at hEnc
  · cases hEnc
  · next hMandFalse =>
    split at hEnc
    · cases hEnc
    · split at hEnc
      · cases hEnc
      · split at hEnc
        · cases hEnc
        · split at hEnc
          · cases hEnc
          · next hSecFalse =>
            have hMand :
                cplan.emptyRoot = true ∧
                cplan.unshareAllNamespaces = true ∧
                cplan.mountFreshProc = true ∧
                cplan.mountSafeDev = true ∧
                cplan.directCgroupV2Fs = true ∧
                4 ≤ cplan.landlockMinAbi ∧
                cplan.blockUnixSocketAndSmc = true ∧
                cplan.allowAnonUnixSocketpair = true ∧
                cplan.clone3EnosysFallback = true ∧
                cplan.seccompStrictDenylist = true ∧
                cplan.noNewPrivs = true ∧
                cplan.rlimitCoreZero = true ∧
                cplan.subreaperAndPdeathsig = true ∧
                cplan.cleanEnv = true := by
              simp only [Bool.or_eq_true, Bool.not_eq_true', decide_eq_true_eq,
                not_or, not_lt, Bool.not_eq_false] at hMandFalse
              rcases hMandFalse with
                ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩, h12⟩, h13⟩, h14⟩
              exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14⟩
            have hSecOk :
                seccompBytes.size ≠ 0 ∧ seccompBytes.size % 8 = 0 ∧ seccompBytes.size ≤ 1280 := by
              have hMaxInsns : 8 * SECCOMP_MAX_INSNS = 1280 := rfl
              simp only [Bool.or_eq_true, beq_iff_eq, bne_iff_ne, decide_eq_true_eq,
                not_or, not_ne_iff, not_lt, gt_iff_lt, hMaxInsns] at hSecFalse
              exact ⟨hSecFalse.1.1, hSecFalse.1.2, hSecFalse.2⟩
            cases hPre : encodePlanPrefix cplan with
            | error err =>
              rw [hPre] at hEnc
              cases hEnc
            | ok preBa =>
              rw [hPre] at hEnc
              change Except.ok (pushU32LE preBa (UInt32.ofNat (seccompBytes.size / 8)) ++ seccompBytes) =
                Except.ok bs at hEnc
              have hBsEq : bs = preBa ++ pushU32LE ByteArray.empty (UInt32.ofNat (seccompBytes.size / 8)) ++ seccompBytes := by
                cases hEnc
                rw [pushU32LE_eq_append]
              let data : Slice U8 := Slice.from (byteArrayToBytes bs) hMax
              have hDataVal : data.val = byteArrayToBytes bs := by simp [data]
              unfold encodePlanPrefix at hPre
              rcases hMand with
                ⟨hEr, hUn, hMp, hMd, hCg, hAbi4, hBu, hAp, hCl, hSd, hNnp, hRc, hSr, hCe⟩
              rw [hEr, hUn, hMp, hMd, hCg, hBu, hAp, hCl, hSd, hNnp, hRc, hSr, hCe] at hPre
              have hStepStr :
                  ∀ (x : String) (ba : ByteArray),
                    (do let ba ← pushStr ba x; pure (ForInStep.yield ba)) =
                      (pushStr ByteArray.empty x).map (fun b => ForInStep.yield (ba ++ b)) := by
                intro x ba
                rw [pushStr_eq_append]
                cases pushStr ByteArray.empty x <;> rfl
              have hStepEnv :
                  ∀ (kv : String × String) (ba : ByteArray),
                    (match kv with
                     | (k, v) => do
                         let ba ← pushStr ba k
                         let ba ← pushStr ba v
                         pure (ForInStep.yield ba)) =
                    (encodeEnvPair0 kv).map (fun b => ForInStep.yield (ba ++ b)) := by
                rintro ⟨k, v⟩ ba
                dsimp only
                unfold encodeEnvPair0
                rw [pushStr_eq_append ba k]
                cases pushStr ByteArray.empty k with
                | error e => rfl
                | ok bk =>
                  change (do let ba ← pushStr (ba ++ bk) v; pure (ForInStep.yield ba)) = _
                  rw [pushStr_eq_append (ba ++ bk) v]
                  cases pushStr ByteArray.empty v with
                  | error e => rfl
                  | ok bv =>
                    change Except.ok (ForInStep.yield ((ba ++ bk) ++ bv)) =
                      Except.ok (ForInStep.yield (ba ++ (bk ++ bv)))
                    rw [byteArray_append_assoc]
              have hStepFwd :
                  ∀ (pf : PortForward) (ba : ByteArray),
                    (pure (ForInStep.yield (pushU16LE (pushU16LE ba pf.boxPort) pf.hostPort)) :
                      Except SandboxError (ForInStep ByteArray)) =
                    (encodePortFwd0 pf).map (fun b => ForInStep.yield (ba ++ b)) := by
                intro pf ba
                unfold encodePortFwd0
                change Except.ok (ForInStep.yield (pushU16LE (pushU16LE ba pf.boxPort) pf.hostPort)) =
                  Except.ok (ForInStep.yield (ba ++ (pushU16LE ByteArray.empty pf.boxPort ++ pushU16LE ByteArray.empty pf.hostPort)))
                rw [pushU16LE_eq_append (pushU16LE ba pf.boxPort), pushU16LE_eq_append ba,
                  byteArray_append_assoc]
              let hdrFixed : ByteArray :=
                pushU64LE
                  (pushU8
                    (pushU64LE
                      (pushU8
                        (pushU64LE
                          (pushU8
                            (pushU64LE
                              (pushU8
                                (pushU64LE
                                  (pushU8 (pushU8 (pushU8 (pushU8 (pushU8 (pushU8 (pushU8 (pushU8
                                    (pushU8
                                      (pushU32LE
                                        (pushU8 (pushU8 (pushU8 (pushU8 (pushU8 "LSWP0002".toUTF8 1) 1) 1) 1) 1)
                                        (UInt32.ofNat (Nat.min cplan.landlockMinAbi (UInt32.size - 1))))
                                      (boolU8 cplan.allowBoxLocalhost))
                                    1) 1) 1) 1) 1) 1) 1) 1)
                                  (natToUInt64Sat cplan.limits.timeoutMs))
                                (boolU8 cplan.limits.memoryMaxBytes.isSome))
                              (natToUInt64Sat (cplan.limits.memoryMaxBytes.getD 0)))
                            (boolU8 cplan.limits.pidsMax.isSome))
                          (natToUInt64Sat (cplan.limits.pidsMax.getD 0)))
                        (boolU8 cplan.limits.fileSizeMaxBytes.isSome))
                      (natToUInt64Sat (cplan.limits.fileSizeMaxBytes.getD 0)))
                    (boolU8 cplan.limits.maxOutputBytes.isSome))
                  (natToUInt64Sat (cplan.limits.maxOutputBytes.getD 0))
              have hBool1 : boolU8 true = 1 := rfl
              simp only [hBool1,
                array_forIn_encodeList _ _ hStepStr,
                array_forIn_encodeList _ _ hStepEnv,
                array_forIn_encodeList _ _ hStepFwd] at hPre
              rw [pushStr_eq_append hdrFixed cplan.program] at hPre
              cases hProg : pushStr ByteArray.empty cplan.program with
              | error err =>
                rw [hProg] at hPre
                cases hPre
              | ok progBa =>
                rw [hProg, except_map_ok_bind] at hPre
                rw [pushStr_eq_append (hdrFixed ++ progBa) cplan.cwd] at hPre
                cases hCwd : pushStr ByteArray.empty cplan.cwd with
                | error err =>
                  rw [hCwd] at hPre
                  cases hPre
                | ok cwdBa =>
                  rw [hCwd, except_map_ok_bind] at hPre
                  cases hArgs : encodeList (pushStr ByteArray.empty) cplan.args.toList with
                  | error err =>
                    rw [hArgs] at hPre
                    cases hPre
                  | ok argsBss =>
                    rw [hArgs, except_map_ok_bind] at hPre
                    cases hEnv : encodeList encodeEnvPair0 cplan.env.toList with
                    | error err =>
                      rw [hEnv] at hPre
                      cases hPre
                    | ok envBss =>
                      rw [hEnv, except_map_ok_bind] at hPre
                      replace hPre := step_forIn_encodeList encodeSysEntry0 hPre (by
                        intro e ba
                        cases e with
                        | readOnlyDir p =>
                          dsimp only [encodeSysEntry0]
                          rw [pushU8_eq_append ba 0, pushStr_eq_append]
                          cases pushStr ByteArray.empty p with
                          | error err => rfl
                          | ok bp =>
                            change Except.ok (ForInStep.yield ((ba ++ ByteArray.mk #[0]) ++ bp)) =
                              Except.ok (ForInStep.yield (ba ++ (ByteArray.mk #[0] ++ bp)))
                            rw [byteArray_append_assoc]
                        | topSymlink lp tgt =>
                          dsimp only [encodeSysEntry0]
                          rw [pushU8_eq_append ba 1, pushStr_eq_append]
                          cases pushStr ByteArray.empty lp with
                          | error err => rfl
                          | ok b1 =>
                            change (do let ba ← pushStr ((ba ++ ByteArray.mk #[1]) ++ b1) tgt; pure (ForInStep.yield ba)) = _
                            rw [pushStr_eq_append]
                            cases pushStr ByteArray.empty tgt with
                            | error err => rfl
                            | ok b2 =>
                              change Except.ok (ForInStep.yield (((ba ++ ByteArray.mk #[1]) ++ b1) ++ b2)) =
                                Except.ok (ForInStep.yield (ba ++ ((ByteArray.mk #[1] ++ b1) ++ b2)))
                              simp only [byteArray_append_assoc])
                      cases hSys : encodeList encodeSysEntry0 cplan.presetSystemEntries.toList with
                      | error err =>
                        rw [hSys] at hPre
                        cases hPre
                      | ok sysBss =>
                        rw [hSys, except_map_ok_bind] at hPre
                        cases hEtc : encodeList (pushStr ByteArray.empty) cplan.presetEtcPaths.toList with
                        | error err =>
                          rw [hEtc] at hPre
                          cases hPre
                        | ok etcBss =>
                          rw [hEtc, except_map_ok_bind] at hPre
                          cases hMasks : encodeList (pushStr ByteArray.empty) cplan.maskedPresetPaths.toList with
                          | error err =>
                            rw [hMasks] at hPre
                            cases hPre
                          | ok maskBss =>
                            rw [hMasks, except_map_ok_bind] at hPre
                            replace hPre := step_forIn_encodeList encodeMount0 hPre (by
                              intro m ba
                              cases m with
                              | readOnly hp bp =>
                                dsimp only [encodeMount0]
                                rw [pushU8_eq_append ba 0, pushStr_eq_append]
                                cases pushStr ByteArray.empty hp with
                                | error err => rfl
                                | ok bhp =>
                                  change (do let ba ← pushStr ((ba ++ ByteArray.mk #[0]) ++ bhp) bp; pure (ForInStep.yield ba)) = _
                                  rw [pushStr_eq_append]
                                  cases pushStr ByteArray.empty bp with
                                  | error err => rfl
                                  | ok bbp =>
                                    change Except.ok (ForInStep.yield (((ba ++ ByteArray.mk #[0]) ++ bhp) ++ bbp)) =
                                      Except.ok (ForInStep.yield (ba ++ ((ByteArray.mk #[0] ++ bhp) ++ bbp)))
                                    simp only [byteArray_append_assoc]
                              | readWrite hp bp =>
                                dsimp only [encodeMount0]
                                rw [pushU8_eq_append ba 1, pushStr_eq_append]
                                cases pushStr ByteArray.empty hp with
                                | error err => rfl
                                | ok bhp =>
                                  change (do let ba ← pushStr ((ba ++ ByteArray.mk #[1]) ++ bhp) bp; pure (ForInStep.yield ba)) = _
                                  rw [pushStr_eq_append]
                                  cases pushStr ByteArray.empty bp with
                                  | error err => rfl
                                  | ok bbp =>
                                    change Except.ok (ForInStep.yield (((ba ++ ByteArray.mk #[1]) ++ bhp) ++ bbp)) =
                                      Except.ok (ForInStep.yield (ba ++ ((ByteArray.mk #[1] ++ bhp) ++ bbp)))
                                    simp only [byteArray_append_assoc]
                              | scratch bp =>
                                dsimp only [encodeMount0]
                                rw [pushU8_eq_append ba 2, pushStr_eq_append]
                                cases pushStr ByteArray.empty bp with
                                | error err => rfl
                                | ok bbp =>
                                  change Except.ok (ForInStep.yield ((ba ++ ByteArray.mk #[2]) ++ bbp)) =
                                    Except.ok (ForInStep.yield (ba ++ (ByteArray.mk #[2] ++ bbp)))
                                  rw [byteArray_append_assoc])
                            cases hMnts : encodeList encodeMount0 cplan.userMounts.toList with
                            | error err =>
                              rw [hMnts] at hPre
                              cases hPre
                            | ok mntBss =>
                              rw [hMnts, except_map_ok_bind] at hPre
                              cases hFwds : encodeList encodePortFwd0 cplan.portForwards.toList with
                              | error err =>
                                rw [hFwds] at hPre
                                cases hPre
                              | ok fwdBss =>
                                rw [hFwds] at hPre
                                simp only [Except.map] at hPre
                                have hHdrDecomp :
                                    byteArrayToBytes hdrFixed =
                                      byteArrayToBytes "LSWP0002".toUTF8 ++
                                      byteArrayToBytes
                                        (pushU32LE
                                          (pushU8 (pushU8 (pushU8 (pushU8 (pushU8 ByteArray.empty 1) 1) 1) 1) 1)
                                          (UInt32.ofNat (Nat.min cplan.landlockMinAbi (UInt32.size - 1)))) ++
                                      [u8OfUInt8 (boolU8 cplan.allowBoxLocalhost),
                                       1#u8, 1#u8, 1#u8, 1#u8, 1#u8, 1#u8, 1#u8, 1#u8] ++
                                      (byteArrayToBytes (pushU64LE ByteArray.empty (natToUInt64Sat cplan.limits.timeoutMs)) ++
                                       [u8OfUInt8 (boolU8 cplan.limits.memoryMaxBytes.isSome)] ++
                                       byteArrayToBytes (pushU64LE ByteArray.empty (natToUInt64Sat (cplan.limits.memoryMaxBytes.getD 0))) ++
                                       [u8OfUInt8 (boolU8 cplan.limits.pidsMax.isSome)] ++
                                       byteArrayToBytes (pushU64LE ByteArray.empty (natToUInt64Sat (cplan.limits.pidsMax.getD 0))) ++
                                       [u8OfUInt8 (boolU8 cplan.limits.fileSizeMaxBytes.isSome)] ++
                                       byteArrayToBytes (pushU64LE ByteArray.empty (natToUInt64Sat (cplan.limits.fileSizeMaxBytes.getD 0))) ++
                                       [u8OfUInt8 (boolU8 cplan.limits.maxOutputBytes.isSome)] ++
                                       byteArrayToBytes (pushU64LE ByteArray.empty (natToUInt64Sat (cplan.limits.maxOutputBytes.getD 0)))) := by
                                  dsimp only [hdrFixed]
                                  simp only [byteArrayToBytes_pushU64LE_u64Bytes, byteArrayToBytes_pushU32LE_u32Bytes,
                                    byteArrayToBytes_pushU8_eq, byteArrayToBytes_empty,
                                    List.nil_append, List.cons_append, List.append_assoc]
                                  rfl
                                have hPreBytesEq :
                                    byteArrayToBytes preBa =
                                      byteArrayToBytes hdrFixed ++
                                      byteArrayToBytes progBa ++
                                      byteArrayToBytes cwdBa ++
                                      byteArrayToBytes (pushU32LE ByteArray.empty (UInt32.ofNat cplan.args.size)) ++
                                      byteArrayToBytes (concatByteArrays argsBss) ++
                                      byteArrayToBytes (pushU32LE ByteArray.empty (UInt32.ofNat cplan.env.size)) ++
                                      byteArrayToBytes (concatByteArrays envBss) ++
                                      byteArrayToBytes (pushU32LE ByteArray.empty (UInt32.ofNat cplan.presetSystemEntries.size)) ++
                                      byteArrayToBytes (concatByteArrays sysBss) ++
                                      byteArrayToBytes (pushU32LE ByteArray.empty (UInt32.ofNat cplan.presetEtcPaths.size)) ++
                                      byteArrayToBytes (concatByteArrays etcBss) ++
                                      byteArrayToBytes (pushU32LE ByteArray.empty (UInt32.ofNat cplan.maskedPresetPaths.size)) ++
                                      byteArrayToBytes (concatByteArrays maskBss) ++
                                      byteArrayToBytes (pushU32LE ByteArray.empty (UInt32.ofNat cplan.userMounts.size)) ++
                                      byteArrayToBytes (concatByteArrays mntBss) ++
                                      byteArrayToBytes (pushU32LE ByteArray.empty (UInt32.ofNat cplan.portForwards.size)) ++
                                      byteArrayToBytes (concatByteArrays fwdBss) := by
                                  rw [← except_ok_inj hPre]
                                  simp only [byteArrayToBytes_pushU32LE_u32Bytes, byteArrayToBytes_empty,
                                    byteArrayToBytes_append, List.nil_append, List.append_assoc]
                                have hFullBytes :
                                    data.val =
                                      byteArrayToBytes preBa ++
                                      byteArrayToBytes (pushU32LE ByteArray.empty (UInt32.ofNat (seccompBytes.size / 8))) ++
                                      byteArrayToBytes seccompBytes := by
                                  rw [hDataVal, hBsEq, byteArrayToBytes_append, byteArrayToBytes_append]
                                rw [hPreBytesEq, hHdrDecomp] at hFullBytes
                                let s0 : Bytes := byteArrayToBytes "LSWP0002".toUTF8
                                let s1 : Bytes :=
                                  byteArrayToBytes
                                    (pushU32LE
                                      (pushU8 (pushU8 (pushU8 (pushU8 (pushU8 ByteArray.empty 1) 1) 1) 1) 1)
                                      (UInt32.ofNat (Nat.min cplan.landlockMinAbi (UInt32.size - 1))))
                                let s2 : Bytes :=
                                  [u8OfUInt8 (boolU8 cplan.allowBoxLocalhost),
                                   1#u8, 1#u8, 1#u8, 1#u8, 1#u8, 1#u8, 1#u8, 1#u8]
                                let s3 : Bytes :=
                                  byteArrayToBytes (pushU64LE ByteArray.empty (natToUInt64Sat cplan.limits.timeoutMs)) ++
                                  [u8OfUInt8 (boolU8 cplan.limits.memoryMaxBytes.isSome)] ++
                                  byteArrayToBytes (pushU64LE ByteArray.empty (natToUInt64Sat (cplan.limits.memoryMaxBytes.getD 0))) ++
                                  [u8OfUInt8 (boolU8 cplan.limits.pidsMax.isSome)] ++
                                  byteArrayToBytes (pushU64LE ByteArray.empty (natToUInt64Sat (cplan.limits.pidsMax.getD 0))) ++
                                  [u8OfUInt8 (boolU8 cplan.limits.fileSizeMaxBytes.isSome)] ++
                                  byteArrayToBytes (pushU64LE ByteArray.empty (natToUInt64Sat (cplan.limits.fileSizeMaxBytes.getD 0))) ++
                                  [u8OfUInt8 (boolU8 cplan.limits.maxOutputBytes.isSome)] ++
                                  byteArrayToBytes (pushU64LE ByteArray.empty (natToUInt64Sat (cplan.limits.maxOutputBytes.getD 0)))
                                let s4 : Bytes := byteArrayToBytes progBa
                                let s5 : Bytes := byteArrayToBytes cwdBa
                                let s6 : Bytes := byteArrayToBytes (pushU32LE ByteArray.empty (UInt32.ofNat cplan.args.size))
                                let s7 : Bytes := byteArrayToBytes (concatByteArrays argsBss)
                                let s8 : Bytes := byteArrayToBytes (pushU32LE ByteArray.empty (UInt32.ofNat cplan.env.size))
                                let s9 : Bytes := byteArrayToBytes (concatByteArrays envBss)
                                let s10 : Bytes := byteArrayToBytes (pushU32LE ByteArray.empty (UInt32.ofNat cplan.presetSystemEntries.size))
                                let s11 : Bytes := byteArrayToBytes (concatByteArrays sysBss)
                                let s12 : Bytes := byteArrayToBytes (pushU32LE ByteArray.empty (UInt32.ofNat cplan.presetEtcPaths.size))
                                let s13 : Bytes := byteArrayToBytes (concatByteArrays etcBss)
                                let s14 : Bytes := byteArrayToBytes (pushU32LE ByteArray.empty (UInt32.ofNat cplan.maskedPresetPaths.size))
                                let s15 : Bytes := byteArrayToBytes (concatByteArrays maskBss)
                                let s16 : Bytes := byteArrayToBytes (pushU32LE ByteArray.empty (UInt32.ofNat cplan.userMounts.size))
                                let s17 : Bytes := byteArrayToBytes (concatByteArrays mntBss)
                                let s18 : Bytes := byteArrayToBytes (pushU32LE ByteArray.empty (UInt32.ofNat cplan.portForwards.size))
                                let s19 : Bytes := byteArrayToBytes (concatByteArrays fwdBss)
                                let s20 : Bytes :=
                                  byteArrayToBytes (pushU32LE ByteArray.empty (UInt32.ofNat (seccompBytes.size / 8))) ++
                                  byteArrayToBytes seccompBytes
                                have hFullRight :
                                    data.val =
                                      s0 ++ (s1 ++ (s2 ++ (s3 ++ (s4 ++ (s5 ++ (s6 ++ (s7 ++ (s8 ++ (s9 ++
                                      (s10 ++ (s11 ++ (s12 ++ (s13 ++ (s14 ++ (s15 ++ (s16 ++ (s17 ++ (s18 ++
                                      (s19 ++ s20))))))))))))))))))) := by
                                  dsimp only [s0, s1, s2, s3, s4, s5, s6, s7, s8, s9,
                                    s10, s11, s12, s13, s14, s15, s16, s17, s18, s19, s20]
                                  simpa only [List.append_assoc] using hFullBytes
                                obtain ⟨hrMag, hsMag⟩ := check_magic_atOffset data _ (atOffset_zero_of_eq hFullRight)
                                obtain ⟨llAbiU32, hp1Pos, hrPart1, hAbiEq, hAbiGe4, _, hsPart1⟩ :=
                                  parse_header_part1_atOffset data 8#usize cplan.landlockMinAbi _ hAbi4 (atOffset_next hsMag)
                                obtain ⟨hp2Pos, hrPart2, _, hsPart2⟩ :=
                                  parse_header_part2_atOffset data hp1Pos cplan.allowBoxLocalhost _ (atOffset_next hsPart1)
                                obtain ⟨p1, hrLim, _, hsLim⟩ :=
                                  parse_header_limits_atOffset data hp2Pos
                                    (natToUInt64Sat cplan.limits.timeoutMs)
                                    (boolU8 cplan.limits.memoryMaxBytes.isSome)
                                    (natToUInt64Sat (cplan.limits.memoryMaxBytes.getD 0))
                                    (boolU8 cplan.limits.pidsMax.isSome)
                                    (natToUInt64Sat (cplan.limits.pidsMax.getD 0))
                                    cplan.limits.fileSizeMaxBytes.isSome
                                    (natToUInt64Sat (cplan.limits.fileSizeMaxBytes.getD 0))
                                    (boolU8 cplan.limits.maxOutputBytes.isSome)
                                    (natToUInt64Sat (cplan.limits.maxOutputBytes.getD 0))
                                    _ (atOffset_next hsPart2)
                                let hdr : plan.PlanHeader :=
                                  { allow_box_localhost := cplan.allowBoxLocalhost
                                    has_file_size_max := cplan.limits.fileSizeMaxBytes.isSome
                                    file_size_max_bytes := ⟨(natToUInt64Sat (cplan.limits.fileSizeMaxBytes.getD 0)).toBitVec⟩
                                    landlock_min_abi := llAbiU32 }
                                have hrHdr : plan.parse_header data 8#usize = Result.ok (.Ok (hdr, p1)) := by
                                  rw [plan.parse_header]
                                  refine eq_ok_of_try_ok hrPart1 ?_
                                  refine eq_ok_of_try_ok hrPart2 ?_
                                  exact eq_ok_of_try_ok hrLim rfl
                                obtain ⟨progSp, p2, hrProg, _, _, hProgBytes, _, hsProg⟩ :=
                                  read_str_span_atOffset data p1 cplan.program progBa _ hProg (atOffset_next hsLim)
                                obtain ⟨cwdSp, p3, hrCwd, _, _, hCwdBytes, _, hsCwd⟩ :=
                                  read_str_span_atOffset data p2 cplan.cwd cwdBa _ hCwd (atOffset_next hsProg)
                                have hMaxArgc : plan.MAX_ARGC.val = 65536 := by simp [plan.MAX_ARGC]
                                obtain ⟨argcU32, argsPos, hrArgc, hArgcVal, _, hsArgc⟩ :=
                                  read_bounded_count_atOffset data p3 cplan.args.size plan.MAX_ARGC _
                                    (by omega) (atOffset_next hsCwd)
                                obtain ⟨p4, hrArgs, _, hsArgs⟩ :=
                                  scan_str_list_atOffset data argsPos argcU32 cplan.args.toList argsBss _
                                    hArgs (by simp [hArgcVal]) (atOffset_next hsArgc)
                                have hMaxEnvc : plan.MAX_ENVC.val = 65536 := by simp [plan.MAX_ENVC]
                                obtain ⟨envcU32, envPos, hrEnvc, hEnvcVal, _, hsEnvc⟩ :=
                                  read_bounded_count_atOffset data p4 cplan.env.size plan.MAX_ENVC _
                                    (by omega) (atOffset_next hsArgs)
                                obtain ⟨p5, hrEnv, _, hsEnv⟩ :=
                                  scan_env_list_atOffset data envPos envcU32 cplan.env.toList envBss _
                                    hEnv (by simp [hEnvcVal]) (atOffset_next hsEnvc)
                                have hMaxSys : plan.MAX_SYS_ENTRIES.val = 1024 := by simp [plan.MAX_SYS_ENTRIES]
                                obtain ⟨sysU32, sysPos, hrSysCnt, hSysVal, _, hsSysCnt⟩ :=
                                  read_bounded_count_atOffset data p5 cplan.presetSystemEntries.size plan.MAX_SYS_ENTRIES _
                                    (by omega) (atOffset_next hsEnv)
                                obtain ⟨p6, hrSys, _, hsSys⟩ :=
                                  scan_sys_entries_atOffset data sysPos sysU32 cplan.presetSystemEntries.toList sysBss _
                                    hSys (by simp [hSysVal]) (atOffset_next hsSysCnt)
                                have hMaxEtc : plan.MAX_ETC_PATHS.val = 1024 := by simp [plan.MAX_ETC_PATHS]
                                obtain ⟨etcU32, etcPos, hrEtcCnt, hEtcVal, _, hsEtcCnt⟩ :=
                                  read_bounded_count_atOffset data p6 cplan.presetEtcPaths.size plan.MAX_ETC_PATHS _
                                    (by omega) (atOffset_next hsSys)
                                obtain ⟨p7, hrEtc, _, hsEtc⟩ :=
                                  scan_str_list_atOffset data etcPos etcU32 cplan.presetEtcPaths.toList etcBss _
                                    hEtc (by simp [hEtcVal]) (atOffset_next hsEtcCnt)
                                have hMaxMasks : plan.MAX_MASK_PATHS.val = 1024 := by simp [plan.MAX_MASK_PATHS]
                                obtain ⟨masksU32, masksPos, hrMaskCnt, hMasksVal, _, hsMaskCnt⟩ :=
                                  read_bounded_count_atOffset data p7 cplan.maskedPresetPaths.size plan.MAX_MASK_PATHS _
                                    (by omega) (atOffset_next hsEtc)
                                obtain ⟨p8, hrMasks, _, hsMasks⟩ :=
                                  scan_str_list_atOffset data masksPos masksU32 cplan.maskedPresetPaths.toList maskBss _
                                    hMasks (by simp [hMasksVal]) (atOffset_next hsMaskCnt)
                                have hMaxMnts : plan.MAX_MOUNTS.val = 4096 := by simp [plan.MAX_MOUNTS]
                                obtain ⟨mntsU32, mntsPos, hrMntCnt, hMntsVal, _, hsMntCnt⟩ :=
                                  read_bounded_count_atOffset data p8 cplan.userMounts.size plan.MAX_MOUNTS _
                                    (by omega) (atOffset_next hsMasks)
                                obtain ⟨p9, hrMnts, _, hsMnts⟩ :=
                                  scan_mounts_atOffset data mntsPos mntsU32 cplan.userMounts.toList mntBss _
                                    hMnts (by simp [hMntsVal]) (atOffset_next hsMntCnt)
                                have hMaxFwds : plan.MAX_PORT_FORWARDS.val = 1024 := by simp [plan.MAX_PORT_FORWARDS]
                                obtain ⟨fwdsU32, fwdsPos, hrFwdCnt, hFwdsVal, _, hsFwdCnt⟩ :=
                                  read_bounded_count_atOffset data p9 cplan.portForwards.size plan.MAX_PORT_FORWARDS _
                                    (by omega) (atOffset_next hsMnts)
                                have hAtFwds : AtOffset data fwdsPos (byteArrayToBytes (concatByteArrays fwdBss))
                                    (byteArrayToBytes (pushU32LE ByteArray.empty (UInt32.ofNat (seccompBytes.size / 8))) ++
                                     byteArrayToBytes seccompBytes) :=
                                  atOffset_next hsFwdCnt
                                have hFwdsSz : (concatByteArrays fwdBss).size = cplan.portForwards.size * 4 := by
                                  simpa using encodePortFwds_size cplan.portForwards.toList fwdBss hFwds
                                have hFwdsTot := atOffset_len_eq hAtFwds
                                rw [length_byteArrayToBytes, hFwdsSz] at hFwdsTot
                                have h4u : (4#usize).val = 4 := rfl
                                have hDataMax := data.property
                                have hCastFwds : (UScalar.cast .Usize fwdsU32 : Usize).val = cplan.portForwards.size := by
                                  rw [u32_cast_usize_val, hFwdsVal]
                                obtain ⟨fwdsBytes, hMulFwds, hFwdsBytesVal⟩ :=
                                  usize_mul_ok (UScalar.cast .Usize fwdsU32) 4#usize
                                    (by change (UScalar.cast .Usize fwdsU32 : Usize).val * 4 ≤ Usize.max; omega)
                                have hFwdsBytesEq : fwdsBytes.val = cplan.portForwards.size * 4 := by
                                  rw [hFwdsBytesVal, hCastFwds, h4u]
                                have hLenData : (Slice.len data).val = data.val.length := by simp
                                obtain ⟨remFwds, hSubFwds, hRemFwdsVal⟩ :=
                                  usize_sub_ok (Slice.len data) fwdsPos (by rw [hLenData]; omega)
                                have hRemFwdsEq : remFwds.val = data.val.length - fwdsPos.val := by
                                  rw [hRemFwdsVal, hLenData]
                                have hNotGtFwds : ¬ (fwdsBytes > remFwds) := by
                                  intro hGt
                                  have : remFwds.val < fwdsBytes.val := by simpa using hGt
                                  omega
                                obtain ⟨p10, hAddP10, hp10Val⟩ :=
                                  usize_add_ok fwdsPos fwdsBytes (by omega)
                                have hAtSec : AtOffset data p10
                                    (byteArrayToBytes (pushU32LE ByteArray.empty (UInt32.ofNat (seccompBytes.size / 8))))
                                    (byteArrayToBytes seccompBytes) :=
                                  atOffset_step hAtFwds
                                    (by rw [hp10Val, hFwdsBytesVal, hCastFwds, h4u, length_byteArrayToBytes, hFwdsSz])
                                obtain ⟨seccompPos, _, hsSec, hrSec⟩ :=
                                  validate_seccomp_trailer_atOffset data p10
                                    (UInt32.ofNat (seccompBytes.size / 8))
                                    (byteArrayToBytes seccompBytes) hAtSec
                                have hSecNVal : (UInt32.ofNat (seccompBytes.size / 8)).toNat = seccompBytes.size / 8 := by
                                  have hSz32 : UInt32.size = 4294967296 := rfl
                                  exact Nat.mod_eq_of_lt (by omega)
                                have hSecCond :
                                    1 ≤ (UInt32.ofNat (seccompBytes.size / 8)).toNat ∧
                                    (UInt32.ofNat (seccompBytes.size / 8)).toNat ≤ 160 ∧
                                    (byteArrayToBytes seccompBytes).length =
                                      8 * (UInt32.ofNat (seccompBytes.size / 8)).toNat := by
                                  rw [hSecNVal, length_byteArrayToBytes]
                                  rcases hSecOk with ⟨hNe0, hMod8, hLe1280⟩
                                  omega
                                rw [if_true_eq hSecCond] at hrSec
                                let view : plan.PlanView :=
                                  { header := hdr
                                    program := progSp
                                    cwd := cwdSp
                                    argc := argcU32
                                    args_pos := argsPos
                                    envc := envcU32
                                    env_pos := envPos
                                    n_sys := sysU32
                                    sys_pos := sysPos
                                    n_etc := etcU32
                                    etc_pos := etcPos
                                    n_masks := masksU32
                                    masks_pos := masksPos
                                    n_mounts := mntsU32
                                    mounts_pos := mntsPos
                                    n_fwds := fwdsU32
                                    fwds_pos := fwdsPos
                                    seccomp_n := ⟨(UInt32.ofNat (seccompBytes.size / 8)).toBitVec⟩
                                    seccomp_pos := seccompPos }
                                have hSecDrop : (byteArrayToBytes bs).drop seccompPos.val = byteArrayToBytes seccompBytes := by
                                  simpa [hDataVal, List.append_nil] using hsSec.2
                                refine ⟨view, ?_, rfl, rfl, rfl, hAbiEq, hAbiGe4,
                                  by rwa [hDataVal] at hProgBytes,
                                  by rwa [hDataVal] at hCwdBytes,
                                  hArgcVal, hEnvcVal, hSysVal,
                                  hEtcVal, hMasksVal, hMntsVal, hFwdsVal, hSecNVal,
                                  hSecCond.1, hSecCond.2.1, hSecDrop⟩
                                rw [plan.parse_plan]
                                refine eq_ok_of_try_ok hrMag ?_
                                refine eq_ok_of_try_ok hrHdr ?_
                                refine eq_ok_of_try_ok hrProg ?_
                                refine eq_ok_of_try_ok hrCwd ?_
                                refine eq_ok_of_try_ok hrArgc ?_
                                refine eq_ok_of_try_ok hrArgs ?_
                                refine eq_ok_of_try_ok hrEnvc ?_
                                refine eq_ok_of_try_ok hrEnv ?_
                                refine eq_ok_of_try_ok hrSysCnt ?_
                                refine eq_ok_of_try_ok hrSys ?_
                                refine eq_ok_of_try_ok hrEtcCnt ?_
                                refine eq_ok_of_try_ok hrEtc ?_
                                refine eq_ok_of_try_ok hrMaskCnt ?_
                                refine eq_ok_of_try_ok hrMasks ?_
                                refine eq_ok_of_try_ok hrMntCnt ?_
                                refine eq_ok_of_try_ok hrMnts ?_
                                refine eq_ok_of_try_ok hrFwdCnt ?_
                                refine eq_ok_of_bind rfl ?_
                                refine eq_ok_of_bind hMulFwds ?_
                                refine eq_ok_of_bind hSubFwds ?_
                                change (if fwdsBytes > remFwds then _ else _) = _
                                rw [if_false_eq hNotGtFwds]
                                refine eq_ok_of_bind hAddP10 ?_
                                exact eq_ok_of_try_ok hrSec rfl

/-- `ops.install_seccomp` succeeds with `.Ok ()` (recording `(.syscall, view.seccomp_n)` in
`seccompInstalled`) whenever `s.seccompErr? = none`, `1 ≤ view.seccomp_n ≤ 160`, and
`AtOffset data view.seccomp_pos seccompBytes []` with
`seccompBytes.length = 8 * view.seccomp_n.val` (as guaranteed by `parse_plan`). -/
theorem install_seccomp_valid_view_spec
    (s : init_sys.Sys) (data : Slice U8) (view : plan.PlanView) (seccompBytes : Bytes)
    (hLo : 1 ≤ view.seccomp_n.val) (hHi : view.seccomp_n.val ≤ 160)
    (hAt : AtOffset data view.seccomp_pos seccompBytes [])
    (hLen : seccompBytes.length = 8 * view.seccomp_n.val)
    (hNoErr : s.seccompErr? = none) :
    ops.install_seccomp s data view =
      Result.ok (.Ok (),
        { s with
          seccompInstalled := s.seccompInstalled ++ [(.syscall, view.seccomp_n)] }) := by
  have hTot := atOffset_len_eq hAt
  simp only [List.length_nil] at hTot
  have h8u : (8#usize).val = 8 := rfl
  have hDataMax := data.property
  have hCastVal : (UScalar.cast .Usize view.seccomp_n : Usize).val = view.seccomp_n.val :=
    u32_cast_usize_val view.seccomp_n
  obtain ⟨byteLen, hMul, hByteLen⟩ :=
    usize_mul_ok (UScalar.cast .Usize view.seccomp_n) 8#usize
      (by have := usize_max_ge_u32_max; change (UScalar.cast .Usize view.seccomp_n : Usize).val * 8 ≤ Usize.max; omega)
  have hByteLenEq : byteLen.val = view.seccomp_n.val * 8 := by
    rw [hByteLen, hCastVal, h8u]
  have hLenData : (Slice.len data).val = data.val.length := by simp
  have hNotGtPos : ¬ (view.seccomp_pos > Slice.len data) := by
    intro hGt
    have : (Slice.len data).val < view.seccomp_pos.val := by simpa using hGt
    omega
  obtain ⟨rem, hSub, hRem⟩ :=
    usize_sub_ok (Slice.len data) view.seccomp_pos (by rw [hLenData]; omega)
  have hNotGtLen : ¬ (byteLen > rem) := by
    intro hGt
    have : rem.val < byteLen.val := by simpa using hGt
    omega
  obtain ⟨endPos, hAdd, hEndPos⟩ :=
    usize_add_ok view.seccomp_pos byteLen (by omega)
  have hSlice :
      ∃ sl : Slice U8,
        core.slice.index.Slice.index
          (core.slice.index.SliceIndexRangeUsizeSlice U8) data
          { start := view.seccomp_pos, «end» := endPos } = Result.ok sl ∧
        sl.val.length = view.seccomp_n.val * 8 := by
    change ∃ sl : Slice U8,
      core.slice.index.SliceIndexRangeUsizeSlice.index
        { start := view.seccomp_pos, «end» := endPos } data = Result.ok sl ∧ _
    rw [core.slice.index.SliceIndexRangeUsizeSlice.index]
    have hBound :
        ({ start := view.seccomp_pos, «end» := endPos } : core.ops.range.Range Usize).start ≤
          ({ start := view.seccomp_pos, «end» := endPos } : core.ops.range.Range Usize).end ∧
        ({ start := view.seccomp_pos, «end» := endPos } : core.ops.range.Range Usize).end.val ≤
          data.length := by
      refine ⟨?_, ?_⟩
      · change view.seccomp_pos.val ≤ endPos.val; omega
      · change endPos.val ≤ data.val.length; omega
    rw [if_true_eq hBound]
    refine ⟨_, rfl, ?_⟩
    simp [List.slice]
    omega
  obtain ⟨sl, hsl, hslLen⟩ := hSlice
  have hSecCall :
      init_sys.seccomp_set_mode_filter s sl view.seccomp_n =
        Result.ok (.Ok (),
          { s with
            seccompInstalled := s.seccompInstalled ++ [(.syscall, view.seccomp_n)] }) := by
    unfold init_sys.seccomp_set_mode_filter
    have hBad :
        (view.seccomp_n.val == 0 || decide (view.seccomp_n.val > 160) ||
          sl.val.length != view.seccomp_n.val * 8) = false := by
      rw [hslLen]
      have hz : (view.seccomp_n.val == 0) = false := beq_false_of_ne (by omega)
      have hg : decide (view.seccomp_n.val > 160) = false := decide_eq_false (by omega)
      simp [hz, hg]
    change (if (view.seccomp_n.val == 0 || decide (view.seccomp_n.val > 160) ||
        sl.val.length != view.seccomp_n.val * 8) = true then _ else _) = _
    rw [hBad, if_false_eq Bool.false_ne_true]
    simp [hNoErr]
  rw [ops.install_seccomp]
  refine eq_ok_of_bind rfl ?_
  refine eq_ok_of_bind hMul ?_
  change (if view.seccomp_pos > Slice.len data then _ else _) = _
  rw [if_false_eq hNotGtPos]
  refine eq_ok_of_bind hSub ?_
  change (if byteLen > rem then _ else _) = _
  rw [if_false_eq hNotGtLen]
  refine eq_ok_of_bind hAdd ?_
  refine eq_ok_of_bind hsl ?_
  exact eq_ok_of_bind hSecCall rfl

/-- `plan.parse_plan` rejects any wire buffer shorter than 8 bytes with `Err plan.EINVAL`. -/
theorem parse_plan_rejects_short_magic (data : Slice U8) (hShort : data.val.length < 8) :
    plan.parse_plan data = Result.ok (.Err plan.EINVAL) := by
  rw [plan.parse_plan]
  refine eq_ok_of_try_err (check_magic_rejects_short data hShort) ?_
  simp [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]

/-- `plan.parse_header_part1` rejects `landlock_min_abi < 4` with `Err plan.EINVAL`. -/
theorem parse_header_part1_rejects_low_abi (data : Slice U8) (pos : Usize)
    (abi : UInt32) (tail : Bytes)
    (hLow : abi.toNat < 4)
    (h : AtOffset data pos
      ([1#u8, 1#u8, 1#u8, 1#u8, 1#u8] ++ byteArrayToBytes (pushU32LE ByteArray.empty abi)) tail) :
    plan.parse_header_part1 data pos = Result.ok (.Err plan.EINVAL) := by
  have h0 : AtOffset data pos [1#u8]
      ([1#u8] ++ [1#u8] ++ [1#u8] ++ [1#u8] ++ byteArrayToBytes (pushU32LE ByteArray.empty abi) ++ tail) :=
    ⟨h.1, by simpa [List.append_assoc] using h.2⟩
  obtain ⟨p1, hr1, _, hs1⟩ := read_u8_atOffset data pos 1#u8 _ h0
  have h1 : AtOffset data p1 [1#u8]
      ([1#u8] ++ [1#u8] ++ [1#u8] ++ byteArrayToBytes (pushU32LE ByteArray.empty abi) ++ tail) :=
    ⟨hs1.1, by simpa [List.append_assoc] using hs1.2⟩
  obtain ⟨p2, hr2, _, hs2⟩ := read_u8_atOffset data p1 1#u8 _ h1
  have h2 : AtOffset data p2 [1#u8]
      ([1#u8] ++ [1#u8] ++ byteArrayToBytes (pushU32LE ByteArray.empty abi) ++ tail) :=
    ⟨hs2.1, by simpa [List.append_assoc] using hs2.2⟩
  obtain ⟨p3, hr3, _, hs3⟩ := read_u8_atOffset data p2 1#u8 _ h2
  have h3 : AtOffset data p3 [1#u8]
      ([1#u8] ++ byteArrayToBytes (pushU32LE ByteArray.empty abi) ++ tail) :=
    ⟨hs3.1, by simpa [List.append_assoc] using hs3.2⟩
  obtain ⟨p4, hr4, _, hs4⟩ := read_u8_atOffset data p3 1#u8 _ h3
  have h4 : AtOffset data p4 [1#u8]
      (byteArrayToBytes (pushU32LE ByteArray.empty abi) ++ tail) :=
    ⟨hs4.1, by simpa [List.append_assoc] using hs4.2⟩
  obtain ⟨p5, hr5, _, hs5⟩ := read_u8_atOffset data p4 1#u8 _ h4
  have h5 : AtOffset data p5 (byteArrayToBytes (pushU32LE ByteArray.empty abi)) tail :=
    ⟨hs5.1, by simpa [List.append_nil] using hs5.2⟩
  obtain ⟨p6, hr6, _, _⟩ := read_u32_le_atOffset data p5 abi tail h5
  have hNotGe4 : ¬ ((⟨abi.toBitVec⟩ : U32) ≥ 4#u32) := by
    intro hGe
    have hGeNat : (4#u32).val ≤ (⟨abi.toBitVec⟩ : U32).val := hGe
    change 4 ≤ abi.toNat at hGeNat
    omega
  have hCondF :
      ((((((1#u8 != 0#u8) && (1#u8 != 0#u8)) && (1#u8 != 0#u8)) &&
        (1#u8 != 0#u8)) && (1#u8 != 0#u8)) && decide ((⟨abi.toBitVec⟩ : U32) ≥ 4#u32)) = false := by
    rw [decide_eq_false hNotGe4]
    decide
  rw [plan.parse_header_part1]
  refine eq_ok_of_try_ok hr1 ?_
  refine eq_ok_of_try_ok hr2 ?_
  refine eq_ok_of_try_ok hr3 ?_
  refine eq_ok_of_try_ok hr4 ?_
  refine eq_ok_of_try_ok hr5 ?_
  refine eq_ok_of_try_ok hr6 ?_
  change (if ((((((1#u8 != 0#u8) && (1#u8 != 0#u8)) && (1#u8 != 0#u8)) &&
      (1#u8 != 0#u8)) && (1#u8 != 0#u8)) && decide ((⟨abi.toBitVec⟩ : U32) ≥ 4#u32)) = true then
      Result.ok (core.result.Result.Ok ((⟨abi.toBitVec⟩ : U32), p6))
    else Result.ok (core.result.Result.Err plan.EINVAL)) = _
  rw [hCondF, if_false_eq Bool.false_ne_true]

/-- `plan.validate_seccomp_trailer` rejects `seccomp_n = 0` with `Err plan.EINVAL`. -/
theorem validate_seccomp_trailer_rejects_zero (data : Slice U8) (pos : Usize) (seccompBytes : Bytes)
    (h : AtOffset data pos (byteArrayToBytes (pushU32LE ByteArray.empty 0)) seccompBytes) :
    plan.validate_seccomp_trailer data pos = Result.ok (.Err plan.EINVAL) := by
  obtain ⟨_, _, _, hEq⟩ := validate_seccomp_trailer_atOffset data pos 0 seccompBytes h
  rw [hEq, if_false_eq (by simp)]

/-- `plan.validate_seccomp_trailer` rejects `seccomp_n > 160` with `Err plan.EINVAL`. -/
theorem validate_seccomp_trailer_rejects_over_160 (data : Slice U8) (pos : Usize)
    (n : UInt32) (seccompBytes : Bytes)
    (hOver : 160 < n.toNat)
    (h : AtOffset data pos (byteArrayToBytes (pushU32LE ByteArray.empty n)) seccompBytes) :
    plan.validate_seccomp_trailer data pos = Result.ok (.Err plan.EINVAL) := by
  obtain ⟨_, _, _, hEq⟩ := validate_seccomp_trailer_atOffset data pos n seccompBytes h
  rw [hEq, if_false_eq (by omega)]

/-- `plan.validate_seccomp_trailer` rejects trailing/truncated byte counts (`seccompBytes.length ≠ 8 * n.toNat`). -/
theorem validate_seccomp_trailer_rejects_trailing_bytes (data : Slice U8) (pos : Usize)
    (n : UInt32) (seccompBytes : Bytes)
    (hMis : seccompBytes.length ≠ 8 * n.toNat)
    (h : AtOffset data pos (byteArrayToBytes (pushU32LE ByteArray.empty n)) seccompBytes) :
    plan.validate_seccomp_trailer data pos = Result.ok (.Err plan.EINVAL) := by
  obtain ⟨_, _, _, hEq⟩ := validate_seccomp_trailer_atOffset data pos n seccompBytes h
  rw [hEq, if_false_eq (by intro hc; exact hMis hc.2.2)]

end LeanSwe.ProcessSandbox.Init.Proofs
