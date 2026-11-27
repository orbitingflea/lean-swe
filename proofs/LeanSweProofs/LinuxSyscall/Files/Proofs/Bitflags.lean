import LeanSweProofs.LinuxSyscall.Files.SpecTests

namespace LeanSwe.LinuxSyscall.Files

open Core (AllPass)

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

private theorem openFlags_mask_acc (f : OpenFlags) :
    f.toBits &&& (3 : UInt32) = match f.access with | .rdonly => 0 | .wronly => 1 | .rdwr => 2 := by
  unfold OpenFlags.toBits
  dsimp only
  repeat rw [ui32_or_and_distrib]
  rw [ui32_bit_and_mask f.creat 2 3 (by decide),
    ui32_bit_and_mask f.excl 3 3 (by decide),
    ui32_bit_and_mask f.trunc 4 3 (by decide),
    ui32_bit_and_mask f.append 5 3 (by decide),
    ui32_bit_and_mask f.nofollow 6 3 (by decide),
    ui32_bit_and_mask f.directory 7 3 (by decide),
    ui32_bit_and_mask f.nonblock 8 3 (by decide),
    ui32_bit_and_mask f.cloexec 9 3 (by decide),
    ui32_bit_and_mask f.noctty 10 3 (by decide),
    ui32_bit_and_mask f.path 11 3 (by decide)]
  simp only [ui32_or_zero]
  cases f.access <;> decide

private theorem openFlags_extract_bit2 (f : OpenFlags) :
    f.toBits &&& ((1 : UInt32) <<< 2) = if f.creat then (1 : UInt32) <<< 2 else 0 := by
  unfold OpenFlags.toBits
  dsimp only
  repeat rw [ui32_or_and_distrib]
  rw [ui32_bit_and_self f.creat 2 (by decide),
    ui32_bit_and_mask f.excl 3 _ (by decide),
    ui32_bit_and_mask f.trunc 4 _ (by decide),
    ui32_bit_and_mask f.append 5 _ (by decide),
    ui32_bit_and_mask f.nofollow 6 _ (by decide),
    ui32_bit_and_mask f.directory 7 _ (by decide),
    ui32_bit_and_mask f.nonblock 8 _ (by decide),
    ui32_bit_and_mask f.cloexec 9 _ (by decide),
    ui32_bit_and_mask f.noctty 10 _ (by decide),
    ui32_bit_and_mask f.path 11 _ (by decide)]
  cases f.access <;>
    simp only [show (0 : UInt32) &&& ((1 : UInt32) <<< 2) = 0 by decide,
      show (1 : UInt32) &&& ((1 : UInt32) <<< 2) = 0 by decide,
      show (2 : UInt32) &&& ((1 : UInt32) <<< 2) = 0 by decide,
      ui32_zero_or, ui32_or_zero]

private theorem openFlags_extract_bit3 (f : OpenFlags) :
    f.toBits &&& ((1 : UInt32) <<< 3) = if f.excl then (1 : UInt32) <<< 3 else 0 := by
  unfold OpenFlags.toBits
  dsimp only
  repeat rw [ui32_or_and_distrib]
  rw [ui32_bit_and_mask f.creat 2 _ (by decide),
    ui32_bit_and_self f.excl 3 (by decide),
    ui32_bit_and_mask f.trunc 4 _ (by decide),
    ui32_bit_and_mask f.append 5 _ (by decide),
    ui32_bit_and_mask f.nofollow 6 _ (by decide),
    ui32_bit_and_mask f.directory 7 _ (by decide),
    ui32_bit_and_mask f.nonblock 8 _ (by decide),
    ui32_bit_and_mask f.cloexec 9 _ (by decide),
    ui32_bit_and_mask f.noctty 10 _ (by decide),
    ui32_bit_and_mask f.path 11 _ (by decide)]
  cases f.access <;>
    simp only [show (0 : UInt32) &&& ((1 : UInt32) <<< 3) = 0 by decide,
      show (1 : UInt32) &&& ((1 : UInt32) <<< 3) = 0 by decide,
      show (2 : UInt32) &&& ((1 : UInt32) <<< 3) = 0 by decide,
      ui32_zero_or, ui32_or_zero]

private theorem openFlags_extract_bit4 (f : OpenFlags) :
    f.toBits &&& ((1 : UInt32) <<< 4) = if f.trunc then (1 : UInt32) <<< 4 else 0 := by
  unfold OpenFlags.toBits
  dsimp only
  repeat rw [ui32_or_and_distrib]
  rw [ui32_bit_and_mask f.creat 2 _ (by decide),
    ui32_bit_and_mask f.excl 3 _ (by decide),
    ui32_bit_and_self f.trunc 4 (by decide),
    ui32_bit_and_mask f.append 5 _ (by decide),
    ui32_bit_and_mask f.nofollow 6 _ (by decide),
    ui32_bit_and_mask f.directory 7 _ (by decide),
    ui32_bit_and_mask f.nonblock 8 _ (by decide),
    ui32_bit_and_mask f.cloexec 9 _ (by decide),
    ui32_bit_and_mask f.noctty 10 _ (by decide),
    ui32_bit_and_mask f.path 11 _ (by decide)]
  cases f.access <;>
    simp only [show (0 : UInt32) &&& ((1 : UInt32) <<< 4) = 0 by decide,
      show (1 : UInt32) &&& ((1 : UInt32) <<< 4) = 0 by decide,
      show (2 : UInt32) &&& ((1 : UInt32) <<< 4) = 0 by decide,
      ui32_zero_or, ui32_or_zero]

private theorem openFlags_extract_bit5 (f : OpenFlags) :
    f.toBits &&& ((1 : UInt32) <<< 5) = if f.append then (1 : UInt32) <<< 5 else 0 := by
  unfold OpenFlags.toBits
  dsimp only
  repeat rw [ui32_or_and_distrib]
  rw [ui32_bit_and_mask f.creat 2 _ (by decide),
    ui32_bit_and_mask f.excl 3 _ (by decide),
    ui32_bit_and_mask f.trunc 4 _ (by decide),
    ui32_bit_and_self f.append 5 (by decide),
    ui32_bit_and_mask f.nofollow 6 _ (by decide),
    ui32_bit_and_mask f.directory 7 _ (by decide),
    ui32_bit_and_mask f.nonblock 8 _ (by decide),
    ui32_bit_and_mask f.cloexec 9 _ (by decide),
    ui32_bit_and_mask f.noctty 10 _ (by decide),
    ui32_bit_and_mask f.path 11 _ (by decide)]
  cases f.access <;>
    simp only [show (0 : UInt32) &&& ((1 : UInt32) <<< 5) = 0 by decide,
      show (1 : UInt32) &&& ((1 : UInt32) <<< 5) = 0 by decide,
      show (2 : UInt32) &&& ((1 : UInt32) <<< 5) = 0 by decide,
      ui32_zero_or, ui32_or_zero]

private theorem openFlags_extract_bit6 (f : OpenFlags) :
    f.toBits &&& ((1 : UInt32) <<< 6) = if f.nofollow then (1 : UInt32) <<< 6 else 0 := by
  unfold OpenFlags.toBits
  dsimp only
  repeat rw [ui32_or_and_distrib]
  rw [ui32_bit_and_mask f.creat 2 _ (by decide),
    ui32_bit_and_mask f.excl 3 _ (by decide),
    ui32_bit_and_mask f.trunc 4 _ (by decide),
    ui32_bit_and_mask f.append 5 _ (by decide),
    ui32_bit_and_self f.nofollow 6 (by decide),
    ui32_bit_and_mask f.directory 7 _ (by decide),
    ui32_bit_and_mask f.nonblock 8 _ (by decide),
    ui32_bit_and_mask f.cloexec 9 _ (by decide),
    ui32_bit_and_mask f.noctty 10 _ (by decide),
    ui32_bit_and_mask f.path 11 _ (by decide)]
  cases f.access <;>
    simp only [show (0 : UInt32) &&& ((1 : UInt32) <<< 6) = 0 by decide,
      show (1 : UInt32) &&& ((1 : UInt32) <<< 6) = 0 by decide,
      show (2 : UInt32) &&& ((1 : UInt32) <<< 6) = 0 by decide,
      ui32_zero_or, ui32_or_zero]

private theorem openFlags_extract_bit7 (f : OpenFlags) :
    f.toBits &&& ((1 : UInt32) <<< 7) = if f.directory then (1 : UInt32) <<< 7 else 0 := by
  unfold OpenFlags.toBits
  dsimp only
  repeat rw [ui32_or_and_distrib]
  rw [ui32_bit_and_mask f.creat 2 _ (by decide),
    ui32_bit_and_mask f.excl 3 _ (by decide),
    ui32_bit_and_mask f.trunc 4 _ (by decide),
    ui32_bit_and_mask f.append 5 _ (by decide),
    ui32_bit_and_mask f.nofollow 6 _ (by decide),
    ui32_bit_and_self f.directory 7 (by decide),
    ui32_bit_and_mask f.nonblock 8 _ (by decide),
    ui32_bit_and_mask f.cloexec 9 _ (by decide),
    ui32_bit_and_mask f.noctty 10 _ (by decide),
    ui32_bit_and_mask f.path 11 _ (by decide)]
  cases f.access <;>
    simp only [show (0 : UInt32) &&& ((1 : UInt32) <<< 7) = 0 by decide,
      show (1 : UInt32) &&& ((1 : UInt32) <<< 7) = 0 by decide,
      show (2 : UInt32) &&& ((1 : UInt32) <<< 7) = 0 by decide,
      ui32_zero_or, ui32_or_zero]

private theorem openFlags_extract_bit8 (f : OpenFlags) :
    f.toBits &&& ((1 : UInt32) <<< 8) = if f.nonblock then (1 : UInt32) <<< 8 else 0 := by
  unfold OpenFlags.toBits
  dsimp only
  repeat rw [ui32_or_and_distrib]
  rw [ui32_bit_and_mask f.creat 2 _ (by decide),
    ui32_bit_and_mask f.excl 3 _ (by decide),
    ui32_bit_and_mask f.trunc 4 _ (by decide),
    ui32_bit_and_mask f.append 5 _ (by decide),
    ui32_bit_and_mask f.nofollow 6 _ (by decide),
    ui32_bit_and_mask f.directory 7 _ (by decide),
    ui32_bit_and_self f.nonblock 8 (by decide),
    ui32_bit_and_mask f.cloexec 9 _ (by decide),
    ui32_bit_and_mask f.noctty 10 _ (by decide),
    ui32_bit_and_mask f.path 11 _ (by decide)]
  cases f.access <;>
    simp only [show (0 : UInt32) &&& ((1 : UInt32) <<< 8) = 0 by decide,
      show (1 : UInt32) &&& ((1 : UInt32) <<< 8) = 0 by decide,
      show (2 : UInt32) &&& ((1 : UInt32) <<< 8) = 0 by decide,
      ui32_zero_or, ui32_or_zero]

private theorem openFlags_extract_bit9 (f : OpenFlags) :
    f.toBits &&& ((1 : UInt32) <<< 9) = if f.cloexec then (1 : UInt32) <<< 9 else 0 := by
  unfold OpenFlags.toBits
  dsimp only
  repeat rw [ui32_or_and_distrib]
  rw [ui32_bit_and_mask f.creat 2 _ (by decide),
    ui32_bit_and_mask f.excl 3 _ (by decide),
    ui32_bit_and_mask f.trunc 4 _ (by decide),
    ui32_bit_and_mask f.append 5 _ (by decide),
    ui32_bit_and_mask f.nofollow 6 _ (by decide),
    ui32_bit_and_mask f.directory 7 _ (by decide),
    ui32_bit_and_mask f.nonblock 8 _ (by decide),
    ui32_bit_and_self f.cloexec 9 (by decide),
    ui32_bit_and_mask f.noctty 10 _ (by decide),
    ui32_bit_and_mask f.path 11 _ (by decide)]
  cases f.access <;>
    simp only [show (0 : UInt32) &&& ((1 : UInt32) <<< 9) = 0 by decide,
      show (1 : UInt32) &&& ((1 : UInt32) <<< 9) = 0 by decide,
      show (2 : UInt32) &&& ((1 : UInt32) <<< 9) = 0 by decide,
      ui32_zero_or, ui32_or_zero]

private theorem openFlags_extract_bit10 (f : OpenFlags) :
    f.toBits &&& ((1 : UInt32) <<< 10) = if f.noctty then (1 : UInt32) <<< 10 else 0 := by
  unfold OpenFlags.toBits
  dsimp only
  repeat rw [ui32_or_and_distrib]
  rw [ui32_bit_and_mask f.creat 2 _ (by decide),
    ui32_bit_and_mask f.excl 3 _ (by decide),
    ui32_bit_and_mask f.trunc 4 _ (by decide),
    ui32_bit_and_mask f.append 5 _ (by decide),
    ui32_bit_and_mask f.nofollow 6 _ (by decide),
    ui32_bit_and_mask f.directory 7 _ (by decide),
    ui32_bit_and_mask f.nonblock 8 _ (by decide),
    ui32_bit_and_mask f.cloexec 9 _ (by decide),
    ui32_bit_and_self f.noctty 10 (by decide),
    ui32_bit_and_mask f.path 11 _ (by decide)]
  cases f.access <;>
    simp only [show (0 : UInt32) &&& ((1 : UInt32) <<< 10) = 0 by decide,
      show (1 : UInt32) &&& ((1 : UInt32) <<< 10) = 0 by decide,
      show (2 : UInt32) &&& ((1 : UInt32) <<< 10) = 0 by decide,
      ui32_zero_or, ui32_or_zero]

private theorem openFlags_extract_bit11 (f : OpenFlags) :
    f.toBits &&& ((1 : UInt32) <<< 11) = if f.path then (1 : UInt32) <<< 11 else 0 := by
  unfold OpenFlags.toBits
  dsimp only
  repeat rw [ui32_or_and_distrib]
  rw [ui32_bit_and_mask f.creat 2 _ (by decide),
    ui32_bit_and_mask f.excl 3 _ (by decide),
    ui32_bit_and_mask f.trunc 4 _ (by decide),
    ui32_bit_and_mask f.append 5 _ (by decide),
    ui32_bit_and_mask f.nofollow 6 _ (by decide),
    ui32_bit_and_mask f.directory 7 _ (by decide),
    ui32_bit_and_mask f.nonblock 8 _ (by decide),
    ui32_bit_and_mask f.cloexec 9 _ (by decide),
    ui32_bit_and_mask f.noctty 10 _ (by decide),
    ui32_bit_and_self f.path 11 (by decide)]
  cases f.access <;>
    simp only [show (0 : UInt32) &&& ((1 : UInt32) <<< 11) = 0 by decide,
      show (1 : UInt32) &&& ((1 : UInt32) <<< 11) = 0 by decide,
      show (2 : UInt32) &&& ((1 : UInt32) <<< 11) = 0 by decide,
      ui32_zero_or, ui32_or_zero]

private theorem openFlags_toBits_inj {f1 f2 : OpenFlags} (h : f1.toBits = f2.toBits) : f1 = f2 := by
  have hAcc : f1.access = f2.access := by
    have hm := congrArg (· &&& (3 : UInt32)) h
    rw [openFlags_mask_acc, openFlags_mask_acc] at hm
    cases h1 : f1.access <;> cases h2 : f2.access <;>
      first | rfl | (rw [h1, h2] at hm; exact absurd hm (by decide))
  have hc : f1.creat = f2.creat := bool_of_ui32_bit_eq (shift := 2) (by decide) (by
    have hm := congrArg (· &&& ((1 : UInt32) <<< 2)) h
    rwa [openFlags_extract_bit2, openFlags_extract_bit2] at hm)
  have he : f1.excl = f2.excl := bool_of_ui32_bit_eq (shift := 3) (by decide) (by
    have hm := congrArg (· &&& ((1 : UInt32) <<< 3)) h
    rwa [openFlags_extract_bit3, openFlags_extract_bit3] at hm)
  have ht : f1.trunc = f2.trunc := bool_of_ui32_bit_eq (shift := 4) (by decide) (by
    have hm := congrArg (· &&& ((1 : UInt32) <<< 4)) h
    rwa [openFlags_extract_bit4, openFlags_extract_bit4] at hm)
  have hap : f1.append = f2.append := bool_of_ui32_bit_eq (shift := 5) (by decide) (by
    have hm := congrArg (· &&& ((1 : UInt32) <<< 5)) h
    rwa [openFlags_extract_bit5, openFlags_extract_bit5] at hm)
  have hnf : f1.nofollow = f2.nofollow := bool_of_ui32_bit_eq (shift := 6) (by decide) (by
    have hm := congrArg (· &&& ((1 : UInt32) <<< 6)) h
    rwa [openFlags_extract_bit6, openFlags_extract_bit6] at hm)
  have hd : f1.directory = f2.directory := bool_of_ui32_bit_eq (shift := 7) (by decide) (by
    have hm := congrArg (· &&& ((1 : UInt32) <<< 7)) h
    rwa [openFlags_extract_bit7, openFlags_extract_bit7] at hm)
  have hnb : f1.nonblock = f2.nonblock := bool_of_ui32_bit_eq (shift := 8) (by decide) (by
    have hm := congrArg (· &&& ((1 : UInt32) <<< 8)) h
    rwa [openFlags_extract_bit8, openFlags_extract_bit8] at hm)
  have hcl : f1.cloexec = f2.cloexec := bool_of_ui32_bit_eq (shift := 9) (by decide) (by
    have hm := congrArg (· &&& ((1 : UInt32) <<< 9)) h
    rwa [openFlags_extract_bit9, openFlags_extract_bit9] at hm)
  have hnc : f1.noctty = f2.noctty := bool_of_ui32_bit_eq (shift := 10) (by decide) (by
    have hm := congrArg (· &&& ((1 : UInt32) <<< 10)) h
    rwa [openFlags_extract_bit10, openFlags_extract_bit10] at hm)
  have hpt : f1.path = f2.path := bool_of_ui32_bit_eq (shift := 11) (by decide) (by
    have hm := congrArg (· &&& ((1 : UInt32) <<< 11)) h
    rwa [openFlags_extract_bit11, openFlags_extract_bit11] at hm)
  cases f1; cases f2; simp only at hAcc hc he ht hap hnf hd hnb hcl hnc hpt
  subst hAcc hc he ht hap hnf hd hnb hcl hnc hpt
  rfl

private theorem ui64_or_and_distrib (x y m : UInt64) :
    (x ||| y) &&& m = (x &&& m) ||| (y &&& m) := by
  apply UInt64.toNat_inj.mp
  rw [UInt64.toNat_and, UInt64.toNat_or, UInt64.toNat_or, UInt64.toNat_and, UInt64.toNat_and]
  exact Nat.and_or_distrib_right x.toNat y.toNat m.toNat

private theorem ui64_bit_and_mask (b : Bool) (shift mask : UInt64)
    (h0 : ((1 : UInt64) <<< shift) &&& mask = 0) :
    (if b then (1 : UInt64) <<< shift else 0) &&& mask = 0 := by
  cases b
  · simp
  · exact h0

private theorem ui64_bit_and_self (b : Bool) (shift : UInt64)
    (h1 : ((1 : UInt64) <<< shift) &&& ((1 : UInt64) <<< shift) = (1 : UInt64) <<< shift) :
    (if b then (1 : UInt64) <<< shift else 0) &&& ((1 : UInt64) <<< shift) =
      if b then (1 : UInt64) <<< shift else 0 := by
  cases b
  · simp
  · exact h1

private theorem ui64_or_zero (x : UInt64) : x ||| 0 = x := by
  apply UInt64.toNat_inj.mp
  simp

private theorem ui64_zero_or (x : UInt64) : 0 ||| x = x := by
  apply UInt64.toNat_inj.mp
  simp

private theorem bool_of_ui64_bit_eq {b1 b2 : Bool} {shift : UInt64}
    (hne : ((1 : UInt64) <<< shift) ≠ 0)
    (h : (if b1 then (1 : UInt64) <<< shift else 0) =
         (if b2 then (1 : UInt64) <<< shift else 0)) : b1 = b2 := by
  cases b1 <;> cases b2
  · rfl
  · exact absurd h.symm hne
  · exact absurd h hne
  · rfl

private theorem resolveFlags_toBits_inj {r1 r2 : ResolveFlags} (h : r1.toBits = r2.toBits) : r1 = r2 := by
  have ex0 (r : ResolveFlags) : r.toBits &&& ((1 : UInt64) <<< 0) = if r.noXdev then (1 : UInt64) <<< 0 else 0 := by
    unfold ResolveFlags.toBits; dsimp only; repeat rw [ui64_or_and_distrib]
    rw [ui64_bit_and_self r.noXdev 0 (by decide),
      ui64_bit_and_mask r.noMagiclinks 1 _ (by decide),
      ui64_bit_and_mask r.noSymlinks 2 _ (by decide),
      ui64_bit_and_mask r.beneath 3 _ (by decide),
      ui64_bit_and_mask r.inRoot 4 _ (by decide),
      ui64_bit_and_mask r.cached 5 _ (by decide)]
    simp only [ui64_or_zero]
  have ex1 (r : ResolveFlags) : r.toBits &&& ((1 : UInt64) <<< 1) = if r.noMagiclinks then (1 : UInt64) <<< 1 else 0 := by
    unfold ResolveFlags.toBits; dsimp only; repeat rw [ui64_or_and_distrib]
    rw [ui64_bit_and_mask r.noXdev 0 _ (by decide),
      ui64_bit_and_self r.noMagiclinks 1 (by decide),
      ui64_bit_and_mask r.noSymlinks 2 _ (by decide),
      ui64_bit_and_mask r.beneath 3 _ (by decide),
      ui64_bit_and_mask r.inRoot 4 _ (by decide),
      ui64_bit_and_mask r.cached 5 _ (by decide)]
    simp only [ui64_zero_or, ui64_or_zero]
  have ex2 (r : ResolveFlags) : r.toBits &&& ((1 : UInt64) <<< 2) = if r.noSymlinks then (1 : UInt64) <<< 2 else 0 := by
    unfold ResolveFlags.toBits; dsimp only; repeat rw [ui64_or_and_distrib]
    rw [ui64_bit_and_mask r.noXdev 0 _ (by decide),
      ui64_bit_and_mask r.noMagiclinks 1 _ (by decide),
      ui64_bit_and_self r.noSymlinks 2 (by decide),
      ui64_bit_and_mask r.beneath 3 _ (by decide),
      ui64_bit_and_mask r.inRoot 4 _ (by decide),
      ui64_bit_and_mask r.cached 5 _ (by decide)]
    simp only [ui64_zero_or, ui64_or_zero]
  have ex3 (r : ResolveFlags) : r.toBits &&& ((1 : UInt64) <<< 3) = if r.beneath then (1 : UInt64) <<< 3 else 0 := by
    unfold ResolveFlags.toBits; dsimp only; repeat rw [ui64_or_and_distrib]
    rw [ui64_bit_and_mask r.noXdev 0 _ (by decide),
      ui64_bit_and_mask r.noMagiclinks 1 _ (by decide),
      ui64_bit_and_mask r.noSymlinks 2 _ (by decide),
      ui64_bit_and_self r.beneath 3 (by decide),
      ui64_bit_and_mask r.inRoot 4 _ (by decide),
      ui64_bit_and_mask r.cached 5 _ (by decide)]
    simp only [ui64_zero_or, ui64_or_zero]
  have ex4 (r : ResolveFlags) : r.toBits &&& ((1 : UInt64) <<< 4) = if r.inRoot then (1 : UInt64) <<< 4 else 0 := by
    unfold ResolveFlags.toBits; dsimp only; repeat rw [ui64_or_and_distrib]
    rw [ui64_bit_and_mask r.noXdev 0 _ (by decide),
      ui64_bit_and_mask r.noMagiclinks 1 _ (by decide),
      ui64_bit_and_mask r.noSymlinks 2 _ (by decide),
      ui64_bit_and_mask r.beneath 3 _ (by decide),
      ui64_bit_and_self r.inRoot 4 (by decide),
      ui64_bit_and_mask r.cached 5 _ (by decide)]
    simp only [ui64_zero_or, ui64_or_zero]
  have ex5 (r : ResolveFlags) : r.toBits &&& ((1 : UInt64) <<< 5) = if r.cached then (1 : UInt64) <<< 5 else 0 := by
    unfold ResolveFlags.toBits; dsimp only; repeat rw [ui64_or_and_distrib]
    rw [ui64_bit_and_mask r.noXdev 0 _ (by decide),
      ui64_bit_and_mask r.noMagiclinks 1 _ (by decide),
      ui64_bit_and_mask r.noSymlinks 2 _ (by decide),
      ui64_bit_and_mask r.beneath 3 _ (by decide),
      ui64_bit_and_mask r.inRoot 4 _ (by decide),
      ui64_bit_and_self r.cached 5 (by decide)]
    simp only [ui64_zero_or, ui64_or_zero]
  have h0 : r1.noXdev = r2.noXdev := bool_of_ui64_bit_eq (shift := 0) (by decide) (by have hm := congrArg (· &&& ((1 : UInt64) <<< 0)) h; rwa [ex0, ex0] at hm)
  have h1 : r1.noMagiclinks = r2.noMagiclinks := bool_of_ui64_bit_eq (shift := 1) (by decide) (by have hm := congrArg (· &&& ((1 : UInt64) <<< 1)) h; rwa [ex1, ex1] at hm)
  have h2 : r1.noSymlinks = r2.noSymlinks := bool_of_ui64_bit_eq (shift := 2) (by decide) (by have hm := congrArg (· &&& ((1 : UInt64) <<< 2)) h; rwa [ex2, ex2] at hm)
  have h3 : r1.beneath = r2.beneath := bool_of_ui64_bit_eq (shift := 3) (by decide) (by have hm := congrArg (· &&& ((1 : UInt64) <<< 3)) h; rwa [ex3, ex3] at hm)
  have h4 : r1.inRoot = r2.inRoot := bool_of_ui64_bit_eq (shift := 4) (by decide) (by have hm := congrArg (· &&& ((1 : UInt64) <<< 4)) h; rwa [ex4, ex4] at hm)
  have h5 : r1.cached = r2.cached := bool_of_ui64_bit_eq (shift := 5) (by decide) (by have hm := congrArg (· &&& ((1 : UInt64) <<< 5)) h; rwa [ex5, ex5] at hm)
  cases r1; cases r2
  subst h0; subst h1; subst h2; subst h3; subst h4; subst h5
  rfl

private theorem bool_beq_eq_of_inj {α β : Type} [BEq α] [DecidableEq α]
    (hBeq : ∀ x y : α, (x == y) = decide (x = y))
    (f : α → β) [BEq β] [LawfulBEq β]
    (hinj : ∀ x y : α, f x = f y → x = y) (x y : α) : (f x == f y) = (x == y) := by
  rw [hBeq x y]
  by_cases h : x = y
  · subst h; simp
  · have hne : f x ≠ f y := fun hfe => h (hinj x y hfe)
    simp [h, hne]

private theorem bool_beq_eq_decide (a b : Bool) : (a == b) = decide (a = b) := by
  cases a <;> cases b <;> rfl

private theorem accessMode_beq_eq_decide (a b : AccessMode) : (a == b) = decide (a = b) := by
  cases a <;> cases b <;> rfl

private theorem openFlags_beq_eq_decide (x y : OpenFlags) : (x == y) = decide (x = y) := by
  cases x with | mk a1 c1 e1 t1 ap1 nf1 d1 nb1 cl1 nc1 pt1 =>
  cases y with | mk a2 c2 e2 t2 ap2 nf2 d2 nb2 cl2 nc2 pt2 =>
  change ((a1 == a2) && ((c1 == c2) && ((e1 == e2) && ((t1 == t2) &&
    ((ap1 == ap2) && ((nf1 == nf2) && ((d1 == d2) && ((nb1 == nb2) &&
      ((cl1 == cl2) && ((nc1 == nc2) && (pt1 == pt2))))))))))) =
    decide (OpenFlags.mk a1 c1 e1 t1 ap1 nf1 d1 nb1 cl1 nc1 pt1 =
            OpenFlags.mk a2 c2 e2 t2 ap2 nf2 d2 nb2 cl2 nc2 pt2)
  simp [bool_beq_eq_decide, accessMode_beq_eq_decide]

private theorem resolveFlags_beq_eq_decide (x y : ResolveFlags) : (x == y) = decide (x = y) := by
  cases x with | mk a1 b1 c1 d1 e1 f1 =>
  cases y with | mk a2 b2 c2 d2 e2 f2 =>
  change ((a1 == a2) && ((b1 == b2) && ((c1 == c2) && ((d1 == d2) && ((e1 == e2) && (f1 == f2)))))) =
    decide (ResolveFlags.mk a1 b1 c1 d1 e1 f1 = ResolveFlags.mk a2 b2 c2 d2 e2 f2)
  simp [bool_beq_eq_decide]

private theorem atFlags_beq_eq_decide (x y : AtFlags) : (x == y) = decide (x = y) := by
  cases x with | mk a1 b1 c1 =>
  cases y with | mk a2 b2 c2 =>
  change ((a1 == a2) && ((b1 == b2) && (c1 == c2))) =
    decide (AtFlags.mk a1 b1 c1 = AtFlags.mk a2 b2 c2)
  simp [bool_beq_eq_decide]

private theorem accessModeMask_beq_eq_decide (x y : AccessModeMask) : (x == y) = decide (x = y) := by
  cases x with | mk a1 b1 c1 =>
  cases y with | mk a2 b2 c2 =>
  change ((a1 == a2) && ((b1 == b2) && (c1 == c2))) =
    decide (AccessModeMask.mk a1 b1 c1 = AccessModeMask.mk a2 b2 c2)
  simp [bool_beq_eq_decide]

private theorem renameFlags_beq_eq_decide (x y : RenameFlags) : (x == y) = decide (x = y) := by
  cases x with | mk a1 b1 c1 =>
  cases y with | mk a2 b2 c2 =>
  change ((a1 == a2) && ((b1 == b2) && (c1 == c2))) =
    decide (RenameFlags.mk a1 b1 c1 = RenameFlags.mk a2 b2 c2)
  simp [bool_beq_eq_decide]

private theorem flockOp_beq_eq_decide (x y : FlockOp) : (x == y) = decide (x = y) := by
  cases x with
  | shared b1 => cases b1 <;> cases y with
    | shared b2 => cases b2 <;> rfl
    | exclusive b2 => cases b2 <;> rfl
    | unlock => rfl
  | exclusive b1 => cases b1 <;> cases y with
    | shared b2 => cases b2 <;> rfl
    | exclusive b2 => cases b2 <;> rfl
    | unlock => rfl
  | unlock => cases y with
    | shared b2 => cases b2 <;> rfl
    | exclusive b2 => cases b2 <;> rfl
    | unlock => rfl

private theorem fcntlCmd_beq_eq_decide (x y : FcntlCmd) : (x == y) = decide (x = y) := by
  cases x with
  | getFl => cases y with
    | getFl => rfl
    | setFl a b => cases a <;> cases b <;> rfl
    | getFd => rfl
    | setFd a => cases a <;> rfl
    | addSeals _ => rfl
    | getSeals => rfl
  | setFl a1 b1 => cases a1 <;> cases b1 <;> cases y with
    | getFl => rfl
    | setFl a2 b2 => cases a2 <;> cases b2 <;> rfl
    | getFd => rfl
    | setFd a => cases a <;> rfl
    | addSeals _ => rfl
    | getSeals => rfl
  | getFd => cases y with
    | getFl => rfl
    | setFl a b => cases a <;> cases b <;> rfl
    | getFd => rfl
    | setFd a => cases a <;> rfl
    | addSeals _ => rfl
    | getSeals => rfl
  | setFd a1 => cases a1 <;> cases y with
    | getFl => rfl
    | setFl a b => cases a <;> cases b <;> rfl
    | getFd => rfl
    | setFd a2 => cases a2 <;> rfl
    | addSeals _ => rfl
    | getSeals => rfl
  | addSeals s1 => cases y with
    | getFl => rfl
    | setFl a b => cases a <;> cases b <;> rfl
    | getFd => rfl
    | setFd a => cases a <;> rfl
    | addSeals s2 =>
      change (s1 == s2) = decide (FcntlCmd.addSeals s1 = FcntlCmd.addSeals s2)
      by_cases h : s1 = s2
      · subst h; simp
      · simp [h]
    | getSeals => rfl
  | getSeals => cases y with
    | getFl => rfl
    | setFl a b => cases a <;> cases b <;> rfl
    | getFd => rfl
    | setFd a => cases a <;> rfl
    | addSeals _ => rfl
    | getSeals => rfl

private theorem atFlags_toBits_inj (x y : AtFlags) (h : x.toBits = y.toBits) : x = y := by
  cases x with | mk x1 x2 x3 =>
  cases y with | mk y1 y2 y3 =>
  cases x1 <;> cases x2 <;> cases x3 <;> cases y1 <;> cases y2 <;> cases y3 <;>
    first | rfl | exact absurd h (by decide)

private theorem accessModeMask_toBits_inj (x y : AccessModeMask) (h : x.toBits = y.toBits) : x = y := by
  cases x with | mk x1 x2 x3 =>
  cases y with | mk y1 y2 y3 =>
  cases x1 <;> cases x2 <;> cases x3 <;> cases y1 <;> cases y2 <;> cases y3 <;>
    first | rfl | exact absurd h (by decide)

private theorem renameFlags_toBits_inj (x y : RenameFlags) (h : x.toBits = y.toBits) : x = y := by
  cases x with | mk x1 x2 x3 =>
  cases y with | mk y1 y2 y3 =>
  cases x1 <;> cases x2 <;> cases x3 <;> cases y1 <;> cases y2 <;> cases y3 <;>
    first | rfl | exact absurd h (by decide)

private theorem flockOp_toBits_inj (x y : FlockOp) (h : x.toBits = y.toBits) : x = y := by
  cases x with
  | shared b1 => cases b1 <;> (cases y with
    | shared b2 => cases b2 <;> first | rfl | exact absurd h (by decide)
    | exclusive b2 => cases b2 <;> exact absurd h (by decide)
    | unlock => exact absurd h (by decide))
  | exclusive b1 => cases b1 <;> (cases y with
    | shared b2 => cases b2 <;> exact absurd h (by decide)
    | exclusive b2 => cases b2 <;> first | rfl | exact absurd h (by decide)
    | unlock => exact absurd h (by decide))
  | unlock => cases y with
    | shared b2 => cases b2 <;> exact absurd h (by decide)
    | exclusive b2 => cases b2 <;> exact absurd h (by decide)
    | unlock => rfl

private theorem fcntlCmd_toRaw_inj (x y : FcntlCmd) (h : x.toRaw = y.toRaw) : x = y := by
  cases x with
  | getFl => cases y with
    | getFl => rfl
    | setFl a b => cases a <;> cases b <;> exact absurd h (by decide)
    | getFd => exact absurd h (by decide)
    | setFd a => cases a <;> exact absurd h (by decide)
    | addSeals _ => simp [FcntlCmd.toRaw] at h
    | getSeals => exact absurd h (by decide)
  | setFl a1 b1 => cases a1 <;> cases b1 <;> (cases y with
    | getFl => exact absurd h (by decide)
    | setFl a2 b2 => cases a2 <;> cases b2 <;> first | rfl | exact absurd h (by decide)
    | getFd => exact absurd h (by decide)
    | setFd a2 => cases a2 <;> exact absurd h (by decide)
    | addSeals _ => simp [FcntlCmd.toRaw] at h
    | getSeals => exact absurd h (by decide))
  | getFd => cases y with
    | getFl => exact absurd h (by decide)
    | setFl a b => cases a <;> cases b <;> exact absurd h (by decide)
    | getFd => rfl
    | setFd a => cases a <;> exact absurd h (by decide)
    | addSeals _ => simp [FcntlCmd.toRaw] at h
    | getSeals => exact absurd h (by decide)
  | setFd a1 => cases a1 <;> (cases y with
    | getFl => exact absurd h (by decide)
    | setFl a b => cases a <;> cases b <;> exact absurd h (by decide)
    | getFd => exact absurd h (by decide)
    | setFd a2 => cases a2 <;> first | rfl | exact absurd h (by decide)
    | addSeals _ => simp [FcntlCmd.toRaw] at h
    | getSeals => exact absurd h (by decide))
  | addSeals s1 => cases y with
    | getFl => simp [FcntlCmd.toRaw] at h
    | setFl a b => cases a <;> cases b <;> simp [FcntlCmd.toRaw] at h
    | getFd => simp [FcntlCmd.toRaw] at h
    | setFd a => cases a <;> simp [FcntlCmd.toRaw] at h
    | addSeals s2 => simp [FcntlCmd.toRaw] at h; subst h; rfl
    | getSeals => simp [FcntlCmd.toRaw] at h
  | getSeals => cases y with
    | getFl => exact absurd h (by decide)
    | setFl a b => cases a <;> cases b <;> exact absurd h (by decide)
    | getFd => exact absurd h (by decide)
    | setFd a => cases a <;> exact absurd h (by decide)
    | addSeals _ => simp [FcntlCmd.toRaw] at h
    | getSeals => rfl

private theorem seekWhence_beq_eq_decide (x y : SeekWhence) : (x == y) = decide (x = y) := by
  cases x <;> cases y <;> rfl

private theorem seekWhence_toRaw_inj (x y : SeekWhence) (h : x.toRaw = y.toRaw) : x = y := by
  cases x <;> cases y <;> first | rfl | exact absurd h (by decide)

private theorem stdioFd_beq_eq_decide (x y : StdioFd) : (x == y) = decide (x = y) := by
  cases x <;> cases y <;> rfl

private theorem stdioFd_toRaw_inj (x y : StdioFd) (h : x.toRaw = y.toRaw) : x = y := by
  cases x <;> cases y <;> first | rfl | exact absurd h (by decide)

/-- Proof helper for `files_flags_encodersInjective_allPass`. -/
theorem files_flags_encodersInjective_proof :
    AllPass (test_files_flags_encodersInjective OpenFlags.toBits ResolveFlags.toBits
      AtFlags.toBits AccessModeMask.toBits RenameFlags.toBits FlockOp.toBits FcntlCmd.toRaw
      SeekWhence.toRaw StdioFd.toRaw) := by
  intro o1 o2
  refine ⟨bool_beq_eq_of_inj openFlags_beq_eq_decide OpenFlags.toBits (fun _ _ => openFlags_toBits_inj) o1 o2, ?_⟩
  intro r1 r2
  refine ⟨bool_beq_eq_of_inj resolveFlags_beq_eq_decide ResolveFlags.toBits (fun _ _ => resolveFlags_toBits_inj) r1 r2, ?_⟩
  intro a1 a2
  refine ⟨bool_beq_eq_of_inj atFlags_beq_eq_decide AtFlags.toBits atFlags_toBits_inj a1 a2, ?_⟩
  intro m1 m2
  refine ⟨bool_beq_eq_of_inj accessModeMask_beq_eq_decide AccessModeMask.toBits accessModeMask_toBits_inj m1 m2, ?_⟩
  intro rn1 rn2
  refine ⟨bool_beq_eq_of_inj renameFlags_beq_eq_decide RenameFlags.toBits renameFlags_toBits_inj rn1 rn2, ?_⟩
  intro fl1 fl2
  refine ⟨bool_beq_eq_of_inj flockOp_beq_eq_decide FlockOp.toBits flockOp_toBits_inj fl1 fl2, ?_⟩
  intro fc1 fc2
  refine ⟨bool_beq_eq_of_inj fcntlCmd_beq_eq_decide FcntlCmd.toRaw fcntlCmd_toRaw_inj fc1 fc2, ?_⟩
  intro w1 w2
  refine ⟨bool_beq_eq_of_inj seekWhence_beq_eq_decide SeekWhence.toRaw seekWhence_toRaw_inj w1 w2, ?_⟩
  intro s1 s2
  refine ⟨bool_beq_eq_of_inj stdioFd_beq_eq_decide StdioFd.toRaw stdioFd_toRaw_inj s1 s2, trivial⟩

end LeanSwe.LinuxSyscall.Files
