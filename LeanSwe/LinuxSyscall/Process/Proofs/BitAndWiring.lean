import LeanSwe.LinuxSyscall.Process.SpecTests
import LeanSwe.LinuxSyscall.Process.Impl

namespace LeanSwe.LinuxSyscall.Process

open Core (NondetTest AllPass CanReach)
open Core.NondetTest
open LeanSwe.LinuxSyscall

private theorem ui64_or_and_distrib (x y m : UInt64) :
    (x ||| y) &&& m = (x &&& m) ||| (y &&& m) := by
  apply UInt64.toNat_inj.mp
  rw [UInt64.toNat_and, UInt64.toNat_or, UInt64.toNat_or, UInt64.toNat_and, UInt64.toNat_and]
  exact Nat.and_or_distrib_right x.toNat y.toNat m.toNat

private theorem ui32_or_and_distrib (x y m : UInt32) :
    (x ||| y) &&& m = (x &&& m) ||| (y &&& m) := by
  apply UInt32.toNat_inj.mp
  rw [UInt32.toNat_and, UInt32.toNat_or, UInt32.toNat_or, UInt32.toNat_and, UInt32.toNat_and]
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
  apply UInt64.toNat_inj.mp; simp

private theorem ui64_zero_or (x : UInt64) : 0 ||| x = x := by
  apply UInt64.toNat_inj.mp; simp

private theorem bool_of_ui64_bit_eq {b1 b2 : Bool} {shift : UInt64}
    (hne : ((1 : UInt64) <<< shift) ≠ 0)
    (h : (if b1 then (1 : UInt64) <<< shift else 0) =
         (if b2 then (1 : UInt64) <<< shift else 0)) : b1 = b2 := by
  cases b1 <;> cases b2
  · rfl
  · exact absurd h.symm hne
  · exact absurd h hne
  · rfl

private theorem ui64_toNat_toUInt32 (x : UInt32) : x.toUInt64.toNat = x.toNat := by
  exact UInt32.toNat_toUInt64 x

private theorem ui64_shift_u32_rshift (k : UInt64) (hk : k.toNat ≤ 6) (x : UInt32) :
    (x.toUInt64 <<< k) >>> k = x.toUInt64 := by
  apply UInt64.toNat_inj.mp
  have hx : x.toNat < 2 ^ 32 := x.toNat_lt
  rw [UInt64.toNat_shiftRight, UInt64.toNat_shiftLeft, ui64_toNat_toUInt32]
  have hkMod : k.toNat % 64 = k.toNat := Nat.mod_eq_of_lt (by omega)
  rw [hkMod, Nat.shiftLeft_eq]
  have hpow : 2 ^ k.toNat ≤ 64 := by
    have hle := Nat.pow_le_pow_right (by decide : 0 < 2) hk
    exact Nat.le_trans hle (by decide : 2 ^ 6 ≤ 64)
  have hle : x.toNat * 2 ^ k.toNat ≤ x.toNat * 64 := Nat.mul_le_mul_left _ hpow
  have hmul : x.toNat * 2 ^ k.toNat < 2 ^ 64 := by omega
  rw [Nat.mod_eq_of_lt hmul, Nat.shiftRight_eq_div_pow, Nat.mul_div_cancel _ (Nat.two_pow_pos k.toNat)]

private theorem ui64_low_rshift_zero (k : UInt64) (hk : 1 ≤ k.toNat ∧ k.toNat ≤ 6) (v : UInt64)
    (hv : v.toNat < 2 ^ k.toNat) :
    v >>> k = 0 := by
  apply UInt64.toNat_inj.mp
  rw [UInt64.toNat_shiftRight]
  have hkMod : k.toNat % 64 = k.toNat := Nat.mod_eq_of_lt (by omega)
  rw [hkMod, Nat.shiftRight_eq_div_pow, Nat.div_eq_of_lt hv]
  rfl

private theorem ui64_or_rshift_distrib (a b s : UInt64) :
    (a ||| b) >>> s = (a >>> s) ||| (b >>> s) := by
  apply UInt64.toNat_inj.mp
  rw [UInt64.toNat_shiftRight, UInt64.toNat_or, UInt64.toNat_or,
    UInt64.toNat_shiftRight, UInt64.toNat_shiftRight]
  apply Nat.eq_of_testBit_eq
  intro i
  simp [Nat.testBit_shiftRight, Nat.testBit_or]

private theorem ui64_bit_rshift_zero (b : Bool) (bitShift k : UInt64)
    (hlt : bitShift.toNat < k.toNat) (hk : 1 ≤ k.toNat ∧ k.toNat ≤ 6) :
    (if b then (1 : UInt64) <<< bitShift else 0) >>> k = 0 := by
  cases b
  · simp
  · change ((1 : UInt64) <<< bitShift) >>> k = 0
    apply ui64_low_rshift_zero k hk
    rw [UInt64.toNat_shiftLeft]
    have hbMod : bitShift.toNat % 64 = bitShift.toNat := Nat.mod_eq_of_lt (by omega)
    have hpowLe : 2 ^ bitShift.toNat ≤ 32 := by
      have hle := Nat.pow_le_pow_right (by decide : 0 < 2) (by omega : bitShift.toNat ≤ 5)
      exact Nat.le_trans hle (by decide : 2 ^ 5 ≤ 32)
    have h1sh : ((1 : UInt64).toNat <<< bitShift.toNat) % 2 ^ 64 = 2 ^ bitShift.toNat := by
      rw [show (1 : UInt64).toNat = 1 from rfl, Nat.shiftLeft_eq, Nat.one_mul]
      exact Nat.mod_eq_of_lt (by omega)
    rw [hbMod, h1sh]
    exact Nat.pow_lt_pow_right (by decide) hlt

private theorem ui64_shift_u32_and_bit (x : UInt32) (shift bit : UInt64)
    (hbit : bit.toNat < shift.toNat) (hs : shift.toNat ≤ 6) :
    (x.toUInt64 <<< shift) &&& ((1 : UInt64) <<< bit) = 0 := by
  apply UInt64.toNat_inj.mp
  have hx : x.toNat < 2 ^ 32 := x.toNat_lt
  rw [UInt64.toNat_and, UInt64.toNat_shiftLeft, ui64_toNat_toUInt32]
  have hsMod : shift.toNat % 64 = shift.toNat := Nat.mod_eq_of_lt (by omega)
  rw [hsMod, Nat.shiftLeft_eq]
  have hpow : 2 ^ shift.toNat ≤ 64 := by
    have hle := Nat.pow_le_pow_right (by decide : 0 < 2) hs
    exact Nat.le_trans hle (by decide : 2 ^ 6 ≤ 64)
  have hle : x.toNat * 2 ^ shift.toNat ≤ x.toNat * 64 := Nat.mul_le_mul_left _ hpow
  rw [Nat.mod_eq_of_lt (by omega)]
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_and]
  have hzero : (UInt64.toNat 0).testBit i = false := by simp
  rw [hzero]
  have hpowBit : ((1 : UInt64) <<< bit).toNat = 2 ^ bit.toNat := by
    have hbitMod : bit.toNat % 64 = bit.toNat := Nat.mod_eq_of_lt (by omega)
    rw [UInt64.toNat_shiftLeft, hbitMod, show (1 : UInt64).toNat = 1 from rfl, Nat.shiftLeft_eq, Nat.one_mul]
    have h2 : 2 ^ bit.toNat ≤ 32 := by
      have hle2 := Nat.pow_le_pow_right (by decide : 0 < 2) (by omega : bit.toNat ≤ 5)
      exact Nat.le_trans hle2 (by decide : 2 ^ 5 ≤ 32)
    exact Nat.mod_eq_of_lt (by omega)
  rw [hpowBit]
  by_cases hi : i = bit.toNat
  · subst hi
    rw [← Nat.shiftLeft_eq, Nat.testBit_shiftLeft]
    have hlt : ¬ (shift.toNat ≤ bit.toNat) := by omega
    simp [hlt]
  · have htb : Nat.testBit (2 ^ bit.toNat) i = false := by
      rw [Nat.testBit_two_pow]
      exact decide_eq_false (Ne.symm hi)
    rw [htb, Bool.and_false]

private theorem ui64_bit0_rshift_zero (b : Bool) (k : UInt64) (hk : 1 ≤ k.toNat ∧ k.toNat ≤ 6) :
    (if b then (1 : UInt64) else 0) >>> k = 0 := by
  cases b
  · simp
  · apply ui64_low_rshift_zero k hk
    have : 1 < 2 ^ k.toNat := Nat.one_lt_two_pow (by omega)
    exact this

private theorem ui64_bit0_and_mask (b : Bool) (mask : UInt64) (h0 : (1 : UInt64) &&& mask = 0) :
    (if b then (1 : UInt64) else 0) &&& mask = 0 := by
  cases b
  · simp
  · exact h0

private theorem ui64_bit0_and_self (b : Bool) :
    (if b then (1 : UInt64) else 0) &&& ((1 : UInt64) <<< 0) = if b then (1 : UInt64) else 0 := by
  cases b <;> decide

private theorem bool_of_ui64_bit0_eq {b1 b2 : Bool}
    (h : (if b1 then (1 : UInt64) else 0) = (if b2 then (1 : UInt64) else 0)) : b1 = b2 := by
  cases b1 <;> cases b2
  · rfl
  · exact absurd h.symm (by decide)
  · exact absurd h (by decide)
  · rfl

/-- Every `Errno` is accurately classified by `Errno.isTransientOsErrno` and `ProcessErrorKind.ofErrno`. -/
theorem process_errno_classificationAndTransient_allPass :
    AllPass (test_process_errno_classificationAndTransient Errno.isTransientOsErrno ProcessErrorKind.ofErrno) := by
  intro e
  exact ⟨rfl, rfl, rfl, ⟨rfl, rfl, rfl⟩, trivial⟩

private theorem pipeFlags_toBits_inj {f1 f2 : PipeFlags}
    (h : f1.toBits = f2.toBits) : f1 = f2 := by
  have hb0 : f1.cloexec = f2.cloexec := by
    have ha := congrArg (· &&& ((1 : UInt64) <<< 0)) h
    unfold PipeFlags.toBits at ha; dsimp only at ha
    repeat rw [ui64_or_and_distrib] at ha
    rw [ui64_bit_and_self f1.cloexec 0 (by decide),
      ui64_bit_and_mask f1.nonblock 1 _ (by decide),
      ui64_bit_and_mask f1.direct 2 _ (by decide),
      ui64_bit_and_mask f1.notificationPipe 3 _ (by decide),
      ui64_shift_u32_and_bit f1.extraBits 4 0 (by decide) (by decide),
      ui64_bit_and_self f2.cloexec 0 (by decide),
      ui64_bit_and_mask f2.nonblock 1 _ (by decide),
      ui64_bit_and_mask f2.direct 2 _ (by decide),
      ui64_bit_and_mask f2.notificationPipe 3 _ (by decide),
      ui64_shift_u32_and_bit f2.extraBits 4 0 (by decide) (by decide)] at ha
    simp only [ui64_or_zero] at ha
    exact bool_of_ui64_bit_eq (by decide) ha
  have hb1 : f1.nonblock = f2.nonblock := by
    have ha := congrArg (· &&& ((1 : UInt64) <<< 1)) h
    unfold PipeFlags.toBits at ha; dsimp only at ha
    repeat rw [ui64_or_and_distrib] at ha
    rw [ui64_bit_and_mask f1.cloexec 0 _ (by decide),
      ui64_bit_and_self f1.nonblock 1 (by decide),
      ui64_bit_and_mask f1.direct 2 _ (by decide),
      ui64_bit_and_mask f1.notificationPipe 3 _ (by decide),
      ui64_shift_u32_and_bit f1.extraBits 4 1 (by decide) (by decide),
      ui64_bit_and_mask f2.cloexec 0 _ (by decide),
      ui64_bit_and_self f2.nonblock 1 (by decide),
      ui64_bit_and_mask f2.direct 2 _ (by decide),
      ui64_bit_and_mask f2.notificationPipe 3 _ (by decide),
      ui64_shift_u32_and_bit f2.extraBits 4 1 (by decide) (by decide)] at ha
    simp only [ui64_zero_or, ui64_or_zero] at ha
    exact bool_of_ui64_bit_eq (by decide) ha
  have hb2 : f1.direct = f2.direct := by
    have ha := congrArg (· &&& ((1 : UInt64) <<< 2)) h
    unfold PipeFlags.toBits at ha; dsimp only at ha
    repeat rw [ui64_or_and_distrib] at ha
    rw [ui64_bit_and_mask f1.cloexec 0 _ (by decide),
      ui64_bit_and_mask f1.nonblock 1 _ (by decide),
      ui64_bit_and_self f1.direct 2 (by decide),
      ui64_bit_and_mask f1.notificationPipe 3 _ (by decide),
      ui64_shift_u32_and_bit f1.extraBits 4 2 (by decide) (by decide),
      ui64_bit_and_mask f2.cloexec 0 _ (by decide),
      ui64_bit_and_mask f2.nonblock 1 _ (by decide),
      ui64_bit_and_self f2.direct 2 (by decide),
      ui64_bit_and_mask f2.notificationPipe 3 _ (by decide),
      ui64_shift_u32_and_bit f2.extraBits 4 2 (by decide) (by decide)] at ha
    simp only [ui64_zero_or, ui64_or_zero] at ha
    exact bool_of_ui64_bit_eq (by decide) ha
  have hb3 : f1.notificationPipe = f2.notificationPipe := by
    have ha := congrArg (· &&& ((1 : UInt64) <<< 3)) h
    unfold PipeFlags.toBits at ha; dsimp only at ha
    repeat rw [ui64_or_and_distrib] at ha
    rw [ui64_bit_and_mask f1.cloexec 0 _ (by decide),
      ui64_bit_and_mask f1.nonblock 1 _ (by decide),
      ui64_bit_and_mask f1.direct 2 _ (by decide),
      ui64_bit_and_self f1.notificationPipe 3 (by decide),
      ui64_shift_u32_and_bit f1.extraBits 4 3 (by decide) (by decide),
      ui64_bit_and_mask f2.cloexec 0 _ (by decide),
      ui64_bit_and_mask f2.nonblock 1 _ (by decide),
      ui64_bit_and_mask f2.direct 2 _ (by decide),
      ui64_bit_and_self f2.notificationPipe 3 (by decide),
      ui64_shift_u32_and_bit f2.extraBits 4 3 (by decide) (by decide)] at ha
    simp only [ui64_zero_or, ui64_or_zero] at ha
    exact bool_of_ui64_bit_eq (by decide) ha
  have he : f1.extraBits = f2.extraBits := by
    have hr := congrArg (· >>> (4 : UInt64)) h
    unfold PipeFlags.toBits at hr; dsimp only at hr
    repeat rw [ui64_or_rshift_distrib] at hr
    rw [ui64_bit_rshift_zero f1.cloexec 0 4 (by decide) (by decide),
      ui64_bit_rshift_zero f1.nonblock 1 4 (by decide) (by decide),
      ui64_bit_rshift_zero f1.direct 2 4 (by decide) (by decide),
      ui64_bit_rshift_zero f1.notificationPipe 3 4 (by decide) (by decide),
      ui64_shift_u32_rshift 4 (by decide) f1.extraBits,
      ui64_bit_rshift_zero f2.cloexec 0 4 (by decide) (by decide),
      ui64_bit_rshift_zero f2.nonblock 1 4 (by decide) (by decide),
      ui64_bit_rshift_zero f2.direct 2 4 (by decide) (by decide),
      ui64_bit_rshift_zero f2.notificationPipe 3 4 (by decide) (by decide),
      ui64_shift_u32_rshift 4 (by decide) f2.extraBits] at hr
    simp only [ui64_zero_or] at hr
    exact UInt32.toNat_inj.mp (by simpa [ui64_toNat_toUInt32] using congrArg UInt64.toNat hr)
  cases f1; cases f2; subst hb0 hb1 hb2 hb3 he; rfl

private theorem waitFlags_toBits_inj {f1 f2 : WaitFlags}
    (h : f1.toBits = f2.toBits) : f1 = f2 := by
  have hb0 : f1.nohang = f2.nohang := by
    have ha := congrArg (· &&& ((1 : UInt64) <<< 0)) h
    unfold WaitFlags.toBits at ha; dsimp only at ha
    repeat rw [ui64_or_and_distrib] at ha
    rw [ui64_bit_and_self f1.nohang 0 (by decide),
      ui64_bit_and_mask f1.untraced 1 _ (by decide),
      ui64_bit_and_mask f1.continued 2 _ (by decide),
      ui64_bit_and_mask f1.wall 3 _ (by decide),
      ui64_bit_and_mask f1.wclone 4 _ (by decide),
      ui64_bit_and_mask f1.wnothread 5 _ (by decide),
      ui64_shift_u32_and_bit f1.extraBits 6 0 (by decide) (by decide),
      ui64_bit_and_self f2.nohang 0 (by decide),
      ui64_bit_and_mask f2.untraced 1 _ (by decide),
      ui64_bit_and_mask f2.continued 2 _ (by decide),
      ui64_bit_and_mask f2.wall 3 _ (by decide),
      ui64_bit_and_mask f2.wclone 4 _ (by decide),
      ui64_bit_and_mask f2.wnothread 5 _ (by decide),
      ui64_shift_u32_and_bit f2.extraBits 6 0 (by decide) (by decide)] at ha
    simp only [ui64_or_zero] at ha
    exact bool_of_ui64_bit_eq (by decide) ha
  have hb1 : f1.untraced = f2.untraced := by
    have ha := congrArg (· &&& ((1 : UInt64) <<< 1)) h
    unfold WaitFlags.toBits at ha; dsimp only at ha
    repeat rw [ui64_or_and_distrib] at ha
    rw [ui64_bit_and_mask f1.nohang 0 _ (by decide),
      ui64_bit_and_self f1.untraced 1 (by decide),
      ui64_bit_and_mask f1.continued 2 _ (by decide),
      ui64_bit_and_mask f1.wall 3 _ (by decide),
      ui64_bit_and_mask f1.wclone 4 _ (by decide),
      ui64_bit_and_mask f1.wnothread 5 _ (by decide),
      ui64_shift_u32_and_bit f1.extraBits 6 1 (by decide) (by decide),
      ui64_bit_and_mask f2.nohang 0 _ (by decide),
      ui64_bit_and_self f2.untraced 1 (by decide),
      ui64_bit_and_mask f2.continued 2 _ (by decide),
      ui64_bit_and_mask f2.wall 3 _ (by decide),
      ui64_bit_and_mask f2.wclone 4 _ (by decide),
      ui64_bit_and_mask f2.wnothread 5 _ (by decide),
      ui64_shift_u32_and_bit f2.extraBits 6 1 (by decide) (by decide)] at ha
    simp only [ui64_zero_or, ui64_or_zero] at ha
    exact bool_of_ui64_bit_eq (by decide) ha
  have hb2 : f1.continued = f2.continued := by
    have ha := congrArg (· &&& ((1 : UInt64) <<< 2)) h
    unfold WaitFlags.toBits at ha; dsimp only at ha
    repeat rw [ui64_or_and_distrib] at ha
    rw [ui64_bit_and_mask f1.nohang 0 _ (by decide),
      ui64_bit_and_mask f1.untraced 1 _ (by decide),
      ui64_bit_and_self f1.continued 2 (by decide),
      ui64_bit_and_mask f1.wall 3 _ (by decide),
      ui64_bit_and_mask f1.wclone 4 _ (by decide),
      ui64_bit_and_mask f1.wnothread 5 _ (by decide),
      ui64_shift_u32_and_bit f1.extraBits 6 2 (by decide) (by decide),
      ui64_bit_and_mask f2.nohang 0 _ (by decide),
      ui64_bit_and_mask f2.untraced 1 _ (by decide),
      ui64_bit_and_self f2.continued 2 (by decide),
      ui64_bit_and_mask f2.wall 3 _ (by decide),
      ui64_bit_and_mask f2.wclone 4 _ (by decide),
      ui64_bit_and_mask f2.wnothread 5 _ (by decide),
      ui64_shift_u32_and_bit f2.extraBits 6 2 (by decide) (by decide)] at ha
    simp only [ui64_zero_or, ui64_or_zero] at ha
    exact bool_of_ui64_bit_eq (by decide) ha
  have hb3 : f1.wall = f2.wall := by
    have ha := congrArg (· &&& ((1 : UInt64) <<< 3)) h
    unfold WaitFlags.toBits at ha; dsimp only at ha
    repeat rw [ui64_or_and_distrib] at ha
    rw [ui64_bit_and_mask f1.nohang 0 _ (by decide),
      ui64_bit_and_mask f1.untraced 1 _ (by decide),
      ui64_bit_and_mask f1.continued 2 _ (by decide),
      ui64_bit_and_self f1.wall 3 (by decide),
      ui64_bit_and_mask f1.wclone 4 _ (by decide),
      ui64_bit_and_mask f1.wnothread 5 _ (by decide),
      ui64_shift_u32_and_bit f1.extraBits 6 3 (by decide) (by decide),
      ui64_bit_and_mask f2.nohang 0 _ (by decide),
      ui64_bit_and_mask f2.untraced 1 _ (by decide),
      ui64_bit_and_mask f2.continued 2 _ (by decide),
      ui64_bit_and_self f2.wall 3 (by decide),
      ui64_bit_and_mask f2.wclone 4 _ (by decide),
      ui64_bit_and_mask f2.wnothread 5 _ (by decide),
      ui64_shift_u32_and_bit f2.extraBits 6 3 (by decide) (by decide)] at ha
    simp only [ui64_zero_or, ui64_or_zero] at ha
    exact bool_of_ui64_bit_eq (by decide) ha
  have hb4 : f1.wclone = f2.wclone := by
    have ha := congrArg (· &&& ((1 : UInt64) <<< 4)) h
    unfold WaitFlags.toBits at ha; dsimp only at ha
    repeat rw [ui64_or_and_distrib] at ha
    rw [ui64_bit_and_mask f1.nohang 0 _ (by decide),
      ui64_bit_and_mask f1.untraced 1 _ (by decide),
      ui64_bit_and_mask f1.continued 2 _ (by decide),
      ui64_bit_and_mask f1.wall 3 _ (by decide),
      ui64_bit_and_self f1.wclone 4 (by decide),
      ui64_bit_and_mask f1.wnothread 5 _ (by decide),
      ui64_shift_u32_and_bit f1.extraBits 6 4 (by decide) (by decide),
      ui64_bit_and_mask f2.nohang 0 _ (by decide),
      ui64_bit_and_mask f2.untraced 1 _ (by decide),
      ui64_bit_and_mask f2.continued 2 _ (by decide),
      ui64_bit_and_mask f2.wall 3 _ (by decide),
      ui64_bit_and_self f2.wclone 4 (by decide),
      ui64_bit_and_mask f2.wnothread 5 _ (by decide),
      ui64_shift_u32_and_bit f2.extraBits 6 4 (by decide) (by decide)] at ha
    simp only [ui64_zero_or, ui64_or_zero] at ha
    exact bool_of_ui64_bit_eq (by decide) ha
  have hb5 : f1.wnothread = f2.wnothread := by
    have ha := congrArg (· &&& ((1 : UInt64) <<< 5)) h
    unfold WaitFlags.toBits at ha; dsimp only at ha
    repeat rw [ui64_or_and_distrib] at ha
    rw [ui64_bit_and_mask f1.nohang 0 _ (by decide),
      ui64_bit_and_mask f1.untraced 1 _ (by decide),
      ui64_bit_and_mask f1.continued 2 _ (by decide),
      ui64_bit_and_mask f1.wall 3 _ (by decide),
      ui64_bit_and_mask f1.wclone 4 _ (by decide),
      ui64_bit_and_self f1.wnothread 5 (by decide),
      ui64_shift_u32_and_bit f1.extraBits 6 5 (by decide) (by decide),
      ui64_bit_and_mask f2.nohang 0 _ (by decide),
      ui64_bit_and_mask f2.untraced 1 _ (by decide),
      ui64_bit_and_mask f2.continued 2 _ (by decide),
      ui64_bit_and_mask f2.wall 3 _ (by decide),
      ui64_bit_and_mask f2.wclone 4 _ (by decide),
      ui64_bit_and_self f2.wnothread 5 (by decide),
      ui64_shift_u32_and_bit f2.extraBits 6 5 (by decide) (by decide)] at ha
    simp only [ui64_zero_or, ui64_or_zero] at ha
    exact bool_of_ui64_bit_eq (by decide) ha
  have he : f1.extraBits = f2.extraBits := by
    have hr := congrArg (· >>> (6 : UInt64)) h
    unfold WaitFlags.toBits at hr; dsimp only at hr
    repeat rw [ui64_or_rshift_distrib] at hr
    rw [ui64_bit_rshift_zero f1.nohang 0 6 (by decide) (by decide),
      ui64_bit_rshift_zero f1.untraced 1 6 (by decide) (by decide),
      ui64_bit_rshift_zero f1.continued 2 6 (by decide) (by decide),
      ui64_bit_rshift_zero f1.wall 3 6 (by decide) (by decide),
      ui64_bit_rshift_zero f1.wclone 4 6 (by decide) (by decide),
      ui64_bit_rshift_zero f1.wnothread 5 6 (by decide) (by decide),
      ui64_shift_u32_rshift 6 (by decide) f1.extraBits,
      ui64_bit_rshift_zero f2.nohang 0 6 (by decide) (by decide),
      ui64_bit_rshift_zero f2.untraced 1 6 (by decide) (by decide),
      ui64_bit_rshift_zero f2.continued 2 6 (by decide) (by decide),
      ui64_bit_rshift_zero f2.wall 3 6 (by decide) (by decide),
      ui64_bit_rshift_zero f2.wclone 4 6 (by decide) (by decide),
      ui64_bit_rshift_zero f2.wnothread 5 6 (by decide) (by decide),
      ui64_shift_u32_rshift 6 (by decide) f2.extraBits] at hr
    simp only [ui64_zero_or] at hr
    exact UInt32.toNat_inj.mp (by simpa [ui64_toNat_toUInt32] using congrArg UInt64.toNat hr)
  cases f1; cases f2; subst hb0 hb1 hb2 hb3 hb4 hb5 he; rfl

private theorem pidfdOpenFlags_toBits_inj {f1 f2 : PidfdOpenFlags}
    (h : f1.toBits = f2.toBits) : f1 = f2 := by
  have hb0 : f1.nonblock = f2.nonblock := by
    have ha := congrArg (· &&& ((1 : UInt64) <<< 0)) h
    unfold PidfdOpenFlags.toBits at ha; dsimp only at ha
    repeat rw [ui64_or_and_distrib] at ha
    rw [ui64_bit_and_self f1.nonblock 0 (by decide),
      ui64_bit_and_mask f1.thread 1 _ (by decide),
      ui64_shift_u32_and_bit f1.extraBits 2 0 (by decide) (by decide),
      ui64_bit_and_self f2.nonblock 0 (by decide),
      ui64_bit_and_mask f2.thread 1 _ (by decide),
      ui64_shift_u32_and_bit f2.extraBits 2 0 (by decide) (by decide)] at ha
    simp only [ui64_or_zero] at ha
    exact bool_of_ui64_bit_eq (by decide) ha
  have hb1 : f1.thread = f2.thread := by
    have ha := congrArg (· &&& ((1 : UInt64) <<< 1)) h
    unfold PidfdOpenFlags.toBits at ha; dsimp only at ha
    repeat rw [ui64_or_and_distrib] at ha
    rw [ui64_bit_and_mask f1.nonblock 0 _ (by decide),
      ui64_bit_and_self f1.thread 1 (by decide),
      ui64_shift_u32_and_bit f1.extraBits 2 1 (by decide) (by decide),
      ui64_bit_and_mask f2.nonblock 0 _ (by decide),
      ui64_bit_and_self f2.thread 1 (by decide),
      ui64_shift_u32_and_bit f2.extraBits 2 1 (by decide) (by decide)] at ha
    simp only [ui64_zero_or, ui64_or_zero] at ha
    exact bool_of_ui64_bit_eq (by decide) ha
  have he : f1.extraBits = f2.extraBits := by
    have hr := congrArg (· >>> (2 : UInt64)) h
    unfold PidfdOpenFlags.toBits at hr; dsimp only at hr
    repeat rw [ui64_or_rshift_distrib] at hr
    rw [ui64_bit_rshift_zero f1.nonblock 0 2 (by decide) (by decide),
      ui64_bit_rshift_zero f1.thread 1 2 (by decide) (by decide),
      ui64_shift_u32_rshift 2 (by decide) f1.extraBits,
      ui64_bit_rshift_zero f2.nonblock 0 2 (by decide) (by decide),
      ui64_bit_rshift_zero f2.thread 1 2 (by decide) (by decide),
      ui64_shift_u32_rshift 2 (by decide) f2.extraBits] at hr
    simp only [ui64_zero_or] at hr
    exact UInt32.toNat_inj.mp (by simpa [ui64_toNat_toUInt32] using congrArg UInt64.toNat hr)
  cases f1; cases f2; subst hb0 hb1 he; rfl

private theorem pidfdSignalFlags_toBits_inj {f1 f2 : PidfdSignalFlags}
    (h : f1.toBits = f2.toBits) : f1 = f2 := by
  have hb0 : f1.thread = f2.thread := by
    have ha := congrArg (· &&& ((1 : UInt64) <<< 0)) h
    unfold PidfdSignalFlags.toBits at ha; dsimp only at ha
    repeat rw [ui64_or_and_distrib] at ha
    rw [ui64_bit_and_self f1.thread 0 (by decide),
      ui64_bit_and_mask f1.threadGroup 1 _ (by decide),
      ui64_bit_and_mask f1.processGroup 2 _ (by decide),
      ui64_shift_u32_and_bit f1.extraBits 3 0 (by decide) (by decide),
      ui64_bit_and_self f2.thread 0 (by decide),
      ui64_bit_and_mask f2.threadGroup 1 _ (by decide),
      ui64_bit_and_mask f2.processGroup 2 _ (by decide),
      ui64_shift_u32_and_bit f2.extraBits 3 0 (by decide) (by decide)] at ha
    simp only [ui64_or_zero] at ha
    exact bool_of_ui64_bit_eq (by decide) ha
  have hb1 : f1.threadGroup = f2.threadGroup := by
    have ha := congrArg (· &&& ((1 : UInt64) <<< 1)) h
    unfold PidfdSignalFlags.toBits at ha; dsimp only at ha
    repeat rw [ui64_or_and_distrib] at ha
    rw [ui64_bit_and_mask f1.thread 0 _ (by decide),
      ui64_bit_and_self f1.threadGroup 1 (by decide),
      ui64_bit_and_mask f1.processGroup 2 _ (by decide),
      ui64_shift_u32_and_bit f1.extraBits 3 1 (by decide) (by decide),
      ui64_bit_and_mask f2.thread 0 _ (by decide),
      ui64_bit_and_self f2.threadGroup 1 (by decide),
      ui64_bit_and_mask f2.processGroup 2 _ (by decide),
      ui64_shift_u32_and_bit f2.extraBits 3 1 (by decide) (by decide)] at ha
    simp only [ui64_zero_or, ui64_or_zero] at ha
    exact bool_of_ui64_bit_eq (by decide) ha
  have hb2 : f1.processGroup = f2.processGroup := by
    have ha := congrArg (· &&& ((1 : UInt64) <<< 2)) h
    unfold PidfdSignalFlags.toBits at ha; dsimp only at ha
    repeat rw [ui64_or_and_distrib] at ha
    rw [ui64_bit_and_mask f1.thread 0 _ (by decide),
      ui64_bit_and_mask f1.threadGroup 1 _ (by decide),
      ui64_bit_and_self f1.processGroup 2 (by decide),
      ui64_shift_u32_and_bit f1.extraBits 3 2 (by decide) (by decide),
      ui64_bit_and_mask f2.thread 0 _ (by decide),
      ui64_bit_and_mask f2.threadGroup 1 _ (by decide),
      ui64_bit_and_self f2.processGroup 2 (by decide),
      ui64_shift_u32_and_bit f2.extraBits 3 2 (by decide) (by decide)] at ha
    simp only [ui64_zero_or, ui64_or_zero] at ha
    exact bool_of_ui64_bit_eq (by decide) ha
  have he : f1.extraBits = f2.extraBits := by
    have hr := congrArg (· >>> (3 : UInt64)) h
    unfold PidfdSignalFlags.toBits at hr; dsimp only at hr
    repeat rw [ui64_or_rshift_distrib] at hr
    rw [ui64_bit_rshift_zero f1.thread 0 3 (by decide) (by decide),
      ui64_bit_rshift_zero f1.threadGroup 1 3 (by decide) (by decide),
      ui64_bit_rshift_zero f1.processGroup 2 3 (by decide) (by decide),
      ui64_shift_u32_rshift 3 (by decide) f1.extraBits,
      ui64_bit_rshift_zero f2.thread 0 3 (by decide) (by decide),
      ui64_bit_rshift_zero f2.threadGroup 1 3 (by decide) (by decide),
      ui64_bit_rshift_zero f2.processGroup 2 3 (by decide) (by decide),
      ui64_shift_u32_rshift 3 (by decide) f2.extraBits] at hr
    simp only [ui64_zero_or] at hr
    exact UInt32.toNat_inj.mp (by simpa [ui64_toNat_toUInt32] using congrArg UInt64.toNat hr)
  cases f1; cases f2; subst hb0 hb1 hb2 he; rfl

private theorem signal_toRaw_inj {s1 s2 : Signal} (h : s1.toRaw = s2.toRaw) : s1 = s2 := by
  cases s1 <;> cases s2 <;> simp [Signal.toRaw] at h ⊢
  exact h

/-- Portable wire encoders are injective with exact bit positions and validation invariants. -/
theorem process_flagsAndSignals_encodersInjectiveAndValid_allPass :
    AllPass (test_process_flagsAndSignals_encodersInjectiveAndValid
      PipeFlags.toBits PipeFlags.isValid
      WaitFlags.toBits WaitFlags.isValid
      Signal.toRaw Signal.toLinuxNum Signal.isValid
      PidfdOpenFlags.toBits PidfdOpenFlags.isValid
      PidfdSignalFlags.toBits PidfdSignalFlags.isValid) := by
  intro pf1 pf2
  have hPf : (pf1.toBits == pf2.toBits) = (pf1 == pf2) := by
    apply Bool.eq_iff_iff.mpr
    simp only [beq_iff_eq]
    exact ⟨pipeFlags_toBits_inj, congrArg PipeFlags.toBits⟩
  refine ⟨hPf, ?_, rfl, ?_⟩
  · unfold PipeFlags.toBits; dsimp only
    have h0 : (if pf1.cloexec then ((1 : UInt64) <<< 0) else 0) = if pf1.cloexec then 1 else 0 := by cases pf1.cloexec <;> decide
    have h1 : (if pf1.nonblock then ((1 : UInt64) <<< 1) else 0) = if pf1.nonblock then 2 else 0 := by cases pf1.nonblock <;> decide
    have h2 : (if pf1.direct then ((1 : UInt64) <<< 2) else 0) = if pf1.direct then 4 else 0 := by cases pf1.direct <;> decide
    have h3 : (if pf1.notificationPipe then ((1 : UInt64) <<< 3) else 0) = if pf1.notificationPipe then 8 else 0 := by cases pf1.notificationPipe <;> decide
    rw [h0, h1, h2, h3]
  · intro wf1 wf2
    have hWf : (wf1.toBits == wf2.toBits) = (wf1 == wf2) := by
      apply Bool.eq_iff_iff.mpr
      simp only [beq_iff_eq]
      exact ⟨waitFlags_toBits_inj, congrArg WaitFlags.toBits⟩
    refine ⟨hWf, ?_, rfl, ?_⟩
    · unfold WaitFlags.toBits; dsimp only
      have h0 : (if wf1.nohang then ((1 : UInt64) <<< 0) else 0) = if wf1.nohang then 1 else 0 := by cases wf1.nohang <;> decide
      have h1 : (if wf1.untraced then ((1 : UInt64) <<< 1) else 0) = if wf1.untraced then 2 else 0 := by cases wf1.untraced <;> decide
      have h2 : (if wf1.continued then ((1 : UInt64) <<< 2) else 0) = if wf1.continued then 4 else 0 := by cases wf1.continued <;> decide
      have h3 : (if wf1.wall then ((1 : UInt64) <<< 3) else 0) = if wf1.wall then 8 else 0 := by cases wf1.wall <;> decide
      have h4 : (if wf1.wclone then ((1 : UInt64) <<< 4) else 0) = if wf1.wclone then 16 else 0 := by cases wf1.wclone <;> decide
      have h5 : (if wf1.wnothread then ((1 : UInt64) <<< 5) else 0) = if wf1.wnothread then 32 else 0 := by cases wf1.wnothread <;> decide
      rw [h0, h1, h2, h3, h4, h5]
    · intro s1 s2
      have hSig : (s1.toRaw == s2.toRaw) = (s1 == s2) := by
        apply Bool.eq_iff_iff.mpr
        simp only [beq_iff_eq]
        exact ⟨signal_toRaw_inj, congrArg Signal.toRaw⟩
      refine ⟨hSig, ?_, ?_, rfl, ?_⟩
      · cases s1 <;> rfl
      · cases s1 <;> rfl
      · intro po1 po2
        have hPo : (po1.toBits == po2.toBits) = (po1 == po2) := by
          apply Bool.eq_iff_iff.mpr
          simp only [beq_iff_eq]
          exact ⟨pidfdOpenFlags_toBits_inj, congrArg PidfdOpenFlags.toBits⟩
        refine ⟨hPo, ?_, rfl, ?_⟩
        · unfold PidfdOpenFlags.toBits; dsimp only
          have h0 : (if po1.nonblock then ((1 : UInt64) <<< 0) else 0) = if po1.nonblock then 1 else 0 := by cases po1.nonblock <;> decide
          have h1 : (if po1.thread then ((1 : UInt64) <<< 1) else 0) = if po1.thread then 2 else 0 := by cases po1.thread <;> decide
          rw [h0, h1]
        · intro ps1 ps2
          have hPs : (ps1.toBits == ps2.toBits) = (ps1 == ps2) := by
            apply Bool.eq_iff_iff.mpr
            simp only [beq_iff_eq]
            exact ⟨pidfdSignalFlags_toBits_inj, congrArg PidfdSignalFlags.toBits⟩
          refine ⟨hPs, ?_, rfl, trivial⟩
          unfold PidfdSignalFlags.toBits; dsimp only
          have h0 : (if ps1.thread then ((1 : UInt64) <<< 0) else 0) = if ps1.thread then 1 else 0 := by cases ps1.thread <;> decide
          have h1 : (if ps1.threadGroup then ((1 : UInt64) <<< 1) else 0) = if ps1.threadGroup then 2 else 0 := by cases ps1.threadGroup <;> decide
          have h2 : (if ps1.processGroup then ((1 : UInt64) <<< 2) else 0) = if ps1.processGroup then 4 else 0 := by cases ps1.processGroup <;> decide
          rw [h0, h1, h2]

private theorem ui32_hi16_nat (u : UInt16) :
    (u.toUInt32 <<< 16).toNat = u.toNat * 65536 := by
  have hu : u.toNat < 65536 := u.toNat_lt
  rw [UInt32.toNat_shiftLeft]
  have h16 : (16 : UInt32).toNat % 32 = 16 := by decide
  have hu32 : u.toUInt32.toNat = u.toNat := UInt16.toNat_toUInt32 u
  rw [h16, hu32, Nat.shiftLeft_eq]
  exact Nat.mod_eq_of_lt (by omega)

private theorem ui32_low_u8_shift8 (b : UInt8) :
    (b.toUInt32 <<< 8).toNat = b.toNat * 256 := by
  have hb : b.toNat < 256 := b.toNat_lt
  rw [UInt32.toNat_shiftLeft]
  have h8 : (8 : UInt32).toNat % 32 = 8 := by decide
  have hb32 : b.toUInt32.toNat = b.toNat := UInt8.toNat_toUInt32 b
  rw [h8, hb32, Nat.shiftLeft_eq]
  exact Nat.mod_eq_of_lt (by omega)

private theorem ui32_hi16_or_and_low (hi : UInt16) (w mask : UInt32) (hm : mask.toNat < 65536) :
    ((hi.toUInt32 <<< 16) ||| w) &&& mask = w &&& mask := by
  apply UInt32.toNat_inj.mp
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [UInt32.toNat_and, UInt32.toNat_or, Nat.testBit_and, Nat.testBit_or]
  by_cases h16 : i < 16
  · have hhi : Nat.testBit (hi.toUInt32 <<< 16).toNat i = false := by
      rw [ui32_hi16_nat, show hi.toNat * 65536 = hi.toNat <<< 16 from by rw [Nat.shiftLeft_eq]]
      rw [Nat.testBit_shiftLeft]
      have : ¬ (16 ≤ i) := by omega
      simp [this]
    rw [hhi, Bool.false_or]
  · have hmPow : mask.toNat < 2 ^ i :=
      Nat.lt_of_lt_of_le (show mask.toNat < 2 ^ 16 from hm) (Nat.pow_le_pow_right (by decide) (by omega))
    have hm0 : Nat.testBit mask.toNat i = false := Nat.testBit_lt_two_pow hmPow
    rw [hm0, Bool.and_false, Bool.and_false]

private theorem ui32_hi16_or_rshift8_and_ff (hi : UInt16) (w : UInt32) :
    (((hi.toUInt32 <<< 16) ||| w) >>> 8) &&& (0xff : UInt32) = (w >>> 8) &&& (0xff : UInt32) := by
  apply UInt32.toNat_inj.mp
  apply Nat.eq_of_testBit_eq
  intro i
  have h8 : (8 : UInt32).toNat % 32 = 8 := by decide
  simp only [UInt32.toNat_and, UInt32.toNat_shiftRight, UInt32.toNat_or, h8,
    Nat.testBit_and, Nat.testBit_shiftRight, Nat.testBit_or]
  by_cases hi8 : i < 8
  · have hhi : Nat.testBit (hi.toUInt32 <<< 16).toNat (8 + i) = false := by
      rw [ui32_hi16_nat, show hi.toNat * 65536 = hi.toNat <<< 16 from by rw [Nat.shiftLeft_eq]]
      rw [Nat.testBit_shiftLeft]
      have : ¬ (16 ≤ 8 + i) := by omega
      simp [this]
    rw [hhi, Bool.false_or]
  · have hmPow : (0xff : UInt32).toNat < 2 ^ i :=
      Nat.lt_of_lt_of_le (by decide : (0xff : UInt32).toNat < 2 ^ 8) (Nat.pow_le_pow_right (by decide) (by omega))
    have hm0 : Nat.testBit (0xff : UInt32).toNat i = false := Nat.testBit_lt_two_pow hmPow
    rw [hm0, Bool.and_false, Bool.and_false]

private theorem ui32_u8_shift8_low_and (code : UInt8) (low mask : UInt32)
    (_hlow : low.toNat < 256) (hmask : mask.toNat < 256) :
    ((code.toUInt32 <<< 8) ||| low) &&& mask = low &&& mask := by
  apply UInt32.toNat_inj.mp
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [UInt32.toNat_and, UInt32.toNat_or, Nat.testBit_and, Nat.testBit_or]
  by_cases hi8 : i < 8
  · have hc : Nat.testBit (code.toUInt32 <<< 8).toNat i = false := by
      rw [ui32_low_u8_shift8, show code.toNat * 256 = code.toNat <<< 8 from by rw [Nat.shiftLeft_eq]]
      rw [Nat.testBit_shiftLeft]
      have : ¬ (8 ≤ i) := by omega
      simp [this]
    rw [hc, Bool.false_or]
  · have hmPow : mask.toNat < 2 ^ i :=
      Nat.lt_of_lt_of_le (show mask.toNat < 2 ^ 8 from hmask) (Nat.pow_le_pow_right (by decide) (by omega))
    have hm0 : Nat.testBit mask.toNat i = false := Nat.testBit_lt_two_pow hmPow
    rw [hm0, Bool.and_false, Bool.and_false]

private theorem ui32_u8_shift8_low_rshift8_and_ff (code : UInt8) (low : UInt32) (hlow : low.toNat < 256) :
    (((code.toUInt32 <<< 8) ||| low) >>> 8) &&& 0xff = code.toUInt32 := by
  apply UInt32.toNat_inj.mp
  apply Nat.eq_of_testBit_eq
  intro i
  have h8 : (8 : UInt32).toNat % 32 = 8 := by decide
  simp only [UInt32.toNat_and, UInt32.toNat_shiftRight, UInt32.toNat_or, h8,
    Nat.testBit_and, Nat.testBit_shiftRight, Nat.testBit_or]
  by_cases hi8 : i < 8
  · have hlPow : low.toNat < 2 ^ (8 + i) :=
      Nat.lt_of_lt_of_le (show low.toNat < 2 ^ 8 from hlow) (Nat.pow_le_pow_right (by decide) (by omega))
    have hl0 : Nat.testBit low.toNat (8 + i) = false := Nat.testBit_lt_two_pow hlPow
    have hc : Nat.testBit (code.toUInt32 <<< 8).toNat (8 + i) = Nat.testBit code.toUInt32.toNat i := by
      rw [ui32_low_u8_shift8, show code.toNat * 256 = code.toNat <<< 8 from by rw [Nat.shiftLeft_eq]]
      rw [Nat.testBit_shiftLeft]
      have hge : 8 ≤ 8 + i := by omega
      have hsub : 8 + i - 8 = i := by omega
      have hu8 : code.toUInt32.toNat = code.toNat := UInt8.toNat_toUInt32 code
      simp [hge, hsub, hu8]
    have hff : Nat.testBit (0xff : UInt32).toNat i = true := by
      have : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 := by omega
      rcases this with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    rw [hl0, hc, hff, Bool.or_false, Bool.and_true]
  · have hcPow : code.toNat < 2 ^ i :=
      Nat.lt_of_lt_of_le code.toNat_lt (Nat.pow_le_pow_right (by decide) (by omega))
    have hc0 : Nat.testBit code.toUInt32.toNat i = false := by
      rw [UInt8.toNat_toUInt32]
      exact Nat.testBit_lt_two_pow hcPow
    have hffPow : (0xff : UInt32).toNat < 2 ^ i :=
      Nat.lt_of_lt_of_le (by decide : (0xff : UInt32).toNat < 2 ^ 8) (Nat.pow_le_pow_right (by decide) (by omega))
    have hff0 : Nat.testBit (0xff : UInt32).toNat i = false := Nat.testBit_lt_two_pow hffPow
    rw [hff0, Bool.and_false, hc0]

private theorem uint32_and_eq_of_lt (x m : UInt32) (h : x.toNat ≤ m.toNat) (hm : m = 0x7f ∨ m = 0xff) :
    x &&& m = x := by
  apply UInt32.toNat_inj.mp
  apply Nat.eq_of_testBit_eq
  intro i
  rw [UInt32.toNat_and, Nat.testBit_and]
  rcases hm with rfl | rfl
  · by_cases hi7 : i < 7
    · have h7 : Nat.testBit (0x7f : UInt32).toNat i = true := by
        have : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 := by omega
        rcases this with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
      rw [h7, Bool.and_true]
    · have hxPow : x.toNat < 2 ^ i :=
        Nat.lt_of_le_of_lt h (Nat.lt_of_lt_of_le (by decide : (0x7f : UInt32).toNat < 2 ^ 7) (Nat.pow_le_pow_right (by decide) (by omega)))
      have hx0 : Nat.testBit x.toNat i = false := Nat.testBit_lt_two_pow hxPow
      rw [hx0, Bool.false_and]
  · by_cases hi8 : i < 8
    · have h8 : Nat.testBit (0xff : UInt32).toNat i = true := by
        have : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 := by omega
        rcases this with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
      rw [h8, Bool.and_true]
    · have hxPow : x.toNat < 2 ^ i :=
        Nat.lt_of_le_of_lt h (Nat.lt_of_lt_of_le (by decide : (0xff : UInt32).toNat < 2 ^ 8) (Nat.pow_le_pow_right (by decide) (by omega)))
      have hx0 : Nat.testBit x.toNat i = false := Nat.testBit_lt_two_pow hxPow
      rw [hx0, Bool.false_and]

private theorem ui32_or_zero (x : UInt32) : x ||| 0 = x := by
  apply UInt32.toNat_inj.mp; simp

private theorem uint32_u8_toUInt32_toUInt8 (code : UInt8) :
    code.toUInt32.toUInt8 = code := by
  apply UInt8.toNat_inj.mp
  rw [UInt32.toNat_toUInt8, UInt8.toNat_toUInt32]
  exact Nat.mod_eq_of_lt code.toNat_lt

/-- `WaitResult.ofRawWait4` decodes all statuses across arbitrary upper 16-bit payloads. -/
theorem process_waitResult_ofRawWait4_decodesAllStatuses_allPass :
    AllPass (test_process_waitResult_ofRawWait4_decodesAllStatuses WaitResult.ofRawWait4) := by
  intro nonPosPid hNonPos posPid hPos rawSt code termSig hTerm core stopSig upper
  have hNotPos : ¬ (posPid ≤ 0) := Int32.not_le.mpr hPos
  refine ⟨?_, ?_, ?_, ?_, ?_, trivial⟩
  · simp [WaitResult.ofRawWait4, hNonPos]
  · simp only [WaitResult.ofRawWait4, hNotPos, ↓reduceIte]
    have hlow : (((upper.toUInt32 <<< 16) ||| (code.toUInt32 <<< 8)) &&& 0x7f) = 0 := by
      rw [ui32_hi16_or_and_low upper (code.toUInt32 <<< 8) 0x7f (by decide)]
      rw [← ui32_or_zero (code.toUInt32 <<< 8), ui32_u8_shift8_low_and code 0 0x7f (by decide) (by decide)]
      decide
    have hhi : ((((upper.toUInt32 <<< 16) ||| (code.toUInt32 <<< 8)) >>> 8) &&& 0xff) = code.toUInt32 := by
      rw [ui32_hi16_or_rshift8_and_ff, ← ui32_or_zero (code.toUInt32 <<< 8),
        ui32_u8_shift8_low_rshift8_and_ff code 0 (by decide)]
    rw [hlow]
    change WaitResult.exited posPid.toUInt32 ((((upper.toUInt32 <<< 16) ||| (code.toUInt32 <<< 8)) >>> 8) &&& 0xff).toUInt8 =
      WaitResult.exited posPid.toUInt32 code
    rw [hhi, uint32_u8_toUInt32_toUInt8]
  · simp only [WaitResult.ofRawWait4, hNotPos, ↓reduceIte]
    have hsigLt : termSig.toNat ≤ 126 := show termSig.toNat ≤ (126 : UInt8).toNat from hTerm.2
    have hsigGe : 1 ≤ termSig.toNat := show (1 : UInt8).toNat ≤ termSig.toNat from hTerm.1
    have hu32Term : termSig.toUInt32.toNat = termSig.toNat := UInt8.toNat_toUInt32 termSig
    have hlowNat : ((if core then (0x80 : UInt32) else 0) ||| termSig.toUInt32).toNat < 256 := by
      rw [UInt32.toNat_or, show (256 : Nat) = 2 ^ 8 from rfl]
      apply Nat.or_lt_two_pow
      · cases core <;> decide
      · rw [hu32Term]; omega
    have hassoc : (code.toUInt32 <<< 8) ||| (if core then (0x80 : UInt32) else 0) ||| termSig.toUInt32 =
        (code.toUInt32 <<< 8) ||| ((if core then (0x80 : UInt32) else 0) ||| termSig.toUInt32) := UInt32.or_assoc _ _ _
    have hlow7 : (((upper.toUInt32 <<< 16) ||| ((code.toUInt32 <<< 8) ||| (if core then (0x80 : UInt32) else 0) ||| termSig.toUInt32)) &&& 0x7f) = termSig.toUInt32 := by
      rw [hassoc, ui32_hi16_or_and_low upper _ 0x7f (by decide),
        ui32_u8_shift8_low_and code _ 0x7f hlowNat (by decide),
        ui32_or_and_distrib]
      have hc0 : (if core then (0x80 : UInt32) else 0) &&& 0x7f = 0 := by cases core <;> decide
      have ht : termSig.toUInt32 &&& 0x7f = termSig.toUInt32 :=
        uint32_and_eq_of_lt termSig.toUInt32 0x7f (by rw [hu32Term]; exact Nat.le_trans hsigLt (by decide)) (Or.inl rfl)
      rw [hc0, ht]
      apply UInt32.toNat_inj.mp; simp
    have hne0 : (termSig.toUInt32 == 0) = false := by
      apply beq_false_of_ne
      intro heq
      have := congrArg UInt32.toNat heq
      rw [hu32Term] at this
      have : (0 : UInt32).toNat = 0 := rfl
      omega
    have hne7f : (termSig.toUInt32 == 0x7f) = false := by
      apply beq_false_of_ne
      intro heq
      have := congrArg UInt32.toNat heq
      rw [hu32Term] at this
      have : (0x7f : UInt32).toNat = 127 := by decide
      omega
    have hcore80 : ((((upper.toUInt32 <<< 16) ||| ((code.toUInt32 <<< 8) ||| (if core then (0x80 : UInt32) else 0) ||| termSig.toUInt32)) &&& 0x80) != 0) = core := by
      rw [hassoc, ui32_hi16_or_and_low upper _ 0x80 (by decide),
        ui32_u8_shift8_low_and code _ 0x80 hlowNat (by decide),
        ui32_or_and_distrib]
      have ht0 : termSig.toUInt32 &&& 0x80 = 0 := by
        apply UInt32.toNat_inj.mp
        apply Nat.eq_of_testBit_eq
        intro i
        rw [UInt32.toNat_and, Nat.testBit_and]
        have hz : (UInt32.toNat 0).testBit i = false := by simp
        rw [hz]
        by_cases hi7 : i = 7
        · subst hi7
          have : Nat.testBit termSig.toUInt32.toNat 7 = false :=
            Nat.testBit_lt_two_pow (by rw [hu32Term]; omega)
          rw [this, Bool.false_and]
        · have : Nat.testBit (0x80 : UInt32).toNat i = false := by
            by_cases hi8 : i < 8
            · have : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 := by omega
              rcases this with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
            · exact Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le (by decide : (0x80 : UInt32).toNat < 2 ^ 8) (Nat.pow_le_pow_right (by decide) (by omega)))
          rw [this, Bool.and_false]
      rw [ht0]
      cases core <;> decide
    have hassocAll : (upper.toUInt32 <<< 16 ||| code.toUInt32 <<< 8 ||| if core then (0x80 : UInt32) else 0) ||| termSig.toUInt32 =
        (upper.toUInt32 <<< 16) ||| ((code.toUInt32 <<< 8) ||| (if core then (0x80 : UInt32) else 0) ||| termSig.toUInt32) := by
      rw [UInt32.or_assoc, UInt32.or_assoc, UInt32.or_assoc]
    rw [hassocAll, hlow7, hne0, hne7f, hcore80]
    rfl
  · simp only [WaitResult.ofRawWait4, hNotPos, ↓reduceIte]
    have hlow7 : (((upper.toUInt32 <<< 16) ||| ((stopSig.toUInt32 <<< 8) ||| 0x7f)) &&& 0x7f) = 0x7f := by
      rw [ui32_hi16_or_and_low upper _ 0x7f (by decide),
        ui32_u8_shift8_low_and stopSig 0x7f 0x7f (by decide) (by decide)]
      decide
    have hlowff : (((upper.toUInt32 <<< 16) ||| ((stopSig.toUInt32 <<< 8) ||| 0x7f)) &&& 0xff) = 0x7f := by
      rw [ui32_hi16_or_and_low upper _ 0xff (by decide),
        ui32_u8_shift8_low_and stopSig 0x7f 0xff (by decide) (by decide)]
      decide
    have hhi : ((((upper.toUInt32 <<< 16) ||| ((stopSig.toUInt32 <<< 8) ||| 0x7f)) >>> 8) &&& 0xff) = stopSig.toUInt32 := by
      rw [ui32_hi16_or_rshift8_and_ff, ui32_u8_shift8_low_rshift8_and_ff stopSig 0x7f (by decide)]
    have hassocAll : (upper.toUInt32 <<< 16 ||| stopSig.toUInt32 <<< 8) ||| (0x7f : UInt32) =
        (upper.toUInt32 <<< 16) ||| ((stopSig.toUInt32 <<< 8) ||| 0x7f) := UInt32.or_assoc _ _ _
    rw [hassocAll, hlow7, hlowff, hhi]
    rfl
  · simp only [WaitResult.ofRawWait4, hNotPos, ↓reduceIte]
    have hlow7 : (((upper.toUInt32 <<< 16) ||| 0xffff) &&& 0x7f) = 0x7f := by
      rw [ui32_hi16_or_and_low upper 0xffff 0x7f (by decide)]; decide
    have hlowff : (((upper.toUInt32 <<< 16) ||| 0xffff) &&& 0xff) = 0xff := by
      rw [ui32_hi16_or_and_low upper 0xffff 0xff (by decide)]; decide
    rw [hlow7, hlowff]
    rfl

/-- Witness reachability for `test_process_waitResult_ofRawWait4_decodesAllStatuses`. -/
theorem process_waitResult_ofRawWait4_decodesAllStatuses_canReach :
    CanReach (test_process_waitResult_ofRawWait4_decodesAllStatuses WaitResult.ofRawWait4) := by
  refine ⟨0, ?_, 1, ?_, 0, 0, 15, ⟨?_, ?_⟩, false, 19, 0, ?_⟩
  · decide
  · decide
  · decide
  · decide
  · exact process_waitResult_ofRawWait4_decodesAllStatuses_allPass
      0 (by decide) 1 (by decide) 0 0 15 ⟨by decide, by decide⟩ false 19 0

/-- `Internal.mkProcessOps` rejects NPTL `32`/`33` before C and forwards all 7 operations and errors. -/
theorem process_impl_mkProcessOps_wiresEncodersAndDecodesWait4_allPass :
    AllPass (test_process_impl_mkProcessOps_wiresEncodersAndDecodesWait4 Internal.mkProcessOps) := by
  intro pf wpid wf rawTuple kpid sig opid pof pfd psig psf myPid myUid err n0
  dsimp only [test_process_impl_mkProcessOps_wiresEncodersAndDecodesWait4,
    Internal.mkProcessOps, AllPass, NondetTest.nondet, NondetTest.assert,
    StateT.run, bind, pure, Pure.pure, Bind.bind, StateT.bind, StateT.pure,
    modify, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet]
  by_cases hSig : sig.isNptlReserved <;> by_cases hPsig : psig.isNptlReserved <;>
    simp only [hSig, hPsig, ↓reduceIte, beq_self_eq_true, Bool.true_and, StateT.pure] <;>
    (try simp only [and_self]) <;>
    trivial

private def assocSetNaive {α β : Type} [BEq α] (xs : List (α × β)) (k : α) (v : β) : List (α × β) :=
  match xs with
  | [] => [(k, v)]
  | (k', v') :: rest =>
    if k' == k then (k, v) :: rest
    else (k', v') :: assocSetNaive rest k v

private theorem assocSetAux_eq {α β : Type} [BEq α]
    (xs : List (α × β)) (k : α) (v : β) (acc : List (α × β)) :
    assocSetAux xs k v acc = acc.reverse ++ assocSetNaive xs k v := by
  induction xs generalizing acc with
  | nil => simp [assocSetAux, assocSetNaive]
  | cons p rest ih =>
    rcases p with ⟨k', v'⟩
    by_cases h : k' == k
    · simp [assocSetAux, assocSetNaive, h]
    · simp [assocSetAux, assocSetNaive, h, ih, List.reverse_cons]

private theorem assocSet_eq_naive {α β : Type} [BEq α] (xs : List (α × β)) (k : α) (v : β) :
    assocSet xs k v = assocSetNaive xs k v := by
  simp [assocSet, assocSetAux_eq]

private theorem assocGet_assocSet_eq {α β : Type} [BEq α] [LawfulBEq α]
    (xs : List (α × β)) (k : α) (v : β) :
    assocGet (assocSet xs k v) k = some v := by
  rw [assocSet_eq_naive]
  induction xs with
  | nil => simp [assocSetNaive, assocGet]
  | cons p rest ih =>
    rcases p with ⟨k', v'⟩
    by_cases h : k' == k
    · have hk : k' = k := eq_of_beq h
      subst hk
      simp [assocSetNaive, assocGet]
    · simp [assocSetNaive, assocGet, h, ih]

private theorem assocGet_assocSet_ne {α β : Type} [BEq α] [LawfulBEq α]
    (xs : List (α × β)) (k1 k2 : α) (v : β) (hne : k1 ≠ k2) :
    assocGet (assocSet xs k1 v) k2 = assocGet xs k2 := by
  rw [assocSet_eq_naive]
  induction xs with
  | nil =>
    have hbeq : (k1 == k2) = false := beq_false_of_ne hne
    simp [assocSetNaive, assocGet, hbeq]
  | cons p rest ih =>
    rcases p with ⟨k', v'⟩
    by_cases h1 : k' == k1
    · have hk : k' = k1 := eq_of_beq h1
      subst hk
      have hbeq : (k' == k2) = false := beq_false_of_ne hne
      simp [assocSetNaive, assocGet, hbeq]
    · by_cases h2 : k' == k2
      · simp [assocSetNaive, assocGet, h1, h2]
      · simp [assocSetNaive, assocGet, h1, h2, ih]

private theorem nextFreeHid_ge_hint (fds : List (HandleId × ProcessFdDesc)) (hint : HandleId) :
    hint ≤ nextFreeHid fds hint := by
  induction fds generalizing hint with
  | nil => exact Nat.le_refl _
  | cons p rest ih =>
    rcases p with ⟨k, d⟩
    exact Nat.le_trans (Nat.le_max_left _ _) (ih _)

/-- `pipe2` rejects invalid flags without mutating state and allocates pairwise-distinct handles. -/
theorem process_ops_pipe2_flagsAndDistinctHandles_allPass :
    AllPass (test_process_ops_pipe2_flagsAndDistinctHandles modelOps) := by
  intro s0 badFlags hBad
  have hEx0 : (badFlags.extraBits == 0) = false := by
    cases h : (badFlags.extraBits == 0)
    · rfl
    · have : (badFlags.extraBits != 0) = false := by simp [bne, h]
      exact absurd hBad (by simp [this])
  dsimp only [test_process_ops_pipe2_flagsAndDistinctHandles, AllPass,
    NondetTest.nondet, NondetTest.assume, NondetTest.assert,
    modelOps, PipeFlags.isValid, StateT.run, bind, pure, get, getThe,
    MonadStateOf.get, StateT.get, set, StateT.set, Pure.pure, StateT.pure,
    Bind.bind, StateT.bind, commitPipeFds]
  simp only [hEx0, Bool.not_false, ↓reduceIte, beq_self_eq_true, Bool.not_true,
    Bool.false_eq_true]
  refine ⟨?_, ?_⟩
  · rfl
  · let rd1 : Nat := nextFreeHid s0.fds s0.nextHid
    let wr1 : Nat := rd1 + 1
    have hne1 : rd1 ≠ wr1 := by omega
    have hgetRd1 : assocGet (assocSet (assocSet s0.fds rd1 (.pipeRead true false)) wr1 (.pipeWrite true false)) rd1 =
        some (.pipeRead true false) := by
      rw [assocGet_assocSet_ne _ wr1 rd1 _ (Ne.symm hne1), assocGet_assocSet_eq]
    have hgetWr1 : assocGet (assocSet (assocSet s0.fds rd1 (.pipeRead true false)) wr1 (.pipeWrite true false)) wr1 =
        some (.pipeWrite true false) :=
      assocGet_assocSet_eq _ wr1 _
    let fds1 := assocSet (assocSet s0.fds rd1 (.pipeRead true false)) wr1 (.pipeWrite true false)
    let next1 : Nat := max s0.nextHid (max (rd1 + 1) (wr1 + 1))
    let rd2 : Nat := nextFreeHid fds1 next1
    let wr2 : Nat := rd2 + 1
    have hrd2Ge : next1 ≤ rd2 := nextFreeHid_ge_hint fds1 next1
    have hlt : wr1 < rd2 := by omega
    have hne2 : rd2 ≠ wr2 := by omega
    have h1 : rd1 ≠ rd2 := by omega
    have h2 : rd1 ≠ wr2 := by omega
    have h3 : wr1 ≠ rd2 := by omega
    have h4 : wr1 ≠ wr2 := by omega
    have hgetRd2 : assocGet (assocSet (assocSet fds1 rd2 (.pipeRead false true)) wr2 (.pipeWrite false true)) rd2 =
        some (.pipeRead false true) := by
      rw [assocGet_assocSet_ne _ wr2 rd2 _ (Ne.symm hne2), assocGet_assocSet_eq]
    have hgetWr2 : assocGet (assocSet (assocSet fds1 rd2 (.pipeRead false true)) wr2 (.pipeWrite false true)) wr2 =
        some (.pipeWrite false true) :=
      assocGet_assocSet_eq _ wr2 _
    exact ⟨hne1, hgetRd1, hgetWr1, ⟨hne2, h1, h2, h3, h4⟩, hgetRd2, hgetWr2, trivial⟩

/-- Witness reachability for `test_process_ops_pipe2_flagsAndDistinctHandles`. -/
theorem process_ops_pipe2_flagsAndDistinctHandles_canReach :
    CanReach (test_process_ops_pipe2_flagsAndDistinctHandles modelOps) := by
  refine ⟨ProcessSysState.initial, { extraBits := 1 }, ?_, ?_⟩
  · decide
  · exact process_ops_pipe2_flagsAndDistinctHandles_allPass ProcessSysState.initial { extraBits := 1 } (by decide)

private theorem effectiveSelfPid_bounds (s : ProcessSysState) :
    1 ≤ effectiveSelfPid s ∧ effectiveSelfPid s ≤ maxLinuxPid := by
  unfold effectiveSelfPid
  split
  · rename_i h
    simpa [Bool.and_eq_true] using h
  · constructor <;> decide

private theorem modelOps_pipe2_preserves_self (s : ProcessSysState) (pf : PipeFlags) :
    ((modelOps.pipe2 pf).run s).2.selfPid = s.selfPid ∧
    ((modelOps.pipe2 pf).run s).2.selfUid = s.selfUid := by
  dsimp only [modelOps, StateT.run, get, getThe, MonadStateOf.get, StateT.get,
    set, pure, Pure.pure, bind, Bind.bind, StateT.bind, StateT.pure, StateT.set, commitPipeFds]
  cases (!pf.isValid) <;> cases (pf.notificationPipe && !s.watchQueueSupported) <;> exact ⟨rfl, rfl⟩

private theorem deliverSignalToTarget_preserves_self (s : ProcessSysState) (targetPid : UInt32)
    (sig : Signal) (threadScoped : Bool := false) :
    ∀ s', deliverSignalToTarget s targetPid sig threadScoped = .ok s' → s'.selfPid = s.selfPid ∧ s'.selfUid = s.selfUid := by
  intro s' h
  unfold deliverSignalToTarget at h
  dsimp only at h
  cases hres : sig.isNptlReserved <;> simp only [hres, ↓reduceIte] at h
  · cases heq : (targetPid == effectiveSelfPid s) <;> simp only [heq, ↓reduceIte] at h
    · cases hget : assocGet s.procs targetPid with
      | none => simp only [hget] at h; cases h
      | some entry =>
        simp only [hget] at h
        cases hd : (entry.lifecycle == .reaped || entry.lifecycle == .exitDead) <;>
          simp only [hd, ↓reduceIte] at h
        · cases hrole : entry.role with
          | thread leaderPid =>
            simp only [hrole] at h
            cases hle : (leaderPid == effectiveSelfPid s) <;> simp only [hle, ↓reduceIte] at h
            · cases hlg : assocGet s.procs leaderPid with
              | none =>
                simp only [hlg] at h
                cases h1 : (!sig.isValid) <;> cases h2 : (!canSignalEntry sig entry) <;>
                  simp only [h1, h2, ↓reduceIte] at h <;> first | contradiction | (cases h; exact ⟨rfl, rfl⟩)
              | some leader =>
                simp only [hlg] at h
                cases hdead : (leader.lifecycle == .reaped || leader.lifecycle == .exitDead || isPlainZombieLifecycle leader.lifecycle) <;>
                  cases h1 : (!sig.isValid) <;> cases h2 : (!canSignalEntry sig leader) <;>
                  simp only [hdead, h1, h2, ↓reduceIte] at h <;> first | contradiction | (cases h; exact ⟨rfl, rfl⟩)
            · cases h1 : (!sig.isValid) <;> simp only [h1, ↓reduceIte] at h <;>
                first | contradiction | (cases h; exact ⟨rfl, rfl⟩)
          | _ =>
            simp only [hrole] at h
            cases h1 : (!sig.isValid) <;> cases h2 : (!canSignalEntry sig entry) <;>
              simp only [h1, h2, ↓reduceIte] at h <;> first | contradiction | (cases h; exact ⟨rfl, rfl⟩)
        · cases h
    · cases h1 : (!sig.isValid) <;> simp only [h1, ↓reduceIte] at h <;>
        first | contradiction | (cases h; exact ⟨rfl, rfl⟩)
  · cases h

private theorem evalKillProcessGroup_preserves_self (s : ProcessSysState) (targetPgid : UInt32) (sig : Signal) :
    ∀ s', evalKillProcessGroup s targetPgid sig = .ok s' → s'.selfPid = s.selfPid ∧ s'.selfUid = s.selfUid := by
  intro s' h
  unfold evalKillProcessGroup at h
  dsimp only at h
  repeat (first
    | contradiction
    | (cases h; exact ⟨rfl, rfl⟩)
    | split at h)

private theorem evalKill_preserves_self (s : ProcessSysState) (p : Int32) (sig : Signal) :
    ∀ s', evalKill s p sig = .ok s' → s'.selfPid = s.selfPid ∧ s'.selfUid = s.selfUid := by
  intro s' h
  unfold evalKill at h
  dsimp only at h
  cases hres : sig.isNptlReserved <;> simp only [hres, ↓reduceIte] at h
  · cases hmin : (p == Int32.minValue) <;> simp only [hmin, ↓reduceIte] at h
    · by_cases hpos : p > 0
      · simp only [hpos, ↓reduceIte] at h
        exact deliverSignalToTarget_preserves_self s p.toUInt32 sig false s' h
      · simp only [hpos, ↓reduceIte] at h
        cases hz : (p == 0) <;> simp only [hz, ↓reduceIte] at h
        · cases hm1 : (p == -1) <;> simp only [hm1, ↓reduceIte] at h
          · exact evalKillProcessGroup_preserves_self s _ sig s' h
          · repeat (first | contradiction | (cases h; exact ⟨rfl, rfl⟩) | split at h)
        · exact evalKillProcessGroup_preserves_self s _ sig s' h
    · cases h
  · cases h

private theorem reapThreadGroup_preserves_self (s : ProcessSysState) (rPid : UInt32) :
    (reapThreadGroup s rPid).selfPid = s.selfPid ∧ (reapThreadGroup s rPid).selfUid = s.selfUid :=
  ⟨rfl, rfl⟩

private theorem reapSingleProc_preserves_self (s : ProcessSysState) (pid : UInt32) :
    (reapSingleProc s pid).selfPid = s.selfPid ∧ (reapSingleProc s pid).selfUid = s.selfUid :=
  ⟨rfl, rfl⟩

private theorem reapExitDeadSingleTarget_preserves_self (s : ProcessSysState) (pid : UInt32) :
    (reapExitDeadSingleTarget s pid).selfPid = s.selfPid ∧
    (reapExitDeadSingleTarget s pid).selfUid = s.selfUid := by
  dsimp only [reapExitDeadSingleTarget]
  repeat (first | exact ⟨rfl, rfl⟩ | split)

private theorem reapExitDeadGroup_preserves_self (s : ProcessSysState) (pred : UInt32 → ProcEntry → Bool) :
    (reapExitDeadGroup s pred).selfPid = s.selfPid ∧ (reapExitDeadGroup s pred).selfUid = s.selfUid := by
  unfold reapExitDeadGroup reapActiveLeadersWhere
  dsimp only
  split <;> exact ⟨rfl, rfl⟩

private theorem nonLeaderEsrch_getD_preserves_self (s : ProcessSysState) (tid : UInt32) :
    ((nonLeaderEsrch? s tid).getD s).selfPid = s.selfPid ∧
    ((nonLeaderEsrch? s tid).getD s).selfUid = s.selfUid := by
  unfold nonLeaderEsrch?
  dsimp only
  repeat (first | exact ⟨rfl, rfl⟩ | split)

private theorem esrchPidfdOpenNext_preserves_self (s : ProcessSysState) (pid : UInt32) (f : PidfdOpenFlags) :
    (esrchPidfdOpenNext s pid f).selfPid = s.selfPid ∧ (esrchPidfdOpenNext s pid f).selfUid = s.selfUid := by
  dsimp only [esrchPidfdOpenNext]
  split
  · have h1 := reapExitDeadSingleTarget_preserves_self s pid
    have h2 := nonLeaderEsrch_getD_preserves_self (reapExitDeadSingleTarget s pid) pid
    exact ⟨h2.1.trans h1.1, h2.2.trans h1.2⟩
  · exact ⟨rfl, rfl⟩

private theorem esrchKillNext_preserves_self (s : ProcessSysState) (p : Int32) :
    (esrchKillNext s p).selfPid = s.selfPid ∧ (esrchKillNext s p).selfUid = s.selfUid := by
  dsimp only [esrchKillNext]
  split
  · split
    · have h1 := reapExitDeadSingleTarget_preserves_self s p.toUInt32
      have h2 := nonLeaderEsrch_getD_preserves_self (reapExitDeadSingleTarget s p.toUInt32) p.toUInt32
      exact ⟨h2.1.trans h1.1, h2.2.trans h1.2⟩
    · repeat (first | exact ⟨rfl, rfl⟩ | exact reapExitDeadGroup_preserves_self .. | split)
  · exact ⟨rfl, rfl⟩

private theorem modelOps_pidfd_open_preserves_self (s : ProcessSysState) (pid : UInt32) (f : PidfdOpenFlags) :
    ((modelOps.pidfd_open pid f).run s).2.selfPid = s.selfPid ∧
    ((modelOps.pidfd_open pid f).run s).2.selfUid = s.selfUid := by
  dsimp only [modelOps, StateT.run, get, getThe, MonadStateOf.get, StateT.get,
    set, pure, Pure.pure, bind, Bind.bind, StateT.bind, StateT.pure, StateT.set, commitPidfd]
  cases checkPidfdOpenTarget s pid f with
  | ok _ => exact ⟨rfl, rfl⟩
  | error e =>
    by_cases hesrch : e == Errno.ESRCH
    · simp only [hesrch, ↓reduceIte]; exact esrchPidfdOpenNext_preserves_self s pid f
    · simp only [hesrch, Bool.false_eq_true, ↓reduceIte]; exact ⟨rfl, rfl⟩

/-- `getpid` and `getuid` return positive bounded IDs without mutating state and stay stable. -/
theorem process_ops_getpidAndGetuid_consistentAndPositive_allPass :
    AllPass (test_process_ops_getpidAndGetuid_consistentAndPositive modelOps) := by
  intro s0
  have hb := effectiveSelfPid_bounds s0
  have hgetpid : ∀ st, modelOps.getpid.run st = (.ok (effectiveSelfPid st), st) := fun _ => rfl
  have hgetuid : ∀ st, modelOps.getuid.run st = (.ok st.selfUid, st) := fun _ => rfl
  let s3 := ((modelOps.pipe2 {}).run s0).2
  let s4 := ((modelOps.kill (effectiveSelfPid s0).toInt32 .sigzero).run s3).2
  let s5 := ((modelOps.pidfd_open (effectiveSelfPid s0) { nonblock := true }).run s4).2
  have hs3 := modelOps_pipe2_preserves_self s0 {}
  have hs4 : s4.selfPid = s3.selfPid ∧ s4.selfUid = s3.selfUid := by
    dsimp only [s4, modelOps, StateT.run, get, getThe, MonadStateOf.get, StateT.get,
      set, StateT.set, pure, Pure.pure, StateT.pure, bind, Bind.bind, StateT.bind]
    cases he : evalKill s3 (effectiveSelfPid s0).toInt32 .sigzero with
    | ok s' => exact evalKill_preserves_self s3 _ .sigzero s' he
    | error e =>
      by_cases hesrch : e == Errno.ESRCH
      · simp only [hesrch, ↓reduceIte]; exact esrchKillNext_preserves_self s3 _
      · simp only [hesrch, Bool.false_eq_true, ↓reduceIte]; exact ⟨rfl, rfl⟩
  have hs5 := modelOps_pidfd_open_preserves_self s4 (effectiveSelfPid s0) { nonblock := true }
  have hp5 : s5.selfPid = s0.selfPid := by
    rw [hs5.1, hs4.1, hs3.1]
  have hEff : effectiveSelfPid s5 = effectiveSelfPid s0 := by
    simp [effectiveSelfPid, hp5]
  have hUid : s5.selfUid = s0.selfUid := by
    rw [hs5.2, hs4.2, hs3.2]
  dsimp only [test_process_ops_getpidAndGetuid_consistentAndPositive, AllPass,
    NondetTest.nondet, NondetTest.assert, Bind.bind, Pure.pure]
  rw [hgetpid s0]
  dsimp only
  rw [hgetuid s0]
  dsimp only
  rw [show StateT.run (modelOps.pipe2 { }) s0 =
    ((StateT.run (modelOps.pipe2 { }) s0).1, s3) from rfl]
  dsimp only
  rw [show StateT.run (modelOps.kill (effectiveSelfPid s0).toInt32 Signal.sigzero) s3 =
    ((StateT.run (modelOps.kill (effectiveSelfPid s0).toInt32 Signal.sigzero) s3).1, s4) from rfl]
  dsimp only
  rw [show StateT.run (modelOps.pidfd_open (effectiveSelfPid s0) { nonblock := true }) s4 =
    ((StateT.run (modelOps.pidfd_open (effectiveSelfPid s0) { nonblock := true }) s4).1, s5) from rfl]
  dsimp only
  rw [hgetpid s5]
  dsimp only
  rw [hgetuid s5]
  dsimp only
  exact ⟨⟨hb.1, hb.2, rfl, rfl⟩, ⟨rfl, rfl⟩, ⟨congrArg Except.ok hEff, congrArg Except.ok hUid, rfl, rfl⟩, trivial⟩

/-- Structural wiring proof: `Interface.defaultOps` is constructed via `Internal.mkProcessOps` and every wrapper (both explicit-flag and default-flag) delegates directly to it. -/
theorem process_interface_defaultOpsWiring_allPass :
    AllPass (test_process_interface_defaultOpsWiring defaultOps) := by
  dsimp only [AllPass, test_process_interface_defaultOpsWiring, Pure.pure, assert]
  exact ⟨⟨_, rfl⟩, (fun _ => rfl), rfl, (fun _ _ => rfl), (fun _ => rfl),
    (fun _ _ => rfl), (fun _ _ => rfl), (fun _ => rfl), (fun _ _ _ => rfl), (fun _ _ => rfl),
    rfl, rfl, trivial⟩

end LeanSwe.LinuxSyscall.Process
