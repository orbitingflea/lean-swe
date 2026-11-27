import Core.Obeys
import LeanSwe.LinuxSyscall.Process.Impl
import LeanSwe.LinuxSyscall.Process.Interface
import LeanSweProofs.LinuxSyscall.Process.Model.Refines
import LeanSweProofs.LinuxSyscall.Process.Proofs.HealthyStep

/-!
# Raw-to-Package `Core.ObeysStepFrom` Proofs for `LeanSwe.LinuxSyscall.Process`

Proves wire-decoder round-trips and `mkProcessOps_obeysStepFrom` for
`LeanSwe.LinuxSyscall.Process.Proofs`.
-/

namespace LeanSwe.LinuxSyscall.Process.Proofs

open LeanSwe.LinuxSyscall
open LeanSwe.LinuxSyscall.Process

/-- Unfold `StateT.bind` on `StateM W`. -/
@[simp] theorem stateT_bind_eq {W α β : Type} (x : StateM W α) (f : α → StateM W β) (w : W) :
    StateT.bind x f w = f (x w).1 (x w).2 := rfl

/-- Unfold `StateT.pure` on `StateM W`. -/
@[simp] theorem stateT_pure_eq {W α : Type} (a : α) (w : W) :
    StateT.pure (m := Id) a w = (a, w) := rfl

/-- Unfold `StateT.map` on `StateM W`. -/
@[simp] theorem stateT_map_eq {W α β : Type} (g : α → β) (x : StateM W α) (w : W) :
    StateT.map g x w = (g (x w).1, (x w).2) := rfl

private theorem ui64_or_and_distrib (x y m : UInt64) :
    (x ||| y) &&& m = (x &&& m) ||| (y &&& m) := by
  apply UInt64.toNat_inj.mp
  rw [UInt64.toNat_and, UInt64.toNat_or, UInt64.toNat_or, UInt64.toNat_and, UInt64.toNat_and]
  exact Nat.and_or_distrib_right x.toNat y.toNat m.toNat

private theorem ui64_or_rshift_distrib (a b s : UInt64) :
    (a ||| b) >>> s = (a >>> s) ||| (b >>> s) := by
  apply UInt64.toNat_inj.mp
  rw [UInt64.toNat_shiftRight, UInt64.toNat_or, UInt64.toNat_or,
    UInt64.toNat_shiftRight, UInt64.toNat_shiftRight]
  apply Nat.eq_of_testBit_eq
  intro i
  simp [Nat.testBit_shiftRight, Nat.testBit_or]

private theorem ui64_or_zero (x : UInt64) : x ||| 0 = x := by
  apply UInt64.toNat_inj.mp; simp

private theorem ui64_zero_or (x : UInt64) : 0 ||| x = x := by
  apply UInt64.toNat_inj.mp; simp

private theorem ui64_shift_u32_and_low (x : UInt32) (shift mask : UInt64)
    (hs : 1 ≤ shift.toNat ∧ shift.toNat ≤ 6) (hm : mask.toNat < 2 ^ shift.toNat) :
    (x.toUInt64 <<< shift) &&& mask = 0 := by
  apply UInt64.toNat_inj.mp
  have hx : x.toNat < 2 ^ 32 := x.toNat_lt
  rw [UInt64.toNat_and, UInt64.toNat_shiftLeft, UInt32.toNat_toUInt64]
  have hsMod : shift.toNat % 64 = shift.toNat := Nat.mod_eq_of_lt (by omega)
  rw [hsMod, Nat.shiftLeft_eq]
  have hpow : 2 ^ shift.toNat ≤ 64 :=
    Nat.le_trans (Nat.pow_le_pow_right (by decide : 0 < 2) hs.2) (by decide : 2 ^ 6 ≤ 64)
  have hmul : x.toNat * 2 ^ shift.toNat < 2 ^ 64 := by
    have := Nat.mul_le_mul_left x.toNat hpow; omega
  rw [Nat.mod_eq_of_lt hmul]
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_and]
  have hz : (UInt64.toNat 0).testBit i = false := by simp
  rw [hz]
  by_cases hi : i < shift.toNat
  · rw [← Nat.shiftLeft_eq, Nat.testBit_shiftLeft]
    have hlt : ¬ (shift.toNat ≤ i) := by omega
    simp [hlt]
  · have hge : 2 ^ shift.toNat ≤ 2 ^ i := Nat.pow_le_pow_right (by decide) (by omega)
    have hMaskLt : mask.toNat < 2 ^ i := Nat.lt_of_lt_of_le hm hge
    rw [Nat.testBit_lt_two_pow hMaskLt, Bool.and_false]

private theorem ui64_shift_u32_rshift_self (k : UInt64) (hk : k.toNat ≤ 6) (x : UInt32) :
    ((x.toUInt64 <<< k) >>> k).toUInt32 = x := by
  have hEq : (x.toUInt64 <<< k) >>> k = x.toUInt64 := by
    apply UInt64.toNat_inj.mp
    have hx : x.toNat < 2 ^ 32 := x.toNat_lt
    rw [UInt64.toNat_shiftRight, UInt64.toNat_shiftLeft, UInt32.toNat_toUInt64]
    have hkMod : k.toNat % 64 = k.toNat := Nat.mod_eq_of_lt (by omega)
    rw [hkMod, Nat.shiftLeft_eq]
    have hpow : 2 ^ k.toNat ≤ 64 :=
      Nat.le_trans (Nat.pow_le_pow_right (by decide : 0 < 2) hk) (by decide : 2 ^ 6 ≤ 64)
    have hmul : x.toNat * 2 ^ k.toNat < 2 ^ 64 := by
      have := Nat.mul_le_mul_left x.toNat hpow; omega
    rw [Nat.mod_eq_of_lt hmul, Nat.shiftRight_eq_div_pow,
      Nat.mul_div_cancel _ (Nat.two_pow_pos k.toNat)]
  rw [hEq]
  apply UInt32.toNat_inj.mp
  simp [UInt64.toUInt32, UInt32.toNat_toUInt64]

private theorem ui64_shift_u32_rshift_top (k top : UInt64)
    (hk : k.toNat ≤ 6) (ht : top.toNat = k.toNat + 32) (x : UInt32) :
    (x.toUInt64 <<< k) >>> top = 0 := by
  apply UInt64.toNat_inj.mp
  have hx : x.toNat < 2 ^ 32 := x.toNat_lt
  rw [UInt64.toNat_shiftRight, UInt64.toNat_shiftLeft, UInt32.toNat_toUInt64]
  have hkMod : k.toNat % 64 = k.toNat := Nat.mod_eq_of_lt (by omega)
  have htMod : top.toNat % 64 = top.toNat := Nat.mod_eq_of_lt (by omega)
  rw [hkMod, htMod, ht, Nat.shiftLeft_eq]
  have hpow : 2 ^ k.toNat ≤ 64 :=
    Nat.le_trans (Nat.pow_le_pow_right (by decide : 0 < 2) hk) (by decide : 2 ^ 6 ≤ 64)
  have hmul : x.toNat * 2 ^ k.toNat < 2 ^ 64 := by
    have := Nat.mul_le_mul_left x.toNat hpow; omega
  rw [Nat.mod_eq_of_lt hmul, Nat.shiftRight_eq_div_pow, Nat.pow_add, Nat.mul_comm (2 ^ k.toNat)]
  have hlt : x.toNat * 2 ^ k.toNat < 2 ^ 32 * 2 ^ k.toNat :=
    Nat.mul_lt_mul_of_pos_right hx (Nat.two_pow_pos k.toNat)
  exact Nat.div_eq_of_lt hlt

private theorem decodeRawPipeFlags?_toBits (f : PipeFlags) :
    Model.decodeRawPipeFlags? f.toBits = some f := by
  rcases f with ⟨b0, b1, b2, b3, ex⟩
  let bit (b : Bool) (s : UInt64) : UInt64 := if b then ((1 : UInt64) <<< s) else 0
  let lo : UInt64 := bit b0 0 ||| bit b1 1 ||| bit b2 2 ||| bit b3 3
  have hBits : PipeFlags.toBits
      { cloexec := b0, nonblock := b1, direct := b2, notificationPipe := b3, extraBits := ex } =
      lo ||| (ex.toUInt64 <<< 4) := rfl
  rw [hBits]
  unfold Model.decodeRawPipeFlags?
  have hLoTop : lo >>> 36 = 0 := by
    dsimp only [lo, bit]; cases b0 <;> cases b1 <;> cases b2 <;> cases b3 <;> decide
  have hLoSh : lo >>> 4 = 0 := by
    dsimp only [lo, bit]; cases b0 <;> cases b1 <;> cases b2 <;> cases b3 <;> decide
  have hTop : (lo ||| (ex.toUInt64 <<< 4)) >>> 36 = 0 := by
    rw [ui64_or_rshift_distrib, hLoTop, ui64_shift_u32_rshift_top 4 36 (by decide) rfl ex, ui64_zero_or]
  have hEx : ((lo ||| (ex.toUInt64 <<< 4)) >>> 4).toUInt32 = ex := by
    rw [ui64_or_rshift_distrib, hLoSh, ui64_zero_or]
    exact ui64_shift_u32_rshift_self 4 (by decide) ex
  have hAnd1 : (lo ||| (ex.toUInt64 <<< 4)) &&& 1 = lo &&& 1 := by
    rw [ui64_or_and_distrib, ui64_shift_u32_and_low ex 4 1 (by decide) (by decide), ui64_or_zero]
  have hAnd2 : (lo ||| (ex.toUInt64 <<< 4)) &&& 2 = lo &&& 2 := by
    rw [ui64_or_and_distrib, ui64_shift_u32_and_low ex 4 2 (by decide) (by decide), ui64_or_zero]
  have hAnd4 : (lo ||| (ex.toUInt64 <<< 4)) &&& 4 = lo &&& 4 := by
    rw [ui64_or_and_distrib, ui64_shift_u32_and_low ex 4 4 (by decide) (by decide), ui64_or_zero]
  have hAnd8 : (lo ||| (ex.toUInt64 <<< 4)) &&& 8 = lo &&& 8 := by
    rw [ui64_or_and_distrib, ui64_shift_u32_and_low ex 4 8 (by decide) (by decide), ui64_or_zero]
  rw [hTop]
  simp only [beq_self_eq_true, ↓reduceIte, hAnd1, hAnd2, hAnd4, hAnd8, hEx, Option.some.injEq]
  dsimp only [lo, bit]
  cases b0 <;> cases b1 <;> cases b2 <;> cases b3 <;> rfl

private theorem decodeRawWaitFlags?_toBits (f : WaitFlags) :
    Model.decodeRawWaitFlags? f.toBits = some f := by
  rcases f with ⟨b0, b1, b2, b3, b4, b5, ex⟩
  let bit (b : Bool) (s : UInt64) : UInt64 := if b then ((1 : UInt64) <<< s) else 0
  let lo : UInt64 :=
    bit b0 0 ||| bit b1 1 ||| bit b2 2 ||| bit b3 3 ||| bit b4 4 ||| bit b5 5
  have hBits : WaitFlags.toBits
      { nohang := b0, untraced := b1, continued := b2, wall := b3,
        wclone := b4, wnothread := b5, extraBits := ex } =
      lo ||| (ex.toUInt64 <<< 6) := rfl
  rw [hBits]
  unfold Model.decodeRawWaitFlags?
  have hLoTop : lo >>> 38 = 0 := by
    dsimp only [lo, bit]
    cases b0 <;> cases b1 <;> cases b2 <;> cases b3 <;> cases b4 <;> cases b5 <;> decide
  have hLoSh : lo >>> 6 = 0 := by
    dsimp only [lo, bit]
    cases b0 <;> cases b1 <;> cases b2 <;> cases b3 <;> cases b4 <;> cases b5 <;> decide
  have hTop : (lo ||| (ex.toUInt64 <<< 6)) >>> 38 = 0 := by
    rw [ui64_or_rshift_distrib, hLoTop, ui64_shift_u32_rshift_top 6 38 (by decide) rfl ex, ui64_zero_or]
  have hEx : ((lo ||| (ex.toUInt64 <<< 6)) >>> 6).toUInt32 = ex := by
    rw [ui64_or_rshift_distrib, hLoSh, ui64_zero_or]
    exact ui64_shift_u32_rshift_self 6 (by decide) ex
  have h1 : (lo ||| (ex.toUInt64 <<< 6)) &&& 1 = lo &&& 1 := by
    rw [ui64_or_and_distrib, ui64_shift_u32_and_low ex 6 1 (by decide) (by decide), ui64_or_zero]
  have h2 : (lo ||| (ex.toUInt64 <<< 6)) &&& 2 = lo &&& 2 := by
    rw [ui64_or_and_distrib, ui64_shift_u32_and_low ex 6 2 (by decide) (by decide), ui64_or_zero]
  have h4 : (lo ||| (ex.toUInt64 <<< 6)) &&& 4 = lo &&& 4 := by
    rw [ui64_or_and_distrib, ui64_shift_u32_and_low ex 6 4 (by decide) (by decide), ui64_or_zero]
  have h8 : (lo ||| (ex.toUInt64 <<< 6)) &&& 8 = lo &&& 8 := by
    rw [ui64_or_and_distrib, ui64_shift_u32_and_low ex 6 8 (by decide) (by decide), ui64_or_zero]
  have h16 : (lo ||| (ex.toUInt64 <<< 6)) &&& 16 = lo &&& 16 := by
    rw [ui64_or_and_distrib, ui64_shift_u32_and_low ex 6 16 (by decide) (by decide), ui64_or_zero]
  have h32 : (lo ||| (ex.toUInt64 <<< 6)) &&& 32 = lo &&& 32 := by
    rw [ui64_or_and_distrib, ui64_shift_u32_and_low ex 6 32 (by decide) (by decide), ui64_or_zero]
  rw [hTop]
  simp only [beq_self_eq_true, ↓reduceIte, h1, h2, h4, h8, h16, h32, hEx, Option.some.injEq]
  dsimp only [lo, bit]
  cases b0 <;> cases b1 <;> cases b2 <;> cases b3 <;> cases b4 <;> cases b5 <;> rfl

private theorem decodeRawSignal?_toRaw (s : Signal) :
    Model.decodeRawSignal? s.toRaw.1 s.toRaw.2 = some s := by
  cases s <;> rfl

private theorem decodeRawPidfdOpenFlags?_toBits (f : PidfdOpenFlags) :
    Model.decodeRawPidfdOpenFlags? f.toBits = some f := by
  rcases f with ⟨b0, b1, ex⟩
  let bit (b : Bool) (s : UInt64) : UInt64 := if b then ((1 : UInt64) <<< s) else 0
  let lo : UInt64 := bit b0 0 ||| bit b1 1
  have hBits : PidfdOpenFlags.toBits { nonblock := b0, thread := b1, extraBits := ex } =
      lo ||| (ex.toUInt64 <<< 2) := rfl
  rw [hBits]
  unfold Model.decodeRawPidfdOpenFlags?
  have hLoTop : lo >>> 34 = 0 := by dsimp only [lo, bit]; cases b0 <;> cases b1 <;> decide
  have hLoSh : lo >>> 2 = 0 := by dsimp only [lo, bit]; cases b0 <;> cases b1 <;> decide
  have hTop : (lo ||| (ex.toUInt64 <<< 2)) >>> 34 = 0 := by
    rw [ui64_or_rshift_distrib, hLoTop, ui64_shift_u32_rshift_top 2 34 (by decide) rfl ex, ui64_zero_or]
  have hEx : ((lo ||| (ex.toUInt64 <<< 2)) >>> 2).toUInt32 = ex := by
    rw [ui64_or_rshift_distrib, hLoSh, ui64_zero_or]
    exact ui64_shift_u32_rshift_self 2 (by decide) ex
  have h1 : (lo ||| (ex.toUInt64 <<< 2)) &&& 1 = lo &&& 1 := by
    rw [ui64_or_and_distrib, ui64_shift_u32_and_low ex 2 1 (by decide) (by decide), ui64_or_zero]
  have h2 : (lo ||| (ex.toUInt64 <<< 2)) &&& 2 = lo &&& 2 := by
    rw [ui64_or_and_distrib, ui64_shift_u32_and_low ex 2 2 (by decide) (by decide), ui64_or_zero]
  rw [hTop]
  simp only [beq_self_eq_true, ↓reduceIte, h1, h2, hEx, Option.some.injEq]
  dsimp only [lo, bit]
  cases b0 <;> cases b1 <;> rfl

private theorem decodeRawPidfdSignalFlags?_toBits (f : PidfdSignalFlags) :
    Model.decodeRawPidfdSignalFlags? f.toBits = some f := by
  rcases f with ⟨b0, b1, b2, ex⟩
  let bit (b : Bool) (s : UInt64) : UInt64 := if b then ((1 : UInt64) <<< s) else 0
  let lo : UInt64 := bit b0 0 ||| bit b1 1 ||| bit b2 2
  have hBits : PidfdSignalFlags.toBits
      { thread := b0, threadGroup := b1, processGroup := b2, extraBits := ex } =
      lo ||| (ex.toUInt64 <<< 3) := rfl
  rw [hBits]
  unfold Model.decodeRawPidfdSignalFlags?
  have hLoTop : lo >>> 35 = 0 := by
    dsimp only [lo, bit]; cases b0 <;> cases b1 <;> cases b2 <;> decide
  have hLoSh : lo >>> 3 = 0 := by
    dsimp only [lo, bit]; cases b0 <;> cases b1 <;> cases b2 <;> decide
  have hTop : (lo ||| (ex.toUInt64 <<< 3)) >>> 35 = 0 := by
    rw [ui64_or_rshift_distrib, hLoTop, ui64_shift_u32_rshift_top 3 35 (by decide) rfl ex, ui64_zero_or]
  have hEx : ((lo ||| (ex.toUInt64 <<< 3)) >>> 3).toUInt32 = ex := by
    rw [ui64_or_rshift_distrib, hLoSh, ui64_zero_or]
    exact ui64_shift_u32_rshift_self 3 (by decide) ex
  have h1 : (lo ||| (ex.toUInt64 <<< 3)) &&& 1 = lo &&& 1 := by
    rw [ui64_or_and_distrib, ui64_shift_u32_and_low ex 3 1 (by decide) (by decide), ui64_or_zero]
  have h2 : (lo ||| (ex.toUInt64 <<< 3)) &&& 2 = lo &&& 2 := by
    rw [ui64_or_and_distrib, ui64_shift_u32_and_low ex 3 2 (by decide) (by decide), ui64_or_zero]
  have h4 : (lo ||| (ex.toUInt64 <<< 3)) &&& 4 = lo &&& 4 := by
    rw [ui64_or_and_distrib, ui64_shift_u32_and_low ex 3 4 (by decide) (by decide), ui64_or_zero]
  rw [hTop]
  simp only [beq_self_eq_true, ↓reduceIte, h1, h2, h4, hEx, Option.some.injEq]
  dsimp only [lo, bit]
  cases b0 <;> cases b1 <;> cases b2 <;> rfl

private theorem healthyStep_nptl_einval {env : HealthyEnv} {req : ProcessReq}
    (hWf : env.wf = true)
    (hPre : validateReqBeforeKernel env.state req = some Errno.EINVAL) :
    healthyStep env req (.err Errno.EINVAL) = some env := by
  rcases env with ⟨st, budget⟩
  unfold healthyStep allowedStep
  have hNoCrit : isCriticalFault (.err Errno.EINVAL) = false := by decide
  have hNoEi : isEintrOutcome (.err Errno.EINVAL) = false := by decide
  simp [hWf, hNoCrit, hNoEi, hPre]

/-- `Internal.mkProcessOps` lifts any raw C-ABI bundle obeying `Model.allowedRawStep` to `Model.allowedSingleStep`. -/
theorem mkProcessOps_obeysSingleStep :
    Core.ObeysStepFrom id HealthyEnv.wf Model.execRawStep Model.allowedRawStep
      HealthyEnv.wf Internal.mkProcessOps Model.execSingleStep Model.allowedSingleStep := by
  intro W proj raw hRaw w req hWf
  dsimp only [Function.comp, id] at hWf ⊢
  cases req with
  | pipe2 flags =>
    have hStep := hRaw w (.pipe2 flags.toBits) hWf
    simp only [Model.execRawStep, Model.allowedRawStep, Model.decodeRawProcessReq?,
      Model.execSingleStep, execProcessReq, Internal.mkProcessOps, Functor.map, Bind.bind, Pure.pure,
      StateT.run, stateT_bind_eq, stateT_pure_eq, stateT_map_eq, Model.allowedSingleStep,
      decodeRawPipeFlags?_toBits] at hStep ⊢
    rcases hCall : raw.pipe2 flags.toBits w with ⟨res, w'⟩
    try rw [hCall] at hStep
    cases res with
    | ok p => rcases p with ⟨r, wr⟩; simpa [Model.outcomeOfRawPiped, Model.toModelOutcome, outcomeOfPiped] using hStep
    | error e => simpa [Model.outcomeOfRawPiped, Model.toModelOutcome, outcomeOfPiped] using hStep
  | waitpid pid flags =>
    have hStep := hRaw w (.waitpid pid flags.toBits) hWf
    simp only [Model.execRawStep, Model.allowedRawStep, Model.decodeRawProcessReq?,
      Model.execSingleStep, execProcessReq, Internal.mkProcessOps, Functor.map, Bind.bind, Pure.pure,
      StateT.run, stateT_bind_eq, stateT_map_eq, Model.allowedSingleStep,
      decodeRawWaitFlags?_toBits] at hStep ⊢
    rcases hCall : raw.waitpid pid flags.toBits w with ⟨res, w'⟩
    try rw [hCall] at hStep
    cases res <;>
      simpa [Model.outcomeOfRawWaited, Model.toModelOutcome, outcomeOfWaited] using hStep
  | kill pid sig =>
    cases hNptl : sig.isNptlReserved with
    | true =>
      simp only [Model.execSingleStep, execProcessReq, Internal.mkProcessOps,
        Bind.bind, Pure.pure, StateT.run, stateT_bind_eq, stateT_pure_eq,
        Model.allowedSingleStep, hNptl, ↓reduceIte, outcomeOfUnit]
      exact healthyStep_nptl_einval hWf (by simp [validateReqBeforeKernel, hNptl])
    | false =>
      have hStep := hRaw w (.kill pid sig.toRaw.1 sig.toRaw.2) hWf
      simp only [Model.execRawStep, Model.allowedRawStep, Model.decodeRawProcessReq?,
        Model.execSingleStep, execProcessReq, Internal.mkProcessOps, Functor.map, Bind.bind, Pure.pure,
        StateT.run, stateT_bind_eq, stateT_pure_eq, stateT_map_eq, Model.allowedSingleStep,
        hNptl, Bool.false_eq_true, ↓reduceIte, decodeRawSignal?_toRaw] at hStep ⊢
      rcases hCall : raw.kill pid sig.toRaw.1 sig.toRaw.2 w with ⟨res, w'⟩
      try rw [hCall] at hStep
      cases res <;>
        simpa [Model.outcomeOfRawUnit, Model.toModelOutcome, outcomeOfUnit] using hStep
  | pidfd_open pid flags =>
    have hStep := hRaw w (.pidfd_open pid flags.toBits) hWf
    simp only [Model.execRawStep, Model.allowedRawStep, Model.decodeRawProcessReq?,
      Model.execSingleStep, execProcessReq, Internal.mkProcessOps, Functor.map, Bind.bind, Pure.pure,
      StateT.run, stateT_bind_eq, stateT_pure_eq, stateT_map_eq, Model.allowedSingleStep,
      decodeRawPidfdOpenFlags?_toBits] at hStep ⊢
    rcases hCall : raw.pidfd_open pid flags.toBits w with ⟨res, w'⟩
    try rw [hCall] at hStep
    cases res <;>
      simpa [Model.outcomeOfRawOpened, Model.toModelOutcome, outcomeOfOpened] using hStep
  | pidfd_send_signal hid sig flags =>
    cases hNptl : sig.isNptlReserved with
    | true =>
      simp only [Model.execSingleStep, execProcessReq, Internal.mkProcessOps,
        Bind.bind, Pure.pure, StateT.run, stateT_bind_eq, stateT_pure_eq,
        Model.allowedSingleStep, hNptl, ↓reduceIte, outcomeOfUnit]
      exact healthyStep_nptl_einval hWf (by simp [validateReqBeforeKernel, hNptl])
    | false =>
      have hStep := hRaw w (.pidfd_send_signal hid sig.toRaw.1 sig.toRaw.2 flags.toBits) hWf
      simp only [Model.execRawStep, Model.allowedRawStep, Model.decodeRawProcessReq?,
        Model.execSingleStep, execProcessReq, Internal.mkProcessOps, Functor.map, Bind.bind, Pure.pure,
        StateT.run, stateT_bind_eq, stateT_pure_eq, stateT_map_eq, Model.allowedSingleStep,
        hNptl, Bool.false_eq_true, ↓reduceIte, decodeRawSignal?_toRaw,
        decodeRawPidfdSignalFlags?_toBits] at hStep ⊢
      rcases hCall : raw.pidfd_send_signal hid sig.toRaw.1 sig.toRaw.2 flags.toBits w with ⟨res, w'⟩
      try rw [hCall] at hStep
      cases res <;>
        simpa [Model.outcomeOfRawUnit, Model.toModelOutcome, outcomeOfUnit] using hStep
  | getpid =>
    have hStep := hRaw w .getpid hWf
    simp only [Model.execRawStep, Model.allowedRawStep, Model.decodeRawProcessReq?,
      Model.execSingleStep, execProcessReq, Internal.mkProcessOps, Functor.map, Bind.bind, Pure.pure,
      StateT.run, stateT_bind_eq, stateT_pure_eq, stateT_map_eq, Model.allowedSingleStep] at hStep ⊢
    rcases hCall : raw.getpid w with ⟨res, w'⟩
    try rw [hCall] at hStep
    cases res <;>
      simpa [Model.outcomeOfRawU32, Model.toModelOutcome, outcomeOfU32] using hStep
  | getuid =>
    have hStep := hRaw w .getuid hWf
    simp only [Model.execRawStep, Model.allowedRawStep, Model.decodeRawProcessReq?,
      Model.execSingleStep, execProcessReq, Internal.mkProcessOps, Functor.map, Bind.bind, Pure.pure,
      StateT.run, stateT_bind_eq, stateT_pure_eq, stateT_map_eq, Model.allowedSingleStep] at hStep ⊢
    rcases hCall : raw.getuid w with ⟨res, w'⟩
    try rw [hCall] at hStep
    cases res <;>
      simpa [Model.outcomeOfRawU32, Model.toModelOutcome, outcomeOfU32] using hStep

end LeanSwe.LinuxSyscall.Process.Proofs
