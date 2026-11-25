import Core.Obeys
import LeanSwe.LinuxSyscall.Files.Impl
import LeanSwe.LinuxSyscall.Files.Interface
import LeanSwe.LinuxSyscall.Files.Model.Refines
import LeanSwe.LinuxSyscall.Files.Proofs.HealthyStep

/-!
# Raw-to-Package `Core.ObeysStepFrom` Proofs for `LeanSwe.LinuxSyscall.Files`

Proves wire-decoder round-trips and `mkFilesOpsM_obeysStepFrom` for
`LeanSwe.LinuxSyscall.Files.Proofs`.
-/

namespace LeanSwe.LinuxSyscall.Files.Proofs

open LeanSwe.LinuxSyscall
open LeanSwe.LinuxSyscall.Files

@[simp] theorem stateT_bind_eq {W α β : Type} (x : StateM W α) (f : α → StateM W β) (w : W) :
    StateT.bind x f w = f (x w).1 (x w).2 := rfl

@[simp] theorem stateT_pure_eq {W α : Type} (a : α) (w : W) :
    StateT.pure (m := Id) a w = (a, w) := rfl

@[simp] theorem stateT_map_eq {W α β : Type} (g : α → β) (x : StateM W α) (w : W) :
    StateT.map g x w = (g (x w).1, (x w).2) := rfl

/-- `Model.execPkgStep` agrees with `execFilesReq` on `StateM W`. -/
@[simp] theorem execPkgStep_eq {W : Type} (ops : Model.HandleFilesOpsM (StateM W)) (req : FilesReq) :
    Model.execPkgStep ops req = execFilesReq ops req := by
  cases req <;> rfl

private theorem ui32_or_and_distrib (x y m : UInt32) :
    (x ||| y) &&& m = (x &&& m) ||| (y &&& m) := by
  apply UInt32.toNat_inj.mp
  rw [UInt32.toNat_and, UInt32.toNat_or, UInt32.toNat_or, UInt32.toNat_and, UInt32.toNat_and]
  exact Nat.and_or_distrib_right x.toNat y.toNat m.toNat

private theorem ui32_or_lt_pow2 {a b : UInt32} {k : Nat}
    (ha : a.toNat < 2 ^ k) (hb : b.toNat < 2 ^ k) :
    (a ||| b).toNat < 2 ^ k := by
  rw [UInt32.toNat_or]
  exact Nat.or_lt_two_pow ha hb

private theorem ui32_or_assoc (a b c : UInt32) : (a ||| b) ||| c = a ||| (b ||| c) := by
  apply UInt32.toNat_inj.mp
  simp only [UInt32.toNat_or]
  apply Nat.eq_of_testBit_eq
  intro i
  simp [Nat.testBit_or, Bool.or_assoc]

private theorem decodeRawOpenFlags?_toBits (f : OpenFlags) :
    Model.decodeRawOpenFlags? f.toBits = some f := by
  rcases f with ⟨acc, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11⟩
  let accBits : UInt32 := match acc with | .rdonly => 0 | .wronly => 1 | .rdwr => 2
  let bit (b : Bool) (s : UInt32) : UInt32 := if b then ((1 : UInt32) <<< s) else 0
  let lo : UInt32 := accBits ||| bit b2 2 ||| bit b3 3 ||| bit b4 4 ||| bit b5 5
  let hi : UInt32 :=
    bit b6 6 ||| bit b7 7 ||| bit b8 8 ||| bit b9 9 ||| bit b10 10 ||| bit b11 11
  have hAssoc :
      (OpenFlags.mk acc b2 b3 b4 b5 b6 b7 b8 b9 b10 b11).toBits = lo ||| hi := by
    unfold OpenFlags.toBits
    dsimp only [lo, hi, accBits, bit]
    cases acc <;> simp only [ui32_or_assoc]
  rw [hAssoc]
  unfold Model.decodeRawOpenFlags?
  have hLoLt : lo.toNat < 2 ^ 12 := by
    dsimp only [lo, accBits, bit]
    cases acc <;> cases b2 <;> cases b3 <;> cases b4 <;> cases b5 <;> decide
  have hHiLt : hi.toNat < 2 ^ 12 := by
    dsimp only [hi, bit]
    cases b6 <;> cases b7 <;> cases b8 <;> cases b9 <;> cases b10 <;> cases b11 <;> decide
  have hLt : lo ||| hi < 4096 := ui32_or_lt_pow2 hLoLt hHiLt
  have hHiLo0 : ∀ m : UInt32, 0xffc0 &&& m = 0 → (lo ||| hi) &&& m = lo &&& m := by
    intro m hm
    rw [ui32_or_and_distrib]
    have hHiM : hi &&& m = 0 := by
      have hHiSub : hi &&& 0xffc0 = hi := by
        dsimp only [hi, bit]
        cases b6 <;> cases b7 <;> cases b8 <;> cases b9 <;> cases b10 <;> cases b11 <;> decide
      rw [← hHiSub]
      apply UInt32.toNat_inj.mp
      rw [UInt32.toNat_and, UInt32.toNat_and, Nat.and_assoc, ← UInt32.toNat_and, hm]
      simp
    rw [hHiM]
    apply UInt32.toNat_inj.mp; simp
  have hLoHi0 : ∀ m : UInt32, 0x3f &&& m = 0 → (lo ||| hi) &&& m = hi &&& m := by
    intro m hm
    rw [ui32_or_and_distrib]
    have hLoM : lo &&& m = 0 := by
      have hLoSub : lo &&& 0x3f = lo := by
        dsimp only [lo, accBits, bit]
        cases acc <;> cases b2 <;> cases b3 <;> cases b4 <;> cases b5 <;> decide
      rw [← hLoSub]
      apply UInt32.toNat_inj.mp
      rw [UInt32.toNat_and, UInt32.toNat_and, Nat.and_assoc, ← UInt32.toNat_and, hm]
      simp
    rw [hLoM]
    apply UInt32.toNat_inj.mp; simp
  simp only [hLt, ↓reduceIte,
    hHiLo0 3 (by decide),
    hHiLo0 ((1 : UInt32) <<< 2) (by decide), hHiLo0 ((1 : UInt32) <<< 3) (by decide),
    hHiLo0 ((1 : UInt32) <<< 4) (by decide), hHiLo0 ((1 : UInt32) <<< 5) (by decide),
    hLoHi0 ((1 : UInt32) <<< 6) (by decide), hLoHi0 ((1 : UInt32) <<< 7) (by decide),
    hLoHi0 ((1 : UInt32) <<< 8) (by decide), hLoHi0 ((1 : UInt32) <<< 9) (by decide),
    hLoHi0 ((1 : UInt32) <<< 10) (by decide), hLoHi0 ((1 : UInt32) <<< 11) (by decide)]
  have hAcc : Model.decodeRawAccessMode? (lo &&& 3) = some acc := by
    dsimp only [lo, accBits, bit]
    cases acc <;> cases b2 <;> cases b3 <;> cases b4 <;> cases b5 <;> rfl
  have hLoBits :
      ((lo &&& ((1 : UInt32) <<< 2)) != 0) = b2 ∧ ((lo &&& ((1 : UInt32) <<< 3)) != 0) = b3 ∧
      ((lo &&& ((1 : UInt32) <<< 4)) != 0) = b4 ∧ ((lo &&& ((1 : UInt32) <<< 5)) != 0) = b5 := by
    dsimp only [lo, accBits, bit]
    cases acc <;> cases b2 <;> cases b3 <;> cases b4 <;> cases b5 <;> decide
  have hHiBits :
      ((hi &&& ((1 : UInt32) <<< 6)) != 0) = b6 ∧ ((hi &&& ((1 : UInt32) <<< 7)) != 0) = b7 ∧
      ((hi &&& ((1 : UInt32) <<< 8)) != 0) = b8 ∧ ((hi &&& ((1 : UInt32) <<< 9)) != 0) = b9 ∧
      ((hi &&& ((1 : UInt32) <<< 10)) != 0) = b10 ∧ ((hi &&& ((1 : UInt32) <<< 11)) != 0) = b11 := by
    dsimp only [hi, bit]
    cases b6 <;> cases b7 <;> cases b8 <;> cases b9 <;> cases b10 <;> cases b11 <;> decide
  rw [hAcc, hLoBits.1, hLoBits.2.1, hLoBits.2.2.1, hLoBits.2.2.2,
    hHiBits.1, hHiBits.2.1, hHiBits.2.2.1, hHiBits.2.2.2.1, hHiBits.2.2.2.2.1, hHiBits.2.2.2.2.2]

private theorem decodeRawResolveFlags?_toBits (r : ResolveFlags) :
    Model.decodeRawResolveFlags? r.toBits = some r := by
  rcases r with ⟨a, b, c, d, e, f⟩
  cases a <;> cases b <;> cases c <;> cases d <;> cases e <;> cases f <;> decide

private theorem decodeRawAtFlags?_toBits (f : AtFlags) :
    Model.decodeRawAtFlags? f.toBits = some f := by
  rcases f with ⟨a, b, c⟩
  cases a <;> cases b <;> cases c <;> decide

private theorem decodeRawAccessModeMask?_toBits (m : AccessModeMask) :
    Model.decodeRawAccessModeMask? m.toBits = some m := by
  rcases m with ⟨a, b, c⟩
  cases a <;> cases b <;> cases c <;> decide

private theorem decodeRawUnlinkDir?_ite (b : Bool) :
    Model.decodeRawUnlinkDir? (if b then 1 else 0) = some b := by
  cases b <;> rfl

private theorem decodeRawRenameFlags?_toBits (f : RenameFlags) :
    Model.decodeRawRenameFlags? f.toBits = some f := by
  rcases f with ⟨a, b, c⟩
  cases a <;> cases b <;> cases c <;> decide

private theorem decodeRawFlockOp?_toBits (op : FlockOp) :
    Model.decodeRawFlockOp? op.toBits = some op := by
  cases op with
  | shared b => cases b <;> rfl
  | exclusive b => cases b <;> rfl
  | unlock => rfl

private theorem decodeRawFcntlCmd?_toRaw (cmd : FcntlCmd) :
    Model.decodeRawFcntlCmd? cmd.toRaw.1 cmd.toRaw.2 = some cmd := by
  cases cmd with
  | getFl => rfl
  | setFl nb ap => cases nb <;> cases ap <;> decide
  | getFd => rfl
  | setFd clo => cases clo <;> rfl
  | addSeals s => rfl
  | getSeals => rfl

private theorem decodeRawSeekWhence?_toRaw (w : SeekWhence) :
    Model.decodeRawSeekWhence? w.toRaw = some w := by
  cases w <;> rfl

private theorem decodeRawStdioFd?_toRaw (s : StdioFd) :
    Model.decodeRawStdioFd? s.toRaw = some s := by
  cases s <;> rfl

private theorem healthyStep_pathWrapperEinval {env : HealthyEnv} {req : FilesReq}
    (hWf : env.wf = true)
    (hNoClose : ∀ h, req ≠ .close h)
    (hNoDup : ∀ sl, req ≠ .dupStdio sl)
    (hDirNone : directHid? req = none)
    (hWrap : evalReq env.state req = .wrapperErr Errno.EINVAL) :
    healthyStep env req (.err Errno.EINVAL) = some env := by
  rcases env with ⟨s, budget⟩
  have hNoCrit : isCriticalFault (.err Errno.EINVAL) = false := by decide
  have hNoBusy : isCloseEbusy req (.err Errno.EINVAL) = false := by
    cases req with
    | close h => exact absurd rfl (hNoClose h)
    | _ => rfl
  have hNoEi : isEintrOutcome (.err Errno.EINVAL) = false := by decide
  have hAl : allowedStep s req (.err Errno.EINVAL) = some s := by
    unfold allowedStep
    cases req with
    | close h => exact absurd rfl (hNoClose h)
    | dupStdio sl => exact absurd rfl (hNoDup sl)
    | _ =>
      rw [hDirNone]
      dsimp only
      split
      · unfold verifyWithSeccomp
        dsimp only at hWrap
        rw [hWrap]
        rfl
      · dsimp only at hWrap
        rw [hWrap]
        rfl
  unfold healthyStep
  simp [hWf, hNoCrit, hNoBusy, hNoEi, hAl]

/-- `Internal.mkFilesOpsM` lifts any raw C-ABI bundle obeying `Model.allowedRawStep` to `Model.allowedPkgStep`. -/
theorem mkFilesOpsM_obeysStepFrom :
    Core.ObeysStepFrom id HealthyEnv.wf Model.execRawStep Model.allowedRawStep
      HealthyEnv.wf Internal.mkFilesOpsM Model.execPkgStep Model.allowedPkgStep := by
  intro W proj raw hRaw w req hWf
  dsimp only [Function.comp, id] at hWf ⊢
  cases req with
  | openat dir path flags mode =>
    cases hNul : hasEmbeddedNul path with
    | true =>
      simp only [execPkgStep_eq, execFilesReq, Internal.mkFilesOpsM,
        Functor.map, Pure.pure, StateT.run, stateT_pure_eq, stateT_map_eq,
        Model.allowedPkgStep, hNul, ↓reduceIte, outcomeOfOpened]
      exact healthyStep_pathWrapperEinval hWf (fun _ h => by cases h) (fun _ h => by cases h)
        rfl (by simp [evalReq, precheckNul, hNul])
    | false =>
      have hStep := hRaw w (.openat dir path flags.toBits mode) hWf
      simp only [Model.execRawStep, Model.allowedRawStep, Model.decodeRawFilesReq?,
        execPkgStep_eq, execFilesReq, Internal.mkFilesOpsM, Functor.map, Pure.pure,
        StateT.run, stateT_map_eq, Model.allowedPkgStep, hNul, Bool.false_eq_true, ↓reduceIte,
        decodeRawOpenFlags?_toBits] at hStep ⊢
      rcases hCall : raw.openat dir path flags.toBits mode w with ⟨res, w'⟩
      rw [hCall] at hStep
      cases res <;>
        simpa [Model.outcomeOfRawOpened, Model.toModelOutcome, outcomeOfOpened] using hStep
  | openat2 dir path how =>
    rcases how with ⟨flags, mode, resolve⟩
    cases hNul : hasEmbeddedNul path with
    | true =>
      simp only [execPkgStep_eq, execFilesReq, Internal.mkFilesOpsM,
        Functor.map, Pure.pure, StateT.run, stateT_pure_eq, stateT_map_eq,
        Model.allowedPkgStep, hNul, ↓reduceIte, outcomeOfOpened]
      exact healthyStep_pathWrapperEinval hWf (fun _ h => by cases h) (fun _ h => by cases h)
        rfl (by simp [evalReq, precheckNul, hNul])
    | false =>
      have hStep := hRaw w (.openat2 dir path flags.toBits mode resolve.toBits) hWf
      simp only [Model.execRawStep, Model.allowedRawStep, Model.decodeRawFilesReq?,
        execPkgStep_eq, execFilesReq, Internal.mkFilesOpsM, Functor.map, Pure.pure,
        StateT.run, stateT_map_eq, Model.allowedPkgStep, hNul, Bool.false_eq_true, ↓reduceIte,
        decodeRawOpenFlags?_toBits, decodeRawResolveFlags?_toBits] at hStep ⊢
      rcases hCall : raw.openat2 dir path flags.toBits mode resolve.toBits w with ⟨res, w'⟩
      rw [hCall] at hStep
      cases res <;>
        simpa [Model.outcomeOfRawOpened, Model.toModelOutcome, outcomeOfOpened] using hStep
  | close hid =>
    have hStep := hRaw w (.close hid) hWf
    simp only [Model.execRawStep, Model.allowedRawStep, Model.decodeRawFilesReq?,
      execPkgStep_eq, execFilesReq, Internal.mkFilesOpsM, Functor.map,
      StateT.run, stateT_map_eq, Model.allowedPkgStep] at hStep ⊢
    rcases hCall : raw.close hid w with ⟨res, w'⟩
    rw [hCall] at hStep
    cases res <;>
      simpa [Model.outcomeOfRawUnit, Model.toModelOutcome, outcomeOfUnit] using hStep
  | read hid maxBytes =>
    have hStep := hRaw w (.read hid maxBytes) hWf
    simp only [Model.execRawStep, Model.allowedRawStep, Model.decodeRawFilesReq?,
      execPkgStep_eq, execFilesReq, Internal.mkFilesOpsM, Functor.map,
      StateT.run, stateT_map_eq, Model.allowedPkgStep] at hStep ⊢
    rcases hCall : raw.read hid maxBytes w with ⟨res, w'⟩
    rw [hCall] at hStep
    cases res <;>
      simpa [Model.outcomeOfRawBytes, Model.toModelOutcome, outcomeOfBytes] using hStep
  | write hid data =>
    have hStep := hRaw w (.write hid data) hWf
    simp only [Model.execRawStep, Model.allowedRawStep, Model.decodeRawFilesReq?,
      execPkgStep_eq, execFilesReq, Internal.mkFilesOpsM, Functor.map,
      StateT.run, stateT_map_eq, Model.allowedPkgStep] at hStep ⊢
    rcases hCall : raw.write hid data w with ⟨res, w'⟩
    rw [hCall] at hStep
    cases res <;>
      simpa [Model.outcomeOfRawU32, Model.toModelOutcome, outcomeOfU32] using hStep
  | fstat hid =>
    have hStep := hRaw w (.fstat hid) hWf
    simp only [Model.execRawStep, Model.allowedRawStep, Model.decodeRawFilesReq?,
      execPkgStep_eq, execFilesReq, Internal.mkFilesOpsM, Functor.map, Bind.bind, Pure.pure,
      StateT.run, stateT_bind_eq, stateT_map_eq, Model.allowedPkgStep] at hStep ⊢
    rcases hCall : raw.fstat hid w with ⟨res, w'⟩
    rw [hCall] at hStep
    cases res <;>
      simpa [Model.outcomeOfRawStat, Model.toModelOutcome, outcomeOfStatted] using hStep
  | fstatat dir path flags =>
    cases hNul : hasEmbeddedNul path with
    | true =>
      simp only [execPkgStep_eq, execFilesReq, Internal.mkFilesOpsM,
        Functor.map, Pure.pure, StateT.run, stateT_pure_eq, stateT_map_eq,
        Model.allowedPkgStep, hNul, ↓reduceIte, outcomeOfStatted]
      exact healthyStep_pathWrapperEinval hWf (fun _ h => by cases h) (fun _ h => by cases h)
        rfl (by simp [evalReq, precheckNul, hNul])
    | false =>
      cases hEa : flags.eaccess with
      | true =>
        simp only [execPkgStep_eq, execFilesReq, Internal.mkFilesOpsM,
          Functor.map, Pure.pure, StateT.run, stateT_pure_eq, stateT_map_eq,
          Model.allowedPkgStep, hNul, Bool.false_eq_true, hEa, ↓reduceIte, outcomeOfStatted]
        exact healthyStep_pathWrapperEinval hWf (fun _ h => by cases h) (fun _ h => by cases h)
          rfl (by simp [evalReq, precheckNul, hNul, hEa])
      | false =>
        have hStep := hRaw w (.fstatat dir path flags.toBits) hWf
        simp only [Model.execRawStep, Model.allowedRawStep, Model.decodeRawFilesReq?,
          execPkgStep_eq, execFilesReq, Internal.mkFilesOpsM, Functor.map, Bind.bind, Pure.pure,
          StateT.run, stateT_bind_eq, stateT_map_eq, Model.allowedPkgStep,
          hNul, hEa, Bool.false_eq_true, ↓reduceIte, decodeRawAtFlags?_toBits] at hStep ⊢
        rcases hCall : raw.fstatat dir path flags.toBits w with ⟨res, w'⟩
        rw [hCall] at hStep
        cases res <;>
          simpa [Model.outcomeOfRawStat, Model.toModelOutcome, outcomeOfStatted] using hStep
  | faccessat dir path mask flags =>
    cases hNul : hasEmbeddedNul path with
    | true =>
      simp only [execPkgStep_eq, execFilesReq, Internal.mkFilesOpsM,
        Functor.map, Pure.pure, StateT.run, stateT_pure_eq, stateT_map_eq,
        Model.allowedPkgStep, hNul, ↓reduceIte, outcomeOfUnit]
      exact healthyStep_pathWrapperEinval hWf (fun _ h => by cases h) (fun _ h => by cases h)
        rfl (by simp [evalReq, precheckNul, hNul])
    | false =>
      have hStep := hRaw w (.faccessat dir path mask.toBits flags.toBits) hWf
      simp only [Model.execRawStep, Model.allowedRawStep, Model.decodeRawFilesReq?,
        execPkgStep_eq, execFilesReq, Internal.mkFilesOpsM, Functor.map, Pure.pure,
        StateT.run, stateT_map_eq, Model.allowedPkgStep, hNul, Bool.false_eq_true, ↓reduceIte,
        decodeRawAccessModeMask?_toBits, decodeRawAtFlags?_toBits] at hStep ⊢
      rcases hCall : raw.faccessat dir path mask.toBits flags.toBits w with ⟨res, w'⟩
      rw [hCall] at hStep
      cases res <;>
        simpa [Model.outcomeOfRawUnit, Model.toModelOutcome, outcomeOfUnit] using hStep
  | mkdirat dir path mode =>
    cases hNul : hasEmbeddedNul path with
    | true =>
      simp only [execPkgStep_eq, execFilesReq, Internal.mkFilesOpsM,
        Functor.map, Pure.pure, StateT.run, stateT_pure_eq, stateT_map_eq,
        Model.allowedPkgStep, hNul, ↓reduceIte, outcomeOfUnit]
      exact healthyStep_pathWrapperEinval hWf (fun _ h => by cases h) (fun _ h => by cases h)
        rfl (by simp [evalReq, precheckNul, hNul])
    | false =>
      have hStep := hRaw w (.mkdirat dir path mode) hWf
      simp only [Model.execRawStep, Model.allowedRawStep, Model.decodeRawFilesReq?,
        execPkgStep_eq, execFilesReq, Internal.mkFilesOpsM, Functor.map, Pure.pure,
        StateT.run, stateT_map_eq, Model.allowedPkgStep, hNul, Bool.false_eq_true, ↓reduceIte] at hStep ⊢
      rcases hCall : raw.mkdirat dir path mode w with ⟨res, w'⟩
      rw [hCall] at hStep
      cases res <;>
        simpa [Model.outcomeOfRawUnit, Model.toModelOutcome, outcomeOfUnit] using hStep
  | unlinkat dir path removeDir =>
    cases hNul : hasEmbeddedNul path with
    | true =>
      simp only [execPkgStep_eq, execFilesReq, Internal.mkFilesOpsM,
        Functor.map, Pure.pure, StateT.run, stateT_pure_eq, stateT_map_eq,
        Model.allowedPkgStep, hNul, ↓reduceIte, outcomeOfUnit]
      exact healthyStep_pathWrapperEinval hWf (fun _ h => by cases h) (fun _ h => by cases h)
        rfl (by simp [evalReq, precheckNul, hNul])
    | false =>
      have hStep := hRaw w (.unlinkat dir path (if removeDir then 1 else 0)) hWf
      simp only [Model.execRawStep, Model.allowedRawStep, Model.decodeRawFilesReq?,
        execPkgStep_eq, execFilesReq, Internal.mkFilesOpsM, Functor.map, Pure.pure,
        StateT.run, stateT_map_eq, Model.allowedPkgStep, hNul, Bool.false_eq_true, ↓reduceIte,
        decodeRawUnlinkDir?_ite] at hStep ⊢
      rcases hCall : raw.unlinkat dir path (if removeDir then 1 else 0) w with ⟨res, w'⟩
      rw [hCall] at hStep
      cases res <;>
        simpa [Model.outcomeOfRawUnit, Model.toModelOutcome, outcomeOfUnit] using hStep
  | renameat2 od op nd np flags =>
    cases hNul : (hasEmbeddedNul op || hasEmbeddedNul np) with
    | true =>
      simp only [execPkgStep_eq, execFilesReq, Internal.mkFilesOpsM,
        Functor.map, Pure.pure, StateT.run, stateT_pure_eq, stateT_map_eq,
        Model.allowedPkgStep, hNul, ↓reduceIte, outcomeOfUnit]
      exact healthyStep_pathWrapperEinval hWf (fun _ h => by cases h) (fun _ h => by cases h)
        rfl (by simp [evalReq, precheckNul, hNul])
    | false =>
      have hStep := hRaw w (.renameat2 od op nd np flags.toBits) hWf
      simp only [Model.execRawStep, Model.allowedRawStep, Model.decodeRawFilesReq?,
        execPkgStep_eq, execFilesReq, Internal.mkFilesOpsM, Functor.map, Pure.pure,
        StateT.run, stateT_map_eq, Model.allowedPkgStep, hNul, Bool.false_eq_true, ↓reduceIte,
        decodeRawRenameFlags?_toBits] at hStep ⊢
      rcases hCall : raw.renameat2 od op nd np flags.toBits w with ⟨res, w'⟩
      rw [hCall] at hStep
      cases res <;>
        simpa [Model.outcomeOfRawUnit, Model.toModelOutcome, outcomeOfUnit] using hStep
  | symlinkat target dir linkPath =>
    cases hNul : (hasEmbeddedNul target || hasEmbeddedNul linkPath) with
    | true =>
      simp only [execPkgStep_eq, execFilesReq, Internal.mkFilesOpsM,
        Functor.map, Pure.pure, StateT.run, stateT_pure_eq, stateT_map_eq,
        Model.allowedPkgStep, hNul, ↓reduceIte, outcomeOfUnit]
      exact healthyStep_pathWrapperEinval hWf (fun _ h => by cases h) (fun _ h => by cases h)
        rfl (by simp [evalReq, precheckNul, hNul])
    | false =>
      have hStep := hRaw w (.symlinkat target dir linkPath) hWf
      simp only [Model.execRawStep, Model.allowedRawStep, Model.decodeRawFilesReq?,
        execPkgStep_eq, execFilesReq, Internal.mkFilesOpsM, Functor.map, Pure.pure,
        StateT.run, stateT_map_eq, Model.allowedPkgStep, hNul, Bool.false_eq_true, ↓reduceIte] at hStep ⊢
      rcases hCall : raw.symlinkat target dir linkPath w with ⟨res, w'⟩
      rw [hCall] at hStep
      cases res <;>
        simpa [Model.outcomeOfRawUnit, Model.toModelOutcome, outcomeOfUnit] using hStep
  | readlinkat dir path cap =>
    cases hNul : hasEmbeddedNul path with
    | true =>
      simp only [execPkgStep_eq, execFilesReq, Internal.mkFilesOpsM,
        Functor.map, Pure.pure, StateT.run, stateT_pure_eq, stateT_map_eq,
        Model.allowedPkgStep, hNul, ↓reduceIte, outcomeOfBytes]
      exact healthyStep_pathWrapperEinval hWf (fun _ h => by cases h) (fun _ h => by cases h)
        rfl (by simp [evalReq, precheckNul, hNul])
    | false =>
      have hStep := hRaw w (.readlinkat dir path cap) hWf
      simp only [Model.execRawStep, Model.allowedRawStep, Model.decodeRawFilesReq?,
        execPkgStep_eq, execFilesReq, Internal.mkFilesOpsM, Functor.map, Pure.pure,
        StateT.run, stateT_map_eq, Model.allowedPkgStep, hNul, Bool.false_eq_true, ↓reduceIte] at hStep ⊢
      rcases hCall : raw.readlinkat dir path cap w with ⟨res, w'⟩
      rw [hCall] at hStep
      cases res <;>
        simpa [Model.outcomeOfRawBytes, Model.toModelOutcome, outcomeOfBytes] using hStep
  | getdents64 hid cap =>
    have hStep := hRaw w (.getdents64 hid cap) hWf
    simp only [Model.execRawStep, Model.allowedRawStep, Model.decodeRawFilesReq?,
      execPkgStep_eq, execFilesReq, Internal.mkFilesOpsM, Functor.map,
      StateT.run, stateT_map_eq, Model.allowedPkgStep] at hStep ⊢
    rcases hCall : raw.getdents64 hid cap w with ⟨res, w'⟩
    rw [hCall] at hStep
    cases res <;>
      simpa [Model.outcomeOfRawBytes, Model.toModelOutcome, outcomeOfBytes] using hStep
  | fchmodat dir path mode =>
    cases hNul : hasEmbeddedNul path with
    | true =>
      simp only [execPkgStep_eq, execFilesReq, Internal.mkFilesOpsM,
        Functor.map, Pure.pure, StateT.run, stateT_pure_eq, stateT_map_eq,
        Model.allowedPkgStep, hNul, ↓reduceIte, outcomeOfUnit]
      exact healthyStep_pathWrapperEinval hWf (fun _ h => by cases h) (fun _ h => by cases h)
        rfl (by simp [evalReq, precheckNul, hNul])
    | false =>
      have hStep := hRaw w (.fchmodat dir path mode) hWf
      simp only [Model.execRawStep, Model.allowedRawStep, Model.decodeRawFilesReq?,
        execPkgStep_eq, execFilesReq, Internal.mkFilesOpsM, Functor.map, Pure.pure,
        StateT.run, stateT_map_eq, Model.allowedPkgStep, hNul, Bool.false_eq_true, ↓reduceIte] at hStep ⊢
      rcases hCall : raw.fchmodat dir path mode w with ⟨res, w'⟩
      rw [hCall] at hStep
      cases res <;>
        simpa [Model.outcomeOfRawUnit, Model.toModelOutcome, outcomeOfUnit] using hStep
  | fchmod hid mode =>
    have hStep := hRaw w (.fchmod hid mode) hWf
    simp only [Model.execRawStep, Model.allowedRawStep, Model.decodeRawFilesReq?,
      execPkgStep_eq, execFilesReq, Internal.mkFilesOpsM, Functor.map,
      StateT.run, stateT_map_eq, Model.allowedPkgStep] at hStep ⊢
    rcases hCall : raw.fchmod hid mode w with ⟨res, w'⟩
    rw [hCall] at hStep
    cases res <;>
      simpa [Model.outcomeOfRawUnit, Model.toModelOutcome, outcomeOfUnit] using hStep
  | flock hid op =>
    have hStep := hRaw w (.flock hid op.toBits) hWf
    simp only [Model.execRawStep, Model.allowedRawStep, Model.decodeRawFilesReq?,
      execPkgStep_eq, execFilesReq, Internal.mkFilesOpsM, Functor.map,
      StateT.run, stateT_map_eq, Model.allowedPkgStep, decodeRawFlockOp?_toBits] at hStep ⊢
    rcases hCall : raw.flock hid op.toBits w with ⟨res, w'⟩
    rw [hCall] at hStep
    cases res <;>
      simpa [Model.outcomeOfRawUnit, Model.toModelOutcome, outcomeOfUnit] using hStep
  | fcntl hid cmd =>
    have hStep := hRaw w (.fcntl hid cmd.toRaw.1 cmd.toRaw.2) hWf
    simp only [Model.execRawStep, Model.allowedRawStep, Model.decodeRawFilesReq?,
      execPkgStep_eq, execFilesReq, Internal.mkFilesOpsM, Functor.map,
      StateT.run, stateT_map_eq, Model.allowedPkgStep, decodeRawFcntlCmd?_toRaw] at hStep ⊢
    rcases hCall : raw.fcntl hid cmd.toRaw.1 cmd.toRaw.2 w with ⟨res, w'⟩
    rw [hCall] at hStep
    cases res <;>
      simpa [Model.outcomeOfRawU32, Model.toModelOutcome, outcomeOfU32] using hStep
  | fsync hid =>
    have hStep := hRaw w (.fsync hid) hWf
    simp only [Model.execRawStep, Model.allowedRawStep, Model.decodeRawFilesReq?,
      execPkgStep_eq, execFilesReq, Internal.mkFilesOpsM, Functor.map,
      StateT.run, stateT_map_eq, Model.allowedPkgStep] at hStep ⊢
    rcases hCall : raw.fsync hid w with ⟨res, w'⟩
    rw [hCall] at hStep
    cases res <;>
      simpa [Model.outcomeOfRawUnit, Model.toModelOutcome, outcomeOfUnit] using hStep
  | getcwd cap =>
    have hStep := hRaw w (.getcwd cap) hWf
    simp only [Model.execRawStep, Model.allowedRawStep, Model.decodeRawFilesReq?,
      execPkgStep_eq, execFilesReq, Internal.mkFilesOpsM, Functor.map,
      StateT.run, stateT_map_eq, Model.allowedPkgStep] at hStep ⊢
    rcases hCall : raw.getcwd cap w with ⟨res, w'⟩
    rw [hCall] at hStep
    cases res <;>
      simpa [Model.outcomeOfRawBytes, Model.toModelOutcome, outcomeOfBytes] using hStep
  | lseek hid off whence =>
    have hStep := hRaw w (.lseek hid off whence.toRaw) hWf
    simp only [Model.execRawStep, Model.allowedRawStep, Model.decodeRawFilesReq?,
      execPkgStep_eq, execFilesReq, Internal.mkFilesOpsM, Functor.map,
      StateT.run, stateT_map_eq, Model.allowedPkgStep, decodeRawSeekWhence?_toRaw] at hStep ⊢
    rcases hCall : raw.lseek hid off whence.toRaw w with ⟨res, w'⟩
    rw [hCall] at hStep
    cases res <;>
      simpa [Model.outcomeOfRawU64, Model.toModelOutcome, outcomeOfU64] using hStep
  | reopenReadOnly hid =>
    have hStep := hRaw w (.reopenReadOnly hid) hWf
    simp only [Model.execRawStep, Model.allowedRawStep, Model.decodeRawFilesReq?,
      execPkgStep_eq, execFilesReq, Internal.mkFilesOpsM, Functor.map,
      StateT.run, stateT_map_eq, Model.allowedPkgStep] at hStep ⊢
    rcases hCall : raw.reopenReadOnly hid w with ⟨res, w'⟩
    rw [hCall] at hStep
    cases res <;>
      simpa [Model.outcomeOfRawOpened, Model.toModelOutcome, outcomeOfOpened] using hStep
  | dupStdio slot =>
    have hStep := hRaw w (.dupStdio slot.toRaw) hWf
    simp only [Model.execRawStep, Model.allowedRawStep, Model.decodeRawFilesReq?,
      execPkgStep_eq, execFilesReq, Internal.mkFilesOpsM, Functor.map,
      StateT.run, stateT_map_eq, Model.allowedPkgStep, decodeRawStdioFd?_toRaw] at hStep ⊢
    rcases hCall : raw.dupStdio slot.toRaw w with ⟨res, w'⟩
    rw [hCall] at hStep
    cases res <;>
      simpa [Model.outcomeOfRawOpened, Model.toModelOutcome, outcomeOfOpened] using hStep

end LeanSwe.LinuxSyscall.Files.Proofs
