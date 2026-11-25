import LeanSwe.Fs.Interface
import LeanSwe.Fs.Proofs.SysBridgeScopedRefines
import LeanSwe.Fs.Proofs.SysBridgeDirRefines

namespace LeanSwe.Fs.Proofs

open LeanSwe.LinuxSyscall
open LeanSwe.LinuxSyscall.Files
open LeanSwe.Fs
open LeanSwe.Fs.Model

private def badFsWorld : FsWorld :=
  { env := { state := { FilesState.initial with ambientSeccomp := true }, eintrBudget := 0 }, tempSeq := 0 }

private theorem badFsWorld_wf : fsWorldWf badFsWorld = false := rfl

/-- Pin `proj : W → FsDepsWorld` to a fixed `hidOf : RawFd → HandleId` and `time.wf = true`, falling back to `badFsWorld` outside the invariant. -/
noncomputable def pinToHidProj {W : Type} (proj : W → FsDepsWorld) (hidOf : RawFd → HandleId) (s : W) : FsWorld :=
  open Classical in
  if (proj s).toHid = hidOf ∧ (proj s).time.wf = true then (proj s).fs else badFsWorld

/-- Evaluate `pinToHidProj` when the `toHid` and `time.wf` invariants hold. -/
theorem pinToHidProj_eq_of_inv {W : Type} {proj : W → FsDepsWorld} {hidOf : RawFd → HandleId} {s : W}
    (hHid : (proj s).toHid = hidOf) (hTwf : (proj s).time.wf = true) :
    pinToHidProj proj hidOf s = (proj s).fs := by
  classical
  simp [pinToHidProj, hHid, hTwf]

/-- Extract the `FsDepsWorld` invariants from `fsWorldWf (pinToHidProj proj hidOf s) = true`. -/
theorem pinToHidProj_wf_inv {W : Type} {proj : W → FsDepsWorld} {hidOf : RawFd → HandleId} {s : W}
    (hWf : fsWorldWf (pinToHidProj proj hidOf s) = true) :
    (proj s).toHid = hidOf ∧ (proj s).time.wf = true ∧
    fsWorldWf (proj s).fs = true ∧ fsDepsWorldWf (proj s) = true := by
  classical
  unfold pinToHidProj at hWf
  by_cases hCond : (proj s).toHid = hidOf ∧ (proj s).time.wf = true
  · simp only [hCond, and_self, ↓reduceIte] at hWf
    exact ⟨hCond.1, hCond.2, hWf, by simp [fsDepsWorldWf, hWf, hCond.2]⟩
  · simp only [hCond, ↓reduceIte, badFsWorld_wf] at hWf
    cases hWf

private theorem fsWorld_ext {a b : FsWorld} (hEnv : a.env = b.env) (hSeq : a.tempSeq = b.tempSeq) : a = b := by
  cases a; cases b; simp_all

private theorem execTimeRand_preserves_pin {W : Type} {proj : W → FsDepsWorld}
    {caps : FsSysCapsM (StateM W)}
    (hCaps : Core.ObeysStep proj fsDepsWorldWf (execFsSysCapStep caps) allowedFsSysCapStep)
    (hidOf : RawFd → HandleId) (treq : TimeRand.TimeRandReq)
    {s : W} (hWf : fsWorldWf (pinToHidProj proj hidOf s) = true) :
    let q := (TimeRand.execTimeRandReq caps.timeRand treq).run s
    fsWorldWf (pinToHidProj proj hidOf q.2) = true ∧
    pinToHidProj proj hidOf q.2 = pinToHidProj proj hidOf s := by
  obtain ⟨hHid, hTwf, hFsWf, hDepsWf⟩ := pinToHidProj_wf_inv hWf
  have hStep := hCaps s (.timeRand treq) hDepsWf
  cases hR : (TimeRand.execTimeRandReq caps.timeRand treq s) with
  | mk out s1 =>
    have hRun : (execFsSysCapStep caps (.timeRand treq)).run s = (.timeRand out, s1) := by
      simp [execFsSysCapStep, Functor.map, StateT.map, StateT.run, hR]
    rw [hRun] at hStep
    dsimp only [allowedFsSysCapStep] at hStep
    obtain ⟨_, hDepsWf1, hHid1, hSeq1, _, hEnv1⟩ := hStep
    have hWfSplit := (Bool.and_eq_true _ _).mp hDepsWf1
    have hEq0 := pinToHidProj_eq_of_inv hHid hTwf
    have hEq1 := pinToHidProj_eq_of_inv (hHid1.trans hHid) hWfSplit.2
    have hFsEq : (proj s1).fs = (proj s).fs := fsWorld_ext hEnv1 hSeq1
    simp only [StateT.run, hR]
    rw [hEq1, hEq0, hFsEq]
    exact ⟨hFsWf, rfl⟩

/-- Bridge `Core.ObeysStep` over `FsSysCapsM` (`RawFd` + `TimeRand`) to `RefinesFsFilesFixed` for any pinned `hidOf`. -/
theorem refinesFsFilesFixed_of_fsSysCaps {W : Type} {proj : W → FsDepsWorld}
    {caps : FsSysCapsM (StateM W)}
    (hCaps : Core.ObeysStep proj fsDepsWorldWf (execFsSysCapStep caps) allowedFsSysCapStep)
    (hidOf : RawFd → HandleId) :
    RefinesFsFilesFixed (pinToHidProj proj hidOf) hidOf caps.files
      (SysBridge.nextTimeRandNonce caps.timeRand) where
  file_step := by
    intro s req hWf
    obtain ⟨hHid, hTwf, _, hDepsWf⟩ := pinToHidProj_wf_inv hWf
    have hStep := hCaps s (.files req) hDepsWf
    cases hR : (execRawFilesReq caps.files req s) with
    | mk out s1 =>
      have hRun : (execFsSysCapStep caps (.files req)).run s = (.files out, s1) := by
        simp [execFsSysCapStep, Functor.map, StateT.map, StateT.run, hR]
      rw [hRun] at hStep
      dsimp only [allowedFsSysCapStep] at hStep
      obtain ⟨_, hDepsWf1, hHid1, hSeq1, hHealthy, _⟩ := hStep
      have hWfSplit := (Bool.and_eq_true _ _).mp hDepsWf1
      have hEq0 := pinToHidProj_eq_of_inv hHid hTwf
      have hEq1 := pinToHidProj_eq_of_inv (hHid1.trans hHid) hWfSplit.2
      rw [hHid] at hHealthy
      simp only [StateT.run, hR, hEq0, hEq1]
      exact ⟨hWfSplit.1, hHealthy, hSeq1⟩
  nonce_step := by
    intro s hWf
    have hCg := execTimeRand_preserves_pin hCaps hidOf (.clock_gettime .monotonic) hWf
    dsimp only at hCg
    cases hR1 : (caps.timeRand.clock_gettime .monotonic s) with
    | mk r1 s1 =>
      have hExec1 : ((TimeRand.execTimeRandReq caps.timeRand (.clock_gettime .monotonic)).run s).2 = s1 := by
        simp [TimeRand.execTimeRandReq, Functor.map, StateT.map, StateT.run, hR1]
      rw [hExec1] at hCg
      have hGr := execTimeRand_preserves_pin hCaps hidOf (.getrandom 8 {}) hCg.1
      dsimp only at hGr
      cases hR2 : (caps.timeRand.getrandom 8 {} s1) with
      | mk r2 s2 =>
        have hExec2 : ((TimeRand.execTimeRandReq caps.timeRand (.getrandom 8 {})).run s1).2 = s2 := by
          simp [TimeRand.execTimeRandReq, Functor.map, StateT.map, StateT.run, hR2]
        rw [hExec2] at hGr
        have stepBind : ∀ {α β : Type} (ma : StateM W α) (f : α → StateM W β) (w w' : W) (a : α),
            ma w = (a, w') → (ma >>= f) w = f a w' := by
          intro _ _ ma f w w' a hm
          change (match ma w with | (x, y) => f x y) = f a w'
          rw [hm]
        have hNonce2 : ((SysBridge.nextTimeRandNonce caps.timeRand).run s).2 = s2 := by
          unfold SysBridge.nextTimeRandNonce
          rw [StateT.run, stepBind _ _ s s1 r1 hR1]
          cases r1 <;>
            (dsimp only; rw [stepBind (pure _) _ s1 s1 _ rfl];
             rw [stepBind _ _ s1 s2 r2 hR2]; cases r2 <;> rfl)
        dsimp only
        rw [hNonce2, hGr.2.trans hCg.2]
        exact ⟨hWf, rfl, Nat.le_refl _⟩

/-- Evaluate `fsDepsWorldToFsWorld` on any world with well-formed `time`. -/
theorem fsDepsWorldToFsWorld_eq_of_wf {w : FsDepsWorld} (hTwf : w.time.wf = true) :
    fsDepsWorldToFsWorld w = w.fs := by
  simp [fsDepsWorldToFsWorld, hTwf]

/-- `fsWorldWf (fsDepsWorldToFsWorld w)` holds iff `fsDepsWorldWf w` holds. -/
theorem fsWorldWf_fsDepsWorldToFsWorld_iff (w : FsDepsWorld) :
    fsWorldWf (fsDepsWorldToFsWorld w) = true ↔ fsDepsWorldWf w = true := by
  unfold fsDepsWorldToFsWorld fsDepsWorldWf
  cases hT : w.time.wf
  · simp [fsWorldWf, HealthyEnv.wf]
  · simp

/-- Every valid `allowedSubtreeStep` transition establishes `fsWorldWf` on the post-world. -/
theorem allowedSubtreeStep_wf {w : FsWorld} {req : SubtreeStepReq} {out : SubtreeStepOut} {w' : FsWorld}
    (h : allowedSubtreeStep w req out w') : fsWorldWf w' = true := by
  rcases req with ⟨rootPath, op⟩
  unfold allowedSubtreeStep at h
  cases out <;> cases op <;> dsimp only at h <;>
    first
    | exact False.elim h
    | (obtain ⟨_, hTr, _⟩ := h; exact hTr.1)

/-- Every valid `allowedFsStep` transition establishes `fsWorldWf` on the post-world. -/
theorem allowedFsStep_wf {w : FsWorld} {req : FsStepReq} {out : FsStepOut} {w' : FsWorld}
    (h : allowedFsStep w req out w') : fsWorldWf w' = true := by
  unfold allowedFsStep at h
  cases out with
  | flag res =>
    cases res with
    | error _ => exact False.elim h
    | ok _ => dsimp only at h; obtain ⟨_, hTr, _⟩ := h; exact hTr.1
  | walkEntries _ | lockVal _ | tryLockVal _ | bytes _ =>
    cases req <;> dsimp only at h <;> first | exact False.elim h | (obtain ⟨_, hTr, _⟩ := h; exact hTr.1)
  | unit _ | stat _ | str _ | names _ =>
    dsimp only at h; obtain ⟨_, hTr, _⟩ := h; exact hTr.1

/-- End-to-end descriptor-confined refinement of `Internal.mkSubtreeOpenerFromCapsM` against `allowedSubtreeStep` over `FsSysCapsM`. -/
theorem refinesStepFromFinally_mkSubtreeOpenerFromCapsM :
    Core.ObeysStepFromFinally
      fsDepsWorldToFsWorld fsDepsWorldWf
      execFsSysCapStep allowedFsSysCapStep
      fsWorldWf Internal.mkSubtreeOpenerFromCapsM
      execSubtreeStep allowedSubtreeStep := by
  intro W proj caps hCaps s req hPkgWf
  have hDepsWf : fsDepsWorldWf (proj s) = true :=
    (fsWorldWf_fsDepsWorldToFsWorld_iff (proj s)).mp hPkgWf
  have hWfSplit := (Bool.and_eq_true _ _).mp hDepsWf
  let hidOf := (proj s).toHid
  have hEq0 : pinToHidProj proj hidOf s = (proj s).fs := pinToHidProj_eq_of_inv rfl hWfSplit.2
  have hMap0 : fsDepsWorldToFsWorld (proj s) = (proj s).fs := fsDepsWorldToFsWorld_eq_of_wf hWfSplit.2
  have hPinWf : fsWorldWf (pinToHidProj proj hidOf s) = true := hEq0 ▸ hWfSplit.1
  have hSub := refinesSubtree_of_refinesFilesFixed
    (refinesFsFilesFixed_of_fsSysCaps hCaps hidOf) s req hPinWf
  have hWf1 := allowedSubtreeStep_wf hSub
  obtain ⟨hHid1, hTwf1, _, _⟩ := pinToHidProj_wf_inv hWf1
  have hEq1 : pinToHidProj proj hidOf ((execSubtreeStep (Internal.mkSubtreeOpenerFromCapsM caps) req).run s).2 =
      (proj ((execSubtreeStep (Internal.mkSubtreeOpenerFromCapsM caps) req).run s).2).fs :=
    pinToHidProj_eq_of_inv hHid1 hTwf1
  have hMap1 : fsDepsWorldToFsWorld (proj ((execSubtreeStep (Internal.mkSubtreeOpenerFromCapsM caps) req).run s).2) =
      (proj ((execSubtreeStep (Internal.mkSubtreeOpenerFromCapsM caps) req).run s).2).fs :=
    fsDepsWorldToFsWorld_eq_of_wf hTwf1
  dsimp only [Function.comp, Internal.mkSubtreeOpenerFromCapsM] at hSub hEq1 hMap1 ⊢
  rw [hEq0, hEq1] at hSub
  rw [hMap0, hMap1]
  exact hSub

end LeanSwe.Fs.Proofs
