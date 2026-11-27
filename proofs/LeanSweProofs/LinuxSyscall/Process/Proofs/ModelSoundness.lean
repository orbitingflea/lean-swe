import LeanSweProofs.LinuxSyscall.Process.SpecTests
import LeanSwe.LinuxSyscall.Process.Impl
import LeanSweProofs.LinuxSyscall.Process.Proofs.ModelSoundnessReq

namespace LeanSwe.LinuxSyscall.Process

open Core (AllPass)

/-- Soundness bridge: any `raw` shim satisfying `RawPosixShimSound` yields `Internal.mkProcessOps raw` accepted by `allowedStep`. -/
theorem mkProcessOps_sound_for_allowedStep
    (raw : PosixProcessOpsM (StateM ProcessSysState) HandleId)
    (hsound : RawPosixShimSound raw) (s : ProcessSysState) (req : ProcessReq) :
    let r := (execProcessReq (Internal.mkProcessOps raw) req).run s
    allowedStep s req r.1 = some r.2 := by
  cases req with
  | pipe2 pf =>
    have hp := hsound.pipe2_sound s pf
    dsimp only [execProcessReq, Internal.mkProcessOps, StateT.run, bind, Bind.bind, StateT.bind, pure, Pure.pure, StateT.pure] at hp ⊢
    cases hres : raw.pipe2 pf.toBits s with
    | mk out s' =>
      rw [hres] at hp
      cases out with
      | ok fds => exact hp
      | error e => exact hp
  | waitpid pid wf =>
    have hw := hsound.waitpid_sound s pid wf
    dsimp only [execProcessReq, Internal.mkProcessOps, StateT.run, bind, Bind.bind, StateT.bind, pure, Pure.pure, StateT.pure] at hw ⊢
    cases hres : raw.waitpid pid wf.toBits s with
    | mk out s' =>
      rw [hres] at hw
      cases out with
      | ok t => exact hw
      | error e => exact hw
  | kill pid sig =>
    dsimp only [execProcessReq, Internal.mkProcessOps, StateT.run, bind, Bind.bind, StateT.bind, pure, Pure.pure, StateT.pure]
    cases hres : sig.isNptlReserved with
    | true =>
      simp [outcomeOfUnit, pure, Pure.pure, StateT.pure, hres, allowedStep, validateReqBeforeKernel]
    | false =>
      have hk := hsound.kill_sound s pid sig hres
      dsimp only [StateT.run] at hk
      simp only [Bool.false_eq_true, ↓reduceIte]
      cases hcall : raw.kill pid sig.toRaw.1 sig.toRaw.2 s with
      | mk out s' =>
        rw [hcall] at hk
        cases out with
        | ok u => cases u; exact hk
        | error e => exact hk
  | pidfd_open pid pof =>
    have ho := hsound.pidfd_open_sound s pid pof
    dsimp only [execProcessReq, Internal.mkProcessOps, StateT.run, bind, Bind.bind, StateT.bind, pure, Pure.pure, StateT.pure] at ho ⊢
    cases hres : raw.pidfd_open pid pof.toBits s with
    | mk out s' =>
      rw [hres] at ho
      cases out with
      | ok h => exact ho
      | error e => exact ho
  | pidfd_send_signal hid sig psf =>
    dsimp only [execProcessReq, Internal.mkProcessOps, StateT.run, bind, Bind.bind, StateT.bind, pure, Pure.pure, StateT.pure]
    cases hres : sig.isNptlReserved with
    | true =>
      simp [outcomeOfUnit, pure, Pure.pure, StateT.pure, hres, allowedStep, validateReqBeforeKernel]
    | false =>
      have hs := hsound.pidfd_send_signal_sound s hid sig psf hres
      dsimp only [StateT.run] at hs
      simp only [Bool.false_eq_true, ↓reduceIte]
      cases hcall : raw.pidfd_send_signal hid sig.toRaw.1 sig.toRaw.2 psf.toBits s with
      | mk out s' =>
        rw [hcall] at hs
        cases out with
        | ok u => cases u; exact hs
        | error e => exact hs
  | getpid =>
    have hg := hsound.getpid_sound s
    dsimp only [execProcessReq, Internal.mkProcessOps, StateT.run, bind, Bind.bind, StateT.bind, pure, Pure.pure, StateT.pure] at hg ⊢
    cases hres : raw.getpid s with
    | mk out s' =>
      rw [hres] at hg
      cases out with
      | ok p => exact hg
      | error e => exact hg
  | getuid =>
    have hu := hsound.getuid_sound s
    dsimp only [execProcessReq, Internal.mkProcessOps, StateT.run, bind, Bind.bind, StateT.bind, pure, Pure.pure, StateT.pure] at hu ⊢
    cases hres : raw.getuid s with
    | mk out s' =>
      rw [hres] at hu
      cases out with
      | ok u => exact hu
      | error e => exact hu

/-- Universal soundness: `modelOps` always produces an outcome and next state accepted by `allowedStep`. -/
theorem process_model_modelOpsSoundForAllowedStep_allPass :
    AllPass (test_process_model_modelOpsSoundForAllowedStep modelOps allowedStep) := by
  intro s req
  exact ⟨modelOps_execProcessReq_sound s req, trivial⟩

/-- Universal soundness and polymorphic `{m} [Monad m]` delegation proof for `Internal.mkProcessOps`. -/
theorem process_impl_mkProcessOpsSound_allPass :
    AllPass (test_process_impl_mkProcessOpsSound Internal.mkProcessOps) := by
  dsimp only [AllPass, test_process_impl_mkProcessOpsSound, Bind.bind, Pure.pure, Core.NondetTest.assert]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, trivial⟩
  · intro raw hs s req
    exact mkProcessOps_sound_for_allowedStep raw hs s req
  · intro _ _ _ _ _; rfl
  · intro _ _ _ _ _ _; rfl
  · intro _ _ _ _ _ _; rfl
  · intro _ _ _ _ _ _; rfl
  · intro _ _ _ _ _ _ _; rfl
  · intro _ _ _ _; rfl
  · intro _ _ _ _; rfl

end LeanSwe.LinuxSyscall.Process
