import Core.Obeys
import LeanSwe.CmdLine.Interface
import LeanSwe.CmdLine.Proofs.ParserCore
import LeanSwe.CmdLine.Proofs.PhraseBridge

namespace LeanSwe.CmdLine.Proofs

open Core LeanSwe.CmdLine LeanSwe.CmdLine.Proofs.Shared

/-- Projecting `CheckedCliStepState.cli` turns a `CheckedCliOpsM` raw contract into a `CliOpsM` raw contract on `ops.cliOps`. -/
theorem checkedOps_cliOps_obeysRawStep {W : Type} (proj : W → Model.CheckedCliStepState)
    (ops : Model.CheckedCliOpsM (StateM W))
    (hChecked : Core.ObeysStep proj Model.checkedStepWf (Model.execCheckedRawStep ops) Model.allowedCheckedRawStep) :
    Core.ObeysStep (fun w => (proj w).cli) Model.rawStepWf (Model.execRawStep ops.cliOps) Model.allowedRawStep := by
  intro w req _
  have h := hChecked w (.raw req) rfl
  dsimp only [Model.execCheckedRawStep, Functor.map, StateT.map, StateT.run] at h ⊢
  cases hr : Model.execRawStep ops.cliOps req w with
  | mk out w1 =>
    simp only [hr, Model.allowedCheckedRawStep] at h
    exact h.1

/-- Every `ops.cliOps` primitive preserves `stdioErr?` under `allowedCheckedRawStep`. -/
theorem checkedOps_raw_preserves_stdioErr {W : Type} (proj : W → Model.CheckedCliStepState)
    (ops : Model.CheckedCliOpsM (StateM W))
    (hChecked : Core.ObeysStep proj Model.checkedStepWf (Model.execCheckedRawStep ops) Model.allowedCheckedRawStep)
    (req : Model.RawStepReq) (w : W) :
    (proj (Model.execRawStep ops.cliOps req w).2).stdioErr? = (proj w).stdioErr? := by
  have h := hChecked w (.raw req) rfl
  dsimp only [Model.execCheckedRawStep, Functor.map, StateT.map, StateT.run] at h
  cases hr : Model.execRawStep ops.cliOps req w with
  | mk out w1 =>
    simp only [hr, Model.allowedCheckedRawStep] at h
    exact h.2

private theorem resolveSingleOptionFast_preserves_stdioErr {W : Type}
    (proj : W → Model.CheckedCliStepState)
    (getEnv : String → StateM W (Except CmdLineError (Option String)))
    (hEnv : ∀ w k, (proj (getEnv k w).2).stdioErr? = (proj w).stdioErr?)
    (opt : OptSpec) (cliVals : List OptValue) (validators : CustomValidators) (w : W) :
    (proj (Internal.resolveSingleOptionFast getEnv opt cliVals validators w).2).stdioErr? =
      (proj w).stdioErr? := by
  rw [resolveSingleOptionFast_eq]
  unfold Model.resolveSingleOption
  by_cases hcli : !cliVals.isEmpty
  · simp only [hcli, ↓reduceIte]
    split <;> rfl
  · simp only [hcli, Bool.false_eq_true, ↓reduceIte]
    cases opt.envVar with
    | none => rfl
    | some envKey =>
      dsimp only [Bind.bind, StateT.bind, Pure.pure, StateT.pure]
      have hw1 := hEnv w envKey
      cases hg : getEnv envKey w with
      | mk r w1 =>
        simp only [hg] at hw1 ⊢
        cases r with
        | error _ => exact hw1
        | ok v? =>
          cases v? with
          | none => exact hw1
          | some s =>
            if hs : s = "" then
              subst hs; exact hw1
            else
              unfold Model.resolveSingleOption.match_1
              dsimp only
              simp only [hs, ↓reduceDIte]
              cases Model.parseOptValueWith opt.kind s validators with
              | error _ => exact hw1
              | ok v =>
                dsimp only
                by_cases hrb : (opt.repeatable && opt.kind == .bool && v == .bool false) = true <;>
                  simp only [hrb, Bool.false_eq_true, ↓reduceIte] <;>
                  exact hw1

private theorem resolveOptionsTR_preserves_stdioErr {W : Type}
    (proj : W → Model.CheckedCliStepState)
    (getEnv : String → StateM W (Except CmdLineError (Option String)))
    (hEnv : ∀ w k, (proj (getEnv k w).2).stdioErr? = (proj w).stdioErr?)
    (visibleOpts : List OptSpec) (cliOpts : List (String × List OptValue))
    (validators : CustomValidators) (w : W) :
    (proj (Internal.resolveOptionsTR getEnv visibleOpts cliOpts validators w).2).stdioErr? =
      (proj w).stdioErr? := by
  unfold Internal.resolveOptionsTR
  suffices ∀ accRev w0,
      (proj (Internal.resolveOptionsTR.go getEnv cliOpts validators visibleOpts accRev w0).2).stdioErr? =
        (proj w0).stdioErr? from this [] w
  induction visibleOpts with
  | nil => intro accRev w0; unfold Internal.resolveOptionsTR.go; rfl
  | cons opt rest ih =>
    intro accRev w0
    unfold Internal.resolveOptionsTR.go
    dsimp only [Bind.bind, StateT.bind]
    have stepCase : ∀ cliVals,
        (proj ((match Internal.resolveSingleOptionFast getEnv opt cliVals validators w0 with
          | (a, s) =>
            (match a with
             | Except.error e => (pure (Except.error e) : StateM W (Except CmdLineError (List (String × List OptValue))))
             | Except.ok resolved? =>
               match resolved? with
               | none => Internal.resolveOptionsTR.go getEnv cliOpts validators rest accRev
               | some vals => Internal.resolveOptionsTR.go getEnv cliOpts validators rest ((opt.name, vals) :: accRev)) s).2)).stdioErr? =
          (proj w0).stdioErr? := fun cliVals => by
      have hOne := resolveSingleOptionFast_preserves_stdioErr proj getEnv hEnv opt cliVals validators w0
      cases hs : Internal.resolveSingleOptionFast getEnv opt cliVals validators w0 with
      | mk a w1 =>
        rw [hs] at hOne
        cases a with
        | error _ => exact hOne
        | ok resolved? =>
          cases resolved? with
          | none => exact (ih accRev w1).trans hOne
          | some vals => exact (ih ((opt.name, vals) :: accRev) w1).trans hOne
    cases cliOpts.find? (fun p => p.1 == opt.name) with
    | none => exact stepCase []
    | some p => exact stepCase p.2

/-- `Internal.parseWithEnvM` over `ops.cliOps` preserves `stdioErr?`. -/
theorem parseWithEnvM_preserves_stdioErr {W : Type} (proj : W → Model.CheckedCliStepState)
    (ops : Model.CheckedCliOpsM (StateM W))
    (hChecked : Core.ObeysStep proj Model.checkedStepWf (Model.execCheckedRawStep ops) Model.allowedCheckedRawStep)
    (spec : CommandSpec) (args : List String) (validators : CustomValidators) (w : W) :
    (proj (Internal.parseWithEnvM ops.cliOps spec args validators w).2).stdioErr? = (proj w).stdioErr? := by
  have hEnv : ∀ w0 k, (proj (ops.cliOps.getEnv k w0).2).stdioErr? = (proj w0).stdioErr? := fun w0 k => by
    have h := checkedOps_raw_preserves_stdioErr proj ops hChecked (.getEnv k) w0
    dsimp only [Model.execRawStep, Functor.map, StateT.map] at h
    cases hg : ops.cliOps.getEnv k w0 with
    | mk _ w1 => simp only [hg] at h ⊢; exact h
  rw [parseWithEnvM_eq_spec]
  unfold Internal.parseWithEnvSpecM
  cases (!Internal.isValidSpecTR spec) with
  | true => simp only [↓reduceIte]; rfl
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte]
    cases Internal.parseTokens spec.name validators { curSpec := spec, effectiveVersion := spec.version } args with
    | error _ => rfl
    | ok finalState =>
      dsimp only [Bind.bind, StateT.bind, Pure.pure, StateT.pure]
      cases (!finalState.curSpec.subcommands.isEmpty) with
      | true => simp only [↓reduceIte]; cases (!finalState.rawPositionals.isEmpty) <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> rfl
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte]
        dsimp only [Bind.bind, StateT.bind, Pure.pure, StateT.pure]
        have hRo := resolveOptionsTR_preserves_stdioErr proj ops.cliOps.getEnv hEnv
          (finalState.inheritedGlobals ++ finalState.curSpec.options) finalState.cliOpts validators w
        cases hRun : Internal.resolveOptionsTR ops.cliOps.getEnv
            (finalState.inheritedGlobals ++ finalState.curSpec.options) finalState.cliOpts validators w with
        | mk ro w1 =>
          rw [hRun] at hRo
          cases ro with
          | error _ => exact hRo
          | ok _ =>
            cases Internal.resolveArgsTR finalState.curSpec.args finalState.rawPositionals validators <;> exact hRo

/-- `Internal.runCliWith` over `ops.cliOps` with a pure exit-code callback preserves `stdioErr?`. -/
theorem runCliWith_preserves_stdioErr {W : Type} (proj : W → Model.CheckedCliStepState)
    (ops : Model.CheckedCliOpsM (StateM W))
    (hChecked : Core.ObeysStep proj Model.checkedStepWf (Model.execCheckedRawStep ops) Model.allowedCheckedRawStep)
    (spec : CommandSpec) (args : List String) (validators : CustomValidators)
    (exitCode : UInt32) (w : W) :
    (proj (Internal.runCliWith ops.cliOps spec args validators (fun _ => pure exitCode) w).2).stdioErr? =
      (proj w).stdioErr? := by
  have hp := parseWithEnvM_preserves_stdioErr proj ops hChecked spec args validators w
  unfold Internal.runCliWith
  dsimp only [Bind.bind, StateT.bind]
  cases hpr : Internal.parseWithEnvM ops.cliOps spec args validators w with
  | mk res w1 =>
    rw [hpr] at hp
    cases res with
    | ok _ => exact hp
    | error e =>
      dsimp only
      have hOut : (proj ((StateT.bind (ops.cliOps.writeOut e.message) (fun _ => pure (0 : UInt32))) w1).2).stdioErr? = (proj w).stdioErr? := by
        have ho := checkedOps_raw_preserves_stdioErr proj ops hChecked (.writeOut e.message) w1
        dsimp only [Model.execRawStep, SeqRight.seqRight, Bind.bind, StateT.bind, Pure.pure, StateT.pure, Id.instMonad] at ho ⊢
        cases hwo : ops.cliOps.writeOut e.message w1 with
        | mk _ w2 => simp only [hwo] at ho ⊢; exact ho.trans hp
      have hErr : (proj ((StateT.bind (ops.cliOps.writeErr (e.message ++ "\n")) (fun _ => pure (2 : UInt32))) w1).2).stdioErr? = (proj w).stdioErr? := by
        have he := checkedOps_raw_preserves_stdioErr proj ops hChecked (.writeErr (e.message ++ "\n")) w1
        dsimp only [Model.execRawStep, SeqRight.seqRight, Bind.bind, StateT.bind, Pure.pure, StateT.pure, Id.instMonad] at he ⊢
        cases hwe : ops.cliOps.writeErr (e.message ++ "\n") w1 with
        | mk _ w2 => simp only [hwe] at he ⊢; exact he.trans hp
      cases e.kind <;> dsimp only <;> first | exact hOut | exact hErr

/-- Single-step specification of `SysBridge.promptLineChecked` over `CheckedCliOpsM`. -/
theorem promptLineChecked_step_spec {W : Type} (proj : W → Model.CheckedCliStepState)
    (ops : Model.CheckedCliOpsM (StateM W))
    (hChecked : Core.ObeysStep proj Model.checkedStepWf (Model.execCheckedRawStep ops) Model.allowedCheckedRawStep)
    (prompt : String) (default : Option String) (w : W) :
    let r := SysBridge.promptLineChecked ops prompt default w
    (r.1, proj r.2) = Model.stepCheckedPromptLine (proj w) prompt default := by
  dsimp only
  unfold SysBridge.promptLineChecked Model.stepCheckedPromptLine
  dsimp only [Bind.bind, StateT.bind]
  have hw := hChecked w (.writeOutChecked prompt) rfl
  dsimp only [Model.execCheckedRawStep, Model.allowedCheckedRawStep, Functor.map, StateT.map,
    Bind.bind, StateT.bind, Pure.pure, StateT.pure, StateT.run, Id.instMonad] at hw
  cases ho : ops.writeOutChecked prompt w with
  | mk outRes w1 =>
    simp only [ho] at hw ⊢
    dsimp only [Bind.bind, Pure.pure, StateT.pure, Id.instMonad] at hw ⊢
    cases hErr : (proj w).stdioErr? with
    | some msg =>
      simp only [hErr] at hw
      rcases hw with ⟨rfl, hw1⟩
      dsimp only [Pure.pure, StateT.pure]
      rw [hw1]
    | none =>
      simp only [hErr] at hw
      rcases hw with ⟨rfl, hw1⟩
      dsimp only [Bind.bind, StateT.bind]
      have hr := hChecked w1 .readLineChecked rfl
      dsimp only [Model.execCheckedRawStep, Model.allowedCheckedRawStep, Functor.map, StateT.map,
        Bind.bind, StateT.bind, Pure.pure, StateT.pure, StateT.run, Id.instMonad] at hr
      cases hl : ops.readLineChecked w1 with
      | mk lineRes w2 =>
        simp only [hl] at hr ⊢
        rw [hw1] at hr
        dsimp only at hr
        unfold Model.stepCliPromptLine
        cases hlines : (proj w).cli.stdinLines with
        | nil =>
          simp only [hlines] at hr
          rcases hr with ⟨rfl, hw2⟩
          dsimp only [Pure.pure, StateT.pure]
          rw [hw2]
        | cons hd tl =>
          simp only [hlines] at hr
          rcases hr with ⟨rfl, hw2⟩
          cases default <;>
            (by_cases hEmp : (Model.trimAscii hd).isEmpty = true
             · simp only [hEmp, ↓reduceIte, StateT.pure, Pure.pure, hw2]
             · simp only [hEmp, Bool.false_eq_true, ↓reduceIte, StateT.pure, Pure.pure, hw2])

private theorem stepCheckedConfirm_of_none (s : Model.CheckedCliStepState) (hNone : s.stdioErr? = none)
    (prompt : String) (default : Option Bool) (k : Nat) :
    Model.stepCheckedConfirm s prompt default k =
      let (res, c') := Model.stepCliConfirm s.cli prompt default k
      (res, { s with cli := c' }) := by
  cases k with
  | zero => rfl
  | succ m => simp [Model.stepCheckedConfirm, hNone]

/-- Single-step specification of `SysBridge.confirmChecked` over `CheckedCliOpsM`. -/
theorem confirmChecked_step_spec {W : Type} (proj : W → Model.CheckedCliStepState)
    (ops : Model.CheckedCliOpsM (StateM W))
    (hChecked : Core.ObeysStep proj Model.checkedStepWf (Model.execCheckedRawStep ops) Model.allowedCheckedRawStep)
    (prompt : String) (default : Option Bool) (maxAttempts : Nat) :
    ∀ w : W,
      let r := SysBridge.confirmChecked ops prompt default maxAttempts w
      (r.1, proj r.2) = Model.stepCheckedConfirm (proj w) prompt default maxAttempts := by
  induction maxAttempts with
  | zero =>
    intro w
    unfold SysBridge.confirmChecked Model.stepCheckedConfirm
    rfl
  | succ n ih =>
    intro w
    dsimp only
    unfold SysBridge.confirmChecked Model.stepCheckedConfirm
    dsimp only [Bind.bind, StateT.bind]
    have hw := hChecked w (.writeOutChecked prompt) rfl
    dsimp only [Model.execCheckedRawStep, Model.allowedCheckedRawStep, Functor.map, StateT.map,
      Bind.bind, StateT.bind, Pure.pure, StateT.pure, StateT.run, Id.instMonad] at hw
    cases ho : ops.writeOutChecked prompt w with
    | mk outRes w1 =>
      simp only [ho] at hw ⊢
      dsimp only [Bind.bind, Pure.pure, StateT.pure, Id.instMonad] at hw ⊢
      cases hErr : (proj w).stdioErr? with
      | some msg =>
        simp only [hErr] at hw
        rcases hw with ⟨rfl, hw1⟩
        dsimp only [Pure.pure, StateT.pure]
        rw [hw1]
      | none =>
        simp only [hErr] at hw
        rcases hw with ⟨rfl, hw1⟩
        dsimp only [Bind.bind, StateT.bind]
        have hr := hChecked w1 .readLineChecked rfl
        dsimp only [Model.execCheckedRawStep, Model.allowedCheckedRawStep, Functor.map, StateT.map,
          Bind.bind, StateT.bind, Pure.pure, StateT.pure, StateT.run, Id.instMonad] at hr
        cases hl : ops.readLineChecked w1 with
        | mk lineRes w2 =>
          simp only [hl] at hr ⊢
          rw [hw1] at hr
          dsimp only at hr
          unfold Model.stepCliConfirm
          cases hlines : (proj w).cli.stdinLines with
          | nil =>
            simp only [hlines] at hr
            rcases hr with ⟨rfl, hw2⟩
            dsimp only [Pure.pure, StateT.pure]
            rw [hw2]
          | cons hd tl =>
            simp only [hlines] at hr
            rcases hr with ⟨rfl, hw2⟩
            by_cases hEmp : (Model.asciiLower (Model.trimAscii hd)).isEmpty = true
            · simp only [hEmp, ↓reduceIte]
              cases default with
              | some b =>
                dsimp only [Pure.pure, StateT.pure]
                rw [hw2]
              | none =>
                cases n with
                | zero =>
                  dsimp only [Pure.pure, StateT.pure]
                  rw [hw2]
                | succ m =>
                  dsimp only [Bind.bind, StateT.bind]
                  have he := hChecked w2 (.writeErrChecked "Please answer yes or no.\n") rfl
                  dsimp only [Model.execCheckedRawStep, Model.allowedCheckedRawStep, Functor.map, StateT.map,
                    Bind.bind, StateT.bind, Pure.pure, StateT.pure, StateT.run, Id.instMonad] at he
                  cases hwe : ops.writeErrChecked "Please answer yes or no.\n" w2 with
                  | mk errRes w3 =>
                    simp only [hwe] at he ⊢
                    rw [hw2] at he
                    dsimp only at he
                    rcases he with ⟨rfl, hw3⟩
                    have hrec := ih w3
                    dsimp only at hrec
                    have hNone3 : (proj w3).stdioErr? = none := by rw [hw3]
                    rw [hrec, stepCheckedConfirm_of_none (proj w3) hNone3]
                    simp [hw3]
            · simp only [hEmp, Bool.false_eq_true, ↓reduceIte]
              by_cases hYes : (Model.asciiLower (Model.trimAscii hd) == "y" ||
                  Model.asciiLower (Model.trimAscii hd) == "yes") = true
              · simp only [hYes, ↓reduceIte, Pure.pure, StateT.pure, hw2]
              · simp only [hYes, Bool.false_eq_true, ↓reduceIte]
                by_cases hNo : (Model.asciiLower (Model.trimAscii hd) == "n" ||
                    Model.asciiLower (Model.trimAscii hd) == "no") = true
                · simp only [hNo, ↓reduceIte, Pure.pure, StateT.pure, hw2]
                · simp only [hNo, Bool.false_eq_true, ↓reduceIte]
                  cases n with
                  | zero =>
                    dsimp only [Pure.pure, StateT.pure]
                    rw [hw2]
                  | succ m =>
                    dsimp only [Bind.bind, StateT.bind]
                    have he := hChecked w2 (.writeErrChecked "Please answer yes or no.\n") rfl
                    dsimp only [Model.execCheckedRawStep, Model.allowedCheckedRawStep, Functor.map, StateT.map,
                      Bind.bind, StateT.bind, Pure.pure, StateT.pure, StateT.run, Id.instMonad] at he
                    cases hwe : ops.writeErrChecked "Please answer yes or no.\n" w2 with
                    | mk errRes w3 =>
                      simp only [hwe] at he ⊢
                      rw [hw2] at he
                      dsimp only at he
                      rcases he with ⟨rfl, hw3⟩
                      have hrec := ih w3
                      dsimp only at hrec
                      have hNone3 : (proj w3).stdioErr? = none := by rw [hw3]
                      rw [hrec, stepCheckedConfirm_of_none (proj w3) hNone3]
                      simp [hw3]

end LeanSwe.CmdLine.Proofs
