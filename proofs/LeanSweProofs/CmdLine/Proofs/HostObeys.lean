import Core.Obeys
import LeanSwe.CmdLine.Interface
import LeanSweProofs.CmdLine.Proofs.ParserCore
import LeanSweProofs.CmdLine.Proofs.PhraseBridge
import LeanSweProofs.CmdLine.Proofs.CheckedObeys

namespace LeanSwe.CmdLine.Proofs

open Core LeanSwe.CmdLine LeanSwe.CmdLine.Proofs.Shared LeanSwe.LinuxSyscall

private theorem catchStdioM_step_eq {W α : Type}
    (act : ExceptT IO.Error (StateM W) α) (w : W) :
    ((SysBridge.catchStdioM act).run.run w) =
      (.ok (Model.catchHostStdio (act.run.run w).1), (act.run.run w).2) := by
  unfold SysBridge.catchStdioM Model.catchHostStdio
  rw [exceptT_run_tryCatch, exceptT_run_map]
  cases hr : act.run.run w with
  | mk res w1 =>
    cases res <;> rfl

private theorem promptLineCheckedM_step_spec {W : Type} (proj : W → Model.CmdLineHostState)
    (caps : Model.CmdLineCapsM (ExceptT IO.Error (StateM W)))
    (hCaps : Core.ObeysStepExcept proj Model.hostStepWf (Model.execCapsStep caps) Model.allowedHostCapsStep)
    (prompt : String) (default : Option String) (w : W) :
    (((SysBridge.promptLineCheckedM (Internal.mkCliOpsFromCapsM caps) prompt default).run.run w).1,
      proj ((SysBridge.promptLineCheckedM (Internal.mkCliOpsFromCapsM caps) prompt default).run.run w).2) =
      (.ok (Model.stepHostPromptLine (proj w) prompt default).1,
        (Model.stepHostPromptLine (proj w) prompt default).2) := by
  unfold SysBridge.promptLineCheckedM Model.stepHostPromptLine
  rw [exceptT_run_bind, catchStdioM_step_eq]
  have hw := mkCliOps_writeOut_spec proj caps hCaps prompt w
  cases ho : ((Internal.mkCliOpsFromCapsM caps).writeOut prompt).run.run w with
  | mk wOut w1 =>
    rw [ho] at hw
    cases hsw : Model.stepHostWriteSlot true (proj w) prompt with
    | mk mwOut s1 =>
      rw [hsw] at hw
      rcases hw with ⟨rfl, hw1⟩
      dsimp only at hw1 ⊢
      cases hc1 : Model.catchHostStdio wOut with
      | error e =>
        exact Prod.ext rfl hw1
      | ok u =>
        cases u
        dsimp only
        rw [exceptT_run_bind, catchStdioM_step_eq]
        have hr := mkCliOps_readLine_spec proj caps hCaps w1
        rw [hw1] at hr
        cases hl : ((Internal.mkCliOpsFromCapsM caps).readLine).run.run w1 with
        | mk rOut w2 =>
          rw [hl] at hr
          cases hsr : Model.stepHostReadLine s1 with
          | mk mrOut s2 =>
            rw [hsr] at hr
            rcases hr with ⟨rfl, hw2⟩
            dsimp only at hw2 ⊢
            cases hc2 : Model.catchHostStdio rOut with
            | error e =>
              exact Prod.ext rfl hw2
            | ok line? =>
              cases line? with
              | none =>
                exact Prod.ext rfl hw2
              | some line =>
                dsimp only
                rw [internal_trimAscii_eq]
                by_cases hEmp : (Model.trimAscii line).isEmpty = true
                · simp only [hEmp, ↓reduceIte]
                  cases default <;> exact Prod.ext rfl hw2
                · simp only [hEmp, Bool.false_eq_true, ↓reduceIte]
                  dsimp only [exceptT_run_pure]
                  exact Prod.ext rfl hw2

private theorem confirmCheckedM_step_spec {W : Type} (proj : W → Model.CmdLineHostState)
    (caps : Model.CmdLineCapsM (ExceptT IO.Error (StateM W)))
    (hCaps : Core.ObeysStepExcept proj Model.hostStepWf (Model.execCapsStep caps) Model.allowedHostCapsStep)
    (prompt : String) (default : Option Bool) (maxAttempts : Nat) :
    ∀ (w : W),
      (((SysBridge.confirmCheckedM (Internal.mkCliOpsFromCapsM caps) prompt default maxAttempts).run.run w).1,
        proj ((SysBridge.confirmCheckedM (Internal.mkCliOpsFromCapsM caps) prompt default maxAttempts).run.run w).2) =
        (.ok (Model.stepHostConfirm (proj w) prompt default maxAttempts).1,
          (Model.stepHostConfirm (proj w) prompt default maxAttempts).2) := by
  induction maxAttempts with
  | zero =>
    intro w
    unfold SysBridge.confirmCheckedM Model.stepHostConfirm
    rfl
  | succ n ih =>
    intro w
    unfold SysBridge.confirmCheckedM Model.stepHostConfirm
    rw [exceptT_run_bind, catchStdioM_step_eq]
    have hw := mkCliOps_writeOut_spec proj caps hCaps prompt w
    cases ho : ((Internal.mkCliOpsFromCapsM caps).writeOut prompt).run.run w with
    | mk wOut w1 =>
      rw [ho] at hw
      cases hsw : Model.stepHostWriteSlot true (proj w) prompt with
      | mk mwOut s1 =>
        rw [hsw] at hw
        rcases hw with ⟨rfl, hw1⟩
        dsimp only at hw1 ⊢
        cases hc1 : Model.catchHostStdio wOut with
        | error e =>
          exact Prod.ext rfl hw1
        | ok u =>
          cases u
          dsimp only
          rw [exceptT_run_bind, catchStdioM_step_eq]
          have hr := mkCliOps_readLine_spec proj caps hCaps w1
          rw [hw1] at hr
          cases hl : ((Internal.mkCliOpsFromCapsM caps).readLine).run.run w1 with
          | mk rOut w2 =>
            rw [hl] at hr
            cases hsr : Model.stepHostReadLine s1 with
            | mk mrOut s2 =>
              rw [hsr] at hr
              rcases hr with ⟨rfl, hw2⟩
              dsimp only at hw2 ⊢
              cases hc2 : Model.catchHostStdio rOut with
              | error e =>
                exact Prod.ext rfl hw2
              | ok line? =>
                cases line? with
                | none =>
                  exact Prod.ext rfl hw2
                | some line =>
                  dsimp only
                  have retryBranch :
                      ∀ (m : Nat), n = m + 1 →
                        (((do
                            match ← SysBridge.catchStdioM ((Internal.mkCliOpsFromCapsM caps).writeErr "Please answer yes or no.\n") with
                            | Except.error e => return Except.error e
                            | Except.ok () => SysBridge.confirmCheckedM (Internal.mkCliOpsFromCapsM caps) prompt default (m + 1)).run.run w2).1,
                          proj ((do
                            match ← SysBridge.catchStdioM ((Internal.mkCliOpsFromCapsM caps).writeErr "Please answer yes or no.\n") with
                            | Except.error e => return Except.error e
                            | Except.ok () => SysBridge.confirmCheckedM (Internal.mkCliOpsFromCapsM caps) prompt default (m + 1)).run.run w2).2) =
                          (Except.ok (match Model.catchHostStdio (Model.stepHostWriteSlot false s2 "Please answer yes or no.\n").1 with
                                | Except.error e => (Except.error e, (Model.stepHostWriteSlot false s2 "Please answer yes or no.\n").2)
                                | Except.ok () => Model.stepHostConfirm (Model.stepHostWriteSlot false s2 "Please answer yes or no.\n").2 prompt default (m + 1)).1,
                           (match Model.catchHostStdio (Model.stepHostWriteSlot false s2 "Please answer yes or no.\n").1 with
                            | Except.error e => (Except.error e, (Model.stepHostWriteSlot false s2 "Please answer yes or no.\n").2)
                            | Except.ok () => Model.stepHostConfirm (Model.stepHostWriteSlot false s2 "Please answer yes or no.\n").2 prompt default (m + 1)).2) := fun m hmn => by
                    rw [exceptT_run_bind, catchStdioM_step_eq]
                    have he := mkCliOps_writeErr_spec proj caps hCaps "Please answer yes or no.\n" w2
                    rw [hw2] at he
                    cases hwe : ((Internal.mkCliOpsFromCapsM caps).writeErr "Please answer yes or no.\n").run.run w2 with
                    | mk eOut w3 =>
                      rw [hwe] at he
                      cases hse : Model.stepHostWriteSlot false s2 "Please answer yes or no.\n" with
                      | mk meOut s3 =>
                        rw [hse] at he
                        rcases he with ⟨rfl, hw3⟩
                        dsimp only at hw3 ⊢
                        cases hc3 : Model.catchHostStdio eOut with
                        | error e =>
                          exact Prod.ext rfl hw3
                        | ok u2 =>
                          cases u2
                          rw [← hmn]
                          have hRec := ih w3
                          rw [hw3] at hRec
                          exact hRec
                  rw [internal_trimAscii_eq, internal_asciiLower_eq]
                  by_cases hEmp : (Model.asciiLower (Model.trimAscii line)).isEmpty = true
                  · simp only [hEmp, ↓reduceIte]
                    cases default with
                    | some b => exact Prod.ext rfl hw2
                    | none =>
                      cases hN : n with
                      | zero => exact Prod.ext rfl hw2
                      | succ m => exact retryBranch m hN
                  · simp only [hEmp, Bool.false_eq_true, ↓reduceIte]
                    by_cases hYes : (Model.asciiLower (Model.trimAscii line) == "y" ||
                        Model.asciiLower (Model.trimAscii line) == "yes") = true
                    · simp only [hYes, ↓reduceIte]
                      dsimp only [exceptT_run_pure]
                      exact Prod.ext rfl hw2
                    · simp only [hYes, Bool.false_eq_true, ↓reduceIte]
                      by_cases hNo : (Model.asciiLower (Model.trimAscii line) == "n" ||
                          Model.asciiLower (Model.trimAscii line) == "no") = true
                      · simp only [hNo, ↓reduceIte]
                        dsimp only [exceptT_run_pure]
                        exact Prod.ext rfl hw2
                      · simp only [hNo, Bool.false_eq_true, ↓reduceIte]
                        cases hN : n with
                        | zero => exact Prod.ext rfl hw2
                        | succ m => exact retryBranch m hN

private theorem resolveSingleOptionFast_except_eq {W : Type} (proj : W → Model.CmdLineHostState)
    (getEnv : String → ExceptT IO.Error (StateM W) (Except CmdLineError (Option String)))
    (hEnv : ∀ w k, ((getEnv k).run.run w).1 = .ok (Model.lookupHostEnv (proj w).env k) ∧
      proj ((getEnv k).run.run w).2 = proj w)
    (opt : OptSpec) (cliVals : List OptValue) (validators : CustomValidators) (w : W) :
    ((Internal.resolveSingleOptionFast getEnv opt cliVals validators).run.run w).1 =
        .ok (Model.resolveSingleOption (m := Id) (Model.lookupHostEnv (proj w).env) opt cliVals validators) ∧
      proj ((Internal.resolveSingleOptionFast getEnv opt cliVals validators).run.run w).2 = proj w := by
  rw [resolveSingleOptionFast_eq]
  unfold Model.resolveSingleOption
  by_cases hcli : !cliVals.isEmpty
  · simp only [hcli, ↓reduceIte]
    split <;> exact ⟨rfl, rfl⟩
  · simp only [hcli, Bool.false_eq_true, ↓reduceIte]
    cases opt.envVar with
    | none => exact ⟨rfl, rfl⟩
    | some envKey =>
      rw [exceptT_run_bind]
      dsimp only [Bind.bind, Id.instMonad, Pure.pure]
      have hg := hEnv w envKey
      cases hr : (getEnv envKey).run.run w with
      | mk res w1 =>
        rw [hr] at hg
        rcases hg with ⟨rfl, hw1⟩
        dsimp only at hw1 ⊢
        cases Model.lookupHostEnv (proj w).env envKey with
        | error _ => exact ⟨rfl, hw1⟩
        | ok v? =>
          cases v? with
          | none => exact ⟨rfl, hw1⟩
          | some s =>
            if hs : s = "" then
              subst hs; exact ⟨rfl, hw1⟩
            else
              unfold Model.resolveSingleOption.match_1
              dsimp only
              simp only [hs, ↓reduceDIte]
              cases Model.parseOptValueWith opt.kind s validators with
              | error _ =>
                dsimp only [exceptT_run_pure]
                exact ⟨rfl, hw1⟩
              | ok v =>
                dsimp only
                cases (opt.repeatable && opt.kind == .bool && v == .bool false)
                · simp only [Bool.false_eq_true, ↓reduceIte]; exact ⟨rfl, hw1⟩
                · simp only [↓reduceIte]; exact ⟨rfl, hw1⟩

private theorem resolveOptionsTR_except_eq {W : Type} (proj : W → Model.CmdLineHostState)
    (getEnv : String → ExceptT IO.Error (StateM W) (Except CmdLineError (Option String)))
    (hEnv : ∀ w k, ((getEnv k).run.run w).1 = .ok (Model.lookupHostEnv (proj w).env k) ∧
      proj ((getEnv k).run.run w).2 = proj w)
    (visibleOpts : List OptSpec) (cliOpts : List (String × List OptValue))
    (validators : CustomValidators) (w : W) :
    ((Internal.resolveOptionsTR getEnv visibleOpts cliOpts validators).run.run w).1 =
        .ok (Model.resolveOptions (m := Id) (Model.lookupHostEnv (proj w).env) visibleOpts cliOpts validators) ∧
      proj ((Internal.resolveOptionsTR getEnv visibleOpts cliOpts validators).run.run w).2 = proj w := by
  unfold Internal.resolveOptionsTR
  suffices ∀ accRev w0,
      ((Internal.resolveOptionsTR.go getEnv cliOpts validators visibleOpts accRev).run.run w0).1 =
          .ok ((Model.resolveOptions (m := Id) (Model.lookupHostEnv (proj w0).env) visibleOpts cliOpts validators).map
                (fun tail => accRev.reverse ++ tail)) ∧
        proj ((Internal.resolveOptionsTR.go getEnv cliOpts validators visibleOpts accRev).run.run w0).2 = proj w0 by
    have h0 := this [] w
    dsimp only [List.reverse_nil, List.nil_append] at h0
    refine ⟨h0.1.trans (congrArg Except.ok ?_), h0.2⟩
    cases Model.resolveOptions (m := Id) (Model.lookupHostEnv (proj w).env) visibleOpts cliOpts validators <;> rfl
  induction visibleOpts with
  | nil =>
    intro accRev w0
    unfold Internal.resolveOptionsTR.go Model.resolveOptions
    dsimp only [exceptT_run_pure, Pure.pure, Id.instMonad, Except.map]
    simp only [List.append_nil]
    exact ⟨rfl, rfl⟩
  | cons opt rest ih =>
    intro accRev w0
    unfold Internal.resolveOptionsTR.go Model.resolveOptions
    have stepCase : ∀ cliVals,
        ((do
          match ← Internal.resolveSingleOptionFast getEnv opt cliVals validators with
          | Except.error e => return Except.error e
          | Except.ok resolved? =>
            match resolved? with
            | none => Internal.resolveOptionsTR.go getEnv cliOpts validators rest accRev
            | some vals => Internal.resolveOptionsTR.go getEnv cliOpts validators rest ((opt.name, vals) :: accRev)).run.run w0).1 =
          Except.ok ((match Model.resolveSingleOption (m := Id) (Model.lookupHostEnv (proj w0).env) opt cliVals validators with
            | Except.error e => Except.error e
            | Except.ok resolved? =>
              match Model.resolveOptions (m := Id) (Model.lookupHostEnv (proj w0).env) rest cliOpts validators with
              | Except.error e => Except.error e
              | Except.ok tail =>
                match resolved? with
                | none => Except.ok tail
                | some vals => Except.ok ((opt.name, vals) :: tail)).map (fun tail => accRev.reverse ++ tail)) ∧
          proj ((do
            match ← Internal.resolveSingleOptionFast getEnv opt cliVals validators with
            | Except.error e => return Except.error e
            | Except.ok resolved? =>
              match resolved? with
              | none => Internal.resolveOptionsTR.go getEnv cliOpts validators rest accRev
              | some vals => Internal.resolveOptionsTR.go getEnv cliOpts validators rest ((opt.name, vals) :: accRev)).run.run w0).2 = proj w0 := fun cliVals => by
      rw [exceptT_run_bind]
      have hOne := resolveSingleOptionFast_except_eq proj getEnv hEnv opt cliVals validators w0
      cases hs : (Internal.resolveSingleOptionFast getEnv opt cliVals validators).run.run w0 with
      | mk rOne w1 =>
        rw [hs] at hOne
        rcases hOne with ⟨rfl, hw1⟩
        dsimp only at hw1 ⊢
        cases Model.resolveSingleOption (m := Id) (Model.lookupHostEnv (proj w0).env) opt cliVals validators with
        | error _ => exact ⟨rfl, hw1⟩
        | ok res? =>
          cases res? with
          | none =>
            have hRec := ih accRev w1
            rw [hw1] at hRec
            refine ⟨hRec.1.trans (congrArg Except.ok ?_), hRec.2⟩
            cases Model.resolveOptions (m := Id) (Model.lookupHostEnv (proj w0).env) rest cliOpts validators <;> rfl
          | some vals =>
            have hRec := ih ((opt.name, vals) :: accRev) w1
            rw [hw1] at hRec
            refine ⟨hRec.1.trans (congrArg Except.ok ?_), hRec.2⟩
            cases Model.resolveOptions (m := Id) (Model.lookupHostEnv (proj w0).env) rest cliOpts validators with
            | error _ => rfl
            | ok tail => simp [Except.map, List.reverse_cons, List.append_assoc]
    cases cliOpts.find? (fun p => p.1 == opt.name) with
    | none => dsimp only [Bind.bind, Pure.pure, Id.instMonad]; exact stepCase []
    | some p => dsimp only [Bind.bind, Pure.pure, Id.instMonad]; exact stepCase p.2

private def hostEnvStateOps (env : LeanSwe.EnvVars.Raw.Model.EnvironState) : CliOpsM (StateM Unit) :=
  { readLine := pure none
    writeOut := fun _ => pure ()
    writeErr := fun _ => pure ()
    getEnv := fun k => pure (Model.lookupHostEnv env k) }

private theorem parseWithEnvM_except_spec {W : Type} (proj : W → Model.CmdLineHostState)
    (caps : Model.CmdLineCapsM (ExceptT IO.Error (StateM W)))
    (hCaps : Core.ObeysStepExcept proj Model.hostStepWf (Model.execCapsStep caps) Model.allowedHostCapsStep)
    (spec : CommandSpec) (args : List String) (validators : CustomValidators) (w : W) :
    ∃ res : Except CmdLineError ParsedCmd,
      ((Internal.parseWithEnvM (Internal.mkCliOpsFromCapsM caps) spec args validators).run.run w).1 = .ok res ∧
        proj ((Internal.parseWithEnvM (Internal.mkCliOpsFromCapsM caps) spec args validators).run.run w).2 = proj w ∧
        Model.AllowedParseOutcome (Model.lookupHostEnv (proj w).env) spec args validators res := by
  have hEnv := fun w0 k => mkCliOps_getEnv_spec proj caps hCaps k w0
  have hEnvUnit : ∀ visibleOpts cliOpts,
      (Internal.resolveOptionsTR (hostEnvStateOps (proj w).env).getEnv visibleOpts cliOpts validators ()).1 =
        Model.resolveOptions (m := Id) (Model.lookupHostEnv (proj w).env) visibleOpts cliOpts validators := by
    intro visibleOpts cliOpts
    suffices ∀ accRev,
        (Internal.resolveOptionsTR.go (hostEnvStateOps (proj w).env).getEnv cliOpts validators visibleOpts accRev ()).1 =
          (Model.resolveOptions (m := Id) (Model.lookupHostEnv (proj w).env) visibleOpts cliOpts validators).map
            (fun tail => accRev.reverse ++ tail) by
      have h0 := this []
      dsimp only [List.reverse_nil, List.nil_append] at h0
      refine h0.trans ?_
      cases Model.resolveOptions (m := Id) (Model.lookupHostEnv (proj w).env) visibleOpts cliOpts validators <;> rfl
    induction visibleOpts with
    | nil =>
      intro accRev; unfold Internal.resolveOptionsTR.go Model.resolveOptions
      simp [Pure.pure, StateT.pure, Except.map]
    | cons opt rest ih =>
      intro accRev
      unfold Internal.resolveOptionsTR.go Model.resolveOptions
      dsimp only [Bind.bind, StateT.bind, Id.instMonad]
      have hOneEq : ∀ cv,
          (Internal.resolveSingleOptionFast (hostEnvStateOps (proj w).env).getEnv opt cv validators ()).1 =
            Model.resolveSingleOption (m := Id) (Model.lookupHostEnv (proj w).env) opt cv validators := fun cv => by
        rw [resolveSingleOptionFast_eq]
        unfold Model.resolveSingleOption
        by_cases hc : !cv.isEmpty
        · simp only [hc, ↓reduceIte]; split <;> rfl
        · simp only [hc, Bool.false_eq_true, ↓reduceIte]
          cases opt.envVar with
          | none => rfl
          | some ek =>
            dsimp only [hostEnvStateOps, Bind.bind, StateT.bind, Pure.pure, StateT.pure, Id.instMonad]
            cases Model.lookupHostEnv (proj w).env ek with
            | error _ => rfl
            | ok v? =>
              cases v? with
              | none => rfl
              | some s =>
                if hs : s = "" then subst hs; rfl
                else
                  unfold Model.resolveSingleOption.match_1; dsimp only; simp only [hs, ↓reduceDIte]
                  cases Model.parseOptValueWith opt.kind s validators with
                  | error _ => rfl
                  | ok v =>
                    dsimp only
                    cases (opt.repeatable && opt.kind == .bool && v == .bool false)
                    · simp only [Bool.false_eq_true, ↓reduceIte]; rfl
                    · simp only [↓reduceIte]; rfl
      have stepU : ∀ cv,
          (match Internal.resolveSingleOptionFast (hostEnvStateOps (proj w).env).getEnv opt cv validators () with
           | (a, s) =>
             (match a with
              | Except.error e => (pure (Except.error e) : StateM Unit (Except CmdLineError (List (String × List OptValue))))
              | Except.ok resolved? =>
                match resolved? with
                | none => Internal.resolveOptionsTR.go (hostEnvStateOps (proj w).env).getEnv cliOpts validators rest accRev
                | some vals => Internal.resolveOptionsTR.go (hostEnvStateOps (proj w).env).getEnv cliOpts validators rest ((opt.name, vals) :: accRev)) s).1 =
          (match Model.resolveSingleOption (m := Id) (Model.lookupHostEnv (proj w).env) opt cv validators with
           | Except.error e => Except.error e
           | Except.ok resolved? =>
             match Model.resolveOptions (m := Id) (Model.lookupHostEnv (proj w).env) rest cliOpts validators with
             | Except.error e => Except.error e
             | Except.ok tail =>
               match resolved? with
               | none => Except.ok tail
               | some vals => Except.ok ((opt.name, vals) :: tail)).map (fun tail => accRev.reverse ++ tail) := fun cv => by
        have ho := hOneEq cv
        cases hs : Internal.resolveSingleOptionFast (hostEnvStateOps (proj w).env).getEnv opt cv validators () with
        | mk r1 u1 =>
          cases u1
          rw [hs] at ho; dsimp only at ho; rw [ho]
          cases Model.resolveSingleOption (m := Id) (Model.lookupHostEnv (proj w).env) opt cv validators with
          | error _ => rfl
          | ok res? =>
            cases res? with
            | none =>
              refine (ih accRev).trans ?_
              cases Model.resolveOptions (m := Id) (Model.lookupHostEnv (proj w).env) rest cliOpts validators <;> rfl
            | some vals =>
              refine (ih ((opt.name, vals) :: accRev)).trans ?_
              cases Model.resolveOptions (m := Id) (Model.lookupHostEnv (proj w).env) rest cliOpts validators with
              | error _ => rfl
              | ok tail => simp [Except.map, List.reverse_cons, List.append_assoc]
      cases cliOpts.find? (fun p => p.1 == opt.name) with
      | none => dsimp only [Bind.bind, Pure.pure, Id.instMonad]; exact stepU []
      | some p => dsimp only [Bind.bind, Pure.pure, Id.instMonad]; exact stepU p.2
  have hAllowed := parseWithEnvSpecM_allowedOutcome
    (ops := hostEnvStateOps (proj w).env) (spec := spec) (args := args) (validators := validators) (w := ()) hEnvUnit
  rw [parseWithEnvM_eq_spec]
  suffices
      ((Internal.parseWithEnvSpecM (Internal.mkCliOpsFromCapsM caps) spec args validators).run.run w).1 =
        .ok (Internal.parseWithEnvSpecM (hostEnvStateOps (proj w).env) spec args validators ()).1 ∧
      proj ((Internal.parseWithEnvSpecM (Internal.mkCliOpsFromCapsM caps) spec args validators).run.run w).2 = proj w by
    exact ⟨_, this.1, this.2, hAllowed⟩
  unfold Internal.parseWithEnvSpecM
  cases (!Internal.isValidSpecTR spec) with
  | true => simp only [↓reduceIte]; dsimp only [exceptT_run_pure]; exact ⟨rfl, rfl⟩
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte]
    cases Internal.parseTokens spec.name validators { curSpec := spec, effectiveVersion := spec.version } args with
    | error _ => exact ⟨rfl, rfl⟩
    | ok finalState =>
      dsimp only [StateT.bind, StateT.pure]
      cases (!finalState.curSpec.subcommands.isEmpty) with
      | true =>
        simp only [↓reduceIte]
        cases (!finalState.rawPositionals.isEmpty)
        · simp only [Bool.false_eq_true, ↓reduceIte]; dsimp only [exceptT_run_pure]; exact ⟨rfl, rfl⟩
        · simp only [↓reduceIte]; dsimp only [exceptT_run_pure]; exact ⟨rfl, rfl⟩
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte]
        rw [exceptT_run_bind]
        dsimp only [Bind.bind, StateT.bind, Pure.pure, StateT.pure]
        have hRo := resolveOptionsTR_except_eq proj (Internal.mkCliOpsFromCapsM caps).getEnv hEnv
          (finalState.inheritedGlobals ++ finalState.curSpec.options) finalState.cliOpts validators w
        cases hRun : (Internal.resolveOptionsTR (Internal.mkCliOpsFromCapsM caps).getEnv
            (finalState.inheritedGlobals ++ finalState.curSpec.options) finalState.cliOpts validators).run.run w with
        | mk ro w1 =>
          rw [hRun] at hRo
          rcases hRo with ⟨rfl, hw1⟩
          dsimp only at hw1 ⊢
          have hUnit := hEnvUnit (finalState.inheritedGlobals ++ finalState.curSpec.options) finalState.cliOpts
          cases hRunU : Internal.resolveOptionsTR (hostEnvStateOps (proj w).env).getEnv
              (finalState.inheritedGlobals ++ finalState.curSpec.options) finalState.cliOpts validators () with
          | mk roU _ =>
            rw [hRunU] at hUnit; dsimp only at hUnit; rw [← hUnit]
            cases roU with
            | error _ => exact ⟨rfl, hw1⟩
            | ok _ =>
              dsimp only
              cases Internal.resolveArgsTR finalState.curSpec.args finalState.rawPositionals validators <;>
                exact ⟨rfl, hw1⟩

private theorem runCliWith_except_spec {W : Type} (proj : W → Model.CmdLineHostState)
    (caps : Model.CmdLineCapsM (ExceptT IO.Error (StateM W)))
    (hCaps : Core.ObeysStepExcept proj Model.hostStepWf (Model.execCapsStep caps) Model.allowedHostCapsStep)
    (spec : CommandSpec) (args : List String) (validators : CustomValidators)
    (exitCode : UInt32) (w : W) :
    Model.allowedHostRunCliWith (proj w) spec args validators exitCode
      ((Model.PkgStepOut.code <$>
        Internal.runCliWith (Internal.mkCliOpsFromCapsM caps) spec args validators (fun _ => pure exitCode)).run.run w).1
      (proj ((Model.PkgStepOut.code <$>
        Internal.runCliWith (Internal.mkCliOpsFromCapsM caps) spec args validators (fun _ => pure exitCode)).run.run w).2) := by
  rw [exceptT_run_map]
  unfold Internal.runCliWith Model.allowedHostRunCliWith
  rw [exceptT_run_bind]
  rcases parseWithEnvM_except_spec proj caps hCaps spec args validators w with ⟨outcome, hOut, hw1, hParse⟩
  cases hp : (Internal.parseWithEnvM (Internal.mkCliOpsFromCapsM caps) spec args validators).run.run w with
  | mk pRes w1 =>
    rw [hp] at hOut hw1
    dsimp only at hOut hw1
    subst hOut
    refine ⟨outcome, hParse, ?_⟩
    cases outcome with
    | ok _ =>
      exact ⟨rfl, hw1⟩
    | error e =>
      dsimp only
      have hOutBr :
          (((do (Internal.mkCliOpsFromCapsM caps).writeOut e.message; return (0 : UInt32)).run.run w1).1.map Model.PkgStepOut.code,
            proj ((do (Internal.mkCliOpsFromCapsM caps).writeOut e.message; return (0 : UInt32)).run.run w1).2) =
            let (wRes, st) := Model.stepHostWriteSlot true (proj w) e.message
            (wRes.map (fun _ => Model.PkgStepOut.code 0), st) := by
        rw [exceptT_run_bind]
        have ho := mkCliOps_writeOut_spec proj caps hCaps e.message w1
        rw [hw1] at ho
        cases hwo : ((Internal.mkCliOpsFromCapsM caps).writeOut e.message).run.run w1 with
        | mk wo w2 =>
          rw [hwo] at ho
          cases hsw : Model.stepHostWriteSlot true (proj w) e.message with
          | mk mwo st =>
            rw [hsw] at ho; dsimp only at ho ⊢
            rcases ho with ⟨rfl, hw2⟩
            cases wo <;> (dsimp only [exceptT_run_pure]; exact Prod.ext rfl hw2)
      have hErrBr :
          (((do (Internal.mkCliOpsFromCapsM caps).writeErr (e.message ++ "\n"); return (2 : UInt32)).run.run w1).1.map Model.PkgStepOut.code,
            proj ((do (Internal.mkCliOpsFromCapsM caps).writeErr (e.message ++ "\n"); return (2 : UInt32)).run.run w1).2) =
            let (wRes, st) := Model.stepHostWriteSlot false (proj w) (e.message ++ "\n")
            (wRes.map (fun _ => Model.PkgStepOut.code 2), st) := by
        rw [exceptT_run_bind]
        have he := mkCliOps_writeErr_spec proj caps hCaps (e.message ++ "\n") w1
        rw [hw1] at he
        cases hwe : ((Internal.mkCliOpsFromCapsM caps).writeErr (e.message ++ "\n")).run.run w1 with
        | mk we w2 =>
          rw [hwe] at he
          cases hse : Model.stepHostWriteSlot false (proj w) (e.message ++ "\n") with
          | mk mwe st =>
            rw [hse] at he; dsimp only at he ⊢
            rcases he with ⟨rfl, hw2⟩
            cases we <;> (dsimp only [exceptT_run_pure]; exact Prod.ext rfl hw2)
      cases e.kind <;> first | exact hOutBr | exact hErrBr

/-- Compositional `Core.ObeysStepFromExcept` proof for `Internal.mkApiFromCapsM`. -/
theorem obeysStepFromExcept_mkApiFromCapsM :
    Core.ObeysStepFromExcept id Model.hostStepWf Model.execCapsStep Model.allowedHostCapsStep
      Model.hostStepWf Internal.mkApiFromCapsM Model.execPkgExceptStep Model.allowedHostPkgStep := by
  intro W proj caps hCaps w req _
  cases req with
  | parseWithEnv spec args validators =>
    dsimp only [Function.comp, id, Model.execPkgExceptStep, Model.allowedHostPkgStep,
      Internal.mkApiFromCapsM, Internal.mkApiM]
    rw [exceptT_run_map]
    rcases parseWithEnvM_except_spec proj caps hCaps spec args validators w with ⟨res, hOut, hw1, hParse⟩
    cases hp : (Internal.parseWithEnvM (Internal.mkCliOpsFromCapsM caps) spec args validators).run.run w with
    | mk pRes w1 =>
      rw [hp] at hOut hw1
      dsimp only at hOut hw1
      subst hOut
      exact ⟨hw1, hParse⟩
  | promptLine prompt default =>
    dsimp only [Function.comp, id, Model.execPkgExceptStep, Model.allowedHostPkgStep,
      Internal.mkApiFromCapsM, Internal.mkApiM]
    rw [exceptT_run_map]
    have h := promptLineCheckedM_step_spec proj caps hCaps prompt default w
    cases hp : (SysBridge.promptLineCheckedM (Internal.mkCliOpsFromCapsM caps) prompt default).run.run w with
    | mk pRes w1 =>
      rw [hp] at h
      cases hs : Model.stepHostPromptLine (proj w) prompt default with
      | mk mRes st =>
        rw [hs] at h; simp only [Prod.mk.injEq] at h
        rcases h with ⟨rfl, hw1⟩
        exact Prod.ext rfl hw1
  | confirm prompt default maxAttempts =>
    dsimp only [Function.comp, id, Model.execPkgExceptStep, Model.allowedHostPkgStep,
      Internal.mkApiFromCapsM, Internal.mkApiM]
    rw [exceptT_run_map]
    have h := confirmCheckedM_step_spec proj caps hCaps prompt default maxAttempts w
    cases hp : (SysBridge.confirmCheckedM (Internal.mkCliOpsFromCapsM caps) prompt default maxAttempts).run.run w with
    | mk pRes w1 =>
      rw [hp] at h
      cases hs : Model.stepHostConfirm (proj w) prompt default maxAttempts with
      | mk mRes st =>
        rw [hs] at h; simp only [Prod.mk.injEq] at h
        rcases h with ⟨rfl, hw1⟩
        exact Prod.ext rfl hw1
  | runCli spec args exitCode =>
    dsimp only [Function.comp, id, Model.execPkgExceptStep, Model.allowedHostPkgStep,
      Internal.mkApiFromCapsM, Internal.mkApiM, Internal.runCli]
    exact runCliWith_except_spec proj caps hCaps spec args [] exitCode w
  | runCliWith spec args validators exitCode =>
    dsimp only [Function.comp, id, Model.execPkgExceptStep, Model.allowedHostPkgStep,
      Internal.mkApiFromCapsM, Internal.mkApiM]
    exact runCliWith_except_spec proj caps hCaps spec args validators exitCode w

end LeanSwe.CmdLine.Proofs
