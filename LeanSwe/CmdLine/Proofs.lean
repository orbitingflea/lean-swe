import Core.Obeys
import LeanSwe.CmdLine.Proofs.Concrete
import LeanSwe.CmdLine.Proofs.ParserCore
import LeanSwe.CmdLine.Proofs.PhraseBridge
import LeanSwe.CmdLine.Proofs.RoundTrip
import LeanSwe.CmdLine.Proofs.ErrorBounds

namespace LeanSwe.CmdLine.Proofs

open Core LeanSwe.CmdLine LeanSwe.CmdLine.Proofs.Shared

private theorem renderHelpNode_nonEmpty (cmdPath : List String) (visibleOpts : List OptSpec)
    (effectiveVersion : Option String) (targetSpec : CommandSpec) :
    !(Internal.renderHelpNode cmdPath visibleOpts effectiveVersion targetSpec).isEmpty = true := by
  unfold Internal.renderHelpNode
  dsimp only
  cases hb : (let fullCmd := String.intercalate " " cmdPath
    let argUsage := if !targetSpec.subcommands.isEmpty then " <SUBCOMMAND>"
      else String.intercalate "" (targetSpec.args.map fun a =>
        let base := if a.variadic then s!"{a.name}..." else a.name
        if a.required then s!" <{base}>" else s!" [{base}]")
    let usageLine := s!"Usage: {fullCmd} [OPTIONS]{argUsage}"
    let aboutSec := if targetSpec.about.isEmpty then "" else s!"\n\n{targetSpec.about}"
    let subSec := if targetSpec.subcommands.isEmpty then ""
      else "\n\nSUBCOMMANDS:\n" ++ String.intercalate "\n"
        (targetSpec.subcommands.map fun s => if s.about.isEmpty then s!"  {s.name}" else s!"  {s.name}    {s.about}")
    let argsSec := if targetSpec.args.isEmpty then ""
      else "\n\nARGS:\n" ++ String.intercalate "\n"
        (targetSpec.args.map fun a =>
          let tag := if a.variadic then s!"<{a.name}...>" else s!"<{a.name}>"
          if a.help.isEmpty then s!"  {tag}" else s!"  {tag}    {a.help}")
    let optLines := visibleOpts.map fun o =>
      let shortStr := match o.short with | some c => s!"-{c}" | none => "  "
      let longStr := match o.long with
        | some l => if o.short.isSome then s!", --{l}" else s!"--{l}"
        | none => ""
      let valStr := if o.kind == .bool then "" else s!" <{o.valueName.getD "VALUE"}>"
      let head := s!"  {shortStr}{longStr}{valStr}"
      if o.help.isEmpty then head else s!"{head}    {o.help}"
    let helpLine := if targetSpec.shortHelp then "  -h, --help    Print help" else "      --help    Print help"
    let verLines := if effectiveVersion.isSome then
      [if targetSpec.shortVersion then "  -V, --version    Print version" else "      --version    Print version"] else []
    let optsSec := "\n\nOPTIONS:\n" ++ String.intercalate "\n" (optLines ++ [helpLine] ++ verLines)
    usageLine ++ aboutSec ++ subSec ++ argsSec ++ optsSec ++ "\n").isEmpty with
  | false => rfl
  | true =>
    have heq := String.isEmpty_iff.mp hb
    have hlen := congrArg String.length heq
    simp only [String.length_append] at hlen
    have hn : ("\n" : String).length = 1 := rfl
    have hz : ("" : String).length = 0 := rfl
    omega

private theorem allowedRenderHelp_holds (rootSpec : CommandSpec) (subcommandPath : List String) :
    Model.allowedRenderHelp rootSpec subcommandPath (LeanSwe.CmdLine.renderHelp rootSpec subcommandPath) := by
  unfold Model.allowedRenderHelp LeanSwe.CmdLine.renderHelp defaultApi Internal.mkApiM Internal.renderHelp
  dsimp only [Bind.bind, Except.bind]
  rw [isValidSpecTR_eq, findSubcommandPathTR_eq]
  cases hv : Model.isValidSpec rootSpec with
  | false => simp
  | true =>
    simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    cases Model.findSubcommandPath rootSpec subcommandPath with
    | error _ => rfl
    | ok triple => exact renderHelpNode_nonEmpty _ _ _ _

private theorem resolveSingleOptionFast_step_eq {W : Type} (proj : W → Model.CliStepState)
    (getEnv : String → StateM W (Except CmdLineError (Option String)))
    (hEnv : ∀ w k, (getEnv k w).1 = Model.lookupCliStepEnv (proj w) k ∧ proj (getEnv k w).2 = proj w)
    (opt : OptSpec) (cliVals : List OptValue) (validators : CustomValidators) (w : W) :
    let r := Internal.resolveSingleOptionFast getEnv opt cliVals validators w
    r.1 = Model.resolveSingleOption (m := Id) (Model.lookupCliStepEnv (proj w)) opt cliVals validators ∧
      proj r.2 = proj w := by
  rw [resolveSingleOptionFast_eq]
  unfold Model.resolveSingleOption
  by_cases hcli : !cliVals.isEmpty
  · simp only [hcli, ↓reduceIte]
    split <;> exact ⟨rfl, rfl⟩
  · simp only [hcli, Bool.false_eq_true, ↓reduceIte]
    cases opt.envVar with
    | none => exact ⟨rfl, rfl⟩
    | some envKey =>
      dsimp only [Bind.bind, StateT.bind, Id.instMonad, Pure.pure, StateT.pure]
      have ⟨hv1, hw1⟩ := hEnv w envKey
      cases hg : getEnv envKey w with
      | mk r w1 =>
        simp only [hg] at hv1 hw1 ⊢
        rw [hv1]
        cases Model.lookupCliStepEnv (proj w) envKey with
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
              | error _ => exact ⟨rfl, hw1⟩
              | ok v =>
                dsimp only
                by_cases hrb : (opt.repeatable && opt.kind == .bool && v == .bool false) = true <;>
                  simp only [hrb, Bool.false_eq_true, ↓reduceIte] <;>
                  exact ⟨rfl, hw1⟩

private theorem resolveOptionsTR_step_eq {W : Type} (proj : W → Model.CliStepState)
    (getEnv : String → StateM W (Except CmdLineError (Option String)))
    (hEnv : ∀ w k, (getEnv k w).1 = Model.lookupCliStepEnv (proj w) k ∧ proj (getEnv k w).2 = proj w)
    (visibleOpts : List OptSpec) (cliOpts : List (String × List OptValue))
    (validators : CustomValidators) (w : W) :
    let r := Internal.resolveOptionsTR getEnv visibleOpts cliOpts validators w
    r.1 = Model.resolveOptions (m := Id) (Model.lookupCliStepEnv (proj w)) visibleOpts cliOpts validators ∧
      proj r.2 = proj w := by
  unfold Internal.resolveOptionsTR
  suffices ∀ accRev w0,
      let r := Internal.resolveOptionsTR.go getEnv cliOpts validators visibleOpts accRev w0
      r.1 = (Model.resolveOptions (m := Id) (Model.lookupCliStepEnv (proj w0)) visibleOpts cliOpts validators).map
              (fun tail => accRev.reverse ++ tail) ∧
        proj r.2 = proj w0 by
    have h0 := this [] w
    dsimp only [List.reverse_nil, List.nil_append] at h0
    refine ⟨h0.1.trans ?_, h0.2⟩
    cases Model.resolveOptions (m := Id) (Model.lookupCliStepEnv (proj w)) visibleOpts cliOpts validators <;> rfl
  induction visibleOpts with
  | nil =>
    intro accRev w0
    unfold Internal.resolveOptionsTR.go Model.resolveOptions
    simp [Pure.pure, StateT.pure, Except.map]
  | cons opt rest ih =>
    intro accRev w0
    dsimp only
    unfold Internal.resolveOptionsTR.go Model.resolveOptions
    dsimp only [Bind.bind, StateT.bind, Id.instMonad]
    have stepCase : ∀ cliVals,
        (match Internal.resolveSingleOptionFast getEnv opt cliVals validators w0 with
         | (a, s) =>
           (match a with
            | Except.error e => (pure (Except.error e) : StateM W (Except CmdLineError (List (String × List OptValue))))
            | Except.ok resolved? =>
              match resolved? with
              | none => Internal.resolveOptionsTR.go getEnv cliOpts validators rest accRev
              | some vals => Internal.resolveOptionsTR.go getEnv cliOpts validators rest ((opt.name, vals) :: accRev)) s).1 =
        (match Model.resolveSingleOption (m := Id) (Model.lookupCliStepEnv (proj w0)) opt cliVals validators with
         | Except.error e => Except.error e
         | Except.ok resolved? =>
           match Model.resolveOptions (m := Id) (Model.lookupCliStepEnv (proj w0)) rest cliOpts validators with
           | Except.error e => Except.error e
           | Except.ok tail =>
             match resolved? with
             | none => Except.ok tail
             | some vals => Except.ok ((opt.name, vals) :: tail)).map (fun tail => accRev.reverse ++ tail) ∧
        proj (match Internal.resolveSingleOptionFast getEnv opt cliVals validators w0 with
              | (a, s) =>
                (match a with
                 | Except.error e => (pure (Except.error e) : StateM W (Except CmdLineError (List (String × List OptValue))))
                 | Except.ok resolved? =>
                   match resolved? with
                   | none => Internal.resolveOptionsTR.go getEnv cliOpts validators rest accRev
                   | some vals => Internal.resolveOptionsTR.go getEnv cliOpts validators rest ((opt.name, vals) :: accRev)) s).2 =
          proj w0 := fun cliVals => by
      have hOne := resolveSingleOptionFast_step_eq proj getEnv hEnv opt cliVals validators w0
      dsimp only at hOne
      cases hs : Internal.resolveSingleOptionFast getEnv opt cliVals validators w0 with
      | mk r w1 =>
        rw [hs] at hOne
        simp only [] at hOne ⊢
        rcases hOne with ⟨hrEq, hw1⟩
        rw [hrEq]
        cases Model.resolveSingleOption (m := Id) (Model.lookupCliStepEnv (proj w0)) opt cliVals validators with
        | error _ =>
          simp [Pure.pure, StateT.pure, Except.map, hw1]
        | ok res? =>
          dsimp only
          cases res? with
          | none =>
            have hRec := ih accRev w1
            dsimp only at hRec
            rw [hw1] at hRec
            refine ⟨hRec.1.trans ?_, hRec.2⟩
            cases Model.resolveOptions (m := Id) (Model.lookupCliStepEnv (proj w0)) rest cliOpts validators <;> rfl
          | some vals =>
            have hRec := ih ((opt.name, vals) :: accRev) w1
            dsimp only at hRec
            rw [hw1] at hRec
            refine ⟨hRec.1.trans ?_, hRec.2⟩
            cases Model.resolveOptions (m := Id) (Model.lookupCliStepEnv (proj w0)) rest cliOpts validators with
            | error _ => rfl
            | ok tail => simp [Except.map, List.reverse_cons, List.append_assoc]
    cases cliOpts.find? (fun p => p.1 == opt.name) with
    | none => exact stepCase []
    | some p => exact stepCase p.2

private def pureStateOps : CliOpsM (StateM Unit) :=
  { readLine := pure none
    writeOut := fun _ => pure ()
    writeErr := fun _ => pure ()
    getEnv := fun _ => pure (.ok none) }

private theorem allowedParseWith_holds (spec : CommandSpec) (args : List String) (validators : CustomValidators) :
    Model.allowedParseWith spec args validators (LeanSwe.CmdLine.parseWith spec args validators) := by
  unfold Model.allowedParseWith LeanSwe.CmdLine.parseWith defaultApi Internal.mkApiM Internal.parseWith
  dsimp only
  rw [parseWithEnvM_eq_spec]
  have hro_unit : ∀ visibleOpts cliOpts,
      (Internal.resolveOptionsTR pureStateOps.getEnv visibleOpts cliOpts validators ()).1 =
        Model.resolveOptions (m := Id) (fun _ => Except.ok none) visibleOpts cliOpts validators := by
    intro visibleOpts cliOpts
    have h := resolveOptionsTR_step_eq (fun _ : Unit => ({} : Model.CliStepState))
      pureStateOps.getEnv (fun _ _ => ⟨rfl, rfl⟩) visibleOpts cliOpts validators ()
    exact h.1
  have hEq : Internal.parseWithEnvSpecM Internal.pureNoEnvOps spec args validators =
      (Internal.parseWithEnvSpecM pureStateOps spec args validators ()).1 := by
    unfold Internal.parseWithEnvSpecM
    cases (!Internal.isValidSpecTR spec) with
    | true => simp only [↓reduceIte]; rfl
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte]
      cases Internal.parseTokens spec.name validators { curSpec := spec, effectiveVersion := spec.version } args with
      | error _ => rfl
      | ok finalState =>
        dsimp only [Bind.bind, StateT.bind, Id.instMonad, Pure.pure, StateT.pure]
        cases (!finalState.curSpec.subcommands.isEmpty) with
        | true => simp only [↓reduceIte]; cases (!finalState.rawPositionals.isEmpty) <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> rfl
        | false =>
          simp only [Bool.false_eq_true, ↓reduceIte]
          dsimp only [Bind.bind, StateT.bind, Id.instMonad, Pure.pure, StateT.pure]
          have hro_id : Internal.resolveOptionsTR (m := Id) Internal.pureNoEnvOps.getEnv
              (finalState.inheritedGlobals ++ finalState.curSpec.options) finalState.cliOpts validators =
              (Internal.resolveOptionsTR pureStateOps.getEnv
                (finalState.inheritedGlobals ++ finalState.curSpec.options) finalState.cliOpts validators ()).1 := by
            rw [resolveOptionsTR_id_eq, hro_unit]; rfl
          cases hRun : Internal.resolveOptionsTR pureStateOps.getEnv
              (finalState.inheritedGlobals ++ finalState.curSpec.options) finalState.cliOpts validators () with
          | mk roRes _ =>
            rw [hRun] at hro_id; dsimp only at hro_id
            rw [hro_id]
            cases roRes with
            | error _ => rfl
            | ok _ =>
              dsimp only
              cases Internal.resolveArgsTR finalState.curSpec.args finalState.rawPositionals validators <;> rfl
  rw [hEq]
  exact parseWithEnvSpecM_allowedOutcome hro_unit

private theorem parseWithEnvM_step_spec {W : Type} (proj : W → Model.CliStepState)
    (ops : CliOpsM (StateM W))
    (hRaw : Core.ObeysStep proj Model.rawStepWf (Model.execRawStep ops) Model.allowedRawStep)
    (spec : CommandSpec) (args : List String) (validators : CustomValidators) (w : W) :
    let r := Internal.parseWithEnvM ops spec args validators w
    Model.allowedParseWithEnvStep (proj w) spec args validators r.1 (proj r.2) := by
  have hEnv : ∀ w0 k, (ops.getEnv k w0).1 = Model.lookupCliStepEnv (proj w0) k ∧ proj (ops.getEnv k w0).2 = proj w0 :=
    fun w0 k => by
      have h := hRaw w0 (.getEnv k) rfl
      dsimp only [Model.execRawStep, Model.allowedRawStep, Functor.map, StateT.map, Bind.bind,
        StateT.bind, Pure.pure, StateT.pure, StateT.run] at h
      cases hg : ops.getEnv k w0 with
      | mk _ w1 => simp only [hg] at h ⊢; exact h
  rw [parseWithEnvM_eq_spec]
  have hro_eq : ∀ visibleOpts cliOpts,
      (Internal.resolveOptionsTR ops.getEnv visibleOpts cliOpts validators w).1 =
        Model.resolveOptions (m := Id) (Model.lookupCliStepEnv (proj w)) visibleOpts cliOpts validators :=
    fun visibleOpts cliOpts => (resolveOptionsTR_step_eq proj ops.getEnv hEnv visibleOpts cliOpts validators w).1
  have hProjEq : proj (Internal.parseWithEnvSpecM ops spec args validators w).2 = proj w := by
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
          have hRo := resolveOptionsTR_step_eq proj ops.getEnv hEnv
            (finalState.inheritedGlobals ++ finalState.curSpec.options) finalState.cliOpts validators w
          dsimp only at hRo
          cases hRun : Internal.resolveOptionsTR ops.getEnv
              (finalState.inheritedGlobals ++ finalState.curSpec.options) finalState.cliOpts validators w with
          | mk ro w1 =>
            rw [hRun] at hRo
            cases ro with
            | error _ => exact hRo.2
            | ok _ =>
              cases Internal.resolveArgsTR finalState.curSpec.args finalState.rawPositionals validators <;> exact hRo.2
  exact ⟨hProjEq, parseWithEnvSpecM_allowedOutcome hro_eq⟩

private theorem promptLine_step_spec {W : Type} (proj : W → Model.CliStepState)
    (ops : CliOpsM (StateM W))
    (hRaw : Core.ObeysStep proj Model.rawStepWf (Model.execRawStep ops) Model.allowedRawStep)
    (prompt : String) (default : Option String) (w : W) :
    let r := Internal.promptLine ops prompt default w
    (r.1, proj r.2) = Model.stepCliPromptLine (proj w) prompt default := by
  dsimp only
  unfold Internal.promptLine Model.stepCliPromptLine
  dsimp only [SeqRight.seqRight, Bind.bind, StateT.bind]
  have hw := hRaw w (.writeOut prompt) rfl
  dsimp only [Model.execRawStep, Model.allowedRawStep, SeqRight.seqRight, Bind.bind, StateT.bind,
    Pure.pure, StateT.pure, StateT.run] at hw
  cases ho : ops.writeOut prompt w with
  | mk _ w1 =>
    simp only [ho] at hw ⊢
    dsimp only [Bind.bind, Pure.pure, StateT.pure, Id.instMonad]
    have hr := hRaw w1 .readLine rfl
    dsimp only [Model.execRawStep, Model.allowedRawStep, Functor.map, StateT.map, Bind.bind,
      StateT.bind, Pure.pure, StateT.pure, StateT.run] at hr
    cases hl : ops.readLine w1 with
    | mk line? w2 =>
      simp only [hl] at hr ⊢
      rw [hw] at hr
      cases hlines : (proj w).stdinLines with
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

private theorem confirm_step_spec {W : Type} (proj : W → Model.CliStepState)
    (ops : CliOpsM (StateM W))
    (hRaw : Core.ObeysStep proj Model.rawStepWf (Model.execRawStep ops) Model.allowedRawStep)
    (prompt : String) (default : Option Bool) (maxAttempts : Nat) :
    ∀ w : W,
      let r := Internal.confirm ops prompt default maxAttempts w
      (r.1, proj r.2) = Model.stepCliConfirm (proj w) prompt default maxAttempts := by
  induction maxAttempts with
  | zero =>
    intro w
    dsimp only
    unfold Internal.confirm Model.stepCliConfirm
    rfl
  | succ n ih =>
    intro w
    dsimp only
    unfold Internal.confirm Model.stepCliConfirm
    dsimp only [SeqRight.seqRight, Bind.bind, StateT.bind]
    have hw := hRaw w (.writeOut prompt) rfl
    dsimp only [Model.execRawStep, Model.allowedRawStep, SeqRight.seqRight, Bind.bind, StateT.bind,
      Pure.pure, StateT.pure, StateT.run] at hw
    cases ho : ops.writeOut prompt w with
    | mk _ w1 =>
      simp only [ho] at hw ⊢
      dsimp only [Bind.bind, Pure.pure, StateT.pure, Id.instMonad]
      have hr := hRaw w1 .readLine rfl
      dsimp only [Model.execRawStep, Model.allowedRawStep, Functor.map, StateT.map, Bind.bind,
        StateT.bind, Pure.pure, StateT.pure, StateT.run] at hr
      cases hl : ops.readLine w1 with
      | mk line? w2 =>
        simp only [hl] at hr ⊢
        rw [hw] at hr
        cases hlines : (proj w).stdinLines with
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
                dsimp only [SeqRight.seqRight, Bind.bind, StateT.bind]
                have he := hRaw w2 (.writeErr "Please answer yes or no.\n") rfl
                dsimp only [Model.execRawStep, Model.allowedRawStep, SeqRight.seqRight, Bind.bind,
                  StateT.bind, Pure.pure, StateT.pure, StateT.run] at he
                cases hwe : ops.writeErr "Please answer yes or no.\n" w2 with
                | mk _ w3 =>
                  simp only [hwe] at he ⊢
                  rw [hw2] at he
                  have hrec := ih w3
                  dsimp only at hrec
                  rw [← he]
                  exact hrec
          · simp only [hEmp, Bool.false_eq_true, ↓reduceIte]
            by_cases hYes : (Model.asciiLower (Model.trimAscii hd) == "y" ||
                Model.asciiLower (Model.trimAscii hd) == "yes") = true
            · simp only [hYes, ↓reduceIte]
              dsimp only [Pure.pure, StateT.pure]
              rw [hw2]
            · simp only [hYes, Bool.false_eq_true, ↓reduceIte]
              by_cases hNo : (Model.asciiLower (Model.trimAscii hd) == "n" ||
                  Model.asciiLower (Model.trimAscii hd) == "no") = true
              · simp only [hNo, ↓reduceIte]
                dsimp only [Pure.pure, StateT.pure]
                rw [hw2]
              · simp only [hNo, Bool.false_eq_true, ↓reduceIte]
                cases n with
                | zero =>
                  dsimp only [Pure.pure, StateT.pure]
                  rw [hw2]
                | succ m =>
                  dsimp only [SeqRight.seqRight, Bind.bind, StateT.bind]
                  have he := hRaw w2 (.writeErr "Please answer yes or no.\n") rfl
                  dsimp only [Model.execRawStep, Model.allowedRawStep, SeqRight.seqRight, Bind.bind,
                    StateT.bind, Pure.pure, StateT.pure, StateT.run] at he
                  cases hwe : ops.writeErr "Please answer yes or no.\n" w2 with
                  | mk _ w3 =>
                    simp only [hwe] at he ⊢
                    rw [hw2] at he
                    have hrec := ih w3
                    dsimp only at hrec
                    rw [← he]
                    exact hrec

private theorem runCliWith_step_spec {W : Type} (proj : W → Model.CliStepState)
    (ops : CliOpsM (StateM W))
    (hRaw : Core.ObeysStep proj Model.rawStepWf (Model.execRawStep ops) Model.allowedRawStep)
    (spec : CommandSpec) (args : List String) (validators : CustomValidators)
    (exitCode : UInt32) (w : W) :
    let r := Internal.runCliWith ops spec args validators (fun _ => pure exitCode) w
    Model.allowedRunCliWithStep (proj w) spec args validators exitCode r.1 (proj r.2) := by
  have hp := parseWithEnvM_step_spec proj ops hRaw spec args validators w
  dsimp only at hp
  unfold Internal.runCliWith Model.allowedRunCliWithStep
  dsimp only [Bind.bind, StateT.bind] at hp ⊢
  cases hpr : Internal.parseWithEnvM ops spec args validators w with
  | mk res w1 =>
    rw [hpr] at hp
    rcases hp with ⟨hw1, hresSpec⟩
    refine ⟨res, ⟨rfl, hresSpec⟩, ?_⟩
    cases res with
    | ok _ =>
      dsimp only [StateT.pure, Pure.pure]
      exact ⟨rfl, hw1⟩
    | error e =>
      dsimp only
      have hOut :
          ((StateT.bind (ops.writeOut e.message) (fun _ => pure (0 : UInt32)) w1).1 = 0 ∧
            proj (StateT.bind (ops.writeOut e.message) (fun _ => pure (0 : UInt32)) w1).2 =
              { proj w with stdout := (proj w).stdout ++ e.message }) := by
        dsimp only [StateT.bind]
        have ho := hRaw w1 (.writeOut e.message) rfl
        dsimp only [Model.execRawStep, Model.allowedRawStep, SeqRight.seqRight, Bind.bind,
          StateT.bind, Pure.pure, StateT.pure, StateT.run] at ho
        cases hwo : ops.writeOut e.message w1 with
        | mk _ w2 =>
          simp only [hwo] at ho
          dsimp only [Bind.bind, Pure.pure, StateT.pure, Id.instMonad]
          rw [hw1] at ho
          exact ⟨rfl, ho⟩
      have hErr :
          ((StateT.bind (ops.writeErr (e.message ++ "\n")) (fun _ => pure (2 : UInt32)) w1).1 = 2 ∧
            proj (StateT.bind (ops.writeErr (e.message ++ "\n")) (fun _ => pure (2 : UInt32)) w1).2 =
              { proj w with stderr := (proj w).stderr ++ e.message ++ "\n" }) := by
        dsimp only [StateT.bind]
        have he := hRaw w1 (.writeErr (e.message ++ "\n")) rfl
        dsimp only [Model.execRawStep, Model.allowedRawStep, SeqRight.seqRight, Bind.bind,
          StateT.bind, Pure.pure, StateT.pure, StateT.run] at he
        cases hwe : ops.writeErr (e.message ++ "\n") w1 with
        | mk _ w2 =>
          simp only [hwe] at he
          dsimp only [Bind.bind, Pure.pure, StateT.pure, Id.instMonad]
          rw [hw1] at he
          exact ⟨rfl, by simpa [String.append_assoc] using he⟩
      cases e.kind <;> first | exact hOut | exact hErr

private theorem refinesStepFrom_mkApiM :
    Core.ObeysStepFrom id Model.rawStepWf Model.execRawStep Model.allowedRawStep
      Model.rawStepWf Internal.mkApiM Model.execPkgStep Model.allowedPkgStep := by
  intro W proj ops hRaw w req _
  cases req with
  | parseWithEnv spec args validators =>
    have h := parseWithEnvM_step_spec proj ops hRaw spec args validators w
    simp only [Model.execPkgStep, Internal.mkApiM, Functor.map, StateT.map, Bind.bind,
      Pure.pure, StateT.run, Function.comp, Model.allowedPkgStep, id]
    cases hp : Internal.parseWithEnvM ops spec args validators w with
    | mk res w1 =>
      simp only [hp] at h ⊢
      exact h
  | promptLine prompt default =>
    have h := promptLine_step_spec proj ops hRaw prompt default w
    simp only [Model.execPkgStep, Internal.mkApiM, Functor.map, StateT.map, Bind.bind,
      Pure.pure, StateT.run, Function.comp, Model.allowedPkgStep, id]
    cases hp : Internal.promptLine ops prompt default w with
    | mk res w1 =>
      simp only [hp] at h ⊢
      exact h
  | confirm prompt default maxAttempts =>
    have h := confirm_step_spec proj ops hRaw prompt default maxAttempts w
    simp only [Model.execPkgStep, Internal.mkApiM, Functor.map, StateT.map, Bind.bind,
      Pure.pure, StateT.run, Function.comp, Model.allowedPkgStep, id]
    cases hp : Internal.confirm ops prompt default maxAttempts w with
    | mk res w1 =>
      simp only [hp] at h ⊢
      exact h
  | runCli spec args exitCode =>
    have h := runCliWith_step_spec proj ops hRaw spec args [] exitCode w
    simp only [Model.execPkgStep, Internal.mkApiM, Internal.runCli, Functor.map, StateT.map,
      Bind.bind, Pure.pure, StateT.run, Function.comp, Model.allowedPkgStep, id]
    cases hp : Internal.runCliWith ops spec args [] (fun _ => pure exitCode) w with
    | mk res w1 =>
      simp only [hp] at h ⊢
      exact h
  | runCliWith spec args validators exitCode =>
    have h := runCliWith_step_spec proj ops hRaw spec args validators exitCode w
    simp only [Model.execPkgStep, Internal.mkApiM, Functor.map, StateT.map, Bind.bind,
      Pure.pure, StateT.run, Function.comp, Model.allowedPkgStep, id]
    cases hp : Internal.runCliWith ops spec args validators (fun _ => pure exitCode) w with
    | mk res w1 =>
      simp only [hp] at h ⊢
      exact h

/-- Full public `Interface` `Core.Obeys` contract of `LeanSwe.CmdLine` against `LeanSwe.CmdLine.Model`. -/
theorem obeys_model :
    Core.ObeysPureEq LeanSwe.CmdLine.isValidSpec Model.isValidSpec ∧
    Core.ObeysPure2 LeanSwe.CmdLine.parse Model.allowedParse ∧
    Core.ObeysPure3 (@LeanSwe.CmdLine.parseWith) Model.allowedParseWith ∧
    Core.ObeysPure2 (@LeanSwe.CmdLine.renderHelp) Model.allowedRenderHelp ∧
    Core.ObeysPureEq2 LeanSwe.CmdLine.renderVersion Model.renderVersionModel ∧
    Core.ObeysPureEq2 LeanSwe.CmdLine.renderArgs Model.renderArgs ∧
    Core.ObeysStepFrom id Model.rawStepWf Model.execRawStep Model.allowedRawStep
      Model.rawStepWf Internal.mkApiM Model.execPkgStep Model.allowedPkgStep :=
  ⟨isValidSpecTR_eq,
   fun spec args => allowedParseWith_holds spec args [],
   allowedParseWith_holds,
   allowedRenderHelp_holds,
   fun _ _ => rfl,
   renderArgsTR_eq,
   refinesStepFrom_mkApiM⟩

end LeanSwe.CmdLine.Proofs
