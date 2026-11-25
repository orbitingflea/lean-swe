import LeanSwe.CmdLine.Interface
import LeanSwe.CmdLine.SpecTests
import LeanSwe.CmdLine.Proofs.ParserCore
set_option Elab.async false
namespace LeanSwe.CmdLine.Proofs
open Core Core.NondetTest LeanSwe.CmdLine
private theorem string_contains_append_left {a b sub : String} (h : a.contains sub = true) :
    (a ++ b).contains sub = true := by
  rw [String.contains_string_iff] at h ⊢; rcases h with ⟨pre, post, hp⟩
  exact ⟨pre, post ++ b.toList, by rw [String.toList_append, ← hp]; simp [List.append_assoc]⟩
private theorem string_contains_append_right {a b sub : String} (h : b.contains sub = true) :
    (a ++ b).contains sub = true := by
  rw [String.contains_string_iff] at h ⊢; rcases h with ⟨pre, post, hp⟩
  exact ⟨a.toList ++ pre, post, by rw [String.toList_append, ← hp]; simp [List.append_assoc]⟩
private theorem string_contains_mid (pre mid post : String) : (pre ++ mid ++ post).contains mid = true :=
  string_contains_append_left (string_contains_append_right (String.contains_string_iff.mpr ⟨[], [], by simp⟩))
private theorem parse_err_of_pred (spec : CommandSpec) (args : List String) (p : CmdLineError → Bool)
    (h : (match defaultApi.parse spec args with | .ok _ => false | .error e => p e) = true) :
    ∃ e, defaultApi.parse spec args = .error e ∧ p e = true := by
  cases he : defaultApi.parse spec args with
  | ok _ => simp [he] at h
  | error e => simp [he] at h; exact ⟨e, rfl, h⟩
private theorem ne_empty_of_isEmpty_false {s : String} (h : (!s.isEmpty) = true) : s ≠ "" := by
  intro he; rw [he] at h; contradiction
/-- `test_cmdline_validSpec_rejectsFlagCollisions` holds universally for `defaultApi`. -/
theorem allPass_validSpec_rejectsFlagCollisions : AllPass (test_cmdline_validSpec_rejectsFlagCollisions defaultApi) := by
  dsimp only [AllPass, AllPassRun, test_cmdline_validSpec_rejectsFlagCollisions, Bind.bind, Pure.pure, NondetTest.assert, defaultApi, Internal.mkApiFromCapsM, Internal.mkApiM]
  simp only [Shared.isValidSpecTR_eq]; cbv
/-- `test_cmdline_validSpec_rejectsFlagCollisions` is reachable. -/
theorem canReach_validSpec_rejectsFlagCollisions : CanReach (test_cmdline_validSpec_rejectsFlagCollisions defaultApi) := allPass_validSpec_rejectsFlagCollisions
/-- `test_cmdline_validSpec_rejectsStructuralAndEnvErrors` holds universally for `defaultApi`. -/
theorem allPass_validSpec_rejectsStructuralAndEnvErrors : AllPass (test_cmdline_validSpec_rejectsStructuralAndEnvErrors defaultApi) := by
  dsimp only [AllPass, AllPassRun, test_cmdline_validSpec_rejectsStructuralAndEnvErrors, Bind.bind, Pure.pure, NondetTest.assert, defaultApi, Internal.mkApiFromCapsM, Internal.mkApiM]
  simp only [Shared.isValidSpecTR_eq]; cbv
/-- `test_cmdline_validSpec_rejectsStructuralAndEnvErrors` is reachable. -/
theorem canReach_validSpec_rejectsStructuralAndEnvErrors : CanReach (test_cmdline_validSpec_rejectsStructuralAndEnvErrors defaultApi) := allPass_validSpec_rejectsStructuralAndEnvErrors
/-- `test_cmdline_validSpec_shortOptOutAndParseRejectsInvalid` holds universally for `defaultApi`. -/
theorem allPass_validSpec_shortOptOutAndParseRejectsInvalid : AllPass (test_cmdline_validSpec_shortOptOutAndParseRejectsInvalid defaultApi) := by
  dsimp only [AllPass, AllPassRun, test_cmdline_validSpec_shortOptOutAndParseRejectsInvalid, Bind.bind, Pure.pure, NondetTest.assert, defaultApi, Internal.mkApiFromCapsM, Internal.mkApiM, Internal.parse, Internal.parseWith]
  simp only [Shared.parseWithEnvM_eq_spec, Internal.parseWithEnvSpecM, Shared.isValidSpecTR_eq]; cbv
/-- `test_cmdline_validSpec_shortOptOutAndParseRejectsInvalid` is reachable. -/
theorem canReach_validSpec_shortOptOutAndParseRejectsInvalid : CanReach (test_cmdline_validSpec_shortOptOutAndParseRejectsInvalid defaultApi) := allPass_validSpec_shortOptOutAndParseRejectsInvalid
/-- `test_cmdline_parse_shortBundlesAndValues` holds universally for `defaultApi`. -/
theorem allPass_parse_shortBundlesAndValues : AllPass (test_cmdline_parse_shortBundlesAndValues defaultApi) := by
  dsimp only [AllPass, AllPassRun, test_cmdline_parse_shortBundlesAndValues, Bind.bind, Pure.pure, NondetTest.assert, defaultApi, Internal.mkApiFromCapsM, Internal.mkApiM, Internal.parse, Internal.parseWith]
  simp only [Shared.parseWithEnvM_eq_spec, Internal.parseWithEnvSpecM, Shared.isValidSpecTR_eq]; cbv
/-- `test_cmdline_parse_shortBundlesAndValues` is reachable. -/
theorem canReach_parse_shortBundlesAndValues : CanReach (test_cmdline_parse_shortBundlesAndValues defaultApi) := allPass_parse_shortBundlesAndValues
/-- `test_cmdline_parse_shortLeftToRightHelpPrecedence` holds universally for `defaultApi`. -/
theorem allPass_parse_shortLeftToRightHelpPrecedence : AllPass (test_cmdline_parse_shortLeftToRightHelpPrecedence defaultApi) := by
  dsimp only [AllPass, AllPassRun, test_cmdline_parse_shortLeftToRightHelpPrecedence, Bind.bind, Pure.pure, NondetTest.assert, defaultApi, Internal.mkApiFromCapsM, Internal.mkApiM, Internal.parse, Internal.parseWith]
  simp only [Shared.parseWithEnvM_eq_spec, Internal.parseWithEnvSpecM, Shared.isValidSpecTR_eq]; cbv
/-- `test_cmdline_parse_shortLeftToRightHelpPrecedence` is reachable. -/
theorem canReach_parse_shortLeftToRightHelpPrecedence : CanReach (test_cmdline_parse_shortLeftToRightHelpPrecedence defaultApi) := allPass_parse_shortLeftToRightHelpPrecedence
/-- `test_cmdline_parse_duplicatesNegationAndSpaceBool` holds universally for `defaultApi`. -/
theorem allPass_parse_duplicatesNegationAndSpaceBool : AllPass (test_cmdline_parse_duplicatesNegationAndSpaceBool defaultApi) := by
  dsimp only [AllPass, AllPassRun, test_cmdline_parse_duplicatesNegationAndSpaceBool, Bind.bind, Pure.pure, NondetTest.assert, defaultApi, Internal.mkApiFromCapsM, Internal.mkApiM, Internal.parse, Internal.parseWith]
  simp only [Shared.parseWithEnvM_eq_spec, Internal.parseWithEnvSpecM, Shared.isValidSpecTR_eq]; cbv
/-- `test_cmdline_parse_duplicatesNegationAndSpaceBool` is reachable. -/
theorem canReach_parse_duplicatesNegationAndSpaceBool : CanReach (test_cmdline_parse_duplicatesNegationAndSpaceBool defaultApi) := allPass_parse_duplicatesNegationAndSpaceBool
/-- `test_cmdline_parse_negativeNumbersAndDashDash` holds universally for `defaultApi`. -/
theorem allPass_parse_negativeNumbersAndDashDash : AllPass (test_cmdline_parse_negativeNumbersAndDashDash defaultApi) := by
  dsimp only [AllPass, AllPassRun, test_cmdline_parse_negativeNumbersAndDashDash, Bind.bind, Pure.pure, NondetTest.assert, defaultApi, Internal.mkApiFromCapsM, Internal.mkApiM, Internal.parse, Internal.parseWith]
  simp only [Shared.parseWithEnvM_eq_spec, Internal.parseWithEnvSpecM, Shared.isValidSpecTR_eq]; cbv; decide
/-- `test_cmdline_parse_negativeNumbersAndDashDash` is reachable. -/
theorem canReach_parse_negativeNumbersAndDashDash : CanReach (test_cmdline_parse_negativeNumbersAndDashDash defaultApi) := allPass_parse_negativeNumbersAndDashDash
/-- `test_cmdline_parse_subcommandsAndInheritedGlobals` holds universally for `defaultApi`. -/
theorem allPass_parse_subcommandsAndInheritedGlobals : AllPass (test_cmdline_parse_subcommandsAndInheritedGlobals defaultApi) := by
  dsimp only [AllPass, AllPassRun, test_cmdline_parse_subcommandsAndInheritedGlobals, Bind.bind, Pure.pure, NondetTest.assert, defaultApi, Internal.mkApiFromCapsM, Internal.mkApiM, Internal.parse, Internal.parseWith]
  simp only [Shared.parseWithEnvM_eq_spec, Internal.parseWithEnvSpecM, Shared.isValidSpecTR_eq]; cbv
/-- `test_cmdline_parse_subcommandsAndInheritedGlobals` is reachable. -/
theorem canReach_parse_subcommandsAndInheritedGlobals : CanReach (test_cmdline_parse_subcommandsAndInheritedGlobals defaultApi) := allPass_parse_subcommandsAndInheritedGlobals
private def typoSpec : CommandSpec :=
  { name := "tool", options := [ { name := "verbose", long := some "verbose", kind := .bool, global := true } ], subcommands := [ { name := "build" }, { name := "clean" } ] }
/-- `test_cmdline_parse_typoSuggestions` holds universally for `defaultApi`. -/
theorem allPass_parse_typoSuggestions : AllPass (test_cmdline_parse_typoSuggestions defaultApi) := by
  dsimp only [AllPass, AllPassRun, test_cmdline_parse_typoSuggestions, Bind.bind, Pure.pure, NondetTest.assert]
  have h1 : ∃ e, defaultApi.parse typoSpec ["--verbos"] = .error e ∧ e.kind = .unknownOption ∧ e.message.contains "did you mean '--verbose'" = true := by
    rcases parse_err_of_pred typoSpec ["--verbos"] (fun e => decide (e.kind = .unknownOption) && e.message.contains "did you mean '--verbose'") (by cbv) with ⟨e, he, hp⟩
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hp; exact ⟨e, he, hp.1, hp.2⟩
  have h2 : ∃ e, defaultApi.parse typoSpec ["biuld"] = .error e ∧ e.kind = .unknownSubcommand ∧ e.message.contains "did you mean 'build'" = true := by
    rcases parse_err_of_pred typoSpec ["biuld"] (fun e => decide (e.kind = .unknownSubcommand) && e.message.contains "did you mean 'build'") (by cbv) with ⟨e, he, hp⟩
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hp; exact ⟨e, he, hp.1, hp.2⟩
  rcases h1 with ⟨e1, he1, hk1, hm1⟩; rcases h2 with ⟨e2, he2, hk2, hm2⟩
  dsimp only [typoSpec] at he1 he2; rw [he1]; dsimp only; rw [he2]; exact ⟨⟨hk1, hm1⟩, ⟨hk2, hm2⟩, trivial⟩
/-- `test_cmdline_parse_typoSuggestions` is reachable. -/
theorem canReach_parse_typoSuggestions : CanReach (test_cmdline_parse_typoSuggestions defaultApi) := allPass_parse_typoSuggestions
/-- `test_cmdline_parseWith_customValidatorAndDecoder` holds universally for `defaultApi`. -/
theorem allPass_parseWith_customValidatorAndDecoder : AllPass (test_cmdline_parseWith_customValidatorAndDecoder defaultApi) := by
  dsimp only [AllPass, AllPassRun, test_cmdline_parseWith_customValidatorAndDecoder, Bind.bind, Pure.pure, NondetTest.assert, defaultApi, Internal.mkApiFromCapsM, Internal.mkApiM, Internal.parseWith]
  simp only [Shared.parseWithEnvM_eq_spec, Internal.parseWithEnvSpecM, Shared.isValidSpecTR_eq]; cbv
/-- `test_cmdline_parseWith_customValidatorAndDecoder` is reachable. -/
theorem canReach_parseWith_customValidatorAndDecoder : CanReach (test_cmdline_parseWith_customValidatorAndDecoder defaultApi) := allPass_parseWith_customValidatorAndDecoder
/-- `test_cmdline_env_precedenceAndErrorPropagation` holds universally for `Internal.mkApiM`. -/
theorem allPass_env_precedenceAndErrorPropagation : AllPass (test_cmdline_env_precedenceAndErrorPropagation Internal.mkApiM) := by
  dsimp only [AllPass, AllPassRun, test_cmdline_env_precedenceAndErrorPropagation, Bind.bind, Pure.pure, NondetTest.assert, Internal.mkApiM]
  simp only [Shared.parseWithEnvM_eq_spec, Internal.parseWithEnvSpecM, Shared.isValidSpecTR_eq]; cbv
/-- `test_cmdline_env_precedenceAndErrorPropagation` is reachable. -/
theorem canReach_env_precedenceAndErrorPropagation : CanReach (test_cmdline_env_precedenceAndErrorPropagation Internal.mkApiM) := allPass_env_precedenceAndErrorPropagation
/-- `test_cmdline_renderArgs_roundTripEdgeCases` holds universally for `defaultApi`. -/
theorem allPass_renderArgs_roundTripEdgeCases : AllPass (test_cmdline_renderArgs_roundTripEdgeCases defaultApi) := by
  dsimp only [AllPass, AllPassRun, test_cmdline_renderArgs_roundTripEdgeCases, Bind.bind, Pure.pure, NondetTest.assert, defaultApi, Internal.mkApiFromCapsM, Internal.mkApiM, Internal.parse, Internal.parseWith]
  simp only [Shared.parseWithEnvM_eq_spec, Internal.parseWithEnvSpecM, Shared.isValidSpecTR_eq, Shared.renderArgsTR_eq]; cbv
/-- `test_cmdline_renderArgs_roundTripEdgeCases` is reachable. -/
theorem canReach_renderArgs_roundTripEdgeCases : CanReach (test_cmdline_renderArgs_roundTripEdgeCases defaultApi) := allPass_renderArgs_roundTripEdgeCases
private def routingSpec : CommandSpec :=
  { name := "mytool", version := some "2.1.0", options := [ { name := "port", long := some "port", kind := .nat, envVar := some "PORT" } ] }
private theorem runCli_port443_ok (exitCode : UInt32) :
    let r := ((Internal.mkApiM mockCliOps).runCli routingSpec ["--port", "443"] (fun cmd => pure (if cmd.getNat "port" = some 443 then exitCode else 99))).run {}
    r.1 = exitCode ∧ r.2.stderr = "" := by
  have hp : (Internal.parseWithEnvSpecM mockCliOps routingSpec ["--port", "443"] [] : StateM CliMockState (Except CmdLineError ParsedCmd)) {} =
      (Except.ok { options := [("port", [.nat 443])] }, {}) := by cbv
  dsimp only [Internal.mkApiM, Internal.runCli, Internal.runCliWith, StateT.run, Bind.bind, StateT.bind, Pure.pure, StateT.pure]
  rw [Shared.parseWithEnvM_eq_spec, hp]; exact ⟨rfl, rfl⟩
/-- `test_cmdline_runCli_routingAndExitCodes` holds universally for `Internal.mkApiM`. -/
theorem allPass_runCli_routingAndExitCodes : AllPass (test_cmdline_runCli_routingAndExitCodes Internal.mkApiM) := by
  dsimp only [AllPass, AllPassRun, test_cmdline_runCli_routingAndExitCodes, Bind.bind, Pure.pure, NondetTest.nondet, NondetTest.assert]
  refine ⟨?_, ?_, ?_, ?_, fun exitCode => ⟨runCli_port443_ok exitCode, trivial⟩⟩
  · dsimp only [Internal.mkApiM, Internal.runCli, Internal.runCliWith]; simp only [Shared.parseWithEnvM_eq_spec, Internal.parseWithEnvSpecM, Shared.isValidSpecTR_eq]; cbv
  · dsimp only [Internal.mkApiM, Internal.runCli, Internal.runCliWith]; simp only [Shared.parseWithEnvM_eq_spec, Internal.parseWithEnvSpecM, Shared.isValidSpecTR_eq]; cbv
  · dsimp only [Internal.mkApiM, Internal.runCli, Internal.runCliWith]; simp only [Shared.parseWithEnvM_eq_spec, Internal.parseWithEnvSpecM, Shared.isValidSpecTR_eq]; cbv; decide
  · dsimp only [Internal.mkApiM, Internal.runCli, Internal.runCliWith]; simp only [Shared.parseWithEnvM_eq_spec, Internal.parseWithEnvSpecM, Shared.isValidSpecTR_eq]; cbv
/-- `test_cmdline_runCli_routingAndExitCodes` is reachable. -/
theorem canReach_runCli_routingAndExitCodes : CanReach (test_cmdline_runCli_routingAndExitCodes Internal.mkApiM) := by
  have h := allPass_runCli_routingAndExitCodes
  dsimp only [AllPass, AllPassRun, CanReach, CanReachRun, test_cmdline_runCli_routingAndExitCodes, Bind.bind, Pure.pure, NondetTest.nondet, NondetTest.assert] at h ⊢
  exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, 42, h.2.2.2.2 42⟩
/-- `test_cmdline_interactive_promptAndConfirm` holds universally for `Internal.mkApiM`. -/
theorem allPass_interactive_promptAndConfirm : AllPass (test_cmdline_interactive_promptAndConfirm Internal.mkApiM) := by
  dsimp only [AllPass, AllPassRun, test_cmdline_interactive_promptAndConfirm, Bind.bind, Pure.pure, NondetTest.assert]
  refine ⟨by cbv, by cbv, ⟨_, by cbv, by cbv⟩, by cbv, ⟨⟨_, by cbv, by cbv⟩, by cbv⟩, ⟨_, by cbv, by cbv⟩, trivial⟩
/-- `test_cmdline_interactive_promptAndConfirm` is reachable. -/
theorem canReach_interactive_promptAndConfirm : CanReach (test_cmdline_interactive_promptAndConfirm Internal.mkApiM) := allPass_interactive_promptAndConfirm
private def toolHvSpec : CommandSpec :=
  { name := "tool", version := some "1.0", options := [ { name := "port", long := some "port", kind := .nat, global := true } ], subcommands := [ { name := "sub", version := some "2.0" } ] }
/-- `test_cmdline_parse_helpAndVersionRouting` holds universally for `defaultApi`. -/
theorem allPass_parse_helpAndVersionRouting : AllPass (test_cmdline_parse_helpAndVersionRouting defaultApi) := by
  dsimp only [AllPass, AllPassRun, test_cmdline_parse_helpAndVersionRouting, Bind.bind, Pure.pure, NondetTest.assert]
  rcases parse_err_of_pred toolHvSpec ["--help", "--badopt"] (fun e => decide (e.kind = .helpRequested) && !e.message.isEmpty) (by cbv) with ⟨e4, he4, hp4⟩
  dsimp only [toolHvSpec] at he4; simp only [decide_eq_true_eq, Bool.and_eq_true] at hp4
  simp only [defaultApi, Internal.mkApiFromCapsM, Internal.mkApiM, Internal.parse, Internal.parseWith, Shared.parseWithEnvM_eq_spec, Internal.parseWithEnvSpecM, Shared.isValidSpecTR_eq] at he4 ⊢
  have h1 : Model.isValidSpec { name := "app" } = true := by decide
  have h2 : Model.isValidSpec toolHvSpec = true := by decide
  dsimp only [toolHvSpec] at h2
  simp only [h1, h2, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at he4 ⊢
  rw [he4]; dsimp only; refine ⟨by cbv, by cbv, by cbv, ⟨hp4.1, ne_empty_of_isEmpty_false hp4.2⟩, by cbv, by cbv, trivial⟩
/-- `test_cmdline_parse_helpAndVersionRouting` is reachable. -/
theorem canReach_parse_helpAndVersionRouting : CanReach (test_cmdline_parse_helpAndVersionRouting defaultApi) := allPass_parse_helpAndVersionRouting
/-- `test_cmdline_parse_positionalArgsAndErrors` holds universally for `defaultApi`. -/
theorem allPass_parse_positionalArgsAndErrors : AllPass (test_cmdline_parse_positionalArgsAndErrors defaultApi) := by
  dsimp only [AllPass, AllPassRun, test_cmdline_parse_positionalArgsAndErrors, Bind.bind, Pure.pure, NondetTest.assert, defaultApi, Internal.mkApiFromCapsM, Internal.mkApiM, Internal.parse, Internal.parseWith]
  simp only [Shared.parseWithEnvM_eq_spec, Internal.parseWithEnvSpecM, Shared.isValidSpecTR_eq]; cbv
/-- `test_cmdline_parse_positionalArgsAndErrors` is reachable. -/
theorem canReach_parse_positionalArgsAndErrors : CanReach (test_cmdline_parse_positionalArgsAndErrors defaultApi) := allPass_parse_positionalArgsAndErrors
private def toolSpec : CommandSpec :=
  { name := "tool", version := some "3.0", about := "Manage widgets",
    options := [ { name := "cfg", long := some "cfg", help := "Config file", global := true } ],
    subcommands := [ { name := "add", about := "Add widget", args := [ { name := "widget", help := "Widget name" } ] } ] }
private theorem renderHelp_tool_root_eq :
    defaultApi.renderHelp toolSpec [] =
      .ok (("Usage: " ++ "tool" ++ " [OPTIONS] <SUBCOMMAND>\n\nManage widgets\n\n") ++
        ("SUBCOMMANDS:\n  " ++ "add" ++ "    Add widget\n\n") ++ ("OPTIONS:\n    " ++ "--cfg" ++ " <VALUE>    Config file\n") ++
        ("  -h, " ++ "--help" ++ "    Print help\n") ++ ("  -V, " ++ "--version" ++ "    Print version\n")) := by cbv
private theorem renderHelp_tool_add_eq :
    defaultApi.renderHelp toolSpec ["add"] =
      .ok (("Usage: " ++ "tool add" ++ " [OPTIONS] <") ++ ("widget" ++ ">\n\nAdd widget\n\nARGS:\n  <widget>    Widget name\n\n") ++
        ("OPTIONS:\n    " ++ "--cfg" ++ " <VALUE>    Config file\n  -h, --help    Print help\n  -V, --version    Print version\n")) := by
  change Internal.renderHelp toolSpec ["add"] = _
  have hv : Model.isValidSpec toolSpec = true := by decide
  have hp : Model.findSubcommandPath toolSpec ["add"] = .ok ([{ name := "cfg", long := some "cfg", help := "Config file", global := true }], some "3.0",
    { name := "add", about := "Add widget", args := [ { name := "widget", help := "Widget name" } ] }) := by cbv
  unfold Internal.renderHelp; rw [Shared.isValidSpecTR_eq, Shared.findSubcommandPathTR_eq, hv, hp]; dsimp only [Bind.bind, Except.bind, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  apply congrArg Except.ok; unfold Internal.renderHelpNode; dsimp only [toolSpec]
  have h1 : String.intercalate " " ["tool", "add"] = "tool add" := by decide
  have h2 : String.intercalate "" (List.map (fun (a : ArgSpec) => let base := if a.variadic then s!"{a.name}..." else a.name; if a.required then s!" <{base}>" else s!" [{base}]") [{ name := "widget", help := "Widget name" }]) = " <widget>" := by cbv
  have h3 : String.intercalate "\n" (List.map (fun (a : ArgSpec) => let tag := if a.variadic then s!"<{a.name}...>" else s!"<{a.name}>"; if a.help.isEmpty then s!"  {tag}" else s!"  {tag}    {a.help}") [{ name := "widget", help := "Widget name" }]) = "  <widget>    Widget name" := by cbv
  rw [h1, h2, h3]; dsimp only [List.append, List.map]; cbv
private theorem renderHelp_tool_missing_eq :
    defaultApi.renderHelp toolSpec ["missing"] = .error { kind := .unknownSubcommand, message := "unknown subcommand 'missing'", target := some "missing" } := by cbv
/-- `test_cmdline_renderHelpAndVersion` holds universally for `defaultApi`. -/
theorem allPass_renderHelpAndVersion : AllPass (test_cmdline_renderHelpAndVersion defaultApi) := by
  dsimp only [AllPass, AllPassRun, test_cmdline_renderHelpAndVersion, Bind.bind, Pure.pure, NondetTest.assert]
  have hr := renderHelp_tool_root_eq; have ha := renderHelp_tool_add_eq; have hm := renderHelp_tool_missing_eq
  dsimp only [toolSpec] at hr ha hm; rw [hr, ha, hm]; dsimp only; refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩, rfl, rfl, trivial⟩
  · exact string_contains_append_left (string_contains_append_left (string_contains_append_left (string_contains_append_left (string_contains_mid _ _ _))))
  · exact string_contains_append_left (string_contains_append_left (string_contains_append_left (string_contains_append_right (string_contains_mid _ _ _))))
  · exact string_contains_append_left (string_contains_append_left (string_contains_append_right (string_contains_mid _ _ _)))
  · exact string_contains_append_left (string_contains_append_right (string_contains_mid _ _ _))
  · exact string_contains_append_right (string_contains_mid _ _ _)
  · exact string_contains_append_left (string_contains_append_left (string_contains_mid _ _ _))
  · exact string_contains_append_left (string_contains_append_right (string_contains_append_left (String.contains_string_iff.mpr ⟨[], [], by simp⟩)))
  · exact string_contains_append_right (string_contains_mid _ _ _)
/-- `test_cmdline_renderHelpAndVersion` is reachable. -/
theorem canReach_renderHelpAndVersion : CanReach (test_cmdline_renderHelpAndVersion defaultApi) := allPass_renderHelpAndVersion
/-- `test_cmdline_runCliWith_customValidator` holds universally for `Internal.mkApiM`. -/
theorem allPass_runCliWith_customValidator : AllPass (test_cmdline_runCliWith_customValidator Internal.mkApiM) := by
  dsimp only [AllPass, AllPassRun, test_cmdline_runCliWith_customValidator, Bind.bind, Pure.pure, NondetTest.assert, Internal.mkApiM, Internal.runCliWith]
  simp only [Shared.parseWithEnvM_eq_spec, Internal.parseWithEnvSpecM, Shared.isValidSpecTR_eq]; cbv
/-- `test_cmdline_runCliWith_customValidator` is reachable. -/
theorem canReach_runCliWith_customValidator : CanReach (test_cmdline_runCliWith_customValidator Internal.mkApiM) := allPass_runCliWith_customValidator
/-- Proof that `parseWithEnv` under `pureIdCliOps` agrees universally with `parseWith`. -/
theorem allPass_parseWithEnv_unsetEnvMatchesParseWith :
    Core.AllPass (test_cmdline_parseWithEnv_unsetEnvMatchesParseWith defaultApi Internal.mkApiM) := fun _ _ _ => ⟨rfl, trivial⟩

private theorem mkFilesCliOps_eintr_case (k : Nat) (hk : k ≤ 8) :
    let ops := SysBridge.mkFilesCliOpsM (m := ScriptedCliM) scriptedStdioFilesOps (fun _ => pure (.ok none))
    let sRead : ScriptedStdioState :=
      { readQueue :=
          [.ok (ByteArray.mk #[0x68]), .ok (ByteArray.mk #[0x69])] ++
          List.replicate k (.error LeanSwe.LinuxSyscall.Errno.EINTR) ++
          [.ok (ByteArray.mk #[0x0D]), .ok (ByteArray.mk #[0x0A]), .ok (ByteArray.mk #[0x5A])] }
    let (rLine, sRead') := (ops.readLine : StateM ScriptedStdioState _).run sRead
    (match rLine with | .ok v => v == some "hi" | .error _ => false) = true ∧
      sRead'.openFds = [] ∧ sRead'.dupCount = 1 ∧ sRead'.readQueue.length = 1 := by
  rcases hk with _ | ⟨_ | ⟨_ | ⟨_ | ⟨_ | ⟨_ | ⟨_ | ⟨_ | ⟨_ | hbad⟩⟩⟩⟩⟩⟩⟩⟩
  · cbv
  · cbv
  · cbv
  · cbv
  · cbv
  · cbv
  · cbv
  · cbv
  · cbv

/-- `test_cmdline_mkFilesCliOps_eintrPartialWriteAndEof` holds universally for `SysBridge.mkFilesCliOpsM`. -/
theorem allPass_mkFilesCliOps_eintrPartialWriteAndEof :
    Core.AllPass (test_cmdline_mkFilesCliOps_eintrPartialWriteAndEof SysBridge.mkFilesCliOpsM) := by
  intro k hk
  have hc := mkFilesCliOps_eintr_case k hk
  refine ⟨hc.1, hc.2, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, trivial⟩
  · cbv
  · cbv
  · cbv
  · cbv
  · cbv
  · cbv
  · cbv
  · cbv

/-- `test_cmdline_mkFilesCliOps_eintrPartialWriteAndEof` is non-vacuously reachable. -/
theorem canReach_mkFilesCliOps_eintrPartialWriteAndEof :
    Core.CanReach (test_cmdline_mkFilesCliOps_eintrPartialWriteAndEof SysBridge.mkFilesCliOpsM) := by
  refine ⟨1, by decide, ?_⟩
  exact allPass_mkFilesCliOps_eintrPartialWriteAndEof 1 (by decide)

end LeanSwe.CmdLine.Proofs
