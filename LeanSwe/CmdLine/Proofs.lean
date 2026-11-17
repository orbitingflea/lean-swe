import LeanSwe.CmdLine.Interface
import LeanSwe.CmdLine.SpecTests
import LeanSwe.EnvVars.Proofs

set_option Elab.async false

namespace LeanSwe.CmdLine.Proofs

open Core
open Core.NondetTest
open LeanSwe.CmdLine

private theorem string_contains_append_left {a b sub : String} (h : a.contains sub = true) :
    (a ++ b).contains sub = true := by
  rw [String.contains_string_iff] at h ⊢
  rcases h with ⟨pre, post, hp⟩
  exact ⟨pre, post ++ b.toList, by rw [String.toList_append, ← hp]; simp [List.append_assoc]⟩

private theorem string_contains_append_right {a b sub : String} (h : b.contains sub = true) :
    (a ++ b).contains sub = true := by
  rw [String.contains_string_iff] at h ⊢
  rcases h with ⟨pre, post, hp⟩
  exact ⟨a.toList ++ pre, post, by rw [String.toList_append, ← hp]; simp [List.append_assoc]⟩

private theorem string_contains_of_eq_sub (s : String) : s.contains s = true := by
  rw [String.contains_string_iff]
  exact ⟨[], [], by simp⟩

private theorem string_contains_mid (pre mid post : String) :
    (pre ++ mid ++ post).contains mid = true :=
  string_contains_append_left (string_contains_append_right (string_contains_of_eq_sub mid))


private theorem parse_ok_of_pred (spec : CommandSpec) (args : List String)
    (p : ParsedCmd → Bool)
    (h : (match defaultApi.parse spec args with | .ok a => p a | .error _ => false) = true) :
    ∃ a, defaultApi.parse spec args = .ok a ∧ p a = true := by
  cases he : defaultApi.parse spec args with
  | error _ => simp [he] at h
  | ok a => simp [he] at h; exact ⟨a, rfl, h⟩

private theorem parse_err_of_pred (spec : CommandSpec) (args : List String)
    (p : CmdLineError → Bool)
    (h : (match defaultApi.parse spec args with | .ok _ => false | .error e => p e) = true) :
    ∃ e, defaultApi.parse spec args = .error e ∧ p e = true := by
  cases he : defaultApi.parse spec args with
  | ok _ => simp [he] at h
  | error e => simp [he] at h; exact ⟨e, rfl, h⟩

private theorem ne_empty_of_isEmpty_false {s : String} (h : (!s.isEmpty) = true) : s ≠ "" := by
  intro he; rw [he] at h; contradiction


/-- `test_cmdline_validSpec_rejectsFlagCollisions` holds universally for `defaultApi`. -/
theorem allPass_validSpec_rejectsFlagCollisions :
    AllPass (test_cmdline_validSpec_rejectsFlagCollisions defaultApi) := by
  dsimp only [AllPass, AllPassRun, test_cmdline_validSpec_rejectsFlagCollisions, Bind.bind,
    Pure.pure, NondetTest.assert]
  cbv

/-- `test_cmdline_validSpec_rejectsFlagCollisions` is reachable. -/
theorem canReach_validSpec_rejectsFlagCollisions :
    CanReach (test_cmdline_validSpec_rejectsFlagCollisions defaultApi) :=
  allPass_validSpec_rejectsFlagCollisions

/-- `test_cmdline_validSpec_rejectsStructuralAndEnvErrors` holds universally for `defaultApi`. -/
theorem allPass_validSpec_rejectsStructuralAndEnvErrors :
    AllPass (test_cmdline_validSpec_rejectsStructuralAndEnvErrors defaultApi) := by
  dsimp only [AllPass, AllPassRun, test_cmdline_validSpec_rejectsStructuralAndEnvErrors, Bind.bind,
    Pure.pure, NondetTest.assert]
  cbv

/-- `test_cmdline_validSpec_rejectsStructuralAndEnvErrors` is reachable. -/
theorem canReach_validSpec_rejectsStructuralAndEnvErrors :
    CanReach (test_cmdline_validSpec_rejectsStructuralAndEnvErrors defaultApi) :=
  allPass_validSpec_rejectsStructuralAndEnvErrors

/-- `test_cmdline_validSpec_shortOptOutAndParseRejectsInvalid` holds universally for `defaultApi`. -/
theorem allPass_validSpec_shortOptOutAndParseRejectsInvalid :
    AllPass (test_cmdline_validSpec_shortOptOutAndParseRejectsInvalid defaultApi) := by
  dsimp only [AllPass, AllPassRun, test_cmdline_validSpec_shortOptOutAndParseRejectsInvalid,
    Bind.bind, Pure.pure, NondetTest.assert]
  cbv

/-- `test_cmdline_validSpec_shortOptOutAndParseRejectsInvalid` is reachable. -/
theorem canReach_validSpec_shortOptOutAndParseRejectsInvalid :
    CanReach (test_cmdline_validSpec_shortOptOutAndParseRejectsInvalid defaultApi) :=
  allPass_validSpec_shortOptOutAndParseRejectsInvalid

/-- `test_cmdline_parse_shortBundlesAndValues` holds universally for `defaultApi`. -/
theorem allPass_parse_shortBundlesAndValues :
    AllPass (test_cmdline_parse_shortBundlesAndValues defaultApi) := by
  dsimp only [AllPass, AllPassRun, test_cmdline_parse_shortBundlesAndValues, Bind.bind, Pure.pure,
    NondetTest.assert]
  cbv

/-- `test_cmdline_parse_shortBundlesAndValues` is reachable. -/
theorem canReach_parse_shortBundlesAndValues :
    CanReach (test_cmdline_parse_shortBundlesAndValues defaultApi) :=
  allPass_parse_shortBundlesAndValues

/-- `test_cmdline_parse_shortLeftToRightHelpPrecedence` holds universally for `defaultApi`. -/
theorem allPass_parse_shortLeftToRightHelpPrecedence :
    AllPass (test_cmdline_parse_shortLeftToRightHelpPrecedence defaultApi) := by
  dsimp only [AllPass, AllPassRun, test_cmdline_parse_shortLeftToRightHelpPrecedence, Bind.bind,
    Pure.pure, NondetTest.assert]
  cbv

/-- `test_cmdline_parse_shortLeftToRightHelpPrecedence` is reachable. -/
theorem canReach_parse_shortLeftToRightHelpPrecedence :
    CanReach (test_cmdline_parse_shortLeftToRightHelpPrecedence defaultApi) :=
  allPass_parse_shortLeftToRightHelpPrecedence

/-- `test_cmdline_parse_duplicatesNegationAndSpaceBool` holds universally for `defaultApi`. -/
theorem allPass_parse_duplicatesNegationAndSpaceBool :
    AllPass (test_cmdline_parse_duplicatesNegationAndSpaceBool defaultApi) := by
  dsimp only [AllPass, AllPassRun, test_cmdline_parse_duplicatesNegationAndSpaceBool, Bind.bind,
    Pure.pure, NondetTest.assert]
  cbv

/-- `test_cmdline_parse_duplicatesNegationAndSpaceBool` is reachable. -/
theorem canReach_parse_duplicatesNegationAndSpaceBool :
    CanReach (test_cmdline_parse_duplicatesNegationAndSpaceBool defaultApi) :=
  allPass_parse_duplicatesNegationAndSpaceBool

/-- `test_cmdline_parse_negativeNumbersAndDashDash` holds universally for `defaultApi`. -/
theorem allPass_parse_negativeNumbersAndDashDash :
    AllPass (test_cmdline_parse_negativeNumbersAndDashDash defaultApi) := by
  dsimp only [AllPass, AllPassRun, test_cmdline_parse_negativeNumbersAndDashDash, Bind.bind,
    Pure.pure, NondetTest.assert]
  cbv
  decide

/-- `test_cmdline_parse_negativeNumbersAndDashDash` is reachable. -/
theorem canReach_parse_negativeNumbersAndDashDash :
    CanReach (test_cmdline_parse_negativeNumbersAndDashDash defaultApi) :=
  allPass_parse_negativeNumbersAndDashDash

/-- `test_cmdline_parse_subcommandsAndInheritedGlobals` holds universally for `defaultApi`. -/
theorem allPass_parse_subcommandsAndInheritedGlobals :
    AllPass (test_cmdline_parse_subcommandsAndInheritedGlobals defaultApi) := by
  dsimp only [AllPass, AllPassRun, test_cmdline_parse_subcommandsAndInheritedGlobals, Bind.bind,
    Pure.pure, NondetTest.assert]
  cbv

/-- `test_cmdline_parse_subcommandsAndInheritedGlobals` is reachable. -/
theorem canReach_parse_subcommandsAndInheritedGlobals :
    CanReach (test_cmdline_parse_subcommandsAndInheritedGlobals defaultApi) :=
  allPass_parse_subcommandsAndInheritedGlobals

private def typoSpec : CommandSpec :=
  { name := "tool"
    options := [ { name := "verbose", long := some "verbose", kind := .bool, global := true } ]
    subcommands := [ { name := "build" }, { name := "clean" } ] }

private theorem typo_verbos_err :
    ∃ e, defaultApi.parse typoSpec ["--verbos"] = .error e ∧
      e.kind = .unknownOption ∧ e.message.contains "did you mean '--verbose'" = true := by
  rcases parse_err_of_pred typoSpec ["--verbos"]
      (fun e => decide (e.kind = .unknownOption) && e.message.contains "did you mean '--verbose'")
      (by cbv) with ⟨e, he, hp⟩
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hp
  exact ⟨e, he, hp.1, hp.2⟩

private theorem typo_biuld_err :
    ∃ e, defaultApi.parse typoSpec ["biuld"] = .error e ∧
      e.kind = .unknownSubcommand ∧ e.message.contains "did you mean 'build'" = true := by
  rcases parse_err_of_pred typoSpec ["biuld"]
      (fun e => decide (e.kind = .unknownSubcommand) && e.message.contains "did you mean 'build'")
      (by cbv) with ⟨e, he, hp⟩
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hp
  exact ⟨e, he, hp.1, hp.2⟩

/-- `test_cmdline_parse_typoSuggestions` holds universally for `defaultApi`. -/
theorem allPass_parse_typoSuggestions :
    AllPass (test_cmdline_parse_typoSuggestions defaultApi) := by
  dsimp only [AllPass, AllPassRun, test_cmdline_parse_typoSuggestions, Bind.bind, Pure.pure,
    NondetTest.assert]
  rcases typo_verbos_err with ⟨e1, he1, hk1, hm1⟩
  rcases typo_biuld_err with ⟨e2, he2, hk2, hm2⟩
  dsimp only [typoSpec] at he1 he2
  rw [he1]
  dsimp only
  rw [he2]
  exact ⟨⟨hk1, hm1⟩, ⟨hk2, hm2⟩, trivial⟩

/-- `test_cmdline_parse_typoSuggestions` is reachable. -/
theorem canReach_parse_typoSuggestions :
    CanReach (test_cmdline_parse_typoSuggestions defaultApi) :=
  allPass_parse_typoSuggestions

/-- `test_cmdline_parseWith_customValidatorAndDecoder` holds universally for `defaultApi`. -/
theorem allPass_parseWith_customValidatorAndDecoder :
    AllPass (test_cmdline_parseWith_customValidatorAndDecoder defaultApi) := by
  dsimp only [AllPass, AllPassRun, test_cmdline_parseWith_customValidatorAndDecoder, Bind.bind,
    Pure.pure, NondetTest.assert]
  cbv

/-- `test_cmdline_parseWith_customValidatorAndDecoder` is reachable. -/
theorem canReach_parseWith_customValidatorAndDecoder :
    CanReach (test_cmdline_parseWith_customValidatorAndDecoder defaultApi) :=
  allPass_parseWith_customValidatorAndDecoder

/-- `test_cmdline_env_precedenceAndErrorPropagation` holds universally for `Internal.mkApiM`. -/
theorem allPass_env_precedenceAndErrorPropagation :
    AllPass (test_cmdline_env_precedenceAndErrorPropagation Internal.mkApiM) := by
  dsimp only [AllPass, AllPassRun, test_cmdline_env_precedenceAndErrorPropagation, Bind.bind,
    Pure.pure, NondetTest.assert]
  cbv

/-- `test_cmdline_env_precedenceAndErrorPropagation` is reachable. -/
theorem canReach_env_precedenceAndErrorPropagation :
    CanReach (test_cmdline_env_precedenceAndErrorPropagation Internal.mkApiM) :=
  allPass_env_precedenceAndErrorPropagation

private def edgeSpec : CommandSpec :=
  { name := "tool"
    options :=
      [ { name := "sep", short := some 's', kind := .string, global := true },
        { name := "verb", short := some 'v', kind := .bool, repeatable := true, global := true },
        { name := "cache", long := some "cache", kind := .bool, default := some "true", global := true } ]
    subcommands :=
      [ { name := "cp"
          args :=
            [ { name := "src", kind := .string },
              { name := "dst", kind := .string } ] } ] }

private def parsedEdge : ParsedCmd :=
  { subcommandPath := ["cp"]
    options :=
      [ ("sep", [.string ""]),
        ("verb", [.bool true, .bool true]),
        ("cache", [.bool false]) ]
    args := [("src", [.string "a.txt"]), ("dst", [.string "-b.txt"])]
    rawPositionals := ["a.txt", "-b.txt"] }

private theorem edge_parse_eq :
    defaultApi.parse edgeSpec ["cp", "-s", "", "-vv", "--no-cache", "--", "a.txt", "-b.txt"] =
      .ok parsedEdge := by
  have hb : (match defaultApi.parse edgeSpec ["cp", "-s", "", "-vv", "--no-cache", "--", "a.txt", "-b.txt"] with
      | .ok p => decide (p = parsedEdge)
      | .error _ => false) = true := by decide
  cases h : defaultApi.parse edgeSpec ["cp", "-s", "", "-vv", "--no-cache", "--", "a.txt", "-b.txt"] with
  | error e => simp [h] at hb
  | ok p => simp only [h, decide_eq_true_eq] at hb; subst hb; rfl

private theorem edge_render_eq :
    defaultApi.renderArgs edgeSpec parsedEdge =
      .ok ["cp", "-s", "", "-v", "-v", "--no-cache", "--", "a.txt", "-b.txt"] := by
  have hb : (match defaultApi.renderArgs edgeSpec parsedEdge with
      | .ok xs => decide (xs = ["cp", "-s", "", "-v", "-v", "--no-cache", "--", "a.txt", "-b.txt"])
      | .error _ => false) = true := by decide
  cases h : defaultApi.renderArgs edgeSpec parsedEdge with
  | error e => simp [h] at hb
  | ok xs => simp only [h, decide_eq_true_eq] at hb; subst hb; rfl

private theorem edge_round_eq :
    defaultApi.parse edgeSpec ["cp", "-s", "", "-v", "-v", "--no-cache", "--", "a.txt", "-b.txt"] =
      .ok parsedEdge := by
  have hb : (match defaultApi.parse edgeSpec ["cp", "-s", "", "-v", "-v", "--no-cache", "--", "a.txt", "-b.txt"] with
      | .ok p => decide (p = parsedEdge)
      | .error _ => false) = true := by decide
  cases h : defaultApi.parse edgeSpec ["cp", "-s", "", "-v", "-v", "--no-cache", "--", "a.txt", "-b.txt"] with
  | error e => simp [h] at hb
  | ok p => simp only [h, decide_eq_true_eq] at hb; subst hb; rfl

/-- `test_cmdline_renderArgs_roundTripEdgeCases` holds universally for `defaultApi`. -/
theorem allPass_renderArgs_roundTripEdgeCases :
    AllPass (test_cmdline_renderArgs_roundTripEdgeCases defaultApi) := by
  dsimp only [AllPass, AllPassRun, test_cmdline_renderArgs_roundTripEdgeCases, Bind.bind,
    Pure.pure, NondetTest.assert]
  have hp := edge_parse_eq
  have hr := edge_render_eq
  have hro := edge_round_eq
  dsimp only [edgeSpec] at hp hr hro
  rw [hp]
  dsimp only
  refine ⟨⟨rfl, rfl, by cbv, rfl, rfl⟩, ?_⟩
  rw [hr]
  dsimp only
  rw [hro]
  exact ⟨rfl, trivial⟩

/-- `test_cmdline_renderArgs_roundTripEdgeCases` is reachable. -/
theorem canReach_renderArgs_roundTripEdgeCases :
    CanReach (test_cmdline_renderArgs_roundTripEdgeCases defaultApi) :=
  allPass_renderArgs_roundTripEdgeCases

private def routingSpec : CommandSpec :=
  { name := "mytool"
    version := some "2.1.0"
    options := [ { name := "port", long := some "port", kind := .nat, envVar := some "PORT" } ] }

private theorem runCli_help_ok :
    let r := ((Internal.mkApiM mockCliOps).runCli routingSpec ["--help"] (fun _ => do
      mockCliOps.writeOut "HANDLER_CALLED"
      pure 7)).run {}
    r.1 = 0 ∧ r.2.stdout ≠ "" ∧ (!r.2.stdout.contains "HANDLER_CALLED") = true ∧ r.2.stderr = "" := by
  cbv

private theorem runCli_ver_ok :
    let r := ((Internal.mkApiM mockCliOps).runCli routingSpec ["-V"] (fun _ => do
      mockCliOps.writeOut "HANDLER_CALLED"
      pure 7)).run {}
    r.1 = 0 ∧ r.2.stdout = "mytool 2.1.0\n" ∧ r.2.stderr = "" := by
  cbv

private theorem runCli_unknown_ok :
    let r := ((Internal.mkApiM mockCliOps).runCli routingSpec ["--unknown"] (fun _ => do
      mockCliOps.writeOut "HANDLER_CALLED"
      pure 7)).run {}
    r.1 = 2 ∧ r.2.stdout = "" ∧ r.2.stderr ≠ "" := by
  cbv; decide

private theorem runCli_ioErr_ok :
    let r := ((Internal.mkApiM mockCliOps).runCli routingSpec [] (fun _ => do
      mockCliOps.writeOut "HANDLER_CALLED"
      pure 7)).run { env := [("PORT", .error { kind := .ioError, message := "utf8" })] }
    r.1 = 2 ∧ r.2.stdout = "" ∧ r.2.stderr.contains "utf8" = true := by
  cbv

private theorem runCli_port443_ok (exitCode : UInt32) :
    let r := ((Internal.mkApiM mockCliOps).runCli routingSpec ["--port", "443"] (fun cmd =>
      pure (if cmd.getNat "port" = some 443 then exitCode else 99))).run {}
    r.1 = exitCode ∧ r.2.stderr = "" := by
  have hp : (Internal.mkApiM mockCliOps).parseWithEnv routingSpec ["--port", "443"] [] {} =
      (Except.ok { options := [("port", [.nat 443])] }, {}) := by cbv
  dsimp only [Internal.mkApiM, Internal.runCli, Internal.runCliWith, StateT.run, Bind.bind,
    StateT.bind, Pure.pure, StateT.pure] at hp ⊢
  rw [hp]
  exact ⟨rfl, rfl⟩

/-- `test_cmdline_runCli_routingAndExitCodes` holds universally for `Internal.mkApiM`. -/
theorem allPass_runCli_routingAndExitCodes :
    AllPass (test_cmdline_runCli_routingAndExitCodes Internal.mkApiM) := by
  dsimp only [AllPass, AllPassRun, test_cmdline_runCli_routingAndExitCodes, Bind.bind, Pure.pure,
    NondetTest.nondet, NondetTest.assert]
  exact ⟨runCli_help_ok, runCli_ver_ok, runCli_unknown_ok, runCli_ioErr_ok,
    fun exitCode => ⟨runCli_port443_ok exitCode, trivial⟩⟩

/-- `test_cmdline_runCli_routingAndExitCodes` is reachable. -/
theorem canReach_runCli_routingAndExitCodes :
    CanReach (test_cmdline_runCli_routingAndExitCodes Internal.mkApiM) := by
  have h := allPass_runCli_routingAndExitCodes
  dsimp only [AllPass, AllPassRun, CanReach, CanReachRun, test_cmdline_runCli_routingAndExitCodes,
    Bind.bind, Pure.pure, NondetTest.nondet, NondetTest.assert] at h ⊢
  exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, 42, h.2.2.2.2 42⟩

/-- `test_cmdline_interactive_promptAndConfirm` holds universally for `Internal.mkApiM`. -/
theorem allPass_interactive_promptAndConfirm :
    AllPass (test_cmdline_interactive_promptAndConfirm Internal.mkApiM) := by
  dsimp only [AllPass, AllPassRun, test_cmdline_interactive_promptAndConfirm, Bind.bind, Pure.pure,
    NondetTest.assert]
  refine ⟨by cbv, by cbv, ⟨_, by cbv, by cbv⟩, by cbv, ⟨⟨_, by cbv, by cbv⟩, by cbv⟩,
    ⟨_, by cbv, by cbv⟩, trivial⟩

/-- `test_cmdline_interactive_promptAndConfirm` is reachable. -/
theorem canReach_interactive_promptAndConfirm :
    CanReach (test_cmdline_interactive_promptAndConfirm Internal.mkApiM) :=
  allPass_interactive_promptAndConfirm

private def toolHvSpec : CommandSpec :=
  { name := "tool"
    version := some "1.0"
    options := [ { name := "port", long := some "port", kind := .nat, global := true } ]
    subcommands := [ { name := "sub", version := some "2.0" } ] }

/-- `test_cmdline_parse_helpAndVersionRouting` holds universally for `defaultApi`. -/
theorem allPass_parse_helpAndVersionRouting :
    AllPass (test_cmdline_parse_helpAndVersionRouting defaultApi) := by
  dsimp only [AllPass, AllPassRun, test_cmdline_parse_helpAndVersionRouting, Bind.bind, Pure.pure,
    NondetTest.assert]
  rcases parse_err_of_pred { name := "app" } ["--version"] (fun e => decide (e.kind = .unknownOption))
      (by decide) with ⟨e1, he1, hp1⟩
  rcases parse_err_of_pred { name := "app" } ["-V"] (fun e => decide (e.kind = .unknownOption))
      (by decide) with ⟨e2, he2, hp2⟩
  rcases parse_err_of_pred toolHvSpec ["--badopt", "--help"] (fun e => decide (e.kind = .unknownOption))
      (by decide) with ⟨e3, he3, hp3⟩
  rcases parse_err_of_pred toolHvSpec ["--help", "--badopt"]
      (fun e => decide (e.kind = .helpRequested) && !e.message.isEmpty)
      (by cbv) with ⟨e4, he4, hp4⟩
  rcases parse_err_of_pred toolHvSpec ["sub", "-V"]
      (fun e => decide (e.kind = .versionRequested ∧ e.message = "tool 2.0\n"))
      (by decide) with ⟨e5, he5, hp5⟩
  rcases parse_err_of_pred toolHvSpec ["--port", "--help"] (fun e => decide (e.kind = .invalidValue))
      (by decide) with ⟨e6, he6, hp6⟩
  dsimp only [toolHvSpec] at he3 he4 he5 he6
  simp only [decide_eq_true_eq, Bool.and_eq_true] at hp1 hp2 hp3 hp4 hp5 hp6
  rw [he1]; dsimp only
  rw [he2]; dsimp only
  rw [he3]; dsimp only
  rw [he4]; dsimp only
  rw [he5]; dsimp only
  rw [he6]; dsimp only
  exact ⟨hp1, hp2, hp3, ⟨hp4.1, ne_empty_of_isEmpty_false hp4.2⟩, hp5, hp6, trivial⟩

/-- `test_cmdline_parse_helpAndVersionRouting` is reachable. -/
theorem canReach_parse_helpAndVersionRouting :
    CanReach (test_cmdline_parse_helpAndVersionRouting defaultApi) :=
  allPass_parse_helpAndVersionRouting

private def posSpec : CommandSpec :=
  { name := "app"
    options :=
      [ { name := "port", long := some "port", kind := .nat },
        { name := "flag", long := some "flag", kind := .bool },
        { name := "rep", long := some "rep", kind := .bool, repeatable := true } ]
    args :=
      [ { name := "count", kind := .nat },
        { name := "mode", kind := .choice ["fast", "safe"], required := false, default := some "safe" },
        { name := "rest", required := false, variadic := true } ] }

/-- `test_cmdline_parse_positionalArgsAndErrors` holds universally for `defaultApi`. -/
theorem allPass_parse_positionalArgsAndErrors :
    AllPass (test_cmdline_parse_positionalArgsAndErrors defaultApi) := by
  dsimp only [AllPass, AllPassRun, test_cmdline_parse_positionalArgsAndErrors, Bind.bind,
    Pure.pure, NondetTest.assert]
  rcases parse_ok_of_pred posSpec ["10"]
      (fun a => decide (a.getNat "count" = some 10 ∧ a.getChoice "mode" = some "safe" ∧
        a.getList "rest" = [] ∧ a.rawPositionals = ["10"])) (by decide) with ⟨a1, h1, ha1⟩
  rcases parse_ok_of_pred posSpec ["10", "fast", "a", "b"]
      (fun a => decide (a.getNat "count" = some 10 ∧ a.getChoice "mode" = some "fast" ∧
        a.getList "rest" = [.string "a", .string "b"] ∧ a.rawPositionals = ["10", "fast", "a", "b"])) (by decide) with ⟨a2, h2, ha2⟩
  rcases parse_err_of_pred posSpec [] (fun e => decide (e.kind = .missingArgument)) (by decide) with ⟨e3, he3, hp3⟩
  rcases parse_err_of_pred posSpec ["not-nat"] (fun e => decide (e.kind = .invalidValue)) (by decide) with ⟨e4, he4, hp4⟩
  rcases parse_err_of_pred posSpec ["--port"] (fun e => decide (e.kind = .missingArgument)) (by decide) with ⟨e5, he5, hp5⟩
  rcases parse_err_of_pred posSpec ["--no-flag=bar", "1"] (fun e => decide (e.kind = .invalidValue)) (by decide) with ⟨e6, he6, hp6⟩
  rcases parse_err_of_pred posSpec ["--rep=false", "1"] (fun e => decide (e.kind = .invalidValue)) (by decide) with ⟨e7, he7, hp7⟩
  rcases parse_err_of_pred { name := "app", args := [{ name := "one", kind := .string, required := true }] } ["a", "b"]
      (fun e => decide (e.kind = .unexpectedArgument)) (by decide) with ⟨e8, he8, hp8⟩
  dsimp only [posSpec] at h1 h2 he3 he4 he5 he6 he7 he8
  simp only [decide_eq_true_eq] at hp3 hp4 hp5 hp6 hp7 hp8
  rw [h1]; dsimp only
  rw [h2]; dsimp only
  rw [he3]; dsimp only
  rw [he4]; dsimp only
  rw [he5]; dsimp only
  rw [he6]; dsimp only
  rw [he7]; dsimp only
  rw [he8]; dsimp only
  simp only [decide_eq_true_eq] at ha1 ha2
  exact ⟨⟨ha1.1, ha1.2.1, ha1.2.2.1⟩, ⟨ha2.2.1, ha2.2.2.1⟩, hp3, hp4, hp5, hp6, hp7, hp8, trivial⟩

/-- `test_cmdline_parse_positionalArgsAndErrors` is reachable. -/
theorem canReach_parse_positionalArgsAndErrors :
    CanReach (test_cmdline_parse_positionalArgsAndErrors defaultApi) :=
  allPass_parse_positionalArgsAndErrors

private def toolSpec : CommandSpec :=
  { name := "tool"
    version := some "3.0"
    about := "Manage widgets"
    options := [ { name := "cfg", long := some "cfg", help := "Config file", global := true } ]
    subcommands :=
      [ { name := "add"
          about := "Add widget"
          args := [ { name := "widget", help := "Widget name" } ] } ] }

private theorem renderHelp_tool_root_eq :
    defaultApi.renderHelp toolSpec [] =
      .ok (("Usage: " ++ "tool" ++ " [OPTIONS] <SUBCOMMAND>\n\nManage widgets\n\n") ++
        ("SUBCOMMANDS:\n  " ++ "add" ++ "    Add widget\n\n") ++
        ("OPTIONS:\n    " ++ "--cfg" ++ " <VALUE>    Config file\n") ++
        ("  -h, " ++ "--help" ++ "    Print help\n") ++
        ("  -V, " ++ "--version" ++ "    Print version\n")) := by
  cbv

private theorem renderHelp_tool_add_eq :
    defaultApi.renderHelp toolSpec ["add"] =
      .ok (("Usage: " ++ "tool add" ++ " [OPTIONS] <") ++
        ("widget" ++ ">\n\nAdd widget\n\nARGS:\n  <widget>    Widget name\n\n") ++
        ("OPTIONS:\n    " ++ "--cfg" ++ " <VALUE>    Config file\n  -h, --help    Print help\n  -V, --version    Print version\n")) := by
  change Internal.renderHelp toolSpec ["add"] = _
  have hv : Model.isValidSpec toolSpec = true := by decide
  have hp : Model.findSubcommandPath toolSpec ["add"] =
      .ok ([{ name := "cfg", long := some "cfg", help := "Config file", global := true }], some "3.0",
        { name := "add", about := "Add widget", args := [ { name := "widget", help := "Widget name" } ] }) := by
    cbv
  unfold Internal.renderHelp
  rw [hv, hp]
  dsimp only [Bind.bind, Except.bind, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  apply congrArg Except.ok
  unfold Internal.renderHelpNode
  dsimp only [toolSpec]
  have h1 : String.intercalate " " ["tool", "add"] = "tool add" := by decide
  have h2 : String.intercalate "" (List.map (fun (a : ArgSpec) =>
      let base := if a.variadic then s!"{a.name}..." else a.name
      if a.required then s!" <{base}>" else s!" [{base}]")
      [{ name := "widget", help := "Widget name" }]) = " <widget>" := by cbv
  have h3 : String.intercalate "\n" (List.map (fun (a : ArgSpec) =>
      let tag := if a.variadic then s!"<{a.name}...>" else s!"<{a.name}>"
      if a.help.isEmpty then s!"  {tag}" else s!"  {tag}    {a.help}")
      [{ name := "widget", help := "Widget name" }]) = "  <widget>    Widget name" := by cbv
  rw [h1, h2, h3]
  dsimp only [List.append, List.map]
  cbv

private theorem renderHelp_tool_missing_eq :
    defaultApi.renderHelp toolSpec ["missing"] =
      .error { kind := .unknownSubcommand, message := "unknown subcommand 'missing'", target := some "missing" } := by
  cbv

/-- `test_cmdline_renderHelpAndVersion` holds universally for `defaultApi`. -/
theorem allPass_renderHelpAndVersion :
    AllPass (test_cmdline_renderHelpAndVersion defaultApi) := by
  dsimp only [AllPass, AllPassRun, test_cmdline_renderHelpAndVersion, Bind.bind, Pure.pure,
    NondetTest.assert]
  have hr := renderHelp_tool_root_eq
  have ha := renderHelp_tool_add_eq
  have hm := renderHelp_tool_missing_eq
  dsimp only [toolSpec] at hr ha hm
  rw [hr, ha, hm]
  dsimp only
  refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩, rfl, rfl, trivial⟩
  · exact string_contains_append_left (string_contains_append_left (string_contains_append_left (string_contains_append_left (string_contains_mid _ _ _))))
  · exact string_contains_append_left (string_contains_append_left (string_contains_append_left (string_contains_append_right (string_contains_mid _ _ _))))
  · exact string_contains_append_left (string_contains_append_left (string_contains_append_right (string_contains_mid _ _ _)))
  · exact string_contains_append_left (string_contains_append_right (string_contains_mid _ _ _))
  · exact string_contains_append_right (string_contains_mid _ _ _)
  · exact string_contains_append_left (string_contains_append_left (string_contains_mid _ _ _))
  · exact string_contains_append_left (string_contains_append_right (string_contains_append_left (string_contains_of_eq_sub _)))
  · exact string_contains_append_right (string_contains_mid _ _ _)

/-- `test_cmdline_renderHelpAndVersion` is reachable. -/
theorem canReach_renderHelpAndVersion :
    CanReach (test_cmdline_renderHelpAndVersion defaultApi) :=
  allPass_renderHelpAndVersion

/-- `test_cmdline_runCliWith_customValidator` holds universally for `Internal.mkApiM`. -/
theorem allPass_runCliWith_customValidator :
    AllPass (test_cmdline_runCliWith_customValidator Internal.mkApiM) := by
  dsimp only [AllPass, AllPassRun, test_cmdline_runCliWith_customValidator, Bind.bind, Pure.pure,
    NondetTest.assert]
  cbv

/-- `test_cmdline_runCliWith_customValidator` is reachable. -/
theorem canReach_runCliWith_customValidator :
    CanReach (test_cmdline_runCliWith_customValidator Internal.mkApiM) :=
  allPass_runCliWith_customValidator

private def isAsciiDigit (c : Char) : Bool := '0' ≤ c && c ≤ '9'

private theorem digitChar_prop (k : Nat) (hk : k < 10) :
    isAsciiDigit (Nat.digitChar k) = true ∧ (Nat.digitChar k).toNat - 48 = k := by
  match k, hk with
  | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ | 6, _ | 7, _ | 8, _ | 9, _ => decide

private theorem toDigitsCore_acc (fuel n : Nat) (acc : List Char) :
    Nat.toDigitsCore 10 fuel n acc = Nat.toDigitsCore 10 fuel n [] ++ acc := by
  induction fuel generalizing n acc with
  | zero => rfl
  | succ fuel ih =>
    unfold Nat.toDigitsCore
    dsimp only
    by_cases h : n / 10 = 0
    · simp [h]
    · simp only [h, ↓reduceIte]
      rw [ih (n / 10) (Nat.digitChar (n % 10) :: acc), ih (n / 10) [Nat.digitChar (n % 10)]]
      simp [List.append_assoc]

private theorem toDigitsCore_nonempty (fuel n : Nat) (hf : n < fuel) :
    (Nat.toDigitsCore 10 fuel n []).isEmpty = false := by
  cases fuel with
  | zero => omega
  | succ fuel =>
    unfold Nat.toDigitsCore
    dsimp only
    by_cases h : n / 10 = 0
    · simp [h]
    · simp only [h, ↓reduceIte]
      rw [toDigitsCore_acc]
      cases h' : Nat.toDigitsCore 10 fuel (n / 10) [] <;> simp

private theorem toDigitsCore_allDigits (fuel n : Nat) (hf : n < fuel) :
    (Nat.toDigitsCore 10 fuel n []).all isAsciiDigit = true := by
  induction fuel generalizing n with
  | zero => omega
  | succ fuel ih =>
    unfold Nat.toDigitsCore
    dsimp only
    have hlt : n % 10 < 10 := Nat.mod_lt n (by decide)
    have hd := (digitChar_prop (n % 10) hlt).1
    by_cases h : n / 10 = 0
    · simp [h, hd]
    · simp only [h, ↓reduceIte]
      rw [toDigitsCore_acc, List.all_append]
      have hdiv : n / 10 < fuel := by omega
      simp [ih (n / 10) hdiv, hd]

private theorem toDigitsCore_foldl (fuel n : Nat) (hf : n < fuel) :
    (Nat.toDigitsCore 10 fuel n []).foldl (fun acc c => acc * 10 + (c.toNat - 48)) 0 = n := by
  induction fuel generalizing n with
  | zero => omega
  | succ fuel ih =>
    unfold Nat.toDigitsCore
    dsimp only
    have hlt : n % 10 < 10 := Nat.mod_lt n (by decide)
    have hval : (Nat.digitChar (n % 10)).toNat - 48 = n % 10 := (digitChar_prop (n % 10) hlt).2
    by_cases h : n / 10 = 0
    · simp only [h, ↓reduceIte, List.foldl_cons, List.foldl_nil, Nat.zero_mul, Nat.zero_add]
      omega
    · simp only [h, ↓reduceIte]
      rw [toDigitsCore_acc, List.foldl_append, ih (n / 10) (by omega)]
      simp only [List.foldl_cons, List.foldl_nil]
      omega

private theorem parseNatChars_toString (n : Nat) :
    Model.parseNatChars (toString n).toList = some n := by
  change Model.parseNatChars (Nat.repr n).toList = some n
  rw [Nat.repr, String.toList_ofList, Nat.toDigits]
  unfold Model.parseNatChars
  have hne := toDigitsCore_nonempty (n + 1) n (Nat.lt_succ_self n)
  have hall : (Nat.toDigitsCore 10 (n + 1) n []).all (fun c => '0' ≤ c && c ≤ '9') = true :=
    toDigitsCore_allDigits (n + 1) n (Nat.lt_succ_self n)
  have hfold := toDigitsCore_foldl (n + 1) n (Nat.lt_succ_self n)
  simp only [hne, Bool.false_eq_true, ↓reduceIte, hall]
  exact congrArg some hfold

private theorem parseIntChars_of_head_ne_dash (c : Char) (cs : List Char) (hne : c ≠ '-') :
    Model.parseIntChars (c :: cs) = (Model.parseNatChars (c :: cs)).map Int.ofNat := by
  unfold Model.parseIntChars
  cases c with
  | mk val h =>
    split
    · rename_i rest hmatch
      injection hmatch with hc
      exact absurd hc hne
    · rfl

private theorem parseIntChars_toString (i : Int) :
    Model.parseIntChars (toString i).toList = some i := by
  change Model.parseIntChars (Int.repr i).toList = some i
  cases i with
  | ofNat n =>
    simp only [Int.repr]
    have hnat := parseNatChars_toString n
    have hchars : (Nat.repr n).toList = Nat.toDigits 10 n := by rw [Nat.repr, String.toList_ofList]
    have hall : (Nat.toDigits 10 n).all isAsciiDigit = true :=
      toDigitsCore_allDigits (n + 1) n (Nat.lt_succ_self n)
    have hne : (Nat.toDigits 10 n).isEmpty = false :=
      toDigitsCore_nonempty (n + 1) n (Nat.lt_succ_self n)
    cases hc : (Nat.repr n).toList with
    | nil => rw [← hchars, hc] at hne; simp at hne
    | cons c cs =>
      have hc0 : isAsciiDigit c = true := by
        rw [← hchars, hc, List.all_cons, Bool.and_eq_true] at hall; exact hall.1
      have hneDash : c ≠ '-' := by intro hdash; subst hdash; revert hc0; decide
      rw [parseIntChars_of_head_ne_dash c cs hneDash, ← hc]
      change (Model.parseNatChars (toString n).toList).map Int.ofNat = some (Int.ofNat n)
      rw [hnat]; rfl
  | negSucc k =>
    simp only [Int.repr, String.toList_append]
    have hdash : ("-".toList) = ['-'] := rfl
    rw [hdash]
    simp only [List.cons_append, List.nil_append, Model.parseIntChars]
    have hnat : Model.parseNatChars (Nat.repr (k + 1)).toList = some (k + 1) :=
      parseNatChars_toString (k + 1)
    change (Model.parseNatChars (Nat.repr (k + 1)).toList).map (fun n => -(Int.ofNat n)) = some (Int.negSucc k)
    rw [hnat]; rfl

private theorem valueKind_eq_of_beq {a b : ValueKind} (h : (a == b) = true) : a = b := by
  cases a with
  | string => cases b <;> first | rfl | exact Bool.noConfusion h
  | bool => cases b <;> first | rfl | exact Bool.noConfusion h
  | nat => cases b <;> first | rfl | exact Bool.noConfusion h
  | int => cases b <;> first | rfl | exact Bool.noConfusion h
  | choice opts1 =>
    cases b with
    | choice opts2 =>
      have : (opts1 == opts2) = true := h
      rw [beq_iff_eq.mp this]
    | _ => exact Bool.noConfusion h
  | custom t1 =>
    cases b with
    | custom t2 =>
      have : (t1 == t2) = true := h
      rw [beq_iff_eq.mp this]
    | _ => exact Bool.noConfusion h

private theorem valueKind_beq_false_of_ne {a b : ValueKind} (h : a ≠ b) : (a == b) = false := by
  cases heq : a == b
  · rfl
  · exact absurd (valueKind_eq_of_beq heq) h

private def OptValueMatchesKind : ValueKind → OptValue → Prop
  | .string, .string _ => True
  | .bool, .bool _ => True
  | .nat, .nat _ => True
  | .int, .int _ => True
  | .choice opts, .choice s => s ∈ opts
  | .custom _, .custom _ => True
  | _, _ => False

private theorem parseOptValueWith_nil (k : ValueKind) (s : String) :
    Model.parseOptValueWith k s [] = Model.parseOptValue k s := by
  unfold Model.parseOptValueWith Model.validateCustomValue
  cases hk : Model.parseOptValue k s with
  | error e => rfl
  | ok v => cases k <;> simp [Bind.bind, Except.bind, pure, Except.pure]

private theorem parseOptValue_ok_matchesKind {k : ValueKind} {s : String} {v : OptValue}
    (h : Model.parseOptValue k s = .ok v) : OptValueMatchesKind k v := by
  cases k with
  | string => simp only [Model.parseOptValue, Except.ok.injEq] at h; subst h; trivial
  | bool =>
    simp only [Model.parseOptValue] at h
    cases hb : Model.parseBoolString s with
    | none => simp [hb] at h
    | some b => simp [hb] at h; subst h; trivial
  | nat =>
    simp only [Model.parseOptValue] at h
    cases hn : Model.parseNatChars s.toList with
    | none => simp [hn] at h
    | some n => simp [hn] at h; subst h; trivial
  | int =>
    simp only [Model.parseOptValue] at h
    cases hi : Model.parseIntChars s.toList with
    | none => simp [hi] at h
    | some i => simp [hi] at h; subst h; trivial
  | choice opts =>
    simp only [Model.parseOptValue] at h
    by_cases hc : s ∈ opts
    · simp [hc] at h; subst h; exact hc
    · simp [hc] at h
  | custom _ => simp only [Model.parseOptValue, Except.ok.injEq] at h; subst h; trivial

private theorem parseOptValue_optValueToString {k : ValueKind} {v : OptValue}
    (hv : OptValueMatchesKind k v) :
    Model.parseOptValue k (Model.optValueToString v) = .ok v := by
  cases k <;> cases v <;> simp only [OptValueMatchesKind] at hv
  case string.string s => rfl
  case bool.bool b => cases b <;> rfl
  case nat.nat n => simp only [Model.parseOptValue, Model.optValueToString, parseNatChars_toString]
  case int.int i => simp only [Model.parseOptValue, Model.optValueToString, parseIntChars_toString]
  case choice.choice opts s =>
    simp only [Model.parseOptValue, Model.optValueToString, List.contains_iff_mem.mpr hv, ↓reduceIte]
  case custom.custom _ s => rfl

private theorem splitFirstEq_go_append (rev cs vs : List Char) (hno : '=' ∉ cs) :
    Internal.splitFirstEq.go (String.ofList (rev.reverse ++ cs ++ ('=' :: vs))) rev (cs ++ ('=' :: vs)) =
      (String.ofList (rev.reverse ++ cs), some (String.ofList vs)) := by
  induction cs generalizing rev with
  | nil => simp [Internal.splitFirstEq.go]
  | cons c cs ih =>
    have hne : c ≠ '=' := fun h => hno (by simp [h])
    have hno' : '=' ∉ cs := fun h => hno (by simp [h])
    simp only [List.cons_append, Internal.splitFirstEq.go, beq_iff_eq, hne, ↓reduceIte]
    have h1 : (c :: rev).reverse ++ cs = rev.reverse ++ (c :: cs) := by simp
    have h2 := ih (c :: rev) hno'
    rw [h1] at h2
    exact h2

private theorem splitFirstEq_append (l val : String) (hno : '=' ∉ l.toList) :
    Internal.splitFirstEq (l ++ "=" ++ val) = (l, some val) := by
  unfold Internal.splitFirstEq
  have heq : (l ++ "=" ++ val).toList = l.toList ++ ('=' :: val.toList) := by
    simp [String.toList_append]
  have h1 : String.ofList ([].reverse ++ l.toList ++ ('=' :: val.toList)) = l ++ "=" ++ val := by
    rw [List.reverse_nil, List.nil_append, ← heq, String.ofList_toList]
  have h2 : String.ofList ([].reverse ++ l.toList) = l := by simp [String.ofList_toList]
  have h3 := splitFirstEq_go_append [] l.toList val.toList hno
  simp only [String.ofList_toList] at h3
  rw [heq]; rw [h1, h2] at h3; exact h3

private theorem splitFirstEq_go_none (rev cs : List Char) (hno : '=' ∉ cs) :
    Internal.splitFirstEq.go (String.ofList (rev.reverse ++ cs)) rev cs =
      (String.ofList (rev.reverse ++ cs), none) := by
  induction cs generalizing rev with
  | nil => simp [Internal.splitFirstEq.go]
  | cons c cs ih =>
    have hne : c ≠ '=' := fun h => hno (by simp [h])
    have hno' : '=' ∉ cs := fun h => hno (by simp [h])
    simp only [Internal.splitFirstEq.go, beq_iff_eq, hne, ↓reduceIte]
    have h1 : (c :: rev).reverse ++ cs = rev.reverse ++ (c :: cs) := by simp
    have h2 := ih (c :: rev) hno'
    rw [h1] at h2
    exact h2

private theorem splitFirstEq_none (l : String) (hno : '=' ∉ l.toList) :
    Internal.splitFirstEq l = (l, none) := by
  unfold Internal.splitFirstEq
  have h3 := splitFirstEq_go_none [] l.toList hno
  simp only [List.reverse_nil, List.nil_append, String.ofList_toList] at h3
  exact h3

private theorem allDistinct_nodup {α : Type} [BEq α] [LawfulBEq α] {xs : List α}
    (h : Model.allDistinct xs = true) : xs.Nodup := by
  induction xs with
  | nil => exact List.nodup_nil
  | cons x xs ih =>
    simp only [Model.allDistinct, Bool.and_eq_true, Bool.not_eq_true'] at h
    rw [List.nodup_cons]
    refine ⟨?_, ih h.2⟩
    intro hx
    have hc : xs.contains x = true := List.contains_iff_mem.mpr hx
    rw [h.1] at hc; cases hc

private theorem find?_unique_key {α β : Type} [BEq β] [LawfulBEq β]
    (key : α → Option β) (xs : List α) (hnd : (xs.filterMap key).Nodup)
    (x : α) (hx : x ∈ xs) (b : β) (hk : key x = some b) :
    xs.find? (fun y => key y == some b) = some x := by
  induction xs with
  | nil => cases hx
  | cons y ys ih =>
    simp only [List.mem_cons] at hx
    rcases hx with rfl | hmem
    · simp [hk]
    · cases hyk : key y with
      | none => simp only [List.filterMap_cons, hyk] at hnd; simp [hyk, ih hnd hmem]
      | some by' =>
        simp only [List.filterMap_cons, hyk, List.nodup_cons] at hnd
        have hmemB : b ∈ ys.filterMap key := List.mem_filterMap.mpr ⟨x, hmem, hk⟩
        have hne : by' ≠ b := fun heq => hnd.1 (heq ▸ hmemB)
        simp [hyk, hne, ih hnd.2 hmem]

private theorem collectVisibleLongs_cons (y : OptSpec) (ys : List OptSpec) :
    Model.collectVisibleLongs (y :: ys) =
      match y.long with
      | none => Model.collectVisibleLongs ys
      | some l =>
        if y.kind == .bool && !y.repeatable then l :: ("no-" ++ l) :: Model.collectVisibleLongs ys
        else l :: Model.collectVisibleLongs ys := rfl

private theorem mem_collectVisibleLongs_of_long (opts : List OptSpec) {o : OptSpec} {l : String}
    (ho : o ∈ opts) (hl : o.long = some l) : l ∈ Model.collectVisibleLongs opts := by
  induction opts with
  | nil => cases ho
  | cons y ys ih =>
    simp only [List.mem_cons] at ho
    rw [collectVisibleLongs_cons]
    rcases ho with rfl | hmem
    · rw [hl]; dsimp only; split <;> simp
    · have ih' := ih hmem
      cases y.long with
      | none => exact ih'
      | some ly => dsimp only; split <;> simp [ih']

private theorem mem_collectVisibleLongs_of_neg (opts : List OptSpec) {o : OptSpec} {l : String}
    (ho : o ∈ opts) (hk : o.kind = .bool) (hnr : o.repeatable = false) (hl : o.long = some l) :
    ("no-" ++ l) ∈ Model.collectVisibleLongs opts := by
  induction opts with
  | nil => cases ho
  | cons y ys ih =>
    simp only [List.mem_cons] at ho
    rw [collectVisibleLongs_cons]
    rcases ho with rfl | hmem
    · have hb : (o.kind == .bool && !o.repeatable) = true := by simp [hk, hnr]; rfl
      rw [hl]; dsimp only; rw [hb]; simp
    · have ih' := ih hmem
      cases y.long with
      | none => exact ih'
      | some ly => dsimp only; split <;> simp [ih']

private theorem filterMap_long_nodup (opts : List OptSpec)
    (h : (Model.collectVisibleLongs opts).Nodup) :
    (opts.filterMap (·.long)).Nodup := by
  induction opts with
  | nil => exact List.nodup_nil
  | cons y ys ih =>
    rw [collectVisibleLongs_cons] at h
    cases hyl : y.long with
    | none => rw [hyl] at h; simp only [List.filterMap_cons, hyl]; exact ih h
    | some ly =>
      rw [hyl] at h; dsimp only at h
      split at h
      · have h1 := List.nodup_cons.mp h
        have h2 := List.nodup_cons.mp h1.2
        simp only [List.filterMap_cons, hyl, List.nodup_cons]
        refine ⟨fun hmem => ?_, ih h2.2⟩
        rcases List.mem_filterMap.mp hmem with ⟨x, hx, hxl⟩
        exact h1.1 (by simp [mem_collectVisibleLongs_of_long ys hx hxl])
      · have h1 := List.nodup_cons.mp h
        simp only [List.filterMap_cons, hyl, List.nodup_cons]
        refine ⟨fun hmem => ?_, ih h1.2⟩
        rcases List.mem_filterMap.mp hmem with ⟨x, hx, hxl⟩
        exact h1.1 (mem_collectVisibleLongs_of_long ys hx hxl)

private theorem no_opt_with_neg_long (opts : List OptSpec)
    (h : (Model.collectVisibleLongs opts).Nodup)
    {o : OptSpec} (ho : o ∈ opts) (hk : o.kind = .bool) (hnr : o.repeatable = false)
    {l : String} (hl : o.long = some l) :
    ∀ x ∈ opts, x.long ≠ some ("no-" ++ l) := by
  induction opts with
  | nil => cases ho
  | cons y ys ih =>
    simp only [List.mem_cons] at ho
    rw [collectVisibleLongs_cons] at h
    intro x hx hxl
    simp only [List.mem_cons] at hx
    rcases ho with rfl | hoy
    · have hb : (o.kind == .bool && !o.repeatable) = true := by simp [hk, hnr]; rfl
      rw [hl] at h; dsimp only at h; rw [hb] at h; simp only [↓reduceIte] at h
      have h1 := List.nodup_cons.mp h
      have h2 := List.nodup_cons.mp h1.2
      rcases hx with rfl | hxy
      · rw [hl] at hxl
        injection hxl with hlen
        have hlen' := congrArg String.length hlen
        simp at hlen'
      · exact h2.1 (mem_collectVisibleLongs_of_long ys hxy hxl)
    · rcases hx with rfl | hxy
      · rw [hxl] at h; dsimp only at h
        split at h
        · have h1 := List.nodup_cons.mp h
          exact h1.1 (by simp [mem_collectVisibleLongs_of_neg ys hoy hk hnr hl])
        · have h1 := List.nodup_cons.mp h
          exact h1.1 (mem_collectVisibleLongs_of_neg ys hoy hk hnr hl)
      · cases hyl : y.long with
        | none => rw [hyl] at h; exact ih h hoy x hxy hxl
        | some ly =>
          rw [hyl] at h; dsimp only at h
          split at h
          · have h1 := List.nodup_cons.mp h
            have h2 := List.nodup_cons.mp h1.2
            exact ih h2.2 hoy x hxy hxl
          · have h1 := List.nodup_cons.mp h
            exact ih h1.2 hoy x hxy hxl

private theorem find?_none_of_all_ne {α : Type} (p : α → Bool) (xs : List α)
    (h : ∀ x ∈ xs, p x = false) : xs.find? p = none := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.find?]
    have hx := h x (by simp)
    rw [hx]
    exact ih (fun y hy => h y (by simp [hy]))

private theorem find?_bool_pred_of_find?_long (opts : List OptSpec) {o : OptSpec}
    (hk : o.kind = .bool) (hnr : o.repeatable = false) {l : String}
    (hf : opts.find? (fun x => x.long == some l) = some o) :
    opts.find? (fun x => x.kind == .bool && !x.repeatable && x.long == some l) = some o := by
  induction opts with
  | nil => cases hf
  | cons y ys ih =>
    simp only [List.find?] at hf ⊢
    cases hyl : (y.long == some l) with
    | true =>
      rw [hyl] at hf
      injection hf with hyo
      subst hyo
      have hb : (y.kind == .bool && !y.repeatable) = true := by simp [hk, hnr]; rfl
      rw [hb]; rfl
    | false =>
      rw [hyl] at hf
      simp only [Bool.and_false]
      exact ih hf

private theorem lookupLongOpt_pos (opts : List OptSpec)
    (hnd : (Model.collectVisibleLongs opts).Nodup)
    {o : OptSpec} (ho : o ∈ opts) {l : String} (hl : o.long = some l) :
    Internal.lookupLongOpt opts l = some (o, false) := by
  have hfm : (opts.filterMap (·.long)).Nodup := filterMap_long_nodup opts hnd
  have hf : opts.find? (fun x => x.long == some l) = some o :=
    find?_unique_key (·.long) opts hfm o ho l hl
  unfold Internal.lookupLongOpt
  rw [hf]

private theorem lookupLongOpt_neg (opts : List OptSpec)
    (hnd : (Model.collectVisibleLongs opts).Nodup)
    {o : OptSpec} (ho : o ∈ opts) (hk : o.kind = .bool) (hnr : o.repeatable = false)
    {l : String} (hl : o.long = some l) :
    Internal.lookupLongOpt opts ("no-" ++ l) = some (o, true) := by
  have hno := no_opt_with_neg_long opts hnd ho hk hnr hl
  have hnone : opts.find? (fun x => x.long == some ("no-" ++ l)) = none := by
    apply find?_none_of_all_ne
    intro x hx
    simp only [beq_eq_false_iff_ne, ne_eq]
    exact hno x hx
  have hsnd : Model.startsWithNoDash ("no-" ++ l) = true := by
    unfold Model.startsWithNoDash; rw [String.toList_append]; rfl
  have hdrop : String.ofList (("no-" ++ l).toList.drop 3) = l := by
    rw [String.toList_append]
    have hpre : "no-".toList = ['n', 'o', '-'] := rfl
    rw [hpre]; simp [String.ofList_toList]
  have hf : opts.find? (fun x => x.long == some l) = some o :=
    find?_unique_key (·.long) opts (filterMap_long_nodup opts hnd) o ho l hl
  have hpred := find?_bool_pred_of_find?_long opts hk hnr hf
  unfold Internal.lookupLongOpt
  rw [hnone, hsnd, hdrop]
  simp [hpred]

private theorem lookupLongOpt_mem {opts : List OptSpec} {namePart : String}
    {opt : OptSpec} {isNeg : Bool}
    (h : Internal.lookupLongOpt opts namePart = some (opt, isNeg)) :
    opt ∈ opts ∧
    opt.long.isNone = false ∧
    (isNeg = true → opt.kind = .bool ∧ opt.repeatable = false) := by
  unfold Internal.lookupLongOpt at h
  cases hf : opts.find? (fun o => o.long == some namePart) with
  | some o =>
    rw [hf] at h
    injection h with hpair
    injection hpair with ho hn
    subst ho hn
    have hp := List.find?_some hf
    simp only [beq_iff_eq] at hp
    exact ⟨List.mem_of_find?_eq_some hf, by rw [hp]; rfl, fun hc => by cases hc⟩
  | none =>
    rw [hf] at h
    dsimp only at h
    split at h
    · cases hf2 : opts.find? (fun o => o.kind == .bool && !o.repeatable && o.long == some _) with
      | none => rw [hf2] at h; cases h
      | some o =>
        rw [hf2] at h
        injection h with hpair
        injection hpair with ho hn
        subst ho hn
        have hp := List.find?_some hf2
        simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true'] at hp
        exact ⟨List.mem_of_find?_eq_some hf2, ⟨by rw [hp.2]; rfl,
          fun _ => ⟨valueKind_eq_of_beq hp.1.1, hp.1.2⟩⟩⟩
    · cases h

private def NodeInv (node : CommandSpec) (g : List OptSpec) (v : Option String) : Prop :=
  Model.isValidCommandNode node g v = true ∧ g.all Model.isValidOptLocal = true

private theorem isValidSubcommandList_mem {subs : List CommandSpec} {ng : List OptSpec}
    {nv : Option String} (h : Model.isValidSubcommandList subs ng nv = true)
    {sub : CommandSpec} (hs : sub ∈ subs) :
    Model.isValidCommandNode sub ng nv = true := by
  induction subs with
  | nil => cases hs
  | cons y ys ih =>
    unfold Model.isValidSubcommandList at h
    simp only [Bool.and_eq_true] at h
    simp only [List.mem_cons] at hs
    rcases hs with rfl | hmem
    · exact h.1
    · exact ih h.2 hmem

private theorem nodeInv_sub {node : CommandSpec} {g : List OptSpec} {v : Option String}
    (h : NodeInv node g v) {sub : CommandSpec} (hs : sub ∈ node.subcommands) :
    NodeInv sub (g ++ node.options) (node.version <|> v) := by
  rcases node with ⟨name, version, about, shortHelp, shortVersion, options, args, subcommands⟩
  rcases h with ⟨hvalid, hg⟩
  unfold Model.isValidCommandNode at hvalid
  dsimp only at hvalid
  simp only [Bool.and_eq_true] at hvalid
  have ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨_, hopts⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, hsub⟩ := hvalid
  have hall : (g ++ options).all Model.isValidOptLocal = true := by
    rw [List.all_append, hg, hopts]; rfl
  exact ⟨isValidSubcommandList_mem hsub hs, hall⟩

private theorem nodeInv_props {node : CommandSpec} {g : List OptSpec} {v : Option String}
    (h : NodeInv node g v) :
    Model.isValidCommandName node.name = true ∧
    (∀ o ∈ g ++ node.options, Model.isValidOptLocal o = true) ∧
    ((g ++ node.options).map (·.name)).Nodup ∧
    (Model.collectVisibleLongs (g ++ node.options)).Nodup ∧
    ((g ++ node.options).filterMap (·.short)).Nodup ∧
    (node.shortHelp = true → 'h' ∉ (g ++ node.options).filterMap (·.short)) ∧
    ((node.shortVersion && (node.version <|> v).isSome) = true →
      'V' ∉ (g ++ node.options).filterMap (·.short)) ∧
    (node.subcommands.map (·.name)).Nodup := by
  rcases node with ⟨name, version, about, shortHelp, shortVersion, options, args, subcommands⟩
  rcases h with ⟨hvalid, hg⟩
  unfold Model.isValidCommandNode at hvalid
  dsimp only at hvalid
  simp only [Bool.and_eq_true] at hvalid
  have ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hcmd, hopts⟩, hnames⟩, hlongs⟩, hshorts⟩, _⟩, hh⟩, hV⟩, _⟩, _⟩, _⟩, _⟩, _⟩, hsubs⟩, _⟩ := hvalid
  refine ⟨hcmd, ?_, allDistinct_nodup hnames, allDistinct_nodup hlongs, allDistinct_nodup hshorts, ?_, ?_,
    allDistinct_nodup hsubs⟩
  · intro o ho
    rw [List.mem_append] at ho
    rcases ho with ho | ho
    · exact List.all_eq_true.mp hg o ho
    · exact List.all_eq_true.mp hopts o ho
  · intro hsh hmem
    dsimp only at hsh hmem
    rw [hsh] at hh
    simp only [Bool.not_true, Bool.false_or, Bool.not_eq_true'] at hh
    have hc : ((g ++ options).filterMap (·.short)).contains 'h' = true := List.contains_iff_mem.mpr hmem
    rw [hh] at hc; cases hc
  · intro hsv hmem
    dsimp only at hsv hmem
    rw [hsv] at hV
    simp only [Bool.not_true, Bool.false_or, Bool.not_eq_true'] at hV
    have hc : ((g ++ options).filterMap (·.short)).contains 'V' = true := List.contains_iff_mem.mpr hmem
    rw [hV] at hc; cases hc

private def lookupCli (cliOpts : List (String × List OptValue)) (name : String) : List OptValue :=
  match cliOpts.find? (fun p => p.1 == name) with
  | some p => p.2
  | none => []

private theorem recordCliOpt_lookupCli_same (cliOpts : List (String × List OptValue))
    (name : String) (v : OptValue) :
    lookupCli (Internal.recordCliOpt cliOpts name v) name = lookupCli cliOpts name ++ [v] := by
  induction cliOpts with
  | nil => simp [Internal.recordCliOpt, lookupCli]
  | cons p rest ih =>
    rcases p with ⟨k, vs⟩
    unfold Internal.recordCliOpt
    by_cases hk : k == name
    · simp [hk, lookupCli]
    · simp [hk, lookupCli]; exact ih

private theorem recordCliOpt_lookupCli_ne (cliOpts : List (String × List OptValue))
    (name k' : String) (v : OptValue) (hne : k' ≠ name) :
    lookupCli (Internal.recordCliOpt cliOpts name v) k' = lookupCli cliOpts k' := by
  induction cliOpts with
  | nil => simp [Internal.recordCliOpt, lookupCli, hne.symm]
  | cons p rest ih =>
    rcases p with ⟨k, vs⟩
    unfold Internal.recordCliOpt
    by_cases hk : k == name
    · have hk' : (k == k') = false := by
        simp only [beq_iff_eq] at hk
        simp [beq_eq_false_iff_ne, hk, hne.symm]
      simp [hk, lookupCli, hk']
    · by_cases hk' : k == k'
      · simp [hk, lookupCli, hk']
      · simp [hk, lookupCli, hk']; exact ih

private def recordCliOptMany (cliOpts : List (String × List OptValue)) (name : String)
    (vals : List OptValue) : List (String × List OptValue) :=
  vals.foldl (fun acc v => Internal.recordCliOpt acc name v) cliOpts

private theorem recordCliOptMany_lookupCli_same (cliOpts : List (String × List OptValue))
    (name : String) (vals : List OptValue) :
    lookupCli (recordCliOptMany cliOpts name vals) name = lookupCli cliOpts name ++ vals := by
  induction vals generalizing cliOpts with
  | nil => simp [recordCliOptMany]
  | cons v vs ih =>
    simp only [recordCliOptMany, List.foldl_cons]
    change lookupCli (recordCliOptMany (Internal.recordCliOpt cliOpts name v) name vs) name = _
    rw [ih, recordCliOpt_lookupCli_same, List.append_assoc]
    rfl

private theorem recordCliOptMany_lookupCli_ne (cliOpts : List (String × List OptValue))
    (name k' : String) (vals : List OptValue) (hne : k' ≠ name) :
    lookupCli (recordCliOptMany cliOpts name vals) k' = lookupCli cliOpts k' := by
  induction vals generalizing cliOpts with
  | nil => simp [recordCliOptMany]
  | cons v vs ih =>
    simp only [recordCliOptMany, List.foldl_cons]
    change lookupCli (recordCliOptMany (Internal.recordCliOpt cliOpts name v) name vs) k' = _
    rw [ih, recordCliOpt_lookupCli_ne _ _ _ _ hne]

private def CliOptsInv (visibleOpts : List OptSpec) (cliOpts : List (String × List OptValue)) : Prop :=
  (∀ k, lookupCli cliOpts k ≠ [] → ∃ opt ∈ visibleOpts, opt.name = k) ∧
  (∀ opt ∈ visibleOpts, ∀ v ∈ lookupCli cliOpts opt.name,
    OptValueMatchesKind opt.kind v ∧
    (opt.kind == .bool && opt.repeatable → v = .bool true) ∧
    (opt.kind == .bool && opt.long.isNone → v = .bool true))

private theorem cliOptsInv_record {visibleOpts : List OptSpec} {cliOpts : List (String × List OptValue)}
    (hnd : (visibleOpts.map (·.name)).Nodup) (hinv : CliOptsInv visibleOpts cliOpts)
    {opt : OptSpec} (ho : opt ∈ visibleOpts) {v : OptValue}
    (hm : OptValueMatchesKind opt.kind v)
    (hrep : opt.kind == .bool && opt.repeatable → v = .bool true)
    (hnl : opt.kind == .bool && opt.long.isNone → v = .bool true) :
    CliOptsInv visibleOpts (Internal.recordCliOpt cliOpts opt.name v) := by
  refine ⟨fun k hk => ?_, fun o ho' v' hv' => ?_⟩
  · by_cases hko : k = opt.name
    · exact ⟨opt, ho, hko.symm⟩
    · rw [recordCliOpt_lookupCli_ne _ _ _ _ hko] at hk
      exact hinv.1 k hk
  · by_cases hoo : o.name = opt.name
    · have heq : o = opt := by
        clear hinv hv'
        induction visibleOpts with
        | nil => cases ho
        | cons y ys ih =>
          simp only [List.map_cons, List.nodup_cons, List.mem_map] at hnd
          simp only [List.mem_cons] at ho ho'
          rcases ho with rfl | ho <;> rcases ho' with rfl | ho'
          · rfl
          · exact absurd ⟨o, ho', hoo⟩ hnd.1
          · exact absurd ⟨opt, ho, hoo.symm⟩ hnd.1
          · exact ih hnd.2 ho ho'
      subst heq
      rw [recordCliOpt_lookupCli_same, List.mem_append] at hv'
      rcases hv' with hv' | hv'
      · exact hinv.2 o ho' v' hv'
      · simp only [List.mem_singleton] at hv'; subst hv'; exact ⟨hm, hrep, hnl⟩
    · rw [recordCliOpt_lookupCli_ne _ _ _ _ hoo] at hv'
      exact hinv.2 o ho' v' hv'

private theorem cliOptsInv_weaken_sub {visibleOpts subOpts : List OptSpec}
    {cliOpts : List (String × List OptValue)}
    (hnd : ((visibleOpts ++ subOpts).map (·.name)).Nodup)
    (hinv : CliOptsInv visibleOpts cliOpts) :
    CliOptsInv (visibleOpts ++ subOpts) cliOpts := by
  refine ⟨fun k hk => ?_, fun o ho v hv => ?_⟩
  · rcases hinv.1 k hk with ⟨opt, hmem, hname⟩
    exact ⟨opt, List.mem_append_left subOpts hmem, hname⟩
  · rw [List.mem_append] at ho
    rcases ho with ho | ho
    · exact hinv.2 o ho v hv
    · have hne : lookupCli cliOpts o.name = [] :=
        Classical.byContradiction fun hne => by
          rcases hinv.1 o.name hne with ⟨opt, hmem, hname⟩
          rw [List.map_append, List.nodup_append] at hnd
          exact hnd.2.2 opt.name (List.mem_map.mpr ⟨opt, hmem, rfl⟩) o.name
            (List.mem_map.mpr ⟨o, ho, rfl⟩) hname
      rw [hne] at hv
      cases hv

private theorem parseShortBundle_inv (visibleOpts : List OptSpec) (shortHelp shortVersion : Bool)
    (rootName : String) (subPath : List String) (effVer : Option String) (curSpec : CommandSpec)
    (hnd : (visibleOpts.map (·.name)).Nodup)
    (cliOpts : List (String × List OptValue)) (hinv : CliOptsInv visibleOpts cliOpts)
    (cs : List Char) {nextCli : List (String × List OptValue)} {nextPend : Option OptSpec}
    (h : Internal.parseShortBundle visibleOpts shortHelp shortVersion rootName subPath effVer
      curSpec [] cliOpts cs = .ok (nextCli, nextPend)) :
    CliOptsInv visibleOpts nextCli ∧
    (∀ o, nextPend = some o → o ∈ visibleOpts ∧ o.kind ≠ .bool) := by
  induction cs generalizing cliOpts with
  | nil =>
    unfold Internal.parseShortBundle at h
    injection h with hpair; injection hpair with hc hp; subst hc hp
    exact ⟨hinv, fun _ hc => by cases hc⟩
  | cons c rest ih =>
    unfold Internal.parseShortBundle at h
    split at h
    · cases h
    · split at h
      · cases effVer <;> cases h
      · cases hf : visibleOpts.find? (fun o => o.short == some c) with
        | none => simp [hf] at h
        | some opt =>
          simp only [hf] at h
          have ho : opt ∈ visibleOpts := List.mem_of_find?_eq_some hf
          by_cases hbool : opt.kind == .bool
          · simp only [hbool, ↓reduceIte] at h
            have hbk : opt.kind = .bool := valueKind_eq_of_beq hbool
            have hinv' := cliOptsInv_record hnd hinv ho
              (by rw [hbk]; trivial) (fun _ => rfl) (fun _ => rfl)
            exact ih _ hinv' h
          · simp only [hbool, Bool.false_eq_true, ↓reduceIte] at h
            have hnk : opt.kind ≠ .bool := fun hk => hbool (by simp [hk]; rfl)
            cases hr : rest.isEmpty with
            | false =>
              have hr' : (!rest.isEmpty) = true := by simp [hr]
              simp only [hr', ↓reduceIte] at h
              rw [parseOptValueWith_nil] at h
              cases hp : Model.parseOptValue opt.kind (String.ofList rest) with
              | error e => simp [hp, Bind.bind, Except.bind] at h
              | ok v =>
                simp only [hp, Bind.bind, Except.bind, Except.ok.injEq, Prod.mk.injEq] at h
                rcases h with ⟨hc, hnp⟩
                subst hc hnp
                refine ⟨cliOptsInv_record hnd hinv ho (parseOptValue_ok_matchesKind hp)
                  (fun hb => absurd (valueKind_eq_of_beq ((Bool.and_eq_true _ _).mp hb).1) hnk)
                  (fun hb => absurd (valueKind_eq_of_beq ((Bool.and_eq_true _ _).mp hb).1) hnk),
                  fun _ hc => by cases hc⟩
            | true =>
              have hr' : (!rest.isEmpty) = false := by simp [hr]
              simp only [hr', Bool.false_eq_true, ↓reduceIte, Except.ok.injEq, Prod.mk.injEq] at h
              rcases h with ⟨hc, hnp⟩
              subst hc hnp
              exact ⟨hinv, fun o heq => by injection heq with ho'; subst ho'; exact ⟨ho, hnk⟩⟩

private theorem findSubcommandPath_go_step_aux (g : List OptSpec) (v : Option String)
    (cur sub : CommandSpec) (path : List String)
    (hfind : cur.subcommands.find? (fun s => s.name == sub.name) = some sub) :
    ∀ g0 v0 node,
      Model.findSubcommandPath.go g0 v0 node path = .ok (g, v, cur) →
      Model.findSubcommandPath.go g0 v0 node (path ++ [sub.name]) =
        .ok (g ++ cur.options, sub.version <|> v, sub) := by
  intro g0 v0 node
  induction path generalizing g0 v0 node with
  | nil =>
    intro hp0
    unfold Model.findSubcommandPath.go at hp0
    injection hp0 with hp'
    injection hp' with hg ht
    injection ht with hv hc
    subst hg hv hc
    simp [Model.findSubcommandPath.go, hfind]
  | cons p ps ih =>
    intro hp0
    unfold Model.findSubcommandPath.go at hp0
    cases hfp : node.subcommands.find? (fun s => s.name == p) with
    | none => simp [hfp] at hp0
    | some next =>
      simp only [hfp] at hp0
      simp only [List.cons_append, Model.findSubcommandPath.go, hfp]
      exact ih (g0 ++ node.options) (node.version <|> v0) next hp0

private theorem findSubcommandPath_go_step (g : List OptSpec) (v : Option String)
    (root cur sub : CommandSpec) (path : List String)
    (hp : Model.findSubcommandPath.go [] none root path = .ok (g, v, cur))
    (hfind : cur.subcommands.find? (fun s => s.name == sub.name) = some sub) :
    Model.findSubcommandPath.go [] none root (path ++ [sub.name]) =
      .ok (g ++ cur.options, sub.version <|> v, sub) :=
  findSubcommandPath_go_step_aux g v cur sub path hfind [] none root hp

private def ParseStateInv (rootSpec : CommandSpec) (st : Internal.ParseState) : Prop :=
  (∃ verParent, NodeInv st.curSpec st.inheritedGlobals verParent ∧
    st.effectiveVersion = (st.curSpec.version <|> verParent)) ∧
  Model.findSubcommandPath rootSpec st.subPath =
    .ok (st.inheritedGlobals, st.effectiveVersion, st.curSpec) ∧
  CliOptsInv (st.inheritedGlobals ++ st.curSpec.options) st.cliOpts ∧
  (∀ o, st.pendingOpt = some o →
    o ∈ st.inheritedGlobals ++ st.curSpec.options ∧ o.kind ≠ .bool)

private theorem parseTokens_sound (rootSpec : CommandSpec) (st : Internal.ParseState)
    (hinv : ParseStateInv rootSpec st) (toks : List String)
    {finalState : Internal.ParseState}
    (h : Internal.parseTokens rootSpec.name [] st toks = .ok finalState) :
    ParseStateInv rootSpec finalState ∧ finalState.pendingOpt = none := by
  induction toks generalizing st with
  | nil =>
    unfold Internal.parseTokens at h
    cases hp : st.pendingOpt with
    | some _ => simp [hp] at h
    | none =>
      simp only [hp, Except.ok.injEq] at h
      subst h
      exact ⟨hinv, hp⟩
  | cons tok rest ih =>
    rcases hinv with ⟨⟨vp, hnode, heff⟩, hpath, hcli, hpend⟩
    have hprops := nodeInv_props hnode
    have hndNames := hprops.2.2.1
    unfold Internal.parseTokens at h
    cases hp : st.pendingOpt with
    | some opt =>
      rw [hp] at h
      dsimp only at h
      rw [parseOptValueWith_nil] at h
      cases hpv : Model.parseOptValue opt.kind tok with
      | error e => simp [hpv, Bind.bind, Except.bind] at h
      | ok v =>
        simp only [hpv, Bind.bind, Except.bind] at h
        rcases hpend opt hp with ⟨ho, hnk⟩
        have hcli' := cliOptsInv_record hndNames hcli ho (parseOptValue_ok_matchesKind hpv)
          (fun hb => absurd (valueKind_eq_of_beq ((Bool.and_eq_true _ _).mp hb).1) hnk)
          (fun hb => absurd (valueKind_eq_of_beq ((Bool.and_eq_true _ _).mp hb).1) hnk)
        exact ih { st with pendingOpt := none, cliOpts := Internal.recordCliOpt st.cliOpts opt.name v }
          ⟨⟨vp, hnode, heff⟩, hpath, hcli', fun _ hc => by cases hc⟩ h
    | none =>
      rw [hp] at h
      dsimp only at h
      by_cases had : st.afterDashDash
      · simp only [had, ↓reduceIte] at h
        exact ih { st with afterDashDash := true, pendingOpt := none, rawPositionals := st.rawPositionals ++ [tok] }
          ⟨⟨vp, hnode, heff⟩, hpath, hcli, fun _ hc => by cases hc⟩ h
      · simp only [had, Bool.false_eq_true, ↓reduceIte] at h
        by_cases hdd : tok == "--"
        · simp only [hdd, ↓reduceIte] at h
          exact ih { st with afterDashDash := true, pendingOpt := none }
            ⟨⟨vp, hnode, heff⟩, hpath, hcli, fun _ hc => by cases hc⟩ h
        · simp only [hdd, Bool.false_eq_true, ↓reduceIte] at h
          by_cases hhelp : tok == "--help"
          · simp [hhelp] at h
          · simp only [hhelp, Bool.false_eq_true, ↓reduceIte] at h
            by_cases hver : (tok == "--version" && st.effectiveVersion.isSome)
            · simp only [hver, ↓reduceIte] at h
              cases hev : st.effectiveVersion <;> simp [hev] at h
            · simp only [hver, Bool.false_eq_true, ↓reduceIte] at h
              split at h
              · split at h
                · cases h
                · split at h
                  · cases h
                  · rename_i longRest _ _ _
                    cases hlkp : Internal.lookupLongOpt (st.inheritedGlobals ++ st.curSpec.options)
                        (Internal.splitFirstEq (String.ofList longRest)).fst with
                    | none => simp [hlkp] at h
                    | some p =>
                      rcases p with ⟨opt, isNeg⟩
                      simp only [hlkp] at h
                      rcases lookupLongOpt_mem hlkp with ⟨ho, hln, hneg⟩
                      by_cases hin : isNeg
                      · simp only [hin, ↓reduceIte] at h
                        cases heqv : (Internal.splitFirstEq (String.ofList longRest)).snd with
                        | some val => rw [heqv] at h; cases h
                        | none =>
                          rw [heqv] at h
                          dsimp only at h
                          rcases hneg hin with ⟨hk, hnr⟩
                          have hcli' := cliOptsInv_record hndNames hcli ho (v := .bool false)
                            (by rw [hk]; trivial)
                            (fun hb => by rw [hnr, Bool.and_false] at hb; cases hb)
                            (fun hb => by rw [hln, Bool.and_false] at hb; cases hb)
                          exact ih { st with afterDashDash := false, pendingOpt := none, cliOpts := Internal.recordCliOpt st.cliOpts opt.name (.bool false) }
                            ⟨⟨vp, hnode, heff⟩, hpath, hcli', fun _ hc => by cases hc⟩ h
                      · simp only [hin, Bool.false_eq_true, ↓reduceIte] at h
                        by_cases hbool : opt.kind == .bool
                        · simp only [hbool, ↓reduceIte] at h
                          have hk := valueKind_eq_of_beq hbool
                          cases heqv : (Internal.splitFirstEq (String.ofList longRest)).snd with
                          | none =>
                            rw [heqv] at h
                            dsimp only at h
                            have hcli' := cliOptsInv_record hndNames hcli ho (v := .bool true)
                              (by rw [hk]; trivial) (fun _ => rfl) (fun _ => rfl)
                            exact ih { st with afterDashDash := false, pendingOpt := none, cliOpts := Internal.recordCliOpt st.cliOpts opt.name (.bool true) }
                              ⟨⟨vp, hnode, heff⟩, hpath, hcli', fun _ hc => by cases hc⟩ h
                          | some rawVal =>
                            rw [heqv] at h
                            dsimp only at h
                            cases hpv : Model.parseOptValue .bool rawVal with
                            | error e => rw [hpv] at h; cases h
                            | ok ov =>
                              cases ov with
                              | bool b =>
                                rw [hpv] at h
                                dsimp only at h
                                split at h
                                · cases h
                                · rename_i hnb
                                  have hcli' := cliOptsInv_record hndNames hcli ho (v := .bool b)
                                    (by rw [hk]; trivial)
                                    (fun hb => by
                                      cases hb' : b
                                      · rw [hb'] at hnb
                                        have hrep : opt.repeatable = true := (Bool.and_eq_true _ _).mp hb |>.2
                                        simp [hrep] at hnb
                                      · rfl)
                                    (fun hnl => by rw [hln, Bool.and_false] at hnl; cases hnl)
                                  exact ih { st with afterDashDash := false, pendingOpt := none, cliOpts := Internal.recordCliOpt st.cliOpts opt.name (.bool b) }
                                    ⟨⟨vp, hnode, heff⟩, hpath, hcli', fun _ hc => by cases hc⟩ h
                              | _ => rw [hpv] at h; cases h
                        · simp only [hbool, Bool.false_eq_true, ↓reduceIte] at h
                          have hnk : opt.kind ≠ .bool := fun hk => hbool (by simp [hk]; rfl)
                          cases heqv : (Internal.splitFirstEq (String.ofList longRest)).snd with
                          | some rawVal =>
                            rw [heqv] at h
                            dsimp only at h
                            rw [parseOptValueWith_nil] at h
                            cases hpv : Model.parseOptValue opt.kind rawVal with
                            | error e => rw [hpv] at h; cases h
                            | ok v =>
                              rw [hpv] at h
                              dsimp only [Bind.bind, Except.bind] at h
                              have hcli' := cliOptsInv_record hndNames hcli ho
                                (parseOptValue_ok_matchesKind hpv)
                                (fun hb => absurd (valueKind_eq_of_beq (Bool.and_eq_true _ _ |>.mp hb).1) hnk)
                                (fun hb => absurd (valueKind_eq_of_beq (Bool.and_eq_true _ _ |>.mp hb).1) hnk)
                              exact ih { st with afterDashDash := false, pendingOpt := none, cliOpts := Internal.recordCliOpt st.cliOpts opt.name v }
                                ⟨⟨vp, hnode, heff⟩, hpath, hcli', fun _ hc => by cases hc⟩ h
                          | none =>
                            rw [heqv] at h
                            dsimp only at h
                            exact ih { st with afterDashDash := false, pendingOpt := some opt }
                              ⟨⟨vp, hnode, heff⟩, hpath, hcli, fun o ho' => by
                                injection ho' with heq; subst heq; exact ⟨ho, hnk⟩⟩ h
              · rename_i c shortRest _ _
                cases hsb : Internal.parseShortBundle (st.inheritedGlobals ++ st.curSpec.options)
                    st.curSpec.shortHelp st.curSpec.shortVersion rootSpec.name st.subPath
                    st.effectiveVersion st.curSpec [] st.cliOpts (c :: shortRest) with
                | error e =>
                  rw [hsb] at h
                  cases h
                | ok p =>
                  rcases p with ⟨nextCli, nextPend⟩
                  rw [hsb] at h
                  dsimp only [Bind.bind, Except.bind] at h
                  rcases parseShortBundle_inv (st.inheritedGlobals ++ st.curSpec.options)
                    st.curSpec.shortHelp st.curSpec.shortVersion rootSpec.name st.subPath
                    st.effectiveVersion st.curSpec hndNames st.cliOpts hcli (c :: shortRest) hsb with
                    ⟨hcli', hpend'⟩
                  exact ih { st with afterDashDash := false, cliOpts := nextCli, pendingOpt := nextPend }
                    ⟨⟨vp, hnode, heff⟩, hpath, hcli', hpend'⟩ h
              · split at h
                · cases hfs : st.curSpec.subcommands.find? (fun s => s.name == tok) with
                  | none => simp [hfs] at h
                  | some sub =>
                    simp only [hfs] at h
                    have hs : sub ∈ st.curSpec.subcommands := List.mem_of_find?_eq_some hfs
                    have hsubNode := nodeInv_sub hnode hs
                    rw [← heff] at hsubNode
                    have hsubProps := nodeInv_props hsubNode
                    have hfm : st.curSpec.subcommands.filterMap (fun s => some s.name) =
                        st.curSpec.subcommands.map (·.name) := by
                      clear h hsubNode hsubProps hs hfs
                      induction st.curSpec.subcommands <;> simp [*]
                    have hndSubs : (st.curSpec.subcommands.filterMap (fun s => some s.name)).Nodup := by
                      rw [hfm]; exact hprops.2.2.2.2.2.2.2
                    have hfind : st.curSpec.subcommands.find? (fun s => s.name == sub.name) = some sub := by
                      have hraw := find?_unique_key (fun s => some s.name) st.curSpec.subcommands hndSubs
                        sub hs sub.name rfl
                      exact hraw
                    have hpath' := findSubcommandPath_go_step st.inheritedGlobals st.effectiveVersion
                      rootSpec st.curSpec sub st.subPath hpath hfind
                    have hcli' := cliOptsInv_weaken_sub hsubProps.2.2.1 hcli
                    exact ih { st with curSpec := sub, subPath := st.subPath ++ [sub.name], inheritedGlobals := st.inheritedGlobals ++ st.curSpec.options, effectiveVersion := sub.version <|> st.effectiveVersion, afterDashDash := false, pendingOpt := none, rawPositionals := [] }
                      ⟨⟨st.effectiveVersion, hsubNode, rfl⟩, hpath', hcli', fun _ hc => by cases hc⟩ h
                · exact ih { st with afterDashDash := false, pendingOpt := none, rawPositionals := st.rawPositionals ++ [tok] }
                    ⟨⟨vp, hnode, heff⟩, hpath, hcli, fun _ hc => by cases hc⟩ h

private theorem list_all_not_eq_of_true {α : Type} [BEq α] [LawfulBEq α] (xs : List α)
    (a : α) (p : α → Bool) (hp : ∀ c, p c = true → c ≠ a)
    (hall : xs.all p = true) : a ∉ xs := by
  intro hm
  have hpa := List.all_eq_true.mp hall a hm
  exact hp a hpa rfl

private theorem isValidOptLocal_long_props {opt : OptSpec} (h : Model.isValidOptLocal opt = true)
    {l : String} (hl : opt.long = some l) :
    l.toList ≠ [] ∧ l ≠ "help" ∧ l ≠ "version" ∧ '=' ∉ l.toList ∧
      (∀ cs, l.toList ≠ '-' :: cs) ∧
      (opt.kind = .bool → Model.startsWithNoDash l = false) := by
  unfold Model.isValidOptLocal at h
  rw [hl] at h
  simp only [Bool.and_eq_true] at h
  have hln : Model.isValidLongName l = true := h.1.1.1.1.1.1.2.1
  have hnb : (if (opt.kind == .bool) = true then !Model.startsWithNoDash l else true) = true :=
    h.1.1.1.1.1.1.2.2
  unfold Model.isValidLongName at hln
  split at hln
  · cases hln
  · cases hln
  · rename_i hne1 hne2
    simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at hln
    have hall : l.toList.all (fun x => !Model.isForbiddenIdentChar x) = true := hln.1.1
    have hneq : '=' ∉ l.toList := list_all_not_eq_of_true l.toList '=' _
      (fun x hx heq => by subst heq; simp [Model.isForbiddenIdentChar] at hx) hall
    refine ⟨hne1, hln.1.2, hln.2, hneq, hne2, ?_⟩
    intro hk
    rw [hk] at hnb
    have hvb : (ValueKind.bool == ValueKind.bool) = true := rfl
    rw [hvb] at hnb
    simp only [↓reduceIte, Bool.not_eq_true'] at hnb
    exact hnb

private theorem isValidOptLocal_short_ne_dash {opt : OptSpec} (h : Model.isValidOptLocal opt = true)
    {c : Char} (hs : opt.short = some c) : c ≠ '-' := by
  unfold Model.isValidOptLocal at h
  rw [hs] at h
  simp only [Bool.and_eq_true] at h
  have hsc : Model.isValidShortChar c = true := h.1.1.1.1.1.2
  unfold Model.isValidShortChar at hsc
  simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at hsc
  exact hsc.1.1.1.1

private theorem isValidCommandName_props {name : String} (h : Model.isValidCommandName name = true) :
    name.toList ≠ [] ∧ ∀ cs, name.toList ≠ '-' :: cs := by
  unfold Model.isValidCommandName at h
  cases htl : name.toList with
  | nil => rw [htl] at h; cases h
  | cons c cs =>
    constructor
    · simp
    · intro ds hcon
      have : c = '-' := (List.cons.inj hcon).1
      subst this
      rw [htl] at h
      cases h

private theorem string_ofList_ne_special_startsWithLong {l : String} (hne : l.toList ≠ [])
    (hnhelp : l ≠ "help") (hnver : l ≠ "version") :
    ("--" ++ l) ≠ "--" ∧ ("--" ++ l) ≠ "--help" ∧ ("--" ++ l) ≠ "--version" ∧
    ("--" ++ l).toList = '-' :: '-' :: l.toList := by
  have hlist : ("--" ++ l).toList = '-' :: '-' :: l.toList := by
    rw [String.toList_append]; rfl
  refine ⟨?_, ?_, ?_, hlist⟩
  · intro heq
    have := congrArg String.toList heq
    have h2 : ("--").toList = ['-', '-'] := rfl
    rw [hlist, h2] at this
    exact hne (List.cons.inj (List.cons.inj this).2).2
  · intro heq
    have := congrArg String.toList heq
    have h2 : ("--help").toList = ['-', '-', 'h', 'e', 'l', 'p'] := rfl
    rw [hlist, h2] at this
    have hlt : l.toList = "help".toList := (List.cons.inj (List.cons.inj this).2).2
    exact hnhelp (by simpa [String.ofList_toList] using congrArg String.ofList hlt)
  · intro heq
    have := congrArg String.toList heq
    have h2 : ("--version").toList = ['-', '-', 'v', 'e', 'r', 's', 'i', 'o', 'n'] := rfl
    rw [hlist, h2] at this
    have hlt : l.toList = "version".toList := (List.cons.inj (List.cons.inj this).2).2
    exact hnver (by simpa [String.ofList_toList] using congrArg String.ofList hlt)

private theorem long_eq_val_ne_special {l val : String} (_hno : '=' ∉ l.toList) :
    ("--" ++ l ++ "=" ++ val) ≠ "--" ∧
    ("--" ++ l ++ "=" ++ val) ≠ "--help" ∧
    ("--" ++ l ++ "=" ++ val) ≠ "--version" ∧
    ("--" ++ l ++ "=" ++ val).toList = '-' :: '-' :: (l.toList ++ ('=' :: val.toList)) := by
  have hlist : ("--" ++ l ++ "=" ++ val).toList = '-' :: '-' :: (l.toList ++ ('=' :: val.toList)) := by
    rw [String.toList_append, String.toList_append, String.toList_append]
    have h1 : ("--").toList = ['-', '-'] := rfl
    have h2 : ("=").toList = ['='] := rfl
    rw [h1, h2]
    simp [List.append_assoc]
  have hmem : '=' ∈ ("--" ++ l ++ "=" ++ val).toList := by
    rw [hlist]; simp
  refine ⟨?_, ?_, ?_, hlist⟩
  · intro heq; rw [heq] at hmem; simp at hmem
  · intro heq; rw [heq] at hmem; simp at hmem
  · intro heq; rw [heq] at hmem; simp at hmem

private theorem long_neg_ne_special {l : String} :
    ("--no-" ++ l) ≠ "--" ∧ ("--no-" ++ l) ≠ "--help" ∧ ("--no-" ++ l) ≠ "--version" ∧
    ("--no-" ++ l).toList = '-' :: '-' :: ('n' :: 'o' :: '-' :: l.toList) := by
  have hlist : ("--no-" ++ l).toList = '-' :: '-' :: ('n' :: 'o' :: '-' :: l.toList) := by
    rw [String.toList_append]
    have h1 : ("--no-").toList = ['-', '-', 'n', 'o', '-'] := rfl
    rw [h1]; rfl
  refine ⟨?_, ?_, ?_, hlist⟩
  · intro heq; have := congrArg String.toList heq; rw [hlist] at this; cases this
  · intro heq; have := congrArg String.toList heq; rw [hlist] at this
    have h2 : ("--help").toList = ['-', '-', 'h', 'e', 'l', 'p'] := rfl
    rw [h2] at this; cases this
  · intro heq; have := congrArg String.toList heq; rw [hlist] at this
    have h2 : ("--version").toList = ['-', '-', 'v', 'e', 'r', 's', 'i', 'o', 'n'] := rfl
    rw [h2] at this; cases this

private theorem short_tok_ne_special {c : Char} (hc : c ≠ '-') :
    ("-" ++ String.singleton c) ≠ "--" ∧
    ("-" ++ String.singleton c) ≠ "--help" ∧
    ("-" ++ String.singleton c) ≠ "--version" ∧
    ("-" ++ String.singleton c).toList = ['-', c] := by
  have hlist : ("-" ++ String.singleton c).toList = ['-', c] := by
    rw [String.toList_append, String.toList_singleton]
    have h1 : ("-").toList = ['-'] := rfl
    rw [h1]; rfl
  refine ⟨?_, ?_, ?_, hlist⟩
  · intro heq; have := congrArg String.toList heq; rw [hlist] at this
    have h2 : ("--").toList = ['-', '-'] := rfl
    rw [h2] at this; exact hc (List.cons.inj (List.cons.inj this).2).1
  · intro heq; have := congrArg String.toList heq; rw [hlist] at this
    have h2 : ("--help").toList = ['-', '-', 'h', 'e', 'l', 'p'] := rfl
    rw [h2] at this; exact hc (List.cons.inj (List.cons.inj this).2).1
  · intro heq; have := congrArg String.toList heq; rw [hlist] at this
    have h2 : ("--version").toList = ['-', '-', 'v', 'e', 'r', 's', 'i', 'o', 'n'] := rfl
    rw [h2] at this; exact hc (List.cons.inj (List.cons.inj this).2).1

private theorem resolveSingleOption_pureNoEnv (opt : OptSpec) (cliVals : List OptValue) :
    Model.resolveSingleOption (m := Id) Internal.pureNoEnvOps.getEnv opt cliVals [] =
      if !cliVals.isEmpty then
        if !opt.repeatable && decide (cliVals.length > 1) then
          .error
            { kind := .invalidValue,
              message := s!"option '{opt.name}' cannot be specified multiple times",
              target := some opt.name }
        else .ok (some cliVals)
      else Model.resolveOptDefault opt [] := by
  unfold Model.resolveSingleOption
  by_cases hne : !cliVals.isEmpty
  · simp [hne, pure]
  · simp only [hne, Bool.false_eq_true, ↓reduceIte]
    cases he : opt.envVar with
    | none => simp [pure]
    | some k => simp [pure, Bind.bind, Internal.pureNoEnvOps]

private theorem resolveOptDefault_ok_props (opt : OptSpec) {r : Option (List OptValue)}
    (h : Model.resolveOptDefault opt [] = .ok r) :
    match r with
    | none => True
    | some vals => vals ≠ [] ∧ vals.length = 1 ∧ ∀ v ∈ vals, OptValueMatchesKind opt.kind v := by
  unfold Model.resolveOptDefault at h
  cases hd : opt.default with
  | some d =>
    rw [hd] at h
    dsimp only at h
    rw [parseOptValueWith_nil] at h
    cases hp : Model.parseOptValue opt.kind d with
    | error e => rw [hp] at h; cases h
    | ok v =>
      rw [hp] at h
      injection h with hr
      subst hr
      refine ⟨by simp, by simp, fun v' hv' => ?_⟩
      simp only [List.mem_singleton] at hv'
      subst hv'
      exact parseOptValue_ok_matchesKind hp
  | none =>
    rw [hd] at h
    dsimp only at h
    by_cases hreq : opt.required
    · simp [hreq] at h
    · simp only [hreq, Bool.false_eq_true, ↓reduceIte] at h
      by_cases hbool : (opt.kind == .bool && !opt.repeatable)
      · simp only [hbool, ↓reduceIte, Except.ok.injEq] at h
        subst h
        have hk : opt.kind = .bool := valueKind_eq_of_beq ((Bool.and_eq_true _ _).mp hbool).1
        refine ⟨by simp, by simp, fun v' hv' => ?_⟩
        simp only [List.mem_singleton] at hv'; subst hv'
        rw [hk]; trivial
      · simp only [hbool, Bool.false_eq_true, ↓reduceIte, Except.ok.injEq] at h
        subst h; trivial

private theorem resolveOptions_nil (cliOpts : List (String × List OptValue)) :
    Model.resolveOptions (m := Id) Internal.pureNoEnvOps.getEnv [] cliOpts [] = .ok [] := by
  rfl

private theorem resolveOptions_cons (opt : OptSpec) (rest : List OptSpec)
    (cliOpts : List (String × List OptValue)) :
    Model.resolveOptions (m := Id) Internal.pureNoEnvOps.getEnv (opt :: rest) cliOpts [] =
      (match Model.resolveSingleOption (m := Id) Internal.pureNoEnvOps.getEnv opt (lookupCli cliOpts opt.name) [] with
       | .error e => .error e
       | .ok resolved? =>
         match Model.resolveOptions (m := Id) Internal.pureNoEnvOps.getEnv rest cliOpts [] with
         | .error e => .error e
         | .ok tail =>
           match resolved? with
           | none => .ok tail
           | some vals => .ok ((opt.name, vals) :: tail)) := by
  cases rest <;> rfl

private theorem resolveOptions_mem_keys (visibleOpts : List OptSpec)
    (cliOpts resolved : List (String × List OptValue))
    (h : Model.resolveOptions (m := Id) Internal.pureNoEnvOps.getEnv visibleOpts cliOpts [] = .ok resolved) :
    ∀ p ∈ resolved, ∃ opt ∈ visibleOpts, opt.name = p.1 := by
  induction visibleOpts generalizing resolved with
  | nil =>
    rw [resolveOptions_nil] at h
    injection h with heq
    subst heq
    intro p hp; cases hp
  | cons opt rest ih =>
    rw [resolveOptions_cons] at h
    cases hs : Model.resolveSingleOption (m := Id) Internal.pureNoEnvOps.getEnv opt (lookupCli cliOpts opt.name) [] with
    | error e => rw [hs] at h; cases h
    | ok res? =>
      rw [hs] at h
      cases ht : Model.resolveOptions (m := Id) Internal.pureNoEnvOps.getEnv rest cliOpts [] with
      | error e => rw [ht] at h; cases h
      | ok tail =>
        rw [ht] at h
        cases res? with
        | none =>
          rw [Except.ok.injEq] at h
          subst h
          intro p hp
          rcases ih tail ht p hp with ⟨o, ho, heq⟩
          exact ⟨o, by simp [ho], heq⟩
        | some vals =>
          rw [Except.ok.injEq] at h
          subst h
          intro p hp
          simp only [List.mem_cons] at hp
          rcases hp with rfl | hp
          · exact ⟨opt, by simp, rfl⟩
          · rcases ih tail ht p hp with ⟨o, ho, heq⟩
            exact ⟨o, by simp [ho], heq⟩

private theorem resolveOptions_lookup_not_mem (visibleOpts : List OptSpec)
    (cliOpts resolved : List (String × List OptValue)) (k : String)
    (h : Model.resolveOptions (m := Id) Internal.pureNoEnvOps.getEnv visibleOpts cliOpts [] = .ok resolved)
    (hnot : ∀ opt ∈ visibleOpts, opt.name ≠ k) :
    lookupCli resolved k = [] := by
  have hmem := resolveOptions_mem_keys visibleOpts cliOpts resolved h
  clear h
  induction resolved with
  | nil => rfl
  | cons p ps ih =>
    rcases p with ⟨k', vs⟩
    by_cases hkk : k' == k
    · have heq : k' = k := beq_iff_eq.mp hkk
      subst heq
      rcases hmem (k', vs) (by simp) with ⟨o, ho, hon⟩
      exact absurd hon (hnot o ho)
    · have hkkF : (k' == k) = false := Bool.eq_false_iff.mpr hkk
      simp only [lookupCli, List.find?, hkkF]
      exact ih (fun q hq => hmem q (by simp [hq]))

private theorem lookupCli_cons_same (rest : List (String × List OptValue)) (k : String) (v : List OptValue) :
    lookupCli ((k, v) :: rest) k = v := by
  simp [lookupCli, List.find?]

private theorem list_optValue_beq_single_false {xs : List OptValue}
    (h : (xs == [.bool false]) = true) : xs = [.bool false] := by
  cases xs with
  | nil => cases h
  | cons x xs =>
    cases xs with
    | cons y ys =>
      cases (x == .bool false) <;> simp [BEq.beq, List.beq] at h
    | nil =>
      simp only [BEq.beq, List.beq] at h
      cases hx : (x == .bool false)
      · have hx' : instBEqOptValue.beq x (.bool false) = false := hx
        rw [hx'] at h; cases h
      · cases x with
        | bool b => cases b <;> first | rfl | cases hx
        | string _ | nat _ | int _ | choice _ | custom _ => cases hx

private theorem resolveOptions_lookup_aux (opts : List OptSpec)
    (cliOpts resolved : List (String × List OptValue))
    (hnd : (opts.map (·.name)).Nodup)
    (hcli : ∀ opt ∈ opts, ∀ v ∈ lookupCli cliOpts opt.name,
      OptValueMatchesKind opt.kind v ∧
      (opt.kind == .bool && opt.repeatable → v = .bool true) ∧
      (opt.kind == .bool && opt.long.isNone → v = .bool true))
    (h : Model.resolveOptions (m := Id) Internal.pureNoEnvOps.getEnv opts cliOpts [] = .ok resolved) :
    ∀ opt ∈ opts,
      let vals := lookupCli resolved opt.name
      (∀ v ∈ vals, OptValueMatchesKind opt.kind v) ∧
      (opt.repeatable = false → vals.length ≤ 1) ∧
      (vals = [] → lookupCli cliOpts opt.name = []) ∧
      ((opt.kind == .bool && !opt.repeatable && opt.long.isNone && (vals == [.bool false])) = true →
        lookupCli cliOpts opt.name = []) ∧
      (vals ≠ [] →
        Model.resolveSingleOption (m := Id) Internal.pureNoEnvOps.getEnv opt (lookupCli cliOpts opt.name) [] =
          .ok (some vals)) := by
  induction opts generalizing resolved with
  | nil => intro opt ho; cases ho
  | cons o rest ih =>
    simp only [List.map_cons, List.nodup_cons, List.mem_map] at hnd
    have hnotRest : ∀ o' ∈ rest, o'.name ≠ o.name := fun o' ho' heq => hnd.1 ⟨o', ho', heq⟩
    rw [resolveOptions_cons] at h
    cases hs : Model.resolveSingleOption (m := Id) Internal.pureNoEnvOps.getEnv o (lookupCli cliOpts o.name) [] with
    | error e => rw [hs] at h; cases h
    | ok res? =>
      rw [hs] at h
      cases ht : Model.resolveOptions (m := Id) Internal.pureNoEnvOps.getEnv rest cliOpts [] with
      | error e => rw [ht] at h; cases h
      | ok tail =>
        rw [ht] at h
        have hih := ih tail hnd.2 (fun o' ho' => hcli o' (by simp [ho'])) ht
        have hs' := hs
        rw [resolveSingleOption_pureNoEnv] at hs'
        intro opt ho
        simp only [List.mem_cons] at ho
        rcases ho with rfl | hmem
        · have hc := hcli opt (by simp)
          by_cases hne : !(lookupCli cliOpts opt.name).isEmpty
          · simp only [hne, ↓reduceIte] at hs'
            by_cases hlen : (!opt.repeatable && decide ((lookupCli cliOpts opt.name).length > 1))
            · simp [hlen] at hs'
            · simp only [hlen, Bool.false_eq_true, ↓reduceIte] at hs'
              injection hs' with hrs
              subst hrs
              rw [Except.ok.injEq] at h
              subst h
              rw [lookupCli_cons_same]
              refine ⟨fun v hv => (hc v hv).1, ?_, ?_, ?_, fun _ => hs⟩
              · intro hnr
                simp only [hnr, Bool.not_false, Bool.true_and, decide_eq_true_eq, Nat.not_lt] at hlen
                exact hlen
              · intro hnil
                rw [hnil] at hne; cases hne
              · intro hcond
                simp only [Bool.and_eq_true] at hcond
                rcases hcond with ⟨⟨⟨hkb, _⟩, hln⟩, heqv⟩
                have heqv' : lookupCli cliOpts opt.name = [.bool false] := list_optValue_beq_single_false heqv
                have hfb : OptValue.bool false ∈ lookupCli cliOpts opt.name := by rw [heqv']; simp
                have hbt := (hc (.bool false) hfb).2.2 (by simp [hkb, hln])
                cases hbt
          · have hneF : (!(lookupCli cliOpts opt.name).isEmpty) = false := Bool.eq_false_iff.mpr hne
            simp only [hneF, Bool.false_eq_true, ↓reduceIte] at hs'
            have hcliNil : lookupCli cliOpts opt.name = [] := by
              cases hcl : lookupCli cliOpts opt.name
              · rfl
              · simp [hcl] at hne
            have hdef := resolveOptDefault_ok_props opt hs'
            cases res? with
            | none =>
              rw [Except.ok.injEq] at h; subst h
              have hvalsNil : lookupCli tail opt.name = [] :=
                resolveOptions_lookup_not_mem rest cliOpts tail opt.name ht hnotRest
              rw [hvalsNil]
              refine ⟨(fun _ h => by cases h), (fun _ => by simp),
                (fun _ => hcliNil), (fun _ => hcliNil), (fun hne' => absurd rfl hne')⟩
            | some vs =>
              rw [Except.ok.injEq] at h; subst h
              rw [lookupCli_cons_same]
              rcases hdef with ⟨hvne, hvlen, hvkind⟩
              refine ⟨hvkind, fun _ => Nat.le_of_eq hvlen, fun hnil => absurd hnil hvne,
                fun _ => hcliNil, fun _ => hs⟩
        · have hne : opt.name ≠ o.name := hnotRest opt hmem
          have htail : lookupCli resolved opt.name = lookupCli tail opt.name := by
            cases res? with
            | none => rw [Except.ok.injEq] at h; subst h; rfl
            | some vs =>
              rw [Except.ok.injEq] at h; subst h
              unfold lookupCli
              have hbeq : (o.name == opt.name) = false := beq_false_of_ne hne.symm
              simp [hbeq]
          rw [htail]
          exact hih opt hmem

private theorem resolveOptions_lookup (visibleOpts : List OptSpec)
    (cliOpts resolved : List (String × List OptValue))
    (hnd : (visibleOpts.map (·.name)).Nodup)
    (hcli : CliOptsInv visibleOpts cliOpts)
    (h : Model.resolveOptions (m := Id) Internal.pureNoEnvOps.getEnv visibleOpts cliOpts [] = .ok resolved) :
    ∀ opt ∈ visibleOpts,
      let vals := lookupCli resolved opt.name
      (∀ v ∈ vals, OptValueMatchesKind opt.kind v) ∧
      (opt.repeatable = false → vals.length ≤ 1) ∧
      (vals = [] → lookupCli cliOpts opt.name = []) ∧
      ((opt.kind == .bool && !opt.repeatable && opt.long.isNone && (vals == [.bool false])) = true →
        lookupCli cliOpts opt.name = []) ∧
      (vals ≠ [] →
        Model.resolveSingleOption (m := Id) Internal.pureNoEnvOps.getEnv opt (lookupCli cliOpts opt.name) [] =
          .ok (some vals)) :=
  resolveOptions_lookup_aux visibleOpts cliOpts resolved hnd hcli.2 h

private theorem resolveOptions_congr (opts : List OptSpec)
    (cli1 cli2 : List (String × List OptValue))
    (h : ∀ opt ∈ opts,
      Model.resolveSingleOption (m := Id) Internal.pureNoEnvOps.getEnv opt (lookupCli cli1 opt.name) [] =
      Model.resolveSingleOption (m := Id) Internal.pureNoEnvOps.getEnv opt (lookupCli cli2 opt.name) []) :
    Model.resolveOptions (m := Id) Internal.pureNoEnvOps.getEnv opts cli1 [] =
    Model.resolveOptions (m := Id) Internal.pureNoEnvOps.getEnv opts cli2 [] := by
  induction opts with
  | nil => rfl
  | cons o rest ih =>
    rw [resolveOptions_cons, resolveOptions_cons]
    rw [h o (by simp)]
    rw [ih (fun o' ho' => h o' (by simp [ho']))]

private theorem parseTokens_append (rootName : String) (validators : CustomValidators)
    (toks1 toks2 : List String) (st st1 : Internal.ParseState)
    (h1 : Internal.parseTokens rootName validators st toks1 = .ok st1) :
    Internal.parseTokens rootName validators st (toks1 ++ toks2) =
    Internal.parseTokens rootName validators st1 toks2 := by
  induction toks1 generalizing st with
  | nil =>
    unfold Internal.parseTokens at h1
    cases hp : st.pendingOpt with
    | some _ => simp [hp] at h1
    | none =>
      simp only [hp, Except.ok.injEq] at h1
      subst h1
      rfl
  | cons tok rest ih =>
    simp only [List.cons_append]
    unfold Internal.parseTokens at h1
    conv => lhs; unfold Internal.parseTokens
    cases hp : st.pendingOpt with
    | some opt =>
      simp only [hp] at h1 ⊢
      cases hpv : Model.parseOptValueWith opt.kind tok validators with
      | error e => simp [hpv, Bind.bind, Except.bind] at h1
      | ok v =>
        simp only [hpv, Bind.bind, Except.bind] at h1 ⊢
        exact ih _ h1
    | none =>
      simp only [hp] at h1 ⊢
      by_cases had : st.afterDashDash
      · simp only [had, ↓reduceIte] at h1 ⊢
        exact ih _ h1
      · simp only [had, Bool.false_eq_true, ↓reduceIte] at h1 ⊢
        by_cases hdd : tok == "--"
        · simp only [hdd, ↓reduceIte] at h1 ⊢
          exact ih _ h1
        · simp only [hdd, Bool.false_eq_true, ↓reduceIte] at h1 ⊢
          by_cases hhelp : tok == "--help"
          · simp [hhelp] at h1
          · simp only [hhelp, Bool.false_eq_true, ↓reduceIte] at h1 ⊢
            by_cases hver : (tok == "--version" && st.effectiveVersion.isSome)
            · simp only [hver, ↓reduceIte] at h1
              cases hev : st.effectiveVersion <;> simp [hev] at h1
            · simp only [hver, Bool.false_eq_true, ↓reduceIte] at h1 ⊢
              split
              · rename_i longRest heqm
                split at h1
                · rename_i longRest1 heqm1
                  rw [heqm] at heqm1
                  have hlr : longRest = longRest1 := (List.cons.inj (List.cons.inj heqm1).2).2
                  subst hlr
                  by_cases hempty : (Internal.splitFirstEq (String.ofList longRest)).fst.isEmpty
                  · simp [hempty] at h1
                  · simp only [hempty, Bool.false_eq_true, ↓reduceIte] at h1 ⊢
                    by_cases hhv : ((Internal.splitFirstEq (String.ofList longRest)).fst == "help" ||
                        (Internal.splitFirstEq (String.ofList longRest)).fst == "version" && st.effectiveVersion.isSome)
                    · simp [hhv] at h1
                    · simp only [hhv, Bool.false_eq_true, ↓reduceIte] at h1 ⊢
                      cases hlkp : Internal.lookupLongOpt (st.inheritedGlobals ++ st.curSpec.options)
                          (Internal.splitFirstEq (String.ofList longRest)).fst with
                      | none => simp [hlkp] at h1
                      | some p =>
                        rcases p with ⟨opt, isNeg⟩
                        simp only [hlkp] at h1 ⊢
                        by_cases hin : isNeg
                        · simp only [hin, ↓reduceIte] at h1 ⊢
                          cases heqv : (Internal.splitFirstEq (String.ofList longRest)).snd with
                          | some val => rw [heqv] at h1; cases h1
                          | none => rw [heqv] at h1; exact ih _ h1
                        · simp only [hin, Bool.false_eq_true, ↓reduceIte] at h1 ⊢
                          by_cases hbool : opt.kind == .bool
                          · simp only [hbool, ↓reduceIte] at h1 ⊢
                            cases heqv : (Internal.splitFirstEq (String.ofList longRest)).snd with
                            | none => rw [heqv] at h1; exact ih _ h1
                            | some rawVal =>
                              rw [heqv] at h1
                              dsimp only at h1 ⊢
                              cases hpv : Model.parseOptValue .bool rawVal with
                              | error e => rw [hpv] at h1; cases h1
                              | ok ov =>
                                cases ov with
                                | bool b =>
                                  rw [hpv] at h1
                                  dsimp only at h1 ⊢
                                  by_cases hrep : opt.repeatable && !b
                                  · simp [hrep] at h1
                                  · simp only [hrep, Bool.false_eq_true, ↓reduceIte] at h1 ⊢
                                    exact ih _ h1
                                | _ => rw [hpv] at h1; cases h1
                          · simp only [hbool, Bool.false_eq_true, ↓reduceIte] at h1 ⊢
                            cases heqv : (Internal.splitFirstEq (String.ofList longRest)).snd with
                            | some rawVal =>
                              rw [heqv] at h1
                              dsimp only at h1 ⊢
                              cases hpv : Model.parseOptValueWith opt.kind rawVal validators with
                              | error e => rw [hpv] at h1; cases h1
                              | ok v =>
                                rw [hpv] at h1
                                dsimp only at h1 ⊢
                                simp only [Bind.bind, Except.bind] at h1 ⊢
                                exact ih _ h1
                            | none => rw [heqv] at h1; exact ih _ h1
                · rename_i c1 sr1 hn1 heqm1
                  rw [heqm] at heqm1
                  injection heqm1 with _ h2; injection h2 with hc1 _; subst hc1
                  exact False.elim (hn1 rfl)
                · rename_i _ hn1 _; exact False.elim (hn1 _ heqm)
              · rename_i c shortRest hn1 heqm
                split at h1
                · rename_i longRest1 heqm1
                  rw [heqm] at heqm1
                  injection heqm1 with _ h2; injection h2 with hc1 _; subst hc1
                  exact False.elim (hn1 rfl)
                · rename_i c1 shortRest1 _ heqm1
                  rw [heqm] at heqm1
                  have hc : c = c1 := (List.cons.inj (List.cons.inj heqm1).2).1
                  have hsr : shortRest = shortRest1 := (List.cons.inj (List.cons.inj heqm1).2).2
                  subst hc hsr
                  cases hsb : Internal.parseShortBundle (st.inheritedGlobals ++ st.curSpec.options)
                      st.curSpec.shortHelp st.curSpec.shortVersion rootName st.subPath
                      st.effectiveVersion st.curSpec validators st.cliOpts (c :: shortRest) with
                  | error e => rw [hsb] at h1; cases h1
                  | ok p =>
                    rw [hsb] at h1
                    simp only [Bind.bind, Except.bind] at h1 ⊢
                    exact ih _ h1
                · rename_i _ _ hn2; exact False.elim (hn2 _ _ heqm)
              · rename_i _ hn1 hn2
                split at h1
                · rename_i lr heqm1; exact False.elim (hn1 _ heqm1)
                · rename_i c sr _ heqm1; exact False.elim (hn2 _ _ heqm1)
                · by_cases hsub : (!st.curSpec.subcommands.isEmpty && st.rawPositionals.isEmpty)
                  · simp only [hsub, ↓reduceIte] at h1 ⊢
                    cases hfs : st.curSpec.subcommands.find? (fun s => s.name == tok) with
                    | none => simp [hfs] at h1
                    | some sub => simp only [hfs] at h1 ⊢; exact ih _ h1
                  · simp only [hsub, Bool.false_eq_true, ↓reduceIte] at h1 ⊢
                    exact ih _ h1

private theorem parseTokens_subPath_aux (rootName : String) (path : List String)
    (globals : List OptSpec) (effVer : Option String) (targetSpec : CommandSpec) :
    ∀ g0 v0 cur sp,
      NodeInv cur g0 v0 →
      Model.findSubcommandPath.go g0 v0 cur path = .ok (globals, effVer, targetSpec) →
      Internal.parseTokens rootName []
        { curSpec := cur, subPath := sp, inheritedGlobals := g0, effectiveVersion := cur.version <|> v0 }
        path =
        .ok { curSpec := targetSpec, subPath := sp ++ path, inheritedGlobals := globals, effectiveVersion := effVer } := by
  induction path with
  | nil =>
    intro g0 v0 cur sp _ hgo
    unfold Model.findSubcommandPath.go at hgo
    injection hgo with hp
    injection hp with hg ht
    injection ht with hv hc
    subst hg hv hc
    simp [Internal.parseTokens]
  | cons p ps ih =>
    intro g0 v0 cur sp hnode hgo
    unfold Model.findSubcommandPath.go at hgo
    cases hfs : cur.subcommands.find? (fun s => s.name == p) with
    | none => simp [hfs] at hgo
    | some next =>
      simp only [hfs] at hgo
      have hmem : next ∈ cur.subcommands := List.mem_of_find?_eq_some hfs
      have hsubNode := nodeInv_sub hnode hmem
      have hsubProps := nodeInv_props hsubNode
      have hbeq : (next.name == p) = true := List.find?_some (p := fun (s : CommandSpec) => s.name == p) hfs
      have hnameEq : next.name = p := beq_iff_eq.mp hbeq
      have ⟨hne, hnodash⟩ := isValidCommandName_props hsubProps.1
      rw [hnameEq] at hne hnodash
      have hne_dd : (p == "--") = false := beq_false_of_ne (fun heq => by
        have h1 : ("--").toList = ['-', '-'] := rfl
        have := congrArg String.toList heq
        rw [h1] at this
        exact hnodash ['-'] this)
      have hne_help : (p == "--help") = false := beq_false_of_ne (fun heq => by
        have h1 : ("--help").toList = ['-', '-', 'h', 'e', 'l', 'p'] := rfl
        have := congrArg String.toList heq
        rw [h1] at this
        exact hnodash ['-', 'h', 'e', 'l', 'p'] this)
      have hne_ver : (p == "--version") = false := beq_false_of_ne (fun heq => by
        have h1 : ("--version").toList = ['-', '-', 'v', 'e', 'r', 's', 'i', 'o', 'n'] := rfl
        have := congrArg String.toList heq
        rw [h1] at this
        exact hnodash ['-', 'v', 'e', 'r', 's', 'i', 'o', 'n'] this)
      have hnotEmpty : cur.subcommands.isEmpty = false := by
        cases hc : cur.subcommands with
        | nil => rw [hc] at hmem; cases hmem
        | cons _ _ => rfl
      unfold Internal.parseTokens
      simp only [hne_dd, hne_help, hne_ver, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
      cases htl : p.toList with
      | nil => exact absurd htl hne
      | cons c1 cs1 =>
        have hc1n : c1 ≠ '-' := fun heq => by subst heq; exact hnodash cs1 htl
        split
        · rename_i longRest heqm
          exact absurd (List.cons.inj heqm).1 hc1n
        · rename_i c shortRest _ heqm
          exact absurd (List.cons.inj heqm).1 hc1n
        · simp only [hnotEmpty, Bool.not_false, List.isEmpty_nil, Bool.and_self, ↓reduceIte, hfs, hnameEq]
          have hrec := ih (g0 ++ cur.options) (cur.version <|> v0) next (sp ++ [p]) hsubNode hgo
          simpa [List.append_assoc] using hrec

private theorem parseTokens_subPath (rootSpec : CommandSpec) (path : List String)
    {globals : List OptSpec} {effVer : Option String} {targetSpec : CommandSpec}
    (hvalid : Model.isValidSpec rootSpec = true)
    (hpath : Model.findSubcommandPath rootSpec path = .ok (globals, effVer, targetSpec)) :
    Internal.parseTokens rootSpec.name []
      { curSpec := rootSpec, effectiveVersion := rootSpec.version } path =
      .ok { curSpec := targetSpec, subPath := path, inheritedGlobals := globals, effectiveVersion := effVer } := by
  have hnodeRoot : NodeInv rootSpec [] none := by
    refine ⟨?_, rfl⟩
    simpa [Model.isValidSpec] using hvalid
  have hver : rootSpec.version = (rootSpec.version <|> none) := by
    cases rootSpec.version <;> rfl
  have hgo : Model.findSubcommandPath.go [] none rootSpec path = .ok (globals, effVer, targetSpec) := hpath
  have hres := parseTokens_subPath_aux rootSpec.name path globals effVer targetSpec [] none rootSpec [] hnodeRoot hgo
  rw [hver]
  exact hres

private theorem parseTokens_step_longBool (rootName : String) (st : Internal.ParseState)
    (opt : OptSpec) (l : String) (b : Bool)
    (hndLongs : (Model.collectVisibleLongs (st.inheritedGlobals ++ st.curSpec.options)).Nodup)
    (hloc : Model.isValidOptLocal opt = true)
    (ho : opt ∈ st.inheritedGlobals ++ st.curSpec.options)
    (hl : opt.long = some l) (hk : opt.kind = .bool)
    (hnr : b = false → opt.repeatable = false)
    (hp : st.pendingOpt = none) (had : st.afterDashDash = false) :
    Internal.parseTokens rootName [] st [if b then "--" ++ l else "--no-" ++ l] =
      .ok { st with cliOpts := Internal.recordCliOpt st.cliOpts opt.name (.bool b) } := by
  have ⟨hlne, hlhelp, hlver, hleq, _, hlnd⟩ := isValidOptLocal_long_props hloc hl
  have hvisible : st.inheritedGlobals ++ st.curSpec.options = st.inheritedGlobals ++ st.curSpec.options := rfl
  cases b with
  | true =>
    have ⟨hne_dd, hne_help, hne_ver, hlist⟩ := string_ofList_ne_special_startsWithLong hlne hlhelp hlver
    have hlkp := lookupLongOpt_pos (st.inheritedGlobals ++ st.curSpec.options) hndLongs ho hl
    have hsf : Internal.splitFirstEq (String.ofList l.toList) = (l, none) := by
      rw [String.ofList_toList]
      exact splitFirstEq_none l hleq
    have hnie : l.isEmpty = false := by cases h : l.toList <;> simp_all [String.isEmpty]
    have hnhv : ((l == "help") || (l == "version" && st.effectiveVersion.isSome)) = false := by
      simp [beq_false_of_ne hlhelp, beq_false_of_ne hlver]
    unfold Internal.parseTokens
    simp only [hp, had, beq_false_of_ne hne_dd, beq_false_of_ne hne_help, beq_false_of_ne hne_ver,
      Bool.false_and, Bool.false_eq_true, ↓reduceIte]
    split
    · rename_i longRest heq
      rw [hlist] at heq
      have hlr : l.toList = longRest := (List.cons.inj (List.cons.inj heq).2).2
      rw [← hlr, hsf]
      have hvb : (ValueKind.bool == ValueKind.bool) = true := rfl
      simp only [hnie, hnhv, Bool.false_eq_true, ↓reduceIte, hlkp, hk, hvb]
      simp [Internal.parseTokens]
    · rename_i _ _ h1 heq
      rw [hlist] at heq; injection heq with _ h2; injection h2 with hc _; subst hc
      exact False.elim (h1 rfl)
    · rename_i _ h1 _; exact False.elim (h1 _ hlist)
  | false =>
    have hnr' := hnr rfl
    have ⟨hne_dd, hne_help, hne_ver, hlist⟩ := long_neg_ne_special (l := l)
    have hlkp := lookupLongOpt_neg (st.inheritedGlobals ++ st.curSpec.options) hndLongs ho hk hnr' hl
    have hno_eq : '=' ∉ ("no-" ++ l).toList := by
      rw [String.toList_append]
      have hpre : ("no-").toList = ['n', 'o', '-'] := rfl
      rw [hpre]; simp [hleq]
    have hsf : Internal.splitFirstEq (String.ofList ('n' :: 'o' :: '-' :: l.toList)) = ("no-" ++ l, none) := by
      have hpre : String.ofList ('n' :: 'o' :: '-' :: l.toList) = "no-" ++ l := by
        have h1 : ('n' :: 'o' :: '-' :: l.toList) = ("no-" ++ l).toList := by
          rw [String.toList_append]; rfl
        rw [h1, String.ofList_toList]
      rw [hpre]
      exact splitFirstEq_none ("no-" ++ l) hno_eq
    have hnie : ("no-" ++ l).isEmpty = false := by
      simp [String.isEmpty]
    have hnhv : (("no-" ++ l == "help") || ("no-" ++ l == "version" && st.effectiveVersion.isSome)) = false := by
      have hn1 : "no-" ++ l ≠ "help" := fun heq => by
        have := congrArg String.toList heq; simp [String.toList_append] at this
      have hn2 : "no-" ++ l ≠ "version" := fun heq => by
        have := congrArg String.toList heq; simp [String.toList_append] at this
      simp [beq_false_of_ne hn1, beq_false_of_ne hn2]
    unfold Internal.parseTokens
    simp only [hp, had, beq_false_of_ne hne_dd, beq_false_of_ne hne_help, beq_false_of_ne hne_ver,
      Bool.false_and, Bool.false_eq_true, ↓reduceIte]
    split
    · rename_i longRest heq
      rw [hlist] at heq
      have hlr : 'n' :: 'o' :: '-' :: l.toList = longRest := (List.cons.inj (List.cons.inj heq).2).2
      rw [← hlr, hsf]
      simp only [hnie, hnhv, Bool.false_eq_true, ↓reduceIte, hlkp]
      simp [Internal.parseTokens]
    · rename_i _ _ h1 heq
      rw [hlist] at heq; injection heq with _ h2; injection h2 with hc _; subst hc
      exact False.elim (h1 rfl)
    · rename_i _ h1 _; exact False.elim (h1 _ hlist)

private theorem parseTokens_step_longVal (rootName : String) (st : Internal.ParseState)
    (opt : OptSpec) (l : String) (v : OptValue)
    (hndLongs : (Model.collectVisibleLongs (st.inheritedGlobals ++ st.curSpec.options)).Nodup)
    (hloc : Model.isValidOptLocal opt = true)
    (ho : opt ∈ st.inheritedGlobals ++ st.curSpec.options)
    (hl : opt.long = some l) (hnbool : opt.kind ≠ .bool)
    (hmatch : OptValueMatchesKind opt.kind v)
    (hp : st.pendingOpt = none) (had : st.afterDashDash = false) :
    Internal.parseTokens rootName [] st ["--" ++ l ++ "=" ++ Model.optValueToString v] =
      .ok { st with cliOpts := Internal.recordCliOpt st.cliOpts opt.name v } := by
  have ⟨hlne, hlhelp, hlver, hleq, _, _⟩ := isValidOptLocal_long_props hloc hl
  have ⟨hne_dd, hne_help, hne_ver, hlist⟩ := long_eq_val_ne_special (val := Model.optValueToString v) hleq
  have hlkp := lookupLongOpt_pos (st.inheritedGlobals ++ st.curSpec.options) hndLongs ho hl
  have hsf : Internal.splitFirstEq (String.ofList (l.toList ++ ('=' :: (Model.optValueToString v).toList))) =
      (l, some (Model.optValueToString v)) := by
    have heql : String.ofList (l.toList ++ ('=' :: (Model.optValueToString v).toList)) =
        l ++ "=" ++ Model.optValueToString v := by
      have h1 : (l ++ "=" ++ Model.optValueToString v).toList =
          l.toList ++ ('=' :: (Model.optValueToString v).toList) := by
        simp [String.toList_append]
      rw [← h1, String.ofList_toList]
    rw [heql]
    exact splitFirstEq_append l (Model.optValueToString v) hleq
  have hnie : l.isEmpty = false := by
    simp [String.isEmpty]
    exact fun hc => by subst hc; exact hlne rfl
  have hnhv : ((l == "help") || (l == "version" && st.effectiveVersion.isSome)) = false := by
    simp [beq_false_of_ne hlhelp, beq_false_of_ne hlver]
  have hnb : (opt.kind == .bool) = false := valueKind_beq_false_of_ne hnbool
  have hpv : Model.parseOptValue opt.kind (Model.optValueToString v) = .ok v :=
    parseOptValue_optValueToString hmatch
  unfold Internal.parseTokens
  simp only [hp, had, beq_false_of_ne hne_dd, beq_false_of_ne hne_help, beq_false_of_ne hne_ver,
    Bool.false_and, Bool.false_eq_true, ↓reduceIte]
  split
  · rename_i longRest heq
    rw [hlist] at heq
    have hlr : l.toList ++ ('=' :: (Model.optValueToString v).toList) = longRest :=
      (List.cons.inj (List.cons.inj heq).2).2
    rw [← hlr, hsf]
    simp only [hnie, hnhv, Bool.false_eq_true, ↓reduceIte, hlkp, hnb, parseOptValueWith_nil, hpv,
      Bind.bind, Except.bind]
    simp [Internal.parseTokens]
  · rename_i _ _ h1 heq
    rw [hlist] at heq; injection heq with _ h2; injection h2 with hc _; subst hc
    exact False.elim (h1 rfl)
  · rename_i _ h1 _; exact False.elim (h1 _ hlist)

private theorem parseTokens_step_shortTwo (rootName : String) (st : Internal.ParseState)
    (opt : OptSpec) (c : Char) (v : OptValue)
    (hndShorts : ((st.inheritedGlobals ++ st.curSpec.options).filterMap (·.short)).Nodup)
    (hh : st.curSpec.shortHelp = true → 'h' ∉ (st.inheritedGlobals ++ st.curSpec.options).filterMap (·.short))
    (hV : (st.curSpec.shortVersion && st.effectiveVersion.isSome) = true →
      'V' ∉ (st.inheritedGlobals ++ st.curSpec.options).filterMap (·.short))
    (hloc : Model.isValidOptLocal opt = true)
    (ho : opt ∈ st.inheritedGlobals ++ st.curSpec.options)
    (hs : opt.short = some c) (hnbool : opt.kind ≠ .bool)
    (hmatch : OptValueMatchesKind opt.kind v)
    (hp : st.pendingOpt = none) (had : st.afterDashDash = false) :
    Internal.parseTokens rootName [] st ["-" ++ String.singleton c, Model.optValueToString v] =
      .ok { st with cliOpts := Internal.recordCliOpt st.cliOpts opt.name v } := by
  have hc_ne := isValidOptLocal_short_ne_dash hloc hs
  have ⟨hne_dd, hne_help, hne_ver, hlist⟩ := short_tok_ne_special hc_ne
  have hcmem : c ∈ (st.inheritedGlobals ++ st.curSpec.options).filterMap (·.short) :=
    List.mem_filterMap.mpr ⟨opt, ho, hs⟩
  have hnh : (c == 'h' && st.curSpec.shortHelp) = false := by
    cases hsh : st.curSpec.shortHelp
    · simp
    · have hne : c ≠ 'h' := fun heq => by subst heq; exact hh hsh hcmem
      simp [beq_false_of_ne hne]
  have hnV : (c == 'V' && st.curSpec.shortVersion && st.effectiveVersion.isSome) = false := by
    cases hsv : (st.curSpec.shortVersion && st.effectiveVersion.isSome)
    · cases h1 : st.curSpec.shortVersion <;> cases h2 : st.effectiveVersion.isSome <;> simp_all
    · have hne : c ≠ 'V' := fun heq => by subst heq; exact hV hsv hcmem
      simp [beq_false_of_ne hne]
  have hfind : (st.inheritedGlobals ++ st.curSpec.options).find? (fun o => o.short == some c) = some opt :=
    find?_unique_key (·.short) (st.inheritedGlobals ++ st.curSpec.options) hndShorts opt ho c hs
  have hnb : (opt.kind == .bool) = false := valueKind_beq_false_of_ne hnbool
  have hsb : Internal.parseShortBundle (st.inheritedGlobals ++ st.curSpec.options)
      st.curSpec.shortHelp st.curSpec.shortVersion rootName st.subPath st.effectiveVersion
      st.curSpec [] st.cliOpts [c] = .ok (st.cliOpts, some opt) := by
    unfold Internal.parseShortBundle
    simp [hnh, hnV, hfind, hnb]
  have hpv : Model.parseOptValue opt.kind (Model.optValueToString v) = .ok v :=
    parseOptValue_optValueToString hmatch
  unfold Internal.parseTokens
  simp only [hp, had, beq_false_of_ne hne_dd, beq_false_of_ne hne_help, beq_false_of_ne hne_ver,
    Bool.false_and, Bool.false_eq_true, ↓reduceIte]
  rw [hlist]
  split
  · rename_i longRest heq
    exact absurd (List.cons.inj (List.cons.inj heq).2).1 hc_ne
  · rename_i _ c' shortRest' _ heq
    have hc_eq : c = c' := (List.cons.inj (List.cons.inj heq).2).1
    have hsr_eq : [] = shortRest' := (List.cons.inj (List.cons.inj heq).2).2
    rw [← hc_eq, ← hsr_eq, hsb]
    simp only [Bind.bind, Except.bind]
    unfold Internal.parseTokens
    simp only [parseOptValueWith_nil, hpv, Bind.bind, Except.bind]
    simp [Internal.parseTokens]
  · rename_i _ _ h2
    exact absurd rfl (h2 c [])

private theorem parseTokens_step_shortBool (rootName : String) (st : Internal.ParseState)
    (opt : OptSpec) (c : Char)
    (hndShorts : ((st.inheritedGlobals ++ st.curSpec.options).filterMap (·.short)).Nodup)
    (hh : st.curSpec.shortHelp = true → 'h' ∉ (st.inheritedGlobals ++ st.curSpec.options).filterMap (·.short))
    (hV : (st.curSpec.shortVersion && st.effectiveVersion.isSome) = true →
      'V' ∉ (st.inheritedGlobals ++ st.curSpec.options).filterMap (·.short))
    (hloc : Model.isValidOptLocal opt = true)
    (ho : opt ∈ st.inheritedGlobals ++ st.curSpec.options)
    (hs : opt.short = some c) (hk : opt.kind = .bool)
    (hp : st.pendingOpt = none) (had : st.afterDashDash = false) :
    Internal.parseTokens rootName [] st ["-" ++ String.singleton c] =
      .ok { st with cliOpts := Internal.recordCliOpt st.cliOpts opt.name (.bool true) } := by
  have hc_ne := isValidOptLocal_short_ne_dash hloc hs
  have ⟨hne_dd, hne_help, hne_ver, hlist⟩ := short_tok_ne_special hc_ne
  have hcmem : c ∈ (st.inheritedGlobals ++ st.curSpec.options).filterMap (·.short) :=
    List.mem_filterMap.mpr ⟨opt, ho, hs⟩
  have hnh : (c == 'h' && st.curSpec.shortHelp) = false := by
    cases hsh : st.curSpec.shortHelp
    · simp
    · have hne : c ≠ 'h' := fun heq => by subst heq; exact hh hsh hcmem
      simp [beq_false_of_ne hne]
  have hnV : (c == 'V' && st.curSpec.shortVersion && st.effectiveVersion.isSome) = false := by
    cases hsv : (st.curSpec.shortVersion && st.effectiveVersion.isSome)
    · cases h1 : st.curSpec.shortVersion <;> cases h2 : st.effectiveVersion.isSome <;> simp_all
    · have hne : c ≠ 'V' := fun heq => by subst heq; exact hV hsv hcmem
      simp [beq_false_of_ne hne]
  have hfind : (st.inheritedGlobals ++ st.curSpec.options).find? (fun o => o.short == some c) = some opt :=
    find?_unique_key (·.short) (st.inheritedGlobals ++ st.curSpec.options) hndShorts opt ho c hs
  have hsb : Internal.parseShortBundle (st.inheritedGlobals ++ st.curSpec.options)
      st.curSpec.shortHelp st.curSpec.shortVersion rootName st.subPath st.effectiveVersion
      st.curSpec [] st.cliOpts [c] = .ok (Internal.recordCliOpt st.cliOpts opt.name (.bool true), none) := by
    have hvb : (ValueKind.bool == ValueKind.bool) = true := rfl
    unfold Internal.parseShortBundle
    simp only [hnh, hnV, hfind, hk, hvb, Bool.false_eq_true, ↓reduceIte]
    rfl
  unfold Internal.parseTokens
  simp only [hp, had, beq_false_of_ne hne_dd, beq_false_of_ne hne_help, beq_false_of_ne hne_ver,
    Bool.false_and, Bool.false_eq_true, ↓reduceIte]
  rw [hlist]
  split
  · rename_i longRest heq
    exact absurd (List.cons.inj (List.cons.inj heq).2).1 hc_ne
  · rename_i _ c' shortRest' _ heq
    have hc_eq : c = c' := (List.cons.inj (List.cons.inj heq).2).1
    have hsr_eq : [] = shortRest' := (List.cons.inj (List.cons.inj heq).2).2
    rw [← hc_eq, ← hsr_eq, hsb]
    simp only [Bind.bind, Except.bind]
    simp [Internal.parseTokens]
  · rename_i _ _ h2
    exact absurd rfl (h2 c [])

private theorem renderValueList_cons (opt : OptSpec) (v : OptValue) (vs : List OptValue) :
    Model.renderSingleOpt.renderValueList opt (v :: vs) =
      (if opt.kind == .bool && v != .bool true then
         .error
           { kind := .invalidValue,
             message := s!"repeatable boolean option '{opt.name}' cannot render false value",
             target := some opt.name }
       else do
         let toks ←
           match opt.long with
           | some l =>
             if opt.kind == .bool then .ok ["--" ++ l]
             else .ok ["--" ++ l ++ "=" ++ Model.optValueToString v]
           | none =>
             match opt.short with
             | some c =>
               if opt.kind == .bool then .ok ["-" ++ String.singleton c]
               else .ok ["-" ++ String.singleton c, Model.optValueToString v]
             | none =>
               .error
                 { kind := .invalidSpec,
                   message := s!"option '{opt.name}' has neither long nor short flag" }
         let rest ← Model.renderSingleOpt.renderValueList opt vs
         .ok (toks ++ rest)) := by
  cases vs <;> rfl

private theorem parseTokens_renderValueList (rootName : String) (st : Internal.ParseState)
    (opt : OptSpec) (vals : List OptValue) (toks : List String)
    (hndLongs : (Model.collectVisibleLongs (st.inheritedGlobals ++ st.curSpec.options)).Nodup)
    (hndShorts : ((st.inheritedGlobals ++ st.curSpec.options).filterMap (·.short)).Nodup)
    (hh : st.curSpec.shortHelp = true → 'h' ∉ (st.inheritedGlobals ++ st.curSpec.options).filterMap (·.short))
    (hV : (st.curSpec.shortVersion && st.effectiveVersion.isSome) = true →
      'V' ∉ (st.inheritedGlobals ++ st.curSpec.options).filterMap (·.short))
    (hloc : Model.isValidOptLocal opt = true)
    (ho : opt ∈ st.inheritedGlobals ++ st.curSpec.options)
    (hmatch : ∀ v ∈ vals, OptValueMatchesKind opt.kind v)
    (hp : st.pendingOpt = none) (had : st.afterDashDash = false)
    (hr : Model.renderSingleOpt.renderValueList opt vals = .ok toks) :
    Internal.parseTokens rootName [] st toks =
      .ok { st with cliOpts := recordCliOptMany st.cliOpts opt.name vals } := by
  induction vals generalizing st toks with
  | nil =>
    have hnil : Model.renderSingleOpt.renderValueList opt [] = .ok [] := rfl
    rw [hnil] at hr
    injection hr with heq; subst heq
    cases st; dsimp only at hp; subst hp
    simp [recordCliOptMany, Internal.parseTokens]
  | cons v vs ih =>
    rw [renderValueList_cons] at hr
    by_cases hbf : (opt.kind == .bool && v != .bool true)
    · simp [hbf] at hr
    · simp only [hbf, Bool.false_eq_true, ↓reduceIte] at hr
      have hv_match : OptValueMatchesKind opt.kind v := hmatch v (by simp)
      have hvs_match : ∀ v' ∈ vs, OptValueMatchesKind opt.kind v' := fun v' hv' => hmatch v' (by simp [hv'])
      cases hl : opt.long with
      | some l =>
        rw [hl] at hr; dsimp only at hr
        by_cases hbool : opt.kind == .bool
        · simp only [hbool, ↓reduceIte, Bind.bind, Except.bind] at hr
          have hk : opt.kind = .bool := valueKind_eq_of_beq hbool
          have hv : v = .bool true := by
            cases hv' : v <;> rw [hk, hv'] at hv_match <;> simp [OptValueMatchesKind] at hv_match
            rename_i b; cases b
            · simp [hk, hv'] at hbf; exact absurd hbf (by decide)
            · rfl
          subst hv
          cases hrest : Model.renderSingleOpt.renderValueList opt vs with
          | error e => rw [hrest] at hr; cases hr
          | ok restToks =>
            rw [hrest] at hr; injection hr with htoks; subst htoks
            have h1 := parseTokens_step_longBool rootName st opt l true hndLongs hloc ho hl hk (fun hc => by cases hc) hp had
            simp only [↓reduceIte] at h1
            rw [parseTokens_append rootName [] ["--" ++ l] restToks st _ h1]
            exact ih _ restToks hndLongs hndShorts hh hV ho hvs_match hp had hrest
        · simp only [hbool, Bool.false_eq_true, ↓reduceIte, Bind.bind, Except.bind] at hr
          have hnk : opt.kind ≠ .bool := fun hk => hbool (by simp [hk]; rfl)
          cases hrest : Model.renderSingleOpt.renderValueList opt vs with
          | error e => rw [hrest] at hr; cases hr
          | ok restToks =>
            rw [hrest] at hr; injection hr with htoks; subst htoks
            have h1 := parseTokens_step_longVal rootName st opt l v hndLongs hloc ho hl hnk hv_match hp had
            rw [parseTokens_append rootName [] ["--" ++ l ++ "=" ++ Model.optValueToString v] restToks st _ h1]
            exact ih _ restToks hndLongs hndShorts hh hV ho hvs_match hp had hrest
      | none =>
        rw [hl] at hr; dsimp only at hr
        cases hs : opt.short with
        | none => rw [hs] at hr; cases hr
        | some c =>
          rw [hs] at hr; dsimp only at hr
          by_cases hbool : opt.kind == .bool
          · simp only [hbool, ↓reduceIte, Bind.bind, Except.bind] at hr
            have hk : opt.kind = .bool := valueKind_eq_of_beq hbool
            cases hrest : Model.renderSingleOpt.renderValueList opt vs with
            | error e => rw [hrest] at hr; cases hr
            | ok restToks =>
              rw [hrest] at hr; injection hr with htoks; subst htoks
              have hv : v = .bool true := by
                cases hv' : v <;> rw [hk, hv'] at hv_match <;> simp [OptValueMatchesKind] at hv_match
                rename_i b; cases b
                · simp [hk, hv'] at hbf; exact absurd hbf (by decide)
                · rfl
              subst hv
              have h1 := parseTokens_step_shortBool rootName st opt c hndShorts hh hV hloc ho hs hk hp had
              rw [parseTokens_append rootName [] ["-" ++ String.singleton c] restToks st _ h1]
              exact ih _ restToks hndLongs hndShorts hh hV ho hvs_match hp had hrest
          · simp only [hbool, Bool.false_eq_true, ↓reduceIte, Bind.bind, Except.bind] at hr
            have hnk : opt.kind ≠ .bool := fun hk => hbool (by simp [hk]; rfl)
            cases hrest : Model.renderSingleOpt.renderValueList opt vs with
            | error e => rw [hrest] at hr; cases hr
            | ok restToks =>
              rw [hrest] at hr; injection hr with htoks; subst htoks
              have h1 := parseTokens_step_shortTwo rootName st opt c v hndShorts hh hV hloc ho hs hnk hv_match hp had
              rw [parseTokens_append rootName [] ["-" ++ String.singleton c, Model.optValueToString v] restToks st _ h1]
              exact ih _ restToks hndLongs hndShorts hh hV ho hvs_match hp had hrest

private theorem parseTokens_renderSingleOpt (rootName : String) (st : Internal.ParseState)
    (opt : OptSpec) (vals : List OptValue) (toks : List String)
    (hndLongs : (Model.collectVisibleLongs (st.inheritedGlobals ++ st.curSpec.options)).Nodup)
    (hndShorts : ((st.inheritedGlobals ++ st.curSpec.options).filterMap (·.short)).Nodup)
    (hh : st.curSpec.shortHelp = true → 'h' ∉ (st.inheritedGlobals ++ st.curSpec.options).filterMap (·.short))
    (hV : (st.curSpec.shortVersion && st.effectiveVersion.isSome) = true →
      'V' ∉ (st.inheritedGlobals ++ st.curSpec.options).filterMap (·.short))
    (hloc : Model.isValidOptLocal opt = true)
    (ho : opt ∈ st.inheritedGlobals ++ st.curSpec.options)
    (hmatch : ∀ v ∈ vals, OptValueMatchesKind opt.kind v)
    (hlen : opt.repeatable = false → vals.length ≤ 1)
    (hp : st.pendingOpt = none) (had : st.afterDashDash = false)
    (hr : Model.renderSingleOpt opt vals = .ok toks) :
    ∃ delta : List OptValue,
      Internal.parseTokens rootName [] st toks =
        .ok { st with cliOpts := recordCliOptMany st.cliOpts opt.name delta } ∧
      (if (vals.isEmpty || (opt.kind == .bool && !opt.repeatable && opt.long.isNone && (vals == [.bool false])))
       then delta = [] else delta = vals) := by
  unfold Model.renderSingleOpt at hr
  by_cases hempty : vals.isEmpty
  · simp only [hempty, ↓reduceIte, Except.ok.injEq] at hr
    subst hr
    refine ⟨[], ?_, by simp [hempty]⟩
    cases st; dsimp only at hp; subst hp; simp [recordCliOptMany, Internal.parseTokens]
  · simp only [hempty, Bool.false_eq_true, ↓reduceIte] at hr
    by_cases hbnr : (opt.kind == .bool && !opt.repeatable)
    · simp only [hbnr, ↓reduceIte] at hr
      have hk : opt.kind = .bool := valueKind_eq_of_beq ((Bool.and_eq_true _ _).mp hbnr).1
      have hnr : opt.repeatable = false := by
        have := ((Bool.and_eq_true _ _).mp hbnr).2; simpa using this
      cases vals with
      | nil => cases hempty rfl
      | cons v vs =>
        cases vs with
        | cons v2 vs2 =>
          have hle := hlen hnr; simp at hle
        | nil =>
          have hmv := hmatch v (by simp)
          cases hv : v with
          | bool b =>
            subst hv
            cases b with
            | true =>
              dsimp only at hr
              cases hl : opt.long with
              | some l =>
                rw [hl] at hr; injection hr with htoks; subst htoks
                refine ⟨[.bool true], ?_, by simp⟩
                have h1 := parseTokens_step_longBool rootName st opt l true hndLongs hloc ho hl hk (fun hc => by cases hc) hp had
                simpa [recordCliOptMany] using h1
              | none =>
                rw [hl] at hr; dsimp only at hr
                cases hs : opt.short with
                | none => rw [hs] at hr; cases hr
                | some c =>
                  rw [hs] at hr; injection hr with htoks; subst htoks
                  have hvv : ([OptValue.bool true] == [OptValue.bool false]) = false := rfl
                  refine ⟨[.bool true], ?_, by simp [hvv]⟩
                  have h1 := parseTokens_step_shortBool rootName st opt c hndShorts hh hV hloc ho hs hk hp had
                  simpa [recordCliOptMany] using h1
            | false =>
              dsimp only at hr
              cases hl : opt.long with
              | some l =>
                rw [hl] at hr; injection hr with htoks; subst htoks
                refine ⟨[.bool false], ?_, by simp⟩
                have h1 := parseTokens_step_longBool rootName st opt l false hndLongs hloc ho hl hk (fun _ => hnr) hp had
                simpa [recordCliOptMany] using h1
              | none =>
                rw [hl] at hr; dsimp only at hr
                cases hdef : opt.default with
                | none =>
                  rw [hdef] at hr
                  injection hr with htoks; subst htoks
                  refine ⟨[], ?_, ?_⟩
                  · cases st; dsimp only at hp; subst hp; simp [recordCliOptMany, Internal.parseTokens]
                  · have hvb : (opt.kind == .bool) = true := by rw [hk]; rfl
                    have hvv : ([OptValue.bool false] == [OptValue.bool false]) = true := rfl
                    simp [hvb, hnr, hvv]
                | some d =>
                  rw [hdef] at hr; dsimp only at hr
                  by_cases hpb : (Model.parseBoolString d == some true)
                  · simp only [hpb, ↓reduceIte] at hr
                    cases hr
                  · have hpbF : (Model.parseBoolString d == some true) = false := Bool.eq_false_iff.mpr hpb
                    simp only [hpbF, Bool.false_eq_true, ↓reduceIte, Except.ok.injEq] at hr
                    subst hr
                    refine ⟨[], ?_, ?_⟩
                    · cases st; dsimp only at hp; subst hp; simp [recordCliOptMany, Internal.parseTokens]
                    · have hvb : (opt.kind == .bool) = true := by rw [hk]; rfl
                      have hvv : ([OptValue.bool false] == [OptValue.bool false]) = true := rfl
                      simp [hvb, hnr, hvv]
          | _ => rw [hk, hv] at hmv; cases hmv
    · simp only [hbnr, Bool.false_eq_true, ↓reduceIte] at hr
      refine ⟨vals, parseTokens_renderValueList rootName st opt vals toks hndLongs hndShorts hh hV hloc ho hmatch hp had hr, ?_⟩
      have hn : (vals.isEmpty || (opt.kind == .bool && !opt.repeatable && opt.long.isNone && (vals == [.bool false]))) = false := by
        have hbnrF : (opt.kind == .bool && !opt.repeatable) = false := Bool.eq_false_iff.mpr hbnr
        have hemptyF : vals.isEmpty = false := Bool.eq_false_iff.mpr hempty
        rw [hemptyF, Bool.false_or]
        cases h1 : (opt.kind == .bool) <;> cases h2 : opt.repeatable <;> simp_all
      simp [hn]

private theorem renderOpts_cons (parsed : ParsedCmd) (opt : OptSpec) (rest : List OptSpec) :
    Model.renderArgs.renderOpts parsed (opt :: rest) =
      (let vals := lookupCli parsed.options opt.name
       do
         let headToks ← Model.renderSingleOpt opt vals
         let tailToks ← Model.renderArgs.renderOpts parsed rest
         .ok (headToks ++ tailToks)) := by
  cases rest <;> rfl

private theorem parseTokens_renderOpts (rootName : String) (st : Internal.ParseState)
    (parsed : ParsedCmd) (opts : List OptSpec) (toks : List String)
    (hndOpts : (opts.map (·.name)).Nodup)
    (hsub : ∀ opt ∈ opts, opt ∈ st.inheritedGlobals ++ st.curSpec.options)
    (hndLongs : (Model.collectVisibleLongs (st.inheritedGlobals ++ st.curSpec.options)).Nodup)
    (hndShorts : ((st.inheritedGlobals ++ st.curSpec.options).filterMap (·.short)).Nodup)
    (hh : st.curSpec.shortHelp = true → 'h' ∉ (st.inheritedGlobals ++ st.curSpec.options).filterMap (·.short))
    (hV : (st.curSpec.shortVersion && st.effectiveVersion.isSome) = true →
      'V' ∉ (st.inheritedGlobals ++ st.curSpec.options).filterMap (·.short))
    (hloc : ∀ opt ∈ opts, Model.isValidOptLocal opt = true)
    (hmatch : ∀ opt ∈ opts, ∀ v ∈ lookupCli parsed.options opt.name, OptValueMatchesKind opt.kind v)
    (hlen : ∀ opt ∈ opts, opt.repeatable = false → (lookupCli parsed.options opt.name).length ≤ 1)
    (hfresh : ∀ opt ∈ opts, lookupCli st.cliOpts opt.name = [])
    (hp : st.pendingOpt = none) (had : st.afterDashDash = false)
    (hr : Model.renderArgs.renderOpts parsed opts = .ok toks) :
    ∃ cliFinal,
      Internal.parseTokens rootName [] st toks = .ok { st with cliOpts := cliFinal } ∧
      (∀ opt ∈ opts,
        let vals := lookupCli parsed.options opt.name
        if (vals.isEmpty || (opt.kind == .bool && !opt.repeatable && opt.long.isNone && (vals == [.bool false])))
        then lookupCli cliFinal opt.name = []
        else lookupCli cliFinal opt.name = vals) ∧
      (∀ k, (∀ o' ∈ opts, o'.name ≠ k) → lookupCli cliFinal k = lookupCli st.cliOpts k) := by
  induction opts generalizing st toks with
  | nil =>
    have hnil : Model.renderArgs.renderOpts parsed [] = .ok [] := rfl
    rw [hnil] at hr; injection hr with heq; subst heq
    refine ⟨st.cliOpts, ?_, (fun _ h => by cases h), (fun _ _ => rfl)⟩
    cases st; dsimp only at hp; subst hp; rfl
  | cons opt rest ih =>
    simp only [List.map_cons, List.nodup_cons, List.mem_map] at hndOpts
    rw [renderOpts_cons] at hr
    dsimp only at hr
    cases hhead : Model.renderSingleOpt opt (lookupCli parsed.options opt.name) with
    | error e => rw [hhead] at hr; cases hr
    | ok headToks =>
      rw [hhead] at hr
      cases htail : Model.renderArgs.renderOpts parsed rest with
      | error e => rw [htail] at hr; cases hr
      | ok tailToks =>
        rw [htail] at hr
        simp only [Bind.bind, Except.bind, Except.ok.injEq] at hr
        subst hr
        rcases parseTokens_renderSingleOpt rootName st opt (lookupCli parsed.options opt.name) headToks
            hndLongs hndShorts hh hV (hloc opt (by simp)) (hsub opt (by simp))
            (hmatch opt (by simp)) (hlen opt (by simp)) hp had hhead with ⟨delta, h1, hdelta⟩
        have hfresh_rest : ∀ o' ∈ rest, lookupCli (recordCliOptMany st.cliOpts opt.name delta) o'.name = [] := by
          intro o' ho'
          have hne : o'.name ≠ opt.name := fun heq => hndOpts.1 ⟨o', ho', heq⟩
          rw [recordCliOptMany_lookupCli_ne _ _ _ _ hne]
          exact hfresh o' (by simp [ho'])
        rcases ih { st with cliOpts := recordCliOptMany st.cliOpts opt.name delta } tailToks hndOpts.2
            (fun o' ho' => hsub o' (by simp [ho'])) hndLongs hndShorts hh hV
            (fun o' ho' => hloc o' (by simp [ho']))
            (fun o' ho' => hmatch o' (by simp [ho']))
            (fun o' ho' => hlen o' (by simp [ho']))
            hfresh_rest hp had htail with ⟨cliFinal, h2, hres, hk_rest⟩
        refine ⟨cliFinal, ?_, ?_, ?_⟩
        · rw [parseTokens_append rootName [] headToks tailToks st _ h1]
          exact h2
        · intro o' ho'
          simp only [List.mem_cons] at ho'
          rcases ho' with rfl | hmem
          · have hnotRest : ∀ x ∈ rest, x.name ≠ o'.name := fun x hx heq => hndOpts.1 ⟨x, hx, heq⟩
            rw [hk_rest o'.name hnotRest]
            dsimp only
            rw [recordCliOptMany_lookupCli_same, hfresh o' (by simp), List.nil_append]
            split at hdelta <;> simp [*]
          · exact hres o' hmem
        · intro k hk
          rw [hk_rest k (fun o' ho' => hk o' (by simp [ho']))]
          exact recordCliOptMany_lookupCli_ne st.cliOpts opt.name k delta (hk opt (by simp)).symm

private theorem parseTokens_pos_afterDashDash (rootName : String) (st : Internal.ParseState)
    (pos : List String) (had : st.afterDashDash = true) (hp : st.pendingOpt = none) :
    Internal.parseTokens rootName [] st pos =
      .ok { st with rawPositionals := st.rawPositionals ++ pos } := by
  induction pos generalizing st with
  | nil => cases st; dsimp only at hp; subst hp; simp [Internal.parseTokens]
  | cons tok rest ih =>
    unfold Internal.parseTokens
    simp only [hp, had, ↓reduceIte]
    have hrec := ih { st with afterDashDash := true, rawPositionals := st.rawPositionals ++ [tok] } rfl hp
    rw [hp] at hrec
    simpa [had, List.append_assoc] using hrec

private theorem parseTokens_pos_noDash (rootName : String) (st : Internal.ParseState)
    (pos : List String) (hleaf : st.curSpec.subcommands.isEmpty = true)
    (hnd : pos.any Model.startsWithDash = false)
    (hp : st.pendingOpt = none) (had : st.afterDashDash = false) :
    Internal.parseTokens rootName [] st pos =
      .ok { st with rawPositionals := st.rawPositionals ++ pos } := by
  induction pos generalizing st with
  | nil => cases st; dsimp only at hp; subst hp; simp [Internal.parseTokens]
  | cons tok rest ih =>
    have htok_nd : Model.startsWithDash tok = false := by
      have := List.any_eq_false.mp hnd tok (by simp)
      cases h : Model.startsWithDash tok <;> simp_all
    have hrest_nd : rest.any Model.startsWithDash = false :=
      List.any_eq_false.mpr (fun x hx => List.any_eq_false.mp hnd x (by simp [hx]))
    have hnodash : ∀ cs, tok.toList ≠ '-' :: cs := by
      intro cs heq
      unfold Model.startsWithDash at htok_nd
      rw [heq] at htok_nd
      cases htok_nd
    have hne_dd : (tok == "--") = false := beq_false_of_ne (fun heq => by
      have h1 : ("--").toList = ['-', '-'] := rfl
      have := congrArg String.toList heq; rw [h1] at this; exact hnodash ['-'] this)
    have hne_help : (tok == "--help") = false := beq_false_of_ne (fun heq => by
      have h1 : ("--help").toList = ['-', '-', 'h', 'e', 'l', 'p'] := rfl
      have := congrArg String.toList heq; rw [h1] at this; exact hnodash ['-', 'h', 'e', 'l', 'p'] this)
    have hne_ver : (tok == "--version") = false := beq_false_of_ne (fun heq => by
      have h1 : ("--version").toList = ['-', '-', 'v', 'e', 'r', 's', 'i', 'o', 'n'] := rfl
      have := congrArg String.toList heq; rw [h1] at this; exact hnodash ['-', 'v', 'e', 'r', 's', 'i', 'o', 'n'] this)
    have hbranch : Internal.parseTokens rootName [] st (tok :: rest) =
        Internal.parseTokens rootName [] { st with rawPositionals := st.rawPositionals ++ [tok] } rest := by
      conv => lhs; unfold Internal.parseTokens; dsimp only
      simp only [hp, had, hne_dd, hne_help, hne_ver, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
      split
      · rename_i longRest heqm
        unfold Model.startsWithDash at htok_nd; rw [heqm] at htok_nd; cases htok_nd
      · rename_i c shortRest _ heqm
        unfold Model.startsWithDash at htok_nd; rw [heqm] at htok_nd; cases htok_nd
      · simp [hleaf]
    rw [hbranch]
    have hrec := ih { st with rawPositionals := st.rawPositionals ++ [tok] } hleaf hrest_nd hp had
    simpa [List.append_assoc] using hrec

private theorem parseTokens_posTokens (rootName : String) (st : Internal.ParseState)
    (pos : List String)
    (hleaf : st.curSpec.subcommands.isEmpty = true)
    (hp : st.pendingOpt = none) (had : st.afterDashDash = false) :
    Internal.parseTokens rootName [] st
        (if pos.any Model.startsWithDash then "--" :: pos else pos) =
      .ok { st with
          afterDashDash := pos.any Model.startsWithDash
          rawPositionals := st.rawPositionals ++ pos } := by
  by_cases hd : pos.any Model.startsWithDash
  · simp only [hd, ↓reduceIte]
    unfold Internal.parseTokens
    simp only [hp, had, beq_self_eq_true, Bool.false_eq_true, ↓reduceIte]
    have hp' : ({ st with afterDashDash := true, pendingOpt := none } : Internal.ParseState).pendingOpt = none := rfl
    have hres := parseTokens_pos_afterDashDash rootName { st with afterDashDash := true, pendingOpt := none } pos rfl hp'
    cases st; dsimp only at hp; subst hp; exact hres
  · simp only [hd, Bool.false_eq_true, ↓reduceIte]
    have hdF : pos.any Model.startsWithDash = false := Bool.eq_false_iff.mpr hd
    have hres := parseTokens_pos_noDash rootName st pos hleaf hdF hp had
    rw [had] at hres
    exact hres

/-- `test_cmdline_renderArgs_universalRoundTrip` holds universally for `defaultApi`. -/
theorem allPass_renderArgs_universalRoundTrip :
    Core.AllPass (test_cmdline_renderArgs_universalRoundTrip defaultApi) := by
  dsimp only [Core.AllPass, Core.AllPassRun, test_cmdline_renderArgs_universalRoundTrip,
    Bind.bind, Pure.pure, Core.NondetTest.nondet, Core.NondetTest.assume, Core.NondetTest.assert]
  intro spec args hValid
  change Model.isValidSpec spec = true at hValid
  cases hParse : defaultApi.parse spec args with
  | error e => dsimp only; exact fun h => False.elim h
  | ok parsed =>
    dsimp only
    cases hRender : defaultApi.renderArgs spec parsed with
    | error e => dsimp only; exact fun h => False.elim h
    | ok rendered =>
      dsimp only
      change Internal.parseWith spec args = .ok parsed at hParse
      change Model.renderArgs spec parsed = .ok rendered at hRender
      have hValidNot : (!Model.isValidSpec spec) = false := by simp [hValid]
      unfold Internal.parseWith Internal.parseWithEnvM at hParse
      simp only [hValidNot, Bool.false_eq_true, ↓reduceIte, pure, Bind.bind] at hParse
      cases hToks : Internal.parseTokens spec.name [] { curSpec := spec, effectiveVersion := spec.version } args with
      | error e => rw [hToks] at hParse; cases hParse
      | ok finalState =>
        rw [hToks] at hParse
        dsimp only at hParse
        cases hNonEmpty : !finalState.curSpec.subcommands.isEmpty with
        | true =>
          simp only [hNonEmpty, ↓reduceIte] at hParse
          split at hParse <;> cases hParse
        | false =>
          simp only [hNonEmpty, Bool.false_eq_true, ↓reduceIte] at hParse
          have hLeaf : finalState.curSpec.subcommands.isEmpty = true := by
            cases hc : finalState.curSpec.subcommands.isEmpty <;> simp_all
          cases hResOpts : Model.resolveOptions (m := Id) Internal.pureNoEnvOps.getEnv
              (finalState.inheritedGlobals ++ finalState.curSpec.options) finalState.cliOpts [] with
          | error e => rw [hResOpts] at hParse; cases hParse
          | ok resolvedOpts =>
            rw [hResOpts] at hParse; dsimp only at hParse
            cases hResArgs : Model.resolveArgs finalState.curSpec.args finalState.rawPositionals [] with
            | error e => rw [hResArgs] at hParse; cases hParse
            | ok resolvedArgs =>
              rw [hResArgs] at hParse
              injection hParse with hParsedEq
              subst hParsedEq
              have hv0 : spec.version = (spec.version <|> none) := by
                cases spec.version <;> rfl
              have hInitInv : ParseStateInv spec { curSpec := spec, effectiveVersion := spec.version } := by
                refine ⟨⟨none, ⟨by simpa [Model.isValidSpec] using hValid, rfl⟩, hv0⟩, ?_, ?_, fun _ hc => by cases hc⟩
                · unfold Model.findSubcommandPath Model.findSubcommandPath.go
                  exact congrArg (fun v => Except.ok ([], v, spec)) hv0.symm
                · exact ⟨(fun _ hk => absurd rfl hk), (fun _ _ _ hv => by cases hv)⟩
              rcases parseTokens_sound spec { curSpec := spec, effectiveVersion := spec.version } hInitInv args hToks with
                ⟨⟨⟨vp, hFinalNode, hFinalEff⟩, hFinalPath, hFinalCli, _⟩, _⟩
              have hProps := nodeInv_props hFinalNode
              unfold Model.renderArgs at hRender
              rw [hValidNot] at hRender
              dsimp only [Bind.bind, Except.bind] at hRender
              rw [hFinalPath] at hRender
              dsimp only at hRender
              rw [hNonEmpty] at hRender
              cases hRO : Model.renderArgs.renderOpts
                  { subcommandPath := finalState.subPath, options := resolvedOpts,
                    args := resolvedArgs, rawPositionals := finalState.rawPositionals }
                  (finalState.inheritedGlobals ++ finalState.curSpec.options) with
              | error e => rw [hRO] at hRender; cases hRender
              | ok optTokens =>
                rw [hRO] at hRender
                dsimp only [Bind.bind, Except.bind] at hRender
                injection hRender with hRenderedEq
                subst hRenderedEq
                have hLookup := resolveOptions_lookup (finalState.inheritedGlobals ++ finalState.curSpec.options)
                  finalState.cliOpts resolvedOpts hProps.2.2.1 hFinalCli hResOpts
                let stSub : Internal.ParseState := {
                  curSpec := finalState.curSpec
                  subPath := finalState.subPath
                  inheritedGlobals := finalState.inheritedGlobals
                  effectiveVersion := finalState.effectiveVersion }
                have hh' : stSub.curSpec.shortHelp = true →
                    'h' ∉ (stSub.inheritedGlobals ++ stSub.curSpec.options).filterMap (·.short) := hProps.2.2.2.2.2.1
                have hV' : (stSub.curSpec.shortVersion && stSub.effectiveVersion.isSome) = true →
                    'V' ∉ (stSub.inheritedGlobals ++ stSub.curSpec.options).filterMap (·.short) := by
                  rw [← hFinalEff] at hProps
                  exact hProps.2.2.2.2.2.2.1
                rcases parseTokens_renderOpts spec.name stSub
                    { subcommandPath := finalState.subPath, options := resolvedOpts,
                      args := resolvedArgs, rawPositionals := finalState.rawPositionals }
                    (finalState.inheritedGlobals ++ finalState.curSpec.options) optTokens
                    hProps.2.2.1 (fun _ ho => ho) hProps.2.2.2.1 hProps.2.2.2.2.1 hh' hV'
                    hProps.2.1
                    (fun o ho v hv => (hLookup o ho).1 v hv)
                    (fun o ho hnr => (hLookup o ho).2.1 hnr)
                    (fun _ _ => rfl) rfl rfl hRO with ⟨cliFinal, hParseOpts, hCliFinal, _⟩
                have hParseSub := parseTokens_subPath spec finalState.subPath hValid hFinalPath
                have hParsePos := parseTokens_posTokens spec.name { stSub with cliOpts := cliFinal }
                  finalState.rawPositionals hLeaf rfl rfl
                have hParseAll : Internal.parseTokens spec.name []
                    { curSpec := spec, effectiveVersion := spec.version }
                    (finalState.subPath ++ optTokens ++
                      (if finalState.rawPositionals.any Model.startsWithDash then "--" :: finalState.rawPositionals
                       else finalState.rawPositionals)) =
                    .ok { stSub with
                        cliOpts := cliFinal
                        afterDashDash := finalState.rawPositionals.any Model.startsWithDash
                        rawPositionals := finalState.rawPositionals } := by
                  rw [List.append_assoc]
                  rw [parseTokens_append _ _ _ _ _ _ hParseSub]
                  rw [parseTokens_append _ _ _ _ _ _ hParseOpts]
                  exact hParsePos
                have hCongr : Model.resolveOptions (m := Id) Internal.pureNoEnvOps.getEnv
                    (finalState.inheritedGlobals ++ finalState.curSpec.options) cliFinal [] = .ok resolvedOpts := by
                  rw [← hResOpts]
                  apply resolveOptions_congr
                  intro o ho
                  have hCF := hCliFinal o ho
                  have hLo := hLookup o ho
                  dsimp only at hCF hLo
                  by_cases hEmpty : (lookupCli resolvedOpts o.name).isEmpty
                  · have hNil : lookupCli resolvedOpts o.name = [] := by
                      cases hxs : lookupCli resolvedOpts o.name with
                      | nil => rfl
                      | cons _ _ => rw [hxs] at hEmpty; cases hEmpty
                    have hNilOld : lookupCli finalState.cliOpts o.name = [] := hLo.2.2.1 hNil
                    have hNilNew : lookupCli cliFinal o.name = [] := by
                      simp only [hEmpty, Bool.true_or, ↓reduceIte] at hCF
                      exact hCF
                    rw [hNilNew, hNilOld]
                  · by_cases hSpecial : (o.kind == .bool && !o.repeatable && o.long.isNone &&
                        (lookupCli resolvedOpts o.name == [.bool false]))
                    · have hNilOld : lookupCli finalState.cliOpts o.name = [] := hLo.2.2.2.1 hSpecial
                      have hNilNew : lookupCli cliFinal o.name = [] := by
                        simp only [hSpecial, Bool.or_true, ↓reduceIte] at hCF
                        exact hCF
                      rw [hNilNew, hNilOld]
                    · have hEqVals : lookupCli cliFinal o.name = lookupCli resolvedOpts o.name := by
                        have hEmptyF : (lookupCli resolvedOpts o.name).isEmpty = false := Bool.eq_false_iff.mpr hEmpty
                        have hSpecialF : (o.kind == .bool && !o.repeatable && o.long.isNone &&
                            (lookupCli resolvedOpts o.name == [.bool false])) = false := Bool.eq_false_iff.mpr hSpecial
                        simp only [hEmptyF, hSpecialF, Bool.or_self, Bool.false_eq_true, ↓reduceIte] at hCF
                        exact hCF
                      rw [hEqVals]
                      rw [resolveSingleOption_pureNoEnv]
                      have hne : (lookupCli resolvedOpts o.name).isEmpty = false := by
                        cases hxs : lookupCli resolvedOpts o.name with
                        | nil => rw [hxs] at hEmpty; exact absurd rfl hEmpty
                        | cons _ _ => rfl
                      simp only [hne, Bool.not_false, ↓reduceIte]
                      have hlen : (!o.repeatable && decide ((lookupCli resolvedOpts o.name).length > 1)) = false := by
                        cases hrep : o.repeatable
                        · have hle := hLo.2.1 hrep
                          have hnt : decide ((lookupCli resolvedOpts o.name).length > 1) = false :=
                            decide_eq_false (Nat.not_lt.mpr hle)
                          simp [hnt]
                        · simp
                      simp only [hlen, Bool.false_eq_true, ↓reduceIte]
                      have hNotNil : lookupCli resolvedOpts o.name ≠ [] := by
                        intro hc; rw [hc] at hne; cases hne
                      exact (hLo.2.2.2.2 hNotNil).symm
                change Internal.parseWith spec _ = _ ∧ True
                unfold Internal.parseWith Internal.parseWithEnvM
                simp only [hValidNot, Bool.false_eq_true, ↓reduceIte, pure, Bind.bind]
                rw [hParseAll]
                dsimp only [stSub]
                simp only [hNonEmpty, Bool.false_eq_true, ↓reduceIte]
                rw [hCongr]
                dsimp only
                rw [hResArgs]
                exact ⟨rfl, trivial⟩

/-- `test_cmdline_renderArgs_universalRoundTrip` is reachable via a concrete witness. -/
theorem canReach_renderArgs_universalRoundTrip :
    CanReach (test_cmdline_renderArgs_universalRoundTrip defaultApi) :=
  ⟨{ name := "app" }, [], by decide, allPass_renderArgs_universalRoundTrip { name := "app" } [] (by decide)⟩

private def exceptKindIn {α : Type} (P : CmdLineErrorKind → Prop) (r : Except CmdLineError α) : Prop :=
  match r with
  | .ok _ => True
  | .error e => P e.kind

private theorem exceptKindIn_bind {α β : Type} (P : CmdLineErrorKind → Prop)
    (r : Except CmdLineError α) (k : α → Except CmdLineError β)
    (hr : exceptKindIn P r) (hk : ∀ a, exceptKindIn P (k a)) :
    exceptKindIn P (r >>= k) := by
  cases r with
  | error e => exact hr
  | ok a => exact hk a

private theorem exceptKindIn_mk {α : Type} {P : CmdLineErrorKind → Prop}
    {kd : CmdLineErrorKind} {msg : String} {tgt : Option String} (h : P kd) :
    exceptKindIn P (Except.error { kind := kd, message := msg, target := tgt } : Except CmdLineError α) := h

private theorem parseOptValue_kind {k : ValueKind} {s : String} :
    exceptKindIn (fun kd => kd = .invalidValue) (Model.parseOptValue k s) := by
  unfold Model.parseOptValue
  cases k <;> dsimp only
  · trivial
  · cases Model.parseBoolString s <;> trivial
  · cases Model.parseNatChars s.toList <;> trivial
  · cases Model.parseIntChars s.toList <;> trivial
  · split <;> trivial
  · trivial

private theorem validateCustomValue_kind {k : ValueKind} {s : String} {v : CustomValidators} :
    exceptKindIn (fun kd => kd = .invalidValue) (Model.validateCustomValue k s v) := by
  unfold Model.validateCustomValue
  cases k <;> dsimp only
  · trivial
  · trivial
  · trivial
  · trivial
  · trivial
  · cases v.find? _ with
    | none => trivial
    | some p =>
      dsimp only
      cases p.2 s with
      | ok _ => trivial
      | error _ => rfl

private theorem parseOptValueWith_kind {k : ValueKind} {s : String} {v : CustomValidators} :
    exceptKindIn (fun kd => kd = .invalidValue) (Model.parseOptValueWith k s v) := by
  unfold Model.parseOptValueWith
  refine exceptKindIn_bind _ _ _ parseOptValue_kind fun _ => ?_
  refine exceptKindIn_bind _ _ _ validateCustomValue_kind fun _ => trivial

private theorem parseOptValueWith_error {k : ValueKind} {s : String} {v : CustomValidators}
    {e : CmdLineError} (h : Model.parseOptValueWith k s v = Except.error e) :
    e.kind = .invalidValue := by
  have hk := parseOptValueWith_kind (k := k) (s := s) (v := v)
  rw [h] at hk
  exact hk

private theorem parseShortBundle_noEofIo (visibleOpts : List OptSpec) (shortHelp shortVersion : Bool)
    (rootName : String) (subPath : List String) (effVer : Option String)
    (curSpec : CommandSpec) (validators : CustomValidators)
    (cliOpts : List (String × List OptValue)) (cs : List Char) :
    exceptKindIn (fun kd => kd ≠ .eof ∧ kd ≠ .ioError)
      (Internal.parseShortBundle visibleOpts shortHelp shortVersion rootName subPath effVer curSpec validators cliOpts cs) := by
  induction cs generalizing cliOpts with
  | nil => simp [Internal.parseShortBundle, exceptKindIn]
  | cons c rest ih =>
    unfold Internal.parseShortBundle
    dsimp only
    split
    · exact exceptKindIn_mk (by decide)
    · split
      · cases effVer <;> exact exceptKindIn_mk (by decide)
      · cases visibleOpts.find? (fun o => o.short == some c) with
        | none => exact exceptKindIn_mk (by decide)
        | some opt =>
          dsimp only
          split
          · exact ih _
          · split
            · dsimp only [bind, Except.bind]
              cases hp : Model.parseOptValueWith opt.kind (String.ofList rest) validators with
              | error e =>
                exact exceptKindIn_mk (by rw [parseOptValueWith_error hp]; decide)
              | ok v => trivial
            · trivial

private theorem parseTokens_shortBundle_step
    (sb : Except CmdLineError (List (String × List OptValue) × Option OptSpec))
    (hsb : exceptKindIn (fun kd => kd ≠ .eof ∧ kd ≠ .ioError) sb)
    (nextSt : List (String × List OptValue) × Option OptSpec → Internal.ParseState)
    (k : Internal.ParseState → Except CmdLineError Internal.ParseState)
    (hk : ∀ st', exceptKindIn (fun kd => kd ≠ .eof ∧ kd ≠ .ioError) (k st')) :
    exceptKindIn (fun kd => kd ≠ .eof ∧ kd ≠ .ioError)
      (match sb with
      | .error err => .error err
      | .ok v => k (nextSt v)) := by
  cases sb with
  | error e => exact hsb
  | ok v => exact hk _

private theorem parseTokens_noEofIo (rootName : String) (validators : CustomValidators)
    (st : Internal.ParseState) (tokens : List String) :
    exceptKindIn (fun kd => kd ≠ .eof ∧ kd ≠ .ioError)
      (Internal.parseTokens rootName validators st tokens) := by
  induction tokens generalizing st with
  | nil =>
    unfold Internal.parseTokens
    cases st.pendingOpt with
    | none => trivial
    | some _ => exact exceptKindIn_mk (by decide)
  | cons tok rest ih =>
    unfold Internal.parseTokens
    cases st.pendingOpt with
    | some opt =>
      dsimp only [bind, Except.bind]
      cases hp : Model.parseOptValueWith opt.kind tok validators with
      | error e => exact exceptKindIn_mk (by rw [parseOptValueWith_error hp]; decide)
      | ok v => exact ih _
    | none =>
      dsimp only
      cases hdd : st.afterDashDash
      case true => simp only [↓reduceIte]; exact ih _
      case false =>
        simp only [Bool.false_eq_true, ↓reduceIte]
        split
        · exact ih _
        · split
          · exact exceptKindIn_mk (by decide)
          · split
            · cases st.effectiveVersion <;> exact exceptKindIn_mk (by decide)
            · cases htok : tok.toList with
              | nil =>
                dsimp only
                split
                · cases st.curSpec.subcommands.find? (fun s => s.name == tok) with
                  | some _ => exact ih _
                  | none => exact exceptKindIn_mk (by decide)
                · exact ih _
              | cons c1 cs1 =>
                cases c1 with
                | _ =>
                  split
                  · split
                    · exact exceptKindIn_mk (by decide)
                    · split
                      · exact exceptKindIn_mk (by decide)
                      · cases Internal.lookupLongOpt (st.inheritedGlobals ++ st.curSpec.options) _ with
                        | none => exact exceptKindIn_mk (by decide)
                        | some p =>
                          dsimp only
                          split
                          · cases (Internal.splitFirstEq _).2 with
                            | some _ => exact exceptKindIn_mk (by decide)
                            | none => exact ih _
                          · split
                            · cases (Internal.splitFirstEq _).2 with
                              | none => exact ih _
                              | some rawVal =>
                                dsimp only
                                cases hp : Model.parseOptValue .bool rawVal with
                                | error e =>
                                  have h := parseOptValue_kind (k := .bool) (s := rawVal)
                                  rw [hp] at h
                                  exact exceptKindIn_mk (by rw [h]; decide)
                                | ok v =>
                                  cases v with
                                  | bool _ =>
                                    dsimp only
                                    split
                                    · exact exceptKindIn_mk (by decide)
                                    · exact ih _
                                  | _ => exact exceptKindIn_mk (by decide)
                            · cases (Internal.splitFirstEq _).2 with
                              | some rawVal =>
                                dsimp only [bind, Except.bind]
                                cases hp : Model.parseOptValueWith p.1.kind rawVal validators with
                                | error e => exact exceptKindIn_mk (by rw [parseOptValueWith_error hp]; decide)
                                | ok _ => exact ih _
                              | none => exact ih _
                  · dsimp only [bind, Except.bind]
                    rename_i c_s shortRest_s _ _
                    have hsb := parseShortBundle_noEofIo (st.inheritedGlobals ++ st.curSpec.options)
                      st.curSpec.shortHelp st.curSpec.shortVersion rootName st.subPath
                      st.effectiveVersion st.curSpec validators st.cliOpts (c_s :: shortRest_s)
                    split
                    · rename_i err herr
                      rw [herr] at hsb
                      exact hsb
                    · exact ih _
                  · split
                    · cases st.curSpec.subcommands.find? (fun s => s.name == tok) with
                      | some _ => exact ih _
                      | none => exact exceptKindIn_mk (by decide)
                    · exact ih _

private theorem resolveOptDefault_noEofIo (opt : OptSpec) (validators : CustomValidators) :
    exceptKindIn (fun kd => kd ≠ .eof ∧ kd ≠ .ioError)
      (Model.resolveOptDefault opt validators) := by
  unfold Model.resolveOptDefault
  cases opt.default with
  | some d =>
    dsimp only
    cases hp : Model.parseOptValueWith opt.kind d validators with
    | error e => exact exceptKindIn_mk (by rw [parseOptValueWith_error hp]; decide)
    | ok _ => trivial
  | none =>
    dsimp only
    split
    · exact exceptKindIn_mk (by decide)
    · split <;> trivial

private theorem resolveSingleOption_pureNoEnv_noEofIo (opt : OptSpec) (cliVals : List OptValue)
    (validators : CustomValidators) :
    exceptKindIn (fun kd => kd ≠ .eof ∧ kd ≠ .ioError)
      (Model.resolveSingleOption (m := Id) Internal.pureNoEnvOps.getEnv opt cliVals validators) := by
  unfold Model.resolveSingleOption
  split
  · split
    · exact exceptKindIn_mk (by decide)
    · trivial
  · cases opt.envVar with
    | none => exact resolveOptDefault_noEofIo opt validators
    | some _ => exact resolveOptDefault_noEofIo opt validators

private theorem resolveOptions_step_exceptKindIn {P : CmdLineErrorKind → Prop}
    (r1 : Except CmdLineError (Option (List OptValue)))
    (r2 : Except CmdLineError (List (String × List OptValue)))
    (optName : String)
    (h1 : exceptKindIn P r1) (h2 : exceptKindIn P r2) :
    exceptKindIn P (match r1 with
      | .error e => .error e
      | .ok resolved? => match r2 with
        | .error e => .error e
        | .ok tail => match resolved? with
          | .none => .ok tail
          | .some vals => .ok ((optName, vals) :: tail)) := by
  cases r1 with
  | error e => exact h1
  | ok r? => cases r2 with | error e => exact h2 | ok _ => cases r? <;> trivial

private theorem resolveOptions_pureNoEnv_noEofIo (visibleOpts : List OptSpec)
    (cliOpts : List (String × List OptValue)) (validators : CustomValidators) :
    exceptKindIn (fun kd => kd ≠ .eof ∧ kd ≠ .ioError)
      (Model.resolveOptions (m := Id) Internal.pureNoEnvOps.getEnv visibleOpts cliOpts validators) := by
  induction visibleOpts with
  | nil => simp [Model.resolveOptions, exceptKindIn, pure]
  | cons opt rest ih =>
    unfold Model.resolveOptions
    dsimp only [bind, pure]
    exact resolveOptions_step_exceptKindIn _ _ opt.name
      (resolveSingleOption_pureNoEnv_noEofIo opt
        (match cliOpts.find? (fun p => p.1 == opt.name) with | some p => p.2 | none => []) validators)
      ih

private theorem resolveArgs_parseMany_noEofIo (arg : ArgSpec) (validators : CustomValidators)
    (xs : List String) :
    exceptKindIn (fun kd => kd ≠ .eof ∧ kd ≠ .ioError)
      (Model.resolveArgs.parseMany validators arg xs) := by
  induction xs with
  | nil => simp [Model.resolveArgs.parseMany, exceptKindIn]
  | cons s ss ih =>
    unfold Model.resolveArgs.parseMany
    dsimp only [bind, pure, Except.bind, Except.pure]
    cases hp : Model.parseOptValueWith arg.kind s validators with
    | error e => exact exceptKindIn_mk (by rw [parseOptValueWith_error hp]; decide)
    | ok _ =>
      dsimp only
      cases hs : Model.resolveArgs.parseMany validators arg ss with
      | error e => rw [hs] at ih; exact ih
      | ok _ => trivial

private theorem resolveArgs_go_noEofIo (validators : CustomValidators)
    (argSpecs : List ArgSpec) (rawPos : List String) :
    exceptKindIn (fun kd => kd ≠ .eof ∧ kd ≠ .ioError)
      (Model.resolveArgs.go validators argSpecs rawPos) := by
  induction argSpecs generalizing rawPos with
  | nil =>
    cases rawPos with
    | nil => trivial
    | cons _ _ => exact exceptKindIn_mk (by decide)
  | cons arg restArgs ih =>
    unfold Model.resolveArgs.go
    dsimp only
    split
    · split
      · split
        · exact exceptKindIn_mk (by decide)
        · cases arg.default with
          | none => exact ih []
          | some d =>
            dsimp only [bind, pure, Except.bind, Except.pure]
            cases hp : Model.parseOptValueWith arg.kind d validators with
            | error e => dsimp only; exact exceptKindIn_mk (by rw [parseOptValueWith_error hp]; decide)
            | ok _ =>
              dsimp only
              have ih0 := ih []
              cases hg : Model.resolveArgs.go validators restArgs [] with
              | error e => rw [hg] at ih0; exact ih0
              | ok _ => trivial
      · dsimp only [bind, pure, Except.bind, Except.pure]
        have hm := resolveArgs_parseMany_noEofIo arg validators rawPos
        cases hrp : Model.resolveArgs.parseMany validators arg rawPos with
        | error e => rw [hrp] at hm; dsimp only; exact hm
        | ok _ =>
          dsimp only
          have ih0 := ih []
          cases hg : Model.resolveArgs.go validators restArgs [] with
          | error e => rw [hg] at ih0; exact ih0
          | ok _ => trivial
    · cases rawPos with
      | cons s remPos =>
        dsimp only [bind, pure, Except.bind, Except.pure]
        cases hp : Model.parseOptValueWith arg.kind s validators with
        | error e => dsimp only; exact exceptKindIn_mk (by rw [parseOptValueWith_error hp]; decide)
        | ok _ =>
          dsimp only
          have ihr := ih remPos
          cases hg : Model.resolveArgs.go validators restArgs remPos with
          | error e => rw [hg] at ihr; exact ihr
          | ok _ => trivial
      | nil =>
        dsimp only
        split
        · exact exceptKindIn_mk (by decide)
        · cases arg.default with
          | none => exact ih []
          | some d =>
            dsimp only [bind, pure, Except.bind, Except.pure]
            cases hp : Model.parseOptValueWith arg.kind d validators with
            | error e => dsimp only; exact exceptKindIn_mk (by rw [parseOptValueWith_error hp]; decide)
            | ok _ =>
              dsimp only
              have ih0 := ih []
              cases hg : Model.resolveArgs.go validators restArgs [] with
              | error e => rw [hg] at ih0; exact ih0
              | ok _ => trivial

private theorem resolveArgs_noEofIo (argSpecs : List ArgSpec) (rawPos : List String)
    (validators : CustomValidators) :
    exceptKindIn (fun kd => kd ≠ .eof ∧ kd ≠ .ioError)
      (Model.resolveArgs argSpecs rawPos validators) :=
  resolveArgs_go_noEofIo validators argSpecs rawPos

private theorem parseWith_never_of (spec : CommandSpec) (args : List String)
    (validators : CustomValidators) :
    exceptKindIn (fun kd => kd ≠ .eof ∧ kd ≠ .ioError)
      (CmdLine.parseWith spec args validators) := by
  unfold CmdLine.parseWith defaultApi Internal.mkApiM Internal.parseWith
    Internal.parseWithEnvM
  dsimp only [pure, bind]
  split
  · exact exceptKindIn_mk (by decide)
  · have htok := parseTokens_noEofIo spec.name validators
      { curSpec := spec, effectiveVersion := spec.version } args
    cases hp : Internal.parseTokens spec.name validators
        { curSpec := spec, effectiveVersion := spec.version } args with
    | error e => rw [hp] at htok; exact htok
    | ok finalState =>
      dsimp only
      split
      · split <;> exact exceptKindIn_mk (by decide)
      · have hopts := resolveOptions_pureNoEnv_noEofIo
          (finalState.inheritedGlobals ++ finalState.curSpec.options)
          finalState.cliOpts validators
        cases ho : Model.resolveOptions (m := Id) Internal.pureNoEnvOps.getEnv
            (finalState.inheritedGlobals ++ finalState.curSpec.options) finalState.cliOpts validators with
        | error e => rw [ho] at hopts; exact hopts
        | ok _ =>
          dsimp only
          have hargs := resolveArgs_noEofIo finalState.curSpec.args finalState.rawPositionals validators
          cases ha : Model.resolveArgs finalState.curSpec.args finalState.rawPositionals validators with
          | error e => rw [ha] at hargs; exact hargs
          | ok _ => trivial

/-- Proof that `CmdLine.parse` never returns `.eof`. -/
theorem cmdline_parse_never_eof (spec : CommandSpec) (args : List String) :
    Core.NeverErrorKindPure CmdLineError.kind .eof (CmdLine.parse spec args) := by
  have h := parseWith_never_of spec args []
  change exceptKindIn (fun kd => kd ≠ .eof ∧ kd ≠ .ioError) (CmdLine.parse spec args) at h
  unfold Core.NeverErrorKindPure
  cases hr : CmdLine.parse spec args with
  | ok _ => trivial
  | error e => rw [hr] at h; exact h.1

/-- Proof that `CmdLine.parse` never returns `.ioError`. -/
theorem cmdline_parse_never_ioError (spec : CommandSpec) (args : List String) :
    Core.NeverErrorKindPure CmdLineError.kind .ioError (CmdLine.parse spec args) := by
  have h := parseWith_never_of spec args []
  change exceptKindIn (fun kd => kd ≠ .eof ∧ kd ≠ .ioError) (CmdLine.parse spec args) at h
  unfold Core.NeverErrorKindPure
  cases hr : CmdLine.parse spec args with
  | ok _ => trivial
  | error e => rw [hr] at h; exact h.2

/-- Proof that `CmdLine.parseWith` never returns `.eof`. -/
theorem cmdline_parseWith_never_eof (spec : CommandSpec) (args : List String)
    (validators : CustomValidators) :
    Core.NeverErrorKindPure CmdLineError.kind .eof (CmdLine.parseWith spec args validators) := by
  have h := parseWith_never_of spec args validators
  unfold Core.NeverErrorKindPure
  cases hr : CmdLine.parseWith spec args validators with
  | ok _ => trivial
  | error e => rw [hr] at h; exact h.1

/-- Proof that `CmdLine.parseWith` never returns `.ioError`. -/
theorem cmdline_parseWith_never_ioError (spec : CommandSpec) (args : List String)
    (validators : CustomValidators) :
    Core.NeverErrorKindPure CmdLineError.kind .ioError (CmdLine.parseWith spec args validators) := by
  have h := parseWith_never_of spec args validators
  unfold Core.NeverErrorKindPure
  cases hr : CmdLine.parseWith spec args validators with
  | ok _ => trivial
  | error e => rw [hr] at h; exact h.2

private def estOutCmdLineAllowed {α : Type} (P : CmdLineError → Prop)
    (out : EST.Out IO.Error IO.RealWorld (Except CmdLineError α)) : Prop :=
  match out with
  | EST.Out.error _ _ => True
  | EST.Out.ok (.ok _) _ => True
  | EST.Out.ok (.error e) _ => P e

private theorem io_bind_eq {α β : Type} (act : IO α) (k : α → IO β) (w : Void IO.RealWorld)
    {a : α} {w' : Void IO.RealWorld} (h : act w = EST.Out.ok a w') :
    (act >>= k) w = k a w' := by
  change EST.bind act k w = k a w'
  simp [EST.bind, h]

private theorem io_bind_err {α β : Type} (act : IO α) (k : α → IO β) (w : Void IO.RealWorld)
    {ex : IO.Error} {w' : Void IO.RealWorld} (h : act w = EST.Out.error ex w') :
    (act >>= k) w = EST.Out.error ex w' := by
  change EST.bind act k w = EST.Out.error ex w'
  simp [EST.bind, h]

private theorem io_pure_eq {α : Type} (a : α) (w : Void IO.RealWorld) :
    (pure a : IO α) w = EST.Out.ok a w := rfl

private theorem io_bind_allowed {α β : Type} (P : CmdLineError → Prop) (act : IO α)
    (k : α → IO (Except CmdLineError β)) (w : Void IO.RealWorld)
    (hk : ∀ a w', estOutCmdLineAllowed P (k a w')) :
    estOutCmdLineAllowed P ((act >>= k) w) := by
  cases ha : act w with
  | error ex w' =>
    rw [io_bind_err _ _ w ha]
    trivial
  | ok a w' =>
    rw [io_bind_eq _ _ w ha]
    exact hk a w'

private theorem defaultOps_getEnv_noThrow_noEof (key : String) (w : Void IO.RealWorld) :
    (∃ v w', defaultOps.getEnv key w = EST.Out.ok (Except.ok v) w') ∨
    (∃ e w', defaultOps.getEnv key w = EST.Out.ok (Except.error e) w' ∧ e.kind ≠ .eof) := by
  have hnf := EnvVars.Proofs.envvars_getEnv_never_notFound key w
  unfold Core.NeverErrorKindIO at hnf
  unfold defaultOps
  dsimp only
  cases hr : EnvVars.getEnv key w with
  | error _ _ => rw [hr] at hnf; exact False.elim hnf
  | ok res w' =>
    rw [io_bind_eq _ _ w hr]
    cases res with
    | ok v => exact Or.inl ⟨v, w', io_pure_eq _ _⟩
    | error err =>
      refine Or.inr ⟨{ kind := .ioError, message := err.message, target := err.key }, w', io_pure_eq _ _, ?_⟩
      dsimp only
      decide

private theorem resolveSingleOption_env_some (opt : OptSpec) (validators : CustomValidators)
    (s : String) (hs : s ≠ "") (w' : Void IO.RealWorld) :
    ∃ r w'_1,
      (match (Except.ok (some s) : Except CmdLineError (Option String)) with
        | Except.error e => (pure (Except.error e) : IO (Except CmdLineError (Option (List OptValue))))
        | Except.ok none => pure (Model.resolveOptDefault opt validators)
        | Except.ok (some "") => pure (Model.resolveOptDefault opt validators)
        | Except.ok (some s) =>
          match Model.parseOptValueWith opt.kind s validators with
          | Except.error e => pure (Except.error { kind := e.kind, message := e.message, target := some opt.name })
          | Except.ok v =>
            if (opt.repeatable && opt.kind == ValueKind.bool && v == OptValue.bool false) = true then
              pure (Except.ok none)
            else pure (Except.ok (some [v]))) w' = EST.Out.ok r w'_1 ∧
        exceptKindIn (fun kd => kd ≠ .eof) r := by
  have hm :
      (match (Except.ok (some s) : Except CmdLineError (Option String)) with
        | Except.error e => (pure (Except.error e) : IO (Except CmdLineError (Option (List OptValue))))
        | Except.ok none => pure (Model.resolveOptDefault opt validators)
        | Except.ok (some "") => pure (Model.resolveOptDefault opt validators)
        | Except.ok (some s) =>
          match Model.parseOptValueWith opt.kind s validators with
          | Except.error e => pure (Except.error { kind := e.kind, message := e.message, target := some opt.name })
          | Except.ok v =>
            if (opt.repeatable && opt.kind == ValueKind.bool && v == OptValue.bool false) = true then
              pure (Except.ok none)
            else pure (Except.ok (some [v]))) =
      (match Model.parseOptValueWith opt.kind s validators with
        | Except.error e =>
          (pure (Except.error { kind := e.kind, message := e.message, target := some opt.name }) :
            IO (Except CmdLineError (Option (List OptValue))))
        | Except.ok v =>
          if (opt.repeatable && opt.kind == ValueKind.bool && v == OptValue.bool false) = true then
            pure (Except.ok none)
          else pure (Except.ok (some [v]))) := by
    split
    · rename_i heq; cases heq
    · rename_i heq; cases heq
    · rename_i heq; cases heq; exact absurd rfl hs
    · rename_i _ heq; cases heq; rfl
  rw [congrFun hm w']
  cases hp : Model.parseOptValueWith opt.kind s validators with
  | error e =>
    refine ⟨_, w', io_pure_eq _ _, ?_⟩
    dsimp only [exceptKindIn]
    rw [parseOptValueWith_error hp]
    decide
  | ok v =>
    by_cases hrep : (opt.repeatable && opt.kind == ValueKind.bool && v == OptValue.bool false) = true
    · simp only [hrep, ↓reduceIte]
      exact ⟨_, w', io_pure_eq _ _, trivial⟩
    · simp only [hrep, Bool.false_eq_true, ↓reduceIte]
      exact ⟨_, w', io_pure_eq _ _, trivial⟩

private theorem resolveSingleOption_defaultOps_noEof (opt : OptSpec) (cliVals : List OptValue)
    (validators : CustomValidators) (w : Void IO.RealWorld) :
    ∃ r w', Model.resolveSingleOption defaultOps.getEnv opt cliVals validators w = EST.Out.ok r w' ∧
      exceptKindIn (fun kd => kd ≠ .eof) r := by
  unfold Model.resolveSingleOption
  by_cases hcli : !cliVals.isEmpty
  · simp only [hcli, ↓reduceIte]
    split
    · exact ⟨_, w, io_pure_eq _ _, exceptKindIn_mk (by decide)⟩
    · exact ⟨_, w, io_pure_eq _ _, trivial⟩
  · simp only [hcli, Bool.false_eq_true, ↓reduceIte]
    cases opt.envVar with
    | none =>
      refine ⟨_, w, io_pure_eq _ _, ?_⟩
      have h := resolveOptDefault_noEofIo opt validators
      cases hro : Model.resolveOptDefault opt validators with
      | ok _ => trivial
      | error e => rw [hro] at h; exact h.1
    | some envKey =>
      dsimp only
      rcases defaultOps_getEnv_noThrow_noEof envKey w with ⟨v, w', hv⟩ | ⟨e, w', he, hne⟩
      · rw [io_bind_eq _ _ w hv]
        cases v with
        | none =>
          refine ⟨_, w', io_pure_eq _ _, ?_⟩
          have h := resolveOptDefault_noEofIo opt validators
          cases hro : Model.resolveOptDefault opt validators with
          | ok _ => trivial
          | error e => rw [hro] at h; exact h.1
        | some s =>
          by_cases hs : s = ""
          · subst hs
            refine ⟨_, w', io_pure_eq _ _, ?_⟩
            have h := resolveOptDefault_noEofIo opt validators
            cases hro : Model.resolveOptDefault opt validators with
            | ok _ => trivial
            | error e => rw [hro] at h; exact h.1
          · exact resolveSingleOption_env_some opt validators s hs w'
      · rw [io_bind_eq _ _ w he]
        exact ⟨_, w', io_pure_eq _ _, hne⟩

private theorem resolveOptions_step_io (optName : String)
    (act1 : IO (Except CmdLineError (Option (List OptValue))))
    (act2 : IO (Except CmdLineError (List (String × List OptValue))))
    (w : Void IO.RealWorld)
    (h1 : ∃ r w', act1 w = EST.Out.ok r w' ∧ exceptKindIn (fun kd => kd ≠ .eof) r)
    (h2 : ∀ w1, ∃ r w', act2 w1 = EST.Out.ok r w' ∧ exceptKindIn (fun kd => kd ≠ .eof) r) :
    ∃ r w', (act1 >>= fun
      | Except.error e => (pure (Except.error e) : IO (Except CmdLineError (List (String × List OptValue))))
      | Except.ok resolved? =>
        act2 >>= fun
        | Except.error e => (pure (Except.error e) : IO (Except CmdLineError (List (String × List OptValue))))
        | Except.ok tail =>
          match resolved? with
          | none => pure (Except.ok tail)
          | some vals => pure (Except.ok ((optName, vals) :: tail))) w = EST.Out.ok r w' ∧
      exceptKindIn (fun kd => kd ≠ .eof) r := by
  rcases h1 with ⟨r1, w1, hr1, hk1⟩
  rw [io_bind_eq _ _ w hr1]
  cases r1 with
  | error e => exact ⟨_, w1, io_pure_eq _ _, hk1⟩
  | ok resolved? =>
    dsimp only
    rcases h2 w1 with ⟨r2, w2, hr2, hk2⟩
    rw [io_bind_eq _ _ w1 hr2]
    cases r2 with
    | error e => exact ⟨_, w2, io_pure_eq _ _, hk2⟩
    | ok tail => cases resolved? <;> exact ⟨_, w2, io_pure_eq _ _, trivial⟩

private theorem resolveOptions_defaultOps_noEof (visibleOpts : List OptSpec)
    (cliOpts : List (String × List OptValue)) (validators : CustomValidators)
    (w : Void IO.RealWorld) :
    ∃ r w', Model.resolveOptions defaultOps.getEnv visibleOpts cliOpts validators w = EST.Out.ok r w' ∧
      exceptKindIn (fun kd => kd ≠ .eof) r := by
  induction visibleOpts generalizing w with
  | nil => exact ⟨_, w, io_pure_eq _ _, trivial⟩
  | cons opt rest ih =>
    unfold Model.resolveOptions
    exact resolveOptions_step_io opt.name _ _ w
      (resolveSingleOption_defaultOps_noEof opt
        (match cliOpts.find? (fun p => p.1 == opt.name) with | some p => p.2 | none => [])
        validators w)
      ih

/-- Proof that `CmdLine.parseWithEnv` never returns `.eof`. -/
theorem cmdline_parseWithEnv_never_eof (spec : CommandSpec) (args : List String)
    (validators : CustomValidators) (w : Void IO.RealWorld) :
    Core.NeverErrorKindIO CmdLineError.kind .eof (CmdLine.parseWithEnv spec args validators) w := by
  unfold Core.NeverErrorKindIO CmdLine.parseWithEnv defaultApi Internal.mkApiM
    Internal.parseWithEnvM
  dsimp only
  cases hv : Model.isValidSpec spec
  · simp only [Bool.not_false, ↓reduceIte, io_pure_eq]
    decide
  · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    have htok := parseTokens_noEofIo spec.name validators
      { curSpec := spec, effectiveVersion := spec.version } args
    cases hp : Internal.parseTokens spec.name validators
        { curSpec := spec, effectiveVersion := spec.version } args with
    | error e =>
      rw [hp] at htok
      dsimp only
      rw [io_pure_eq]
      exact htok.1
    | ok finalState =>
      dsimp only
      by_cases hsub : finalState.curSpec.subcommands.isEmpty
      · simp only [hsub, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
        rcases resolveOptions_defaultOps_noEof
          (finalState.inheritedGlobals ++ finalState.curSpec.options)
          finalState.cliOpts validators w with ⟨ro, w1, hro, hko⟩
        rw [io_bind_eq _ _ w hro]
        cases ro with
        | error e => dsimp only; rw [io_pure_eq]; exact hko
        | ok resolvedOpts =>
          dsimp only
          have hargs := resolveArgs_noEofIo finalState.curSpec.args finalState.rawPositionals validators
          cases ha : Model.resolveArgs finalState.curSpec.args finalState.rawPositionals validators with
          | error e => rw [ha] at hargs; dsimp only; rw [io_pure_eq]; exact hargs.1
          | ok _ => dsimp only; rw [io_pure_eq]; trivial
      · simp only [hsub, Bool.not_false, ↓reduceIte]
        cases hrp : finalState.rawPositionals.isEmpty <;>
          simp [io_pure_eq]

private theorem findSubcommandPath_kind (spec : CommandSpec) (path : List String) :
    exceptKindIn (fun kd => kd = .unknownSubcommand) (Model.findSubcommandPath spec path) := by
  unfold Model.findSubcommandPath
  have hgo : ∀ (globals : List OptSpec) (ver : Option String) (cur : CommandSpec) (p : List String),
      exceptKindIn (fun kd => kd = .unknownSubcommand)
        (Model.findSubcommandPath.go globals ver cur p) := by
    intro globals ver cur p
    induction p generalizing globals ver cur with
    | nil => simp [Model.findSubcommandPath.go, exceptKindIn]
    | cons name rest ih =>
      unfold Model.findSubcommandPath.go
      cases cur.subcommands.find? (fun s => s.name == name) with
      | none => rfl
      | some sub => exact ih _ _ sub
  exact hgo [] none spec path

private theorem renderHelp_kind (rootSpec : CommandSpec) (subcommandPath : List String) :
    exceptKindIn (fun kd => kd = .invalidSpec ∨ kd = .unknownSubcommand)
      (CmdLine.renderHelp rootSpec subcommandPath) := by
  unfold CmdLine.renderHelp defaultApi Internal.mkApiM Internal.renderHelp
  dsimp only
  split
  · exact Or.inl rfl
  · refine exceptKindIn_bind _ _ _ ?_ fun _ => trivial
    have h := findSubcommandPath_kind rootSpec subcommandPath
    cases hf : Model.findSubcommandPath rootSpec subcommandPath with
    | error e => rw [hf] at h; exact Or.inr h
    | ok _ => trivial

private theorem renderHelp_never_of (rootSpec : CommandSpec) (subcommandPath : List String)
    (k : CmdLineErrorKind) (hk1 : k ≠ .invalidSpec) (hk2 : k ≠ .unknownSubcommand) :
    Core.NeverErrorKindPure CmdLineError.kind k (CmdLine.renderHelp rootSpec subcommandPath) := by
  have h := renderHelp_kind rootSpec subcommandPath
  unfold Core.NeverErrorKindPure
  cases hr : CmdLine.renderHelp rootSpec subcommandPath with
  | ok _ => trivial
  | error e =>
    rw [hr] at h
    rcases h with he | he
    · exact fun heq => hk1 (heq ▸ he)
    · exact fun heq => hk2 (heq ▸ he)

/-- Proof that `CmdLine.renderHelp` never returns `.helpRequested`. -/
theorem cmdline_renderHelp_never_helpRequested (rootSpec : CommandSpec) (subcommandPath : List String) :
    Core.NeverErrorKindPure CmdLineError.kind .helpRequested (CmdLine.renderHelp rootSpec subcommandPath) :=
  renderHelp_never_of rootSpec subcommandPath .helpRequested (by decide) (by decide)

/-- Proof that `CmdLine.renderHelp` never returns `.versionRequested`. -/
theorem cmdline_renderHelp_never_versionRequested (rootSpec : CommandSpec) (subcommandPath : List String) :
    Core.NeverErrorKindPure CmdLineError.kind .versionRequested (CmdLine.renderHelp rootSpec subcommandPath) :=
  renderHelp_never_of rootSpec subcommandPath .versionRequested (by decide) (by decide)

/-- Proof that `CmdLine.renderHelp` never returns `.unknownOption`. -/
theorem cmdline_renderHelp_never_unknownOption (rootSpec : CommandSpec) (subcommandPath : List String) :
    Core.NeverErrorKindPure CmdLineError.kind .unknownOption (CmdLine.renderHelp rootSpec subcommandPath) :=
  renderHelp_never_of rootSpec subcommandPath .unknownOption (by decide) (by decide)

/-- Proof that `CmdLine.renderHelp` never returns `.missingOption`. -/
theorem cmdline_renderHelp_never_missingOption (rootSpec : CommandSpec) (subcommandPath : List String) :
    Core.NeverErrorKindPure CmdLineError.kind .missingOption (CmdLine.renderHelp rootSpec subcommandPath) :=
  renderHelp_never_of rootSpec subcommandPath .missingOption (by decide) (by decide)

/-- Proof that `CmdLine.renderHelp` never returns `.missingArgument`. -/
theorem cmdline_renderHelp_never_missingArgument (rootSpec : CommandSpec) (subcommandPath : List String) :
    Core.NeverErrorKindPure CmdLineError.kind .missingArgument (CmdLine.renderHelp rootSpec subcommandPath) :=
  renderHelp_never_of rootSpec subcommandPath .missingArgument (by decide) (by decide)

/-- Proof that `CmdLine.renderHelp` never returns `.unexpectedArgument`. -/
theorem cmdline_renderHelp_never_unexpectedArgument (rootSpec : CommandSpec) (subcommandPath : List String) :
    Core.NeverErrorKindPure CmdLineError.kind .unexpectedArgument (CmdLine.renderHelp rootSpec subcommandPath) :=
  renderHelp_never_of rootSpec subcommandPath .unexpectedArgument (by decide) (by decide)

/-- Proof that `CmdLine.renderHelp` never returns `.invalidValue`. -/
theorem cmdline_renderHelp_never_invalidValue (rootSpec : CommandSpec) (subcommandPath : List String) :
    Core.NeverErrorKindPure CmdLineError.kind .invalidValue (CmdLine.renderHelp rootSpec subcommandPath) :=
  renderHelp_never_of rootSpec subcommandPath .invalidValue (by decide) (by decide)

/-- Proof that `CmdLine.renderHelp` never returns `.eof`. -/
theorem cmdline_renderHelp_never_eof (rootSpec : CommandSpec) (subcommandPath : List String) :
    Core.NeverErrorKindPure CmdLineError.kind .eof (CmdLine.renderHelp rootSpec subcommandPath) :=
  renderHelp_never_of rootSpec subcommandPath .eof (by decide) (by decide)

/-- Proof that `CmdLine.renderHelp` never returns `.ioError`. -/
theorem cmdline_renderHelp_never_ioError (rootSpec : CommandSpec) (subcommandPath : List String) :
    Core.NeverErrorKindPure CmdLineError.kind .ioError (CmdLine.renderHelp rootSpec subcommandPath) :=
  renderHelp_never_of rootSpec subcommandPath .ioError (by decide) (by decide)

private theorem renderValueList_kind (opt : OptSpec) (vs : List OptValue) :
    exceptKindIn (fun kd => kd = .invalidSpec ∨ kd = .invalidValue)
      (Model.renderSingleOpt.renderValueList opt vs) := by
  induction vs with
  | nil => simp [Model.renderSingleOpt.renderValueList, exceptKindIn]
  | cons v rest ih =>
    unfold Model.renderSingleOpt.renderValueList
    dsimp only [bind, pure, Except.bind, Except.pure]
    split
    · exact exceptKindIn_mk (Or.inr rfl)
    · cases opt.long with
      | some _ =>
        dsimp only
        split
        · cases hr : Model.renderSingleOpt.renderValueList opt rest with
          | error _ => rw [hr] at ih; exact ih
          | ok _ => trivial
        · cases hr : Model.renderSingleOpt.renderValueList opt rest with
          | error _ => rw [hr] at ih; exact ih
          | ok _ => trivial
      | none =>
        dsimp only
        cases opt.short with
        | some _ =>
          dsimp only
          split
          · cases hr : Model.renderSingleOpt.renderValueList opt rest with
            | error _ => rw [hr] at ih; exact ih
            | ok _ => trivial
          · cases hr : Model.renderSingleOpt.renderValueList opt rest with
            | error _ => rw [hr] at ih; exact ih
            | ok _ => trivial
        | none => exact exceptKindIn_mk (Or.inl rfl)

private theorem renderSingleOpt_kind (opt : OptSpec) (vals : List OptValue) :
    exceptKindIn (fun kd => kd = .invalidSpec ∨ kd = .invalidValue)
      (Model.renderSingleOpt opt vals) := by
  unfold Model.renderSingleOpt
  split
  · trivial
  · split
    · cases vals with
      | nil => exact exceptKindIn_mk (P := fun kd => kd = .invalidSpec ∨ kd = .invalidValue) (Or.inr rfl)
      | cons v rest =>
        cases rest with
        | cons _ _ =>
          split
          · rename_i heq; cases heq
          · rename_i heq; cases heq
          · exact exceptKindIn_mk (P := fun kd => kd = .invalidSpec ∨ kd = .invalidValue) (Or.inr rfl)
        | nil =>
          cases v with
          | bool b =>
            cases b
            · cases opt.long with
              | some _ => trivial
              | none =>
                dsimp only
                cases opt.default with
                | none => simp [exceptKindIn]
                | some _ =>
                  dsimp only
                  split
                  · exact exceptKindIn_mk (P := fun kd => kd = .invalidSpec ∨ kd = .invalidValue) (Or.inr rfl)
                  · trivial
            · cases opt.long with
              | some _ => trivial
              | none =>
                cases opt.short with
                | none => exact exceptKindIn_mk (Or.inl rfl)
                | some _ => trivial
          | string _ => exact exceptKindIn_mk (Or.inr rfl)
          | nat _ => exact exceptKindIn_mk (Or.inr rfl)
          | int _ => exact exceptKindIn_mk (Or.inr rfl)
          | choice _ => exact exceptKindIn_mk (Or.inr rfl)
          | custom _ => exact exceptKindIn_mk (Or.inr rfl)
    · exact renderValueList_kind opt vals

private theorem renderOpts_step_kind (r1 r2 : Except CmdLineError (List String))
    (h1 : exceptKindIn (fun kd => kd = .invalidSpec ∨ kd = .invalidValue) r1)
    (h2 : exceptKindIn (fun kd => kd = .invalidSpec ∨ kd = .unknownSubcommand ∨ kd = .missingArgument ∨ kd = .invalidValue) r2) :
    exceptKindIn (fun kd => kd = .invalidSpec ∨ kd = .unknownSubcommand ∨ kd = .missingArgument ∨ kd = .invalidValue)
      (do let v ← r1; let v_1 ← r2; return v ++ v_1) := by
  dsimp only [bind, pure, Except.bind, Except.pure]
  cases r1 with
  | error e => rcases h1 with a | b; exact Or.inl a; exact Or.inr (Or.inr (Or.inr b))
  | ok _ => cases r2 with | error _ => exact h2 | ok _ => trivial

private theorem renderArgs_kind (spec : CommandSpec) (parsed : ParsedCmd) :
    exceptKindIn (fun kd => kd = .invalidSpec ∨ kd = .unknownSubcommand ∨ kd = .missingArgument ∨ kd = .invalidValue)
      (CmdLine.renderArgs spec parsed) := by
  unfold CmdLine.renderArgs defaultApi Internal.mkApiM Model.renderArgs
  dsimp only [bind, pure, Except.bind, Except.pure]
  split
  · exact exceptKindIn_mk (Or.inl rfl)
  · have h := findSubcommandPath_kind spec parsed.subcommandPath
    cases hf : Model.findSubcommandPath spec parsed.subcommandPath with
    | error e => rw [hf] at h; exact Or.inr (Or.inl h)
    | ok p =>
      dsimp only
      split
      · exact exceptKindIn_mk (Or.inr (Or.inr (Or.inl rfl)))
      · have hro : ∀ (opts : List OptSpec),
            exceptKindIn (fun kd => kd = .invalidSpec ∨ kd = .unknownSubcommand ∨ kd = .missingArgument ∨ kd = .invalidValue)
              (Model.renderArgs.renderOpts parsed opts) := by
          intro opts
          induction opts with
          | nil => simp [Model.renderArgs.renderOpts, exceptKindIn]
          | cons o rs ih =>
            unfold Model.renderArgs.renderOpts
            exact renderOpts_step_kind _ _
              (renderSingleOpt_kind o
                (match parsed.options.find? (fun p => p.1 == o.name) with | some p => p.2 | none => []))
              ih
        cases hres : Model.renderArgs.renderOpts parsed (p.1 ++ p.2.2.options) with
        | error e => have hro' := hro (p.1 ++ p.2.2.options); rw [hres] at hro'; exact hro'
        | ok _ => trivial

private theorem renderArgs_never_of (spec : CommandSpec) (parsed : ParsedCmd)
    (k : CmdLineErrorKind)
    (hk1 : k ≠ .invalidSpec) (hk2 : k ≠ .unknownSubcommand)
    (hk3 : k ≠ .missingArgument) (hk4 : k ≠ .invalidValue) :
    Core.NeverErrorKindPure CmdLineError.kind k (CmdLine.renderArgs spec parsed) := by
  have h := renderArgs_kind spec parsed
  unfold Core.NeverErrorKindPure
  cases hr : CmdLine.renderArgs spec parsed with
  | ok _ => trivial
  | error e =>
    rw [hr] at h
    rcases h with he | he | he | he
    · exact fun heq => hk1 (heq ▸ he)
    · exact fun heq => hk2 (heq ▸ he)
    · exact fun heq => hk3 (heq ▸ he)
    · exact fun heq => hk4 (heq ▸ he)

/-- Proof that `CmdLine.renderArgs` never returns `.helpRequested`. -/
theorem cmdline_renderArgs_never_helpRequested (spec : CommandSpec) (parsed : ParsedCmd) :
    Core.NeverErrorKindPure CmdLineError.kind .helpRequested (CmdLine.renderArgs spec parsed) :=
  renderArgs_never_of spec parsed .helpRequested (by decide) (by decide) (by decide) (by decide)

/-- Proof that `CmdLine.renderArgs` never returns `.versionRequested`. -/
theorem cmdline_renderArgs_never_versionRequested (spec : CommandSpec) (parsed : ParsedCmd) :
    Core.NeverErrorKindPure CmdLineError.kind .versionRequested (CmdLine.renderArgs spec parsed) :=
  renderArgs_never_of spec parsed .versionRequested (by decide) (by decide) (by decide) (by decide)

/-- Proof that `CmdLine.renderArgs` never returns `.unknownOption`. -/
theorem cmdline_renderArgs_never_unknownOption (spec : CommandSpec) (parsed : ParsedCmd) :
    Core.NeverErrorKindPure CmdLineError.kind .unknownOption (CmdLine.renderArgs spec parsed) :=
  renderArgs_never_of spec parsed .unknownOption (by decide) (by decide) (by decide) (by decide)

/-- Proof that `CmdLine.renderArgs` never returns `.missingOption`. -/
theorem cmdline_renderArgs_never_missingOption (spec : CommandSpec) (parsed : ParsedCmd) :
    Core.NeverErrorKindPure CmdLineError.kind .missingOption (CmdLine.renderArgs spec parsed) :=
  renderArgs_never_of spec parsed .missingOption (by decide) (by decide) (by decide) (by decide)

/-- Proof that `CmdLine.renderArgs` never returns `.unexpectedArgument`. -/
theorem cmdline_renderArgs_never_unexpectedArgument (spec : CommandSpec) (parsed : ParsedCmd) :
    Core.NeverErrorKindPure CmdLineError.kind .unexpectedArgument (CmdLine.renderArgs spec parsed) :=
  renderArgs_never_of spec parsed .unexpectedArgument (by decide) (by decide) (by decide) (by decide)

/-- Proof that `CmdLine.renderArgs` never returns `.eof`. -/
theorem cmdline_renderArgs_never_eof (spec : CommandSpec) (parsed : ParsedCmd) :
    Core.NeverErrorKindPure CmdLineError.kind .eof (CmdLine.renderArgs spec parsed) :=
  renderArgs_never_of spec parsed .eof (by decide) (by decide) (by decide) (by decide)

/-- Proof that `CmdLine.renderArgs` never returns `.ioError`. -/
theorem cmdline_renderArgs_never_ioError (spec : CommandSpec) (parsed : ParsedCmd) :
    Core.NeverErrorKindPure CmdLineError.kind .ioError (CmdLine.renderArgs spec parsed) :=
  renderArgs_never_of spec parsed .ioError (by decide) (by decide) (by decide) (by decide)

private theorem catchIo_never_of {α : Type} (k : CmdLineErrorKind) (hk : k ≠ .ioError)
    (act : IO (Except CmdLineError α))
    (hact : ∀ w', estOutCmdLineAllowed (fun e => e.kind ≠ k) (act w'))
    (w : Void IO.RealWorld) :
    Core.NeverErrorKindIO CmdLineError.kind k
      (BaseIO.toEIO (EIO.catchExceptions act fun err =>
        let msg := err.toString
        pure (.error { kind := .ioError, message := if msg.isEmpty then "stdio I/O error" else msg }))) w := by
  unfold Core.NeverErrorKindIO BaseIO.toEIO EIO.catchExceptions
  have h := hact w
  cases ha : act w with
  | error ex s =>
    dsimp only [pure, EST.pure, EStateM.pure]
    exact hk.symm
  | ok res s =>
    rw [ha] at h
    cases res with
    | ok _ => trivial
    | error e => exact h

private theorem internal_promptLine_allowed (ops : CliOps) (prompt : String) (default : Option String)
    (k : CmdLineErrorKind) (hk : k ≠ .eof) (w : Void IO.RealWorld) :
    estOutCmdLineAllowed (fun e => e.kind ≠ k) (Internal.promptLine ops prompt default w) := by
  unfold Internal.promptLine
  refine io_bind_allowed _ _ _ w fun _ w1 => ?_
  refine io_bind_allowed _ _ _ w1 fun line? w2 => ?_
  cases line? with
  | none => dsimp only; rw [io_pure_eq]; exact hk.symm
  | some _ =>
    dsimp only
    split
    · cases default <;> dsimp only <;> rw [io_pure_eq] <;> trivial
    · rw [io_pure_eq]; trivial

private theorem internal_confirm_allowed (ops : CliOps) (prompt : String) (default : Option Bool)
    (maxAttempts : Nat) (k : CmdLineErrorKind) (hk1 : k ≠ .eof) (hk2 : k ≠ .invalidValue)
    (w : Void IO.RealWorld) :
    estOutCmdLineAllowed (fun e => e.kind ≠ k) (Internal.confirm ops prompt default maxAttempts w) := by
  induction maxAttempts generalizing w with
  | zero =>
    unfold Internal.confirm
    rw [io_pure_eq]
    exact hk2.symm
  | succ n ih =>
    unfold Internal.confirm
    refine io_bind_allowed _ _ _ w fun _ w1 => ?_
    refine io_bind_allowed _ _ _ w1 fun line? w2 => ?_
    cases line? with
    | none => dsimp only; rw [io_pure_eq]; exact hk1.symm
    | some line =>
      dsimp only
      split
      · cases default with
        | some _ => dsimp only; rw [io_pure_eq]; trivial
        | none =>
          cases n with
          | zero => dsimp only; rw [io_pure_eq]; exact hk2.symm
          | succ m => exact io_bind_allowed _ _ _ w2 fun _ w3 => ih w3
      · split
        · rw [io_pure_eq]; trivial
        · split
          · rw [io_pure_eq]; trivial
          · cases n with
            | zero => dsimp only; rw [io_pure_eq]; exact hk2.symm
            | succ m => exact io_bind_allowed _ _ _ w2 fun _ w3 => ih w3

private theorem promptLine_never_of (prompt : String) (default : Option String)
    (k : CmdLineErrorKind) (hk1 : k ≠ .eof) (hk2 : k ≠ .ioError) (w : Void IO.RealWorld) :
    Core.NeverErrorKindIO CmdLineError.kind k (CmdLine.promptLine prompt default) w := by
  unfold CmdLine.promptLine defaultApi
  dsimp only
  apply catchIo_never_of k hk2
  intro w'
  exact internal_promptLine_allowed defaultOps prompt default k hk1 w'

private theorem confirm_never_of (prompt : String) (default : Option Bool) (maxAttempts : Nat)
    (k : CmdLineErrorKind) (hk1 : k ≠ .eof) (hk2 : k ≠ .invalidValue) (hk3 : k ≠ .ioError)
    (w : Void IO.RealWorld) :
    Core.NeverErrorKindIO CmdLineError.kind k (CmdLine.confirm prompt default maxAttempts) w := by
  unfold CmdLine.confirm defaultApi
  dsimp only
  apply catchIo_never_of k hk3
  intro w'
  exact internal_confirm_allowed defaultOps prompt default maxAttempts k hk1 hk2 w'

/-- Proof that `CmdLine.promptLine` never returns `.helpRequested`. -/
theorem cmdline_promptLine_never_helpRequested (prompt : String) (default : Option String) (w : Void IO.RealWorld) :
    Core.NeverErrorKindIO CmdLineError.kind .helpRequested (CmdLine.promptLine prompt default) w :=
  promptLine_never_of prompt default .helpRequested (by decide) (by decide) w

/-- Proof that `CmdLine.promptLine` never returns `.versionRequested`. -/
theorem cmdline_promptLine_never_versionRequested (prompt : String) (default : Option String) (w : Void IO.RealWorld) :
    Core.NeverErrorKindIO CmdLineError.kind .versionRequested (CmdLine.promptLine prompt default) w :=
  promptLine_never_of prompt default .versionRequested (by decide) (by decide) w

/-- Proof that `CmdLine.promptLine` never returns `.unknownOption`. -/
theorem cmdline_promptLine_never_unknownOption (prompt : String) (default : Option String) (w : Void IO.RealWorld) :
    Core.NeverErrorKindIO CmdLineError.kind .unknownOption (CmdLine.promptLine prompt default) w :=
  promptLine_never_of prompt default .unknownOption (by decide) (by decide) w

/-- Proof that `CmdLine.promptLine` never returns `.missingOption`. -/
theorem cmdline_promptLine_never_missingOption (prompt : String) (default : Option String) (w : Void IO.RealWorld) :
    Core.NeverErrorKindIO CmdLineError.kind .missingOption (CmdLine.promptLine prompt default) w :=
  promptLine_never_of prompt default .missingOption (by decide) (by decide) w

/-- Proof that `CmdLine.promptLine` never returns `.missingArgument`. -/
theorem cmdline_promptLine_never_missingArgument (prompt : String) (default : Option String) (w : Void IO.RealWorld) :
    Core.NeverErrorKindIO CmdLineError.kind .missingArgument (CmdLine.promptLine prompt default) w :=
  promptLine_never_of prompt default .missingArgument (by decide) (by decide) w

/-- Proof that `CmdLine.promptLine` never returns `.unexpectedArgument`. -/
theorem cmdline_promptLine_never_unexpectedArgument (prompt : String) (default : Option String) (w : Void IO.RealWorld) :
    Core.NeverErrorKindIO CmdLineError.kind .unexpectedArgument (CmdLine.promptLine prompt default) w :=
  promptLine_never_of prompt default .unexpectedArgument (by decide) (by decide) w

/-- Proof that `CmdLine.promptLine` never returns `.invalidValue`. -/
theorem cmdline_promptLine_never_invalidValue (prompt : String) (default : Option String) (w : Void IO.RealWorld) :
    Core.NeverErrorKindIO CmdLineError.kind .invalidValue (CmdLine.promptLine prompt default) w :=
  promptLine_never_of prompt default .invalidValue (by decide) (by decide) w

/-- Proof that `CmdLine.promptLine` never returns `.unknownSubcommand`. -/
theorem cmdline_promptLine_never_unknownSubcommand (prompt : String) (default : Option String) (w : Void IO.RealWorld) :
    Core.NeverErrorKindIO CmdLineError.kind .unknownSubcommand (CmdLine.promptLine prompt default) w :=
  promptLine_never_of prompt default .unknownSubcommand (by decide) (by decide) w

/-- Proof that `CmdLine.promptLine` never returns `.invalidSpec`. -/
theorem cmdline_promptLine_never_invalidSpec (prompt : String) (default : Option String) (w : Void IO.RealWorld) :
    Core.NeverErrorKindIO CmdLineError.kind .invalidSpec (CmdLine.promptLine prompt default) w :=
  promptLine_never_of prompt default .invalidSpec (by decide) (by decide) w

/-- Proof that `CmdLine.confirm` never returns `.helpRequested`. -/
theorem cmdline_confirm_never_helpRequested (prompt : String) (default : Option Bool) (maxAttempts : Nat) (w : Void IO.RealWorld) :
    Core.NeverErrorKindIO CmdLineError.kind .helpRequested (CmdLine.confirm prompt default maxAttempts) w :=
  confirm_never_of prompt default maxAttempts .helpRequested (by decide) (by decide) (by decide) w

/-- Proof that `CmdLine.confirm` never returns `.versionRequested`. -/
theorem cmdline_confirm_never_versionRequested (prompt : String) (default : Option Bool) (maxAttempts : Nat) (w : Void IO.RealWorld) :
    Core.NeverErrorKindIO CmdLineError.kind .versionRequested (CmdLine.confirm prompt default maxAttempts) w :=
  confirm_never_of prompt default maxAttempts .versionRequested (by decide) (by decide) (by decide) w

/-- Proof that `CmdLine.confirm` never returns `.unknownOption`. -/
theorem cmdline_confirm_never_unknownOption (prompt : String) (default : Option Bool) (maxAttempts : Nat) (w : Void IO.RealWorld) :
    Core.NeverErrorKindIO CmdLineError.kind .unknownOption (CmdLine.confirm prompt default maxAttempts) w :=
  confirm_never_of prompt default maxAttempts .unknownOption (by decide) (by decide) (by decide) w

/-- Proof that `CmdLine.confirm` never returns `.missingOption`. -/
theorem cmdline_confirm_never_missingOption (prompt : String) (default : Option Bool) (maxAttempts : Nat) (w : Void IO.RealWorld) :
    Core.NeverErrorKindIO CmdLineError.kind .missingOption (CmdLine.confirm prompt default maxAttempts) w :=
  confirm_never_of prompt default maxAttempts .missingOption (by decide) (by decide) (by decide) w

/-- Proof that `CmdLine.confirm` never returns `.missingArgument`. -/
theorem cmdline_confirm_never_missingArgument (prompt : String) (default : Option Bool) (maxAttempts : Nat) (w : Void IO.RealWorld) :
    Core.NeverErrorKindIO CmdLineError.kind .missingArgument (CmdLine.confirm prompt default maxAttempts) w :=
  confirm_never_of prompt default maxAttempts .missingArgument (by decide) (by decide) (by decide) w

/-- Proof that `CmdLine.confirm` never returns `.unexpectedArgument`. -/
theorem cmdline_confirm_never_unexpectedArgument (prompt : String) (default : Option Bool) (maxAttempts : Nat) (w : Void IO.RealWorld) :
    Core.NeverErrorKindIO CmdLineError.kind .unexpectedArgument (CmdLine.confirm prompt default maxAttempts) w :=
  confirm_never_of prompt default maxAttempts .unexpectedArgument (by decide) (by decide) (by decide) w

/-- Proof that `CmdLine.confirm` never returns `.unknownSubcommand`. -/
theorem cmdline_confirm_never_unknownSubcommand (prompt : String) (default : Option Bool) (maxAttempts : Nat) (w : Void IO.RealWorld) :
    Core.NeverErrorKindIO CmdLineError.kind .unknownSubcommand (CmdLine.confirm prompt default maxAttempts) w :=
  confirm_never_of prompt default maxAttempts .unknownSubcommand (by decide) (by decide) (by decide) w

/-- Proof that `CmdLine.confirm` never returns `.invalidSpec`. -/
theorem cmdline_confirm_never_invalidSpec (prompt : String) (default : Option Bool) (maxAttempts : Nat) (w : Void IO.RealWorld) :
    Core.NeverErrorKindIO CmdLineError.kind .invalidSpec (CmdLine.confirm prompt default maxAttempts) w :=
  confirm_never_of prompt default maxAttempts .invalidSpec (by decide) (by decide) (by decide) w

/-- Proof that `parseWithEnv` under `pureIdCliOps` agrees universally with `parseWith`. -/
theorem allPass_parseWithEnv_unsetEnvMatchesParseWith :
    Core.AllPass (test_cmdline_parseWithEnv_unsetEnvMatchesParseWith defaultApi Internal.mkApiM) := by
  intro spec args validators
  exact ⟨rfl, trivial⟩

end LeanSwe.CmdLine.Proofs
