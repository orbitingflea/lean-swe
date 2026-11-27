import Core.NondetTest
import Core.Assumptions
import LeanSwe.CmdLine.Types
import LeanSweProofs.CmdLine.Model
import LeanSweProofs.CmdLine.SpecTests

/-! Compile-time negative specification mutants for `LeanSwe.CmdLine`. -/

namespace LeanSwe.CmdLine

open Core (NondetTest AssumptionObligation ErrorObligation)
open Core.NondetTest

private def stubCmdLineApiM {m : Type → Type} [Monad m] : CmdLineApiM m :=
  { isValidSpec := fun _ => true
    parse := fun _ _ => .ok {}
    parseWith := fun _ _ _ => .ok {}
    parseWithEnv := fun _ _ _ => pure (.ok {})
    renderHelp := fun _ _ => .ok ""
    renderVersion := fun _ _ => ""
    renderArgs := fun _ _ => .ok []
    promptLine := fun _ _ => pure (.ok "")
    confirm := fun _ _ _ => pure (.ok true)
    runCli := fun _ _ _ => pure 0
    runCliWith := fun _ _ _ _ => pure 0 }

example : ¬ Core.AllPass (test_cmdline_validSpec_rejectsFlagCollisions stubCmdLineApiM) := by
  intro h
  simp [Core.AllPass, test_cmdline_validSpec_rejectsFlagCollisions, stubCmdLineApiM, bind, assert] at h

example : ¬ Core.AllPass (test_cmdline_validSpec_rejectsStructuralAndEnvErrors stubCmdLineApiM) := by
  intro h
  simp [Core.AllPass, test_cmdline_validSpec_rejectsStructuralAndEnvErrors, stubCmdLineApiM, bind, assert] at h

example : ¬ Core.AllPass (test_cmdline_validSpec_shortOptOutAndParseRejectsInvalid stubCmdLineApiM) := by
  intro h
  simp [Core.AllPass, test_cmdline_validSpec_shortOptOutAndParseRejectsInvalid, stubCmdLineApiM, bind, assert] at h

example : ¬ Core.AllPass (test_cmdline_parse_shortBundlesAndValues stubCmdLineApiM) := by
  intro h
  simp [Core.AllPass, test_cmdline_parse_shortBundlesAndValues, stubCmdLineApiM, ParsedCmd.hasFlag,
    ParsedCmd.getCount, ParsedCmd.lookupValues, bind, assert] at h

example : ¬ Core.AllPass (test_cmdline_parse_shortLeftToRightHelpPrecedence stubCmdLineApiM) := by
  intro h
  simp [Core.AllPass, test_cmdline_parse_shortLeftToRightHelpPrecedence, stubCmdLineApiM, ParsedCmd.getString,
    ParsedCmd.lookupValues, bind, assert] at h

example : ¬ Core.AllPass (test_cmdline_parse_duplicatesNegationAndSpaceBool stubCmdLineApiM) := by
  intro h
  simp [Core.AllPass, test_cmdline_parse_duplicatesNegationAndSpaceBool, stubCmdLineApiM, bind, assert] at h

example : ¬ Core.AllPass (test_cmdline_parse_negativeNumbersAndDashDash stubCmdLineApiM) := by
  intro h
  simp [Core.AllPass, test_cmdline_parse_negativeNumbersAndDashDash, stubCmdLineApiM, ParsedCmd.getInt,
    ParsedCmd.lookupValues, bind, assert] at h

example : ¬ Core.AllPass (test_cmdline_parse_subcommandsAndInheritedGlobals stubCmdLineApiM) := by
  intro h
  simp [Core.AllPass, test_cmdline_parse_subcommandsAndInheritedGlobals, stubCmdLineApiM, ParsedCmd.getString,
    ParsedCmd.lookupValues, bind, assert] at h

example : ¬ Core.AllPass (test_cmdline_parse_typoSuggestions stubCmdLineApiM) := by
  intro h
  simp [Core.AllPass, test_cmdline_parse_typoSuggestions, stubCmdLineApiM, bind, assert] at h

example : ¬ Core.AllPass (test_cmdline_parseWith_customValidatorAndDecoder stubCmdLineApiM) := by
  intro h
  simp [Core.AllPass, test_cmdline_parseWith_customValidatorAndDecoder, stubCmdLineApiM, bind, assert] at h

example : ¬ Core.AllPass (test_cmdline_env_precedenceAndErrorPropagation (fun _ => stubCmdLineApiM)) := by
  intro h
  simp [Core.AllPass, test_cmdline_env_precedenceAndErrorPropagation, stubCmdLineApiM, StateT.run,
    StateT.pure, pure, ParsedCmd.getNat, ParsedCmd.lookupValues, bind, assert] at h

example : ¬ Core.AllPass (test_cmdline_renderArgs_roundTripEdgeCases stubCmdLineApiM) := by
  intro h
  simp [Core.AllPass, test_cmdline_renderArgs_roundTripEdgeCases, stubCmdLineApiM, bind, assert] at h

example : ¬ Core.AllPass (test_cmdline_renderArgs_universalRoundTrip
    { stubCmdLineApiM with
      isValidSpec := Model.isValidSpec
      parse := fun _ xs => .ok { rawPositionals := xs }
      renderArgs := fun _ _ => .ok ["wrong"] }) := by
  intro h
  have h0 := h { name := "app" } [] rfl
  simp [assert] at h0

example : ¬ Core.AllPass (test_cmdline_runCli_routingAndExitCodes (fun _ => stubCmdLineApiM)) := by
  intro h
  simp [Core.AllPass, test_cmdline_runCli_routingAndExitCodes, stubCmdLineApiM, StateT.run,
    StateT.pure, pure, bind, assert] at h

example : ¬ Core.AllPass (test_cmdline_interactive_promptAndConfirm (fun _ => stubCmdLineApiM)) := by
  intro h
  simp [Core.AllPass, test_cmdline_interactive_promptAndConfirm, stubCmdLineApiM, StateT.run,
    StateT.pure, pure, bind, assert] at h

example : ¬ Core.AllPass (test_cmdline_parse_helpAndVersionRouting stubCmdLineApiM) := by
  intro h
  simp [Core.AllPass, test_cmdline_parse_helpAndVersionRouting, stubCmdLineApiM, bind, assert] at h

example : ¬ Core.AllPass (test_cmdline_parse_positionalArgsAndErrors stubCmdLineApiM) := by
  intro h
  simp [Core.AllPass, test_cmdline_parse_positionalArgsAndErrors, stubCmdLineApiM,
    ParsedCmd.getNat, ParsedCmd.lookupValues, bind, assert] at h

example : ¬ Core.AllPass (test_cmdline_renderHelpAndVersion stubCmdLineApiM) := by
  intro h
  simp [Core.AllPass, test_cmdline_renderHelpAndVersion, stubCmdLineApiM, bind, assert] at h

example : ¬ Core.AllPass (test_cmdline_runCliWith_customValidator (fun _ => stubCmdLineApiM)) := by
  intro h
  simp [Core.AllPass, test_cmdline_runCliWith_customValidator, stubCmdLineApiM, StateT.run,
    StateT.pure, pure, bind, assert] at h

example : ¬ Core.AllPass (test_cmdline_parseWithEnv_unsetEnvMatchesParseWith
    stubCmdLineApiM
    (fun _ => { stubCmdLineApiM with parseWithEnv := fun _ _ _ => .error { kind := .ioError, message := "diverged" } })) := by
  intro h
  have h0 := h { name := "app" } [] []
  simp [stubCmdLineApiM, assert] at h0

example : ¬ Core.AllPass (test_cmdline_mkFilesCliOps_eintrPartialWriteAndEof
    (fun _ getEnvFn =>
      { readLine := throwThe IO.Error (.interrupted "" 4 "eintr aborted")
        writeOut := fun _ => pure ()
        writeErr := fun _ => pure ()
        getEnv := getEnvFn })) := by
  intro h
  have h0 := h 1 (by decide)
  rcases h0 with ⟨h1, _⟩
  cases h1

example : Model.isValidSpec
    { name := "cli"
      version := some "1.0.0"
      options := [ { name := "verbose", short := some 'v', long := some "verbose", kind := .bool, repeatable := true, global := true } ]
      subcommands := [ { name := "run", args := [ { name := "file", kind := .string } ] } ] } = true := by
  decide

example : Model.parseOptValue .nat "42" = .ok (.nat 42) ∧
    Model.parseOptValue .int "-5" = .ok (.int (-5)) ∧
    Model.parseOptValue .bool "YES" = .ok (.bool true) := by
  exact ⟨rfl, rfl, rfl⟩

end LeanSwe.CmdLine
