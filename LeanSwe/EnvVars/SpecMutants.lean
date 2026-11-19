import Core.NondetTest
import Core.Assumptions
import LeanSwe.EnvVars.Types
import LeanSwe.EnvVars.SpecTests

/-! Compile-time negative specification mutants for `LeanSwe.EnvVars`. -/

namespace LeanSwe.EnvVars

open Core (NondetTest ErrorObligation)
open Core.NondetTest

private def mockMapRawError : EnvVarsRawError → EnvVarsError
  | .invalidEncoding key? detail =>
    { kind := .invalidEncoding
      key := key?
      errnoCode := none
      message := if detail.isEmpty then "invalid UTF-8 in environment" else detail }
  | .invalidArgument key? code detail =>
    { kind := .invalidKey
      key := key?
      errnoCode := some code
      message := if detail.isEmpty then "invalid environment variable name" else detail }
  | .otherError code detail =>
    { kind := .ioError
      key := none
      errnoCode := some code
      message := if detail.isEmpty then s!"os error {code}" else detail }
  | .userError detail =>
    { kind := .ioError
      key := none
      errnoCode := none
      message := if detail.isEmpty then "environment error" else detail }

private def stubEnvVarsApi : EnvVarsApi :=
  { mapRawError := mockMapRawError
    getEnv := fun _ => pure (.ok none)
    listEnv := pure (.ok #[])
    homeDir := pure (.error { kind := .notFound, key := some "HOME", message := "stub" })
    splitSearchPath := fun _ => #[] }

private def stubMkApi (raw : RawEnvVarsOpsM Id) : EnvVarsApiM Id :=
  { mapRawError := raw.mapRawError
    getEnv := fun key =>
      match raw.getEnv key with
      | .ok v => .ok v
      | .error e => .error (raw.mapRawError e)
    listEnv :=
      match raw.listEnv with
      | .ok xs => .ok xs
      | .error e => .error (raw.mapRawError e)
    homeDir := do
      match raw.getEnv "HOME" with
      | .error e => pure (.error (raw.mapRawError e))
      | .ok none => pure (.error { kind := .notFound, key := some "HOME", message := "unset" })
      | .ok (some "") => pure (.error { kind := .notFound, key := some "HOME", message := "empty" })
      | .ok (some h) => pure (.ok h)
    splitSearchPath := fun _ => #[] }

example : ¬ Core.AllPass (test_envvars_mapRawError_returnsNonEmptyMessage
    { stubEnvVarsApi with mapRawError := fun _ => { kind := .ioError, message := "" } }) := by
  intro h
  have h0 := h (.userError "boom")
  simp [assert] at h0

example : ¬ Core.AllPass (test_envvars_getEnv_rejectsInvalidKey stubMkApi) := by
  intro h
  have h0 := h "A=B" true (Or.inr (Or.inl (by decide)))
  simp [stubMkApi, assert] at h0

example : ¬ Core.AllPass (test_envvars_getEnv_rejectsInvalidKey stubMkApi) := by
  intro h
  have h0 := h "" true (Or.inl rfl)
  simp [stubMkApi, assert] at h0

example : ¬ Core.AllPass (test_envvars_getEnv_rejectsInvalidKey stubMkApi) := by
  intro h
  have h0 := h (String.ofList ['A', Char.ofNat 0]) true (Or.inr (Or.inr (by decide)))
  simp [stubMkApi, assert] at h0

example : ¬ Core.AllPass (test_envvars_getEnv_foundInMockList fun raw =>
    { stubMkApi raw with getEnv := fun _ => pure (.ok none) }) := by
  intro h
  have h0 := h [("PATH", "/bin")] "PATH" "/bin" (by decide) rfl
  simp [pure, assert] at h0
  cases h0

example : ¬ Core.AllPass (test_envvars_homeDir_missingOrEmptyFails fun raw =>
    { stubMkApi raw with homeDir := pure (.ok "") }) := by
  intro h
  have h0 := h [("HOME", "")] (Or.inr rfl)
  simp [pure, assert] at h0

example : ¬ Core.AllPass (test_envvars_splitSearchPath_emptyReturnsEmpty
    { stubEnvVarsApi with splitSearchPath := fun _ => #[""] }) := by
  intro h
  simp [test_envvars_splitSearchPath_emptyReturnsEmpty, Core.AllPass, assert] at h

example : ¬ Core.AllPass (test_envvars_splitSearchPath_dropsEmptySegments
    { stubEnvVarsApi with splitSearchPath := fun s => #[s] }) := by
  intro h
  have h0 := h "/a" "/b" (by decide) (by decide)
  simp [assert] at h0

example : ¬ Core.AllPass (test_envvars_listEnv_returnsMockEntries fun raw =>
    { stubMkApi raw with listEnv := pure (.ok #[]) }) := by
  intro h
  have h0 := h [("PATH", "/bin")]
  simp [pure, assert] at h0
  cases h0

example : ¬ Core.AllPass (test_envvars_homeDir_returnsNonEmptyHome fun raw =>
    { stubMkApi raw with homeDir := pure (.error { kind := .notFound, key := some "HOME", message := "bug" }) }) := by
  intro h
  have h0 := h [("HOME", "example-home")] "example-home" (by decide) rfl
  simp [pure, assert] at h0

example : ¬ Core.AllPass (test_envvars_mapRawError_delegatesToRaw fun raw =>
    { stubMkApi raw with mapRawError := fun _ => { kind := .ioError, message := "const" } }) := by
  intro h
  have h0 := h (.userError "a") (fun _ => { kind := .invalidKey, message := "x" })
  simp [assert] at h0

example : ¬ Core.AllPass (test_envvars_getEnv_missingInMockList fun raw =>
    { stubMkApi raw with getEnv := fun _ => pure (.ok (some "bogus")) }) := by
  intro h
  have h0 := h [] "PATH" (by decide) rfl
  simp [pure, assert] at h0
  cases h0

example : ¬ Core.AllPass (test_envvars_getEnv_propagatesRawError fun raw =>
    { stubMkApi raw with getEnv := fun _ => pure (.ok none) }) := by
  intro h
  have h0 := h "PATH" (.userError "boom") mockMapRawError (by decide)
  simp [pure, assert] at h0

example : ¬ Core.AllPass (test_envvars_getEnv_invalidEncodingReportsEncodingError
    stubEnvVarsApi fun raw => { stubMkApi raw with getEnv := fun _ => pure (.ok (some "\uFFFD")) }) := by
  intro h
  have h0 := h "BAD_VAL" "invalid UTF-8" (by decide)
  simp [bind, pure, assert] at h0

example : ¬ Core.AllPass (test_envvars_getEnv_invalidEncodingReportsEncodingError
    { stubEnvVarsApi with mapRawError := fun _ => { kind := .ioError, key := none, message := "wrong" } }
    stubMkApi) := by
  intro h
  have h0 := h "BAD_VAL" "invalid UTF-8" (by decide)
  simp [stubMkApi, bind, pure, assert] at h0
  rcases h0.1 with ⟨_, h1, h2, _⟩
  cases h1
  cases h2

example : ¬ Core.AllPass (test_envvars_getEnv_invalidEncodingReportsEncodingError
    stubEnvVarsApi
    (fun raw =>
      { stubMkApi raw with
        homeDir := pure (.error { kind := .notFound, key := some "HOME", message := "masked encoding error" }) })) := by
  intro h
  have h0 := h "BAD_VAL" "invalid UTF-8" (by decide)
  simp [stubMkApi, stubEnvVarsApi, mockMapRawError, bind, pure, assert] at h0
  rcases h0.2 with ⟨_, h1, h2, _⟩
  cases h1
  cases h2

example : ¬ Core.AllPass (test_envvars_listEnv_propagatesRawError fun raw =>
    { stubMkApi raw with listEnv := pure (.ok #[]) }) := by
  intro h
  have h0 := h (.userError "boom") mockMapRawError
  simp [pure, assert] at h0

example : ¬ Core.AllPass (test_envvars_homeDir_propagatesRawError fun raw =>
    { stubMkApi raw with homeDir := pure (.ok "/fake") }) := by
  intro h
  have h0 := h (.userError "boom") mockMapRawError
  simp [pure, assert] at h0

example : ¬ Core.AllPass (test_envvars_splitSearchPath_entriesNonEmptyAndColonFree
    { stubEnvVarsApi with splitSearchPath := fun _ => #[""] }) := by
  intro h
  have h0 := h ""
  simp [String.isEmpty, assert] at h0

example : ¬ Core.AllPass (test_envvars_splitSearchPath_roundTripsCleanSegments
    { stubEnvVarsApi with splitSearchPath := fun _ => #[] }) := by
  intro h
  have h0 := h ["/a"] (by decide)
  simp [assert] at h0

example : ¬ Core.AllPass (test_envvars_mkApi_matchesModel fun raw =>
    { stubMkApi raw with splitSearchPath := fun _ => #["bug"] }) := by
  intro h
  have h0 := h {} "K" "" (.userError "x")
  simp [stubMkApi, Model.modelApi, Model.splitSearchPathModel, Model.splitColonAccModel,
    Bind.bind, assert] at h0

end LeanSwe.EnvVars
