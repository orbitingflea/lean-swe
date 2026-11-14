import Core.NondetTest
import LeanSwe.Env.Types

namespace LeanSwe.Env

open Core (NondetTest)
open Core.NondetTest

private def mockMapRawError : EnvRawError → EnvError
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

private def mockListOps (entries : List (String × String)) : RawEnvOpsM Id :=
  { mapRawError := mockMapRawError
    getEnv := fun key => pure (.ok ((entries.find? fun p => p.1 == key).map (·.2)))
    listEnv := pure (.ok entries.toArray) }

/-- Every error returned by `api.mapRawError` carries a non-empty diagnostic message. -/
def test_env_mapRawError_returnsNonEmptyMessage
    {runner} [NondetTest runner] (api : EnvApi) : runner Unit := do
  let raw ← nondet EnvRawError
  let err := api.mapRawError raw
  NondetTest.assert (err.message ≠ "")

/-- `mkApi raw` delegates `mapRawError` faithfully to `raw.mapRawError`. -/
def test_env_mapRawError_delegatesToRaw
    {runner} [NondetTest runner] (mkApi : RawEnvOpsM Id → EnvApiM Id) : runner Unit := do
  let rawErr ← nondet EnvRawError
  let mapFn ← nondet (EnvRawError → EnvError)
  let raw : RawEnvOpsM Id :=
    { mapRawError := mapFn
      getEnv := fun _ => pure (.ok none)
      listEnv := pure (.ok #[]) }
  NondetTest.assert ((mkApi raw).mapRawError rawErr = mapFn rawErr)

/-- `getEnv` rejects empty keys, keys containing `=`, and keys containing NUL with `.invalidKey` before calling `raw.getEnv`. -/
def test_env_getEnv_rejectsInvalidKey
    {runner} [NondetTest runner] (mkApi : RawEnvOpsM Id → EnvApiM Id) : runner Unit := do
  let key ← nondet String
  let leak ← nondet Bool
  assume (key = "" ∨ '=' ∈ key.toList ∨ Char.ofNat 0 ∈ key.toList)
  let raw : RawEnvOpsM Id :=
    { mapRawError := mockMapRawError
      getEnv := fun _ =>
        if leak then pure (.ok (some "leaked"))
        else pure (.error (.userError "raw_called"))
      listEnv := pure (.ok #[]) }
  let res := (mkApi raw).getEnv key
  NondetTest.assert (∃ e, res = .error e ∧ e.kind = .invalidKey ∧ e.key = some key ∧ e.errnoCode = none ∧ e.message ≠ "")

/-- For a valid key present in a pure `List (String × String)` environment, `getEnv` returns its first matching value. -/
def test_env_getEnv_foundInMockList
    {runner} [NondetTest runner] (mkApi : RawEnvOpsM Id → EnvApiM Id) : runner Unit := do
  let entries ← nondet (List (String × String))
  let key ← nondet String
  let val ← nondet String
  assume (key ≠ "" ∧ '=' ∉ key.toList ∧ Char.ofNat 0 ∉ key.toList)
  assume (entries.find? (fun p => p.1 == key) = some (key, val))
  let api := mkApi (mockListOps entries)
  NondetTest.assert (api.getEnv key = .ok (some val))

/-- For a valid key absent from a pure `List (String × String)` environment, `getEnv` returns `none`. -/
def test_env_getEnv_missingInMockList
    {runner} [NondetTest runner] (mkApi : RawEnvOpsM Id → EnvApiM Id) : runner Unit := do
  let entries ← nondet (List (String × String))
  let key ← nondet String
  assume (key ≠ "" ∧ '=' ∉ key.toList ∧ Char.ofNat 0 ∉ key.toList)
  assume (entries.find? (fun p => p.1 == key) = none)
  let api := mkApi (mockListOps entries)
  NondetTest.assert (api.getEnv key = .ok none)

/-- `getEnv` propagates raw lookup errors through `raw.mapRawError` for valid keys. -/
def test_env_getEnv_propagatesRawError
    {runner} [NondetTest runner] (mkApi : RawEnvOpsM Id → EnvApiM Id) : runner Unit := do
  let key ← nondet String
  let rawErr ← nondet EnvRawError
  let mapFn ← nondet (EnvRawError → EnvError)
  assume (key ≠ "" ∧ '=' ∉ key.toList ∧ Char.ofNat 0 ∉ key.toList)
  let raw : RawEnvOpsM Id :=
    { mapRawError := mapFn
      getEnv := fun _ => pure (.error rawErr)
      listEnv := pure (.ok #[]) }
  NondetTest.assert ((mkApi raw).getEnv key = .error (mapFn rawErr))

/-- `listEnv` returns all entries from the underlying `RawEnvOpsM` listing in order. -/
def test_env_listEnv_returnsMockEntries
    {runner} [NondetTest runner] (mkApi : RawEnvOpsM Id → EnvApiM Id) : runner Unit := do
  let entries ← nondet (List (String × String))
  let api := mkApi (mockListOps entries)
  NondetTest.assert (api.listEnv = .ok entries.toArray)

/-- `listEnv` propagates raw listing errors through `raw.mapRawError`. -/
def test_env_listEnv_propagatesRawError
    {runner} [NondetTest runner] (mkApi : RawEnvOpsM Id → EnvApiM Id) : runner Unit := do
  let rawErr ← nondet EnvRawError
  let mapFn ← nondet (EnvRawError → EnvError)
  let raw : RawEnvOpsM Id :=
    { mapRawError := mapFn
      getEnv := fun _ => pure (.ok none)
      listEnv := pure (.error rawErr) }
  NondetTest.assert ((mkApi raw).listEnv = .error (mapFn rawErr))

/-- `homeDir` returns the non-empty `HOME` value when set. -/
def test_env_homeDir_returnsNonEmptyHome
    {runner} [NondetTest runner] (mkApi : RawEnvOpsM Id → EnvApiM Id) : runner Unit := do
  let entries ← nondet (List (String × String))
  let home ← nondet String
  assume (home ≠ "")
  assume (entries.find? (fun p => p.1 == "HOME") = some ("HOME", home))
  let api := mkApi (mockListOps entries)
  NondetTest.assert (api.homeDir = .ok home)

/-- `homeDir` fails with `.notFound` and `key = some "HOME"` when `HOME` is unset or empty. -/
def test_env_homeDir_missingOrEmptyFails
    {runner} [NondetTest runner] (mkApi : RawEnvOpsM Id → EnvApiM Id) : runner Unit := do
  let entries ← nondet (List (String × String))
  assume (entries.find? (fun p => p.1 == "HOME") = none ∨
    entries.find? (fun p => p.1 == "HOME") = some ("HOME", ""))
  let api := mkApi (mockListOps entries)
  NondetTest.assert (∃ e, api.homeDir = .error e ∧ e.kind = .notFound ∧ e.key = some "HOME" ∧ e.message ≠ "")

/-- `homeDir` propagates raw lookup errors through `raw.mapRawError`. -/
def test_env_homeDir_propagatesRawError
    {runner} [NondetTest runner] (mkApi : RawEnvOpsM Id → EnvApiM Id) : runner Unit := do
  let rawErr ← nondet EnvRawError
  let mapFn ← nondet (EnvRawError → EnvError)
  let raw : RawEnvOpsM Id :=
    { mapRawError := mapFn
      getEnv := fun _ => pure (.error rawErr)
      listEnv := pure (.ok #[]) }
  NondetTest.assert ((mkApi raw).homeDir = .error (mapFn rawErr))

/-- `splitSearchPath ""` returns an empty array. -/
def test_env_splitSearchPath_emptyReturnsEmpty
    {runner} [NondetTest runner] (api : EnvApi) : runner Unit := do
  NondetTest.assert (api.splitSearchPath "" = #[])

/-- Every segment returned by `splitSearchPath` is non-empty and free of `:`. -/
def test_env_splitSearchPath_entriesNonEmptyAndColonFree
    {runner} [NondetTest runner] (api : EnvApi) : runner Unit := do
  let path ← nondet String
  let parts := api.splitSearchPath path
  NondetTest.assert (parts.toList.all fun p => !p.isEmpty && !(':' ∈ p.toList))

/-- `splitSearchPath` drops leading, middle, and trailing empty segments between `:` delimiters. -/
def test_env_splitSearchPath_dropsEmptySegments
    {runner} [NondetTest runner] (api : EnvApi) : runner Unit := do
  let a ← nondet String
  let b ← nondet String
  assume (a ≠ "" ∧ ':' ∉ a.toList)
  assume (b ≠ "" ∧ ':' ∉ b.toList)
  NondetTest.assert (api.splitSearchPath (":" ++ a ++ "::" ++ b ++ ":") = #[a, b] ∧
    api.splitSearchPath ":::" = #[])

/-- `splitSearchPath` is the exact inverse of `:`-intercalation on non-empty, `:`-free segments. -/
def test_env_splitSearchPath_roundTripsCleanSegments
    {runner} [NondetTest runner] (api : EnvApi) : runner Unit := do
  let segs ← nondet (List String)
  assume (segs.all fun s => !s.isEmpty && !(':' ∈ s.toList))
  NondetTest.assert (api.splitSearchPath (String.intercalate ":" segs) = segs.toArray)

private def stubEnvApi : EnvApi :=
  { mapRawError := mockMapRawError
    getEnv := fun _ => pure (.ok none)
    listEnv := pure (.ok #[])
    homeDir := pure (.error { kind := .notFound, key := some "HOME", message := "stub" })
    splitSearchPath := fun _ => #[] }

private def stubMkApi (raw : RawEnvOpsM Id) : EnvApiM Id :=
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

example : ¬ Core.AllPass (test_env_mapRawError_returnsNonEmptyMessage
    { stubEnvApi with mapRawError := fun _ => { kind := .ioError, message := "" } }) := by
  intro h
  have h0 := h (.userError "boom")
  simp [assert] at h0

example : ¬ Core.AllPass (test_env_getEnv_rejectsInvalidKey stubMkApi) := by
  intro h
  have h0 := h "A=B" true (Or.inr (Or.inl (by decide)))
  simp [stubMkApi, assert] at h0

example : ¬ Core.AllPass (test_env_getEnv_rejectsInvalidKey stubMkApi) := by
  intro h
  have h0 := h "" true (Or.inl rfl)
  simp [stubMkApi, assert] at h0

example : ¬ Core.AllPass (test_env_getEnv_rejectsInvalidKey stubMkApi) := by
  intro h
  have h0 := h (String.ofList ['A', Char.ofNat 0]) true (Or.inr (Or.inr (by decide)))
  simp [stubMkApi, assert] at h0

example : ¬ Core.AllPass (test_env_getEnv_foundInMockList fun raw =>
    { stubMkApi raw with getEnv := fun _ => pure (.ok none) }) := by
  intro h
  have h0 := h [("PATH", "/bin")] "PATH" "/bin" (by decide) rfl
  simp [pure, assert] at h0
  cases h0

example : ¬ Core.AllPass (test_env_homeDir_missingOrEmptyFails fun raw =>
    { stubMkApi raw with homeDir := pure (.ok "") }) := by
  intro h
  have h0 := h [("HOME", "")] (Or.inr rfl)
  simp [pure, assert] at h0

example : ¬ Core.AllPass (test_env_splitSearchPath_emptyReturnsEmpty
    { stubEnvApi with splitSearchPath := fun _ => #[""] }) := by
  intro h
  simp [test_env_splitSearchPath_emptyReturnsEmpty, Core.AllPass, assert] at h

example : ¬ Core.AllPass (test_env_splitSearchPath_dropsEmptySegments
    { stubEnvApi with splitSearchPath := fun s => #[s] }) := by
  intro h
  have h0 := h "/a" "/b" (by decide) (by decide)
  simp [assert] at h0

example : ¬ Core.AllPass (test_env_listEnv_returnsMockEntries fun raw =>
    { stubMkApi raw with listEnv := pure (.ok #[]) }) := by
  intro h
  have h0 := h [("PATH", "/bin")]
  simp [pure, assert] at h0
  cases h0

example : ¬ Core.AllPass (test_env_homeDir_returnsNonEmptyHome fun raw =>
    { stubMkApi raw with homeDir := pure (.error { kind := .notFound, key := some "HOME", message := "bug" }) }) := by
  intro h
  have h0 := h [("HOME", "example-home")] "example-home" (by decide) rfl
  simp [pure, assert] at h0

example : ¬ Core.AllPass (test_env_mapRawError_delegatesToRaw fun raw =>
    { stubMkApi raw with mapRawError := fun _ => { kind := .ioError, message := "const" } }) := by
  intro h
  have h0 := h (.userError "a") (fun _ => { kind := .invalidKey, message := "x" })
  simp [assert] at h0

example : ¬ Core.AllPass (test_env_getEnv_missingInMockList fun raw =>
    { stubMkApi raw with getEnv := fun _ => pure (.ok (some "bogus")) }) := by
  intro h
  have h0 := h [] "PATH" (by decide) rfl
  simp [pure, assert] at h0
  cases h0

example : ¬ Core.AllPass (test_env_getEnv_propagatesRawError fun raw =>
    { stubMkApi raw with getEnv := fun _ => pure (.ok none) }) := by
  intro h
  have h0 := h "PATH" (.userError "boom") mockMapRawError (by decide)
  simp [pure, assert] at h0

example : ¬ Core.AllPass (test_env_listEnv_propagatesRawError fun raw =>
    { stubMkApi raw with listEnv := pure (.ok #[]) }) := by
  intro h
  have h0 := h (.userError "boom") mockMapRawError
  simp [pure, assert] at h0

example : ¬ Core.AllPass (test_env_homeDir_propagatesRawError fun raw =>
    { stubMkApi raw with homeDir := pure (.ok "/fake") }) := by
  intro h
  have h0 := h (.userError "boom") mockMapRawError
  simp [pure, assert] at h0

example : ¬ Core.AllPass (test_env_splitSearchPath_entriesNonEmptyAndColonFree
    { stubEnvApi with splitSearchPath := fun _ => #[""] }) := by
  intro h
  have h0 := h ""
  simp [String.isEmpty, assert] at h0

example : ¬ Core.AllPass (test_env_splitSearchPath_roundTripsCleanSegments
    { stubEnvApi with splitSearchPath := fun _ => #[] }) := by
  intro h
  have h0 := h ["/a"] (by decide)
  simp [assert] at h0

end LeanSwe.Env
