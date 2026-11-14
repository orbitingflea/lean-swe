import LeanSwe.Env.Raw.Interface

namespace LeanSwe.Env.Raw.RuntimeTests

open LeanSwe.Env

private def assertTrue (cond : Bool) (msg : String) : IO Unit := do
  if !cond then
    throw (IO.userError s!"ASSERTION FAILED: {msg}")

private def assertOk {α : Type} (res : Except Raw.EnvRawError α) (msg : String) : IO α := do
  match res with
  | .ok v => return v
  | .error e => throw (IO.userError s!"ASSERTION FAILED: {msg} (unexpected error: {repr e})")

/-- Execute primitive OS environment grounding tests for `LeanSwe.Env.Raw`. -/
def runAll : IO Unit := do
  let missingKey := "__LEANSWE_NONEXISTENT_ENV_VAR_9F2A__"
  let missing ← assertOk (← Raw.getEnv missingKey) "Raw.getEnv missing"
  assertTrue (missing == none) "Raw.getEnv missing returns none"

  let pathVal ← assertOk (← Raw.getEnv "PATH") "Raw.getEnv PATH"
  match pathVal with
  | some p => assertTrue (p != "") "Raw.getEnv PATH non-empty"
  | none => pure ()

  let entries ← assertOk (← Raw.listEnv) "Raw.listEnv"
  for (k, _) in entries do
    assertTrue (k != "") "listed env key non-empty"
    assertTrue (!('=' ∈ k.toList)) "listed env key contains no '='"
    let g ← assertOk (← Raw.getEnv k) s!"Raw.getEnv {k}"
    let expected := (entries.find? fun p => p.1 == k).map (·.2)
    assertTrue (g == expected) s!"Raw.listEnv matches Raw.getEnv for {k}"

  let e1 := Raw.mapRawError (.invalidEncoding (some "K") "")
  assertTrue (e1.kind == .invalidEncoding && e1.key == some "K" && e1.message != "") "mapRawError invalidEncoding"
  let e2 := Raw.mapRawError (.invalidArgument (some "K") 22 "")
  assertTrue (e2.kind == .invalidKey && e2.errnoCode == some 22 && e2.message != "") "mapRawError invalidArgument"
  let e3 := Raw.mapRawError (.otherError 12 "")
  assertTrue (e3.kind == .ioError && e3.errnoCode == some 12 && e3.message != "") "mapRawError otherError"
  let e4 := Raw.mapRawError (.userError "")
  assertTrue (e4.kind == .ioError && e4.errnoCode == none && e4.message != "") "mapRawError userError"

  IO.println "PASS: LeanSwe.Env.Raw runtime tests"

end LeanSwe.Env.Raw.RuntimeTests
