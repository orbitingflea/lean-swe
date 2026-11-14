import LeanSwe.EnvVars.Interface

namespace LeanSwe.EnvVars.RuntimeTests

open LeanSwe.EnvVars

private def assertTrue (cond : Bool) (msg : String) : IO Unit := do
  if !cond then
    throw (IO.userError s!"ASSERTION FAILED: {msg}")

private def assertOk {α : Type} (res : Except EnvVarsError α) (msg : String) : IO α := do
  match res with
  | .ok v => return v
  | .error e => throw (IO.userError s!"ASSERTION FAILED: {msg} (unexpected error: {repr e})")

private def assertErrKind {α : Type} (res : Except EnvVarsError α) (expected : EnvVarsErrorKind)
    (expectedKey : Option String) (msg : String) : IO Unit := do
  match res with
  | .ok _ => throw (IO.userError s!"ASSERTION FAILED: {msg} (expected error {repr expected}, got ok)")
  | .error e =>
    if e.kind != expected || e.key != expectedKey || e.errnoCode != none || e.message == "" then
      throw (IO.userError s!"ASSERTION FAILED: {msg} (got {repr e}, expected kind={repr expected} key={repr expectedKey})")

/-- Execute real OS environment grounding tests for `LeanSwe.EnvVars`. -/
def runAll : IO Unit := do
  assertErrKind (← EnvVars.getEnv "") .invalidKey (some "") "empty key rejected"
  assertErrKind (← EnvVars.getEnv "A=B") .invalidKey (some "A=B") "key with '=' rejected"
  assertErrKind (← EnvVars.getEnv "A=1=2") .invalidKey (some "A=1=2") "key with multiple '=' rejected"
  let nulKey := String.ofList ['A', Char.ofNat 0, 'B']
  assertErrKind (← EnvVars.getEnv nulKey) .invalidKey (some nulKey) "key with NUL rejected"

  let missing ← assertOk (← EnvVars.getEnv "__LEANSWE_NONEXISTENT_ENV_VAR_9F2A__") "missing key"
  assertTrue (missing == none) "nonexistent key returns none"

  let pathVal ← assertOk (← EnvVars.getEnv "PATH") "getEnv PATH"
  match pathVal with
  | some p =>
    assertTrue (p != "") "PATH is non-empty"
    let dirs := EnvVars.splitSearchPath p
    assertTrue (dirs.size > 0) "splitSearchPath PATH yields >= 1 dir"
    assertTrue (dirs.toList.all fun d => !d.isEmpty && !(':' ∈ d.toList)) "splitSearchPath PATH segments clean"
  | none => throw (IO.userError "ASSERTION FAILED: expected PATH to be set in test environment")

  let entries ← assertOk (← EnvVars.listEnv) "listEnv"
  let pathFromList := (entries.find? fun p => p.1 == "PATH").map (·.2)
  assertTrue (pathFromList == pathVal) "listEnv PATH matches getEnv PATH"
  for (k, _) in entries do
    let v ← assertOk (← EnvVars.getEnv k) s!"getEnv {k}"
    let expected := (entries.find? fun p => p.1 == k).map (·.2)
    assertTrue (v == expected) s!"listEnv matches getEnv for {k}"

  let homeRaw ← assertOk (← EnvVars.getEnv "HOME") "getEnv HOME"
  match homeRaw with
  | some h =>
    if h == "" then
      assertErrKind (← EnvVars.homeDir) .notFound (some "HOME") "homeDir fails when HOME empty"
    else
      let hd ← assertOk (← EnvVars.homeDir) "homeDir"
      assertTrue (hd == h) "homeDir matches HOME"
  | none =>
    assertErrKind (← EnvVars.homeDir) .notFound (some "HOME") "homeDir fails when HOME unset"

  assertTrue (EnvVars.splitSearchPath "" == #[]) "splitSearchPath empty"
  assertTrue (EnvVars.splitSearchPath ":::" == #[]) "splitSearchPath colons only"
  assertTrue (EnvVars.splitSearchPath ":/usr/bin::/bin:" == #["/usr/bin", "/bin"]) "splitSearchPath drops empties"

  IO.println "PASS: LeanSwe.EnvVars runtime tests"

end LeanSwe.EnvVars.RuntimeTests
