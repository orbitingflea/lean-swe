import LeanSwe.Env.Interface

namespace LeanSwe.Env.RuntimeTests

open LeanSwe.Env

private def assertTrue (cond : Bool) (msg : String) : IO Unit := do
  if !cond then
    throw (IO.userError s!"ASSERTION FAILED: {msg}")

private def assertOk {α : Type} (res : Except EnvError α) (msg : String) : IO α := do
  match res with
  | .ok v => return v
  | .error e => throw (IO.userError s!"ASSERTION FAILED: {msg} (unexpected error: {repr e})")

private def assertErrKind {α : Type} (res : Except EnvError α) (expected : EnvErrorKind)
    (expectedKey : Option String) (msg : String) : IO Unit := do
  match res with
  | .ok _ => throw (IO.userError s!"ASSERTION FAILED: {msg} (expected error {repr expected}, got ok)")
  | .error e =>
    if e.kind != expected || e.key != expectedKey || e.errnoCode != none || e.message == "" then
      throw (IO.userError s!"ASSERTION FAILED: {msg} (got {repr e}, expected kind={repr expected} key={repr expectedKey})")

/-- Execute real OS environment grounding tests for `LeanSwe.Env`. -/
def runAll : IO Unit := do
  assertErrKind (← Env.getEnv "") .invalidKey (some "") "empty key rejected"
  assertErrKind (← Env.getEnv "A=B") .invalidKey (some "A=B") "key with '=' rejected"
  assertErrKind (← Env.getEnv "A=1=2") .invalidKey (some "A=1=2") "key with multiple '=' rejected"
  let nulKey := String.ofList ['A', Char.ofNat 0, 'B']
  assertErrKind (← Env.getEnv nulKey) .invalidKey (some nulKey) "key with NUL rejected"

  let missing ← assertOk (← Env.getEnv "__LEANSWE_NONEXISTENT_ENV_VAR_9F2A__") "missing key"
  assertTrue (missing == none) "nonexistent key returns none"

  let pathVal ← assertOk (← Env.getEnv "PATH") "getEnv PATH"
  match pathVal with
  | some p =>
    assertTrue (p != "") "PATH is non-empty"
    let dirs := Env.splitSearchPath p
    assertTrue (dirs.size > 0) "splitSearchPath PATH yields >= 1 dir"
    assertTrue (dirs.toList.all fun d => !d.isEmpty && !(':' ∈ d.toList)) "splitSearchPath PATH segments clean"
  | none => throw (IO.userError "ASSERTION FAILED: expected PATH to be set in test environment")

  let entries ← assertOk (← Env.listEnv) "listEnv"
  let pathFromList := (entries.find? fun p => p.1 == "PATH").map (·.2)
  assertTrue (pathFromList == pathVal) "listEnv PATH matches getEnv PATH"
  for (k, _) in entries do
    let v ← assertOk (← Env.getEnv k) s!"getEnv {k}"
    let expected := (entries.find? fun p => p.1 == k).map (·.2)
    assertTrue (v == expected) s!"listEnv matches getEnv for {k}"

  let homeRaw ← assertOk (← Env.getEnv "HOME") "getEnv HOME"
  match homeRaw with
  | some h =>
    if h == "" then
      assertErrKind (← Env.homeDir) .notFound (some "HOME") "homeDir fails when HOME empty"
    else
      let hd ← assertOk (← Env.homeDir) "homeDir"
      assertTrue (hd == h) "homeDir matches HOME"
  | none =>
    assertErrKind (← Env.homeDir) .notFound (some "HOME") "homeDir fails when HOME unset"

  assertTrue (Env.splitSearchPath "" == #[]) "splitSearchPath empty"
  assertTrue (Env.splitSearchPath ":::" == #[]) "splitSearchPath colons only"
  assertTrue (Env.splitSearchPath ":/usr/bin::/bin:" == #["/usr/bin", "/bin"]) "splitSearchPath drops empties"

  IO.println "PASS: LeanSwe.Env runtime tests"

end LeanSwe.Env.RuntimeTests
