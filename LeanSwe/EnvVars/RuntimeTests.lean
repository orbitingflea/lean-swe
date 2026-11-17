import Core.Assumptions
import LeanSwe.EnvVars.Interface

namespace LeanSwe.EnvVars.RuntimeTests

private def assertEnvTrue (cond : Bool) (msg : String) : IO Unit := do
  if !cond then
    throw (IO.userError s!"ASSERTION FAILED: {msg}")

private def envHexDigit (n : UInt8) : Char :=
  if n < 10 then Char.ofNat (48 + n.toNat) else Char.ofNat (87 + n.toNat)

private def envUtf8ToHex (s : String) : String := Id.run do
  let mut out : String := ""
  for b in s.toUTF8.data do
    out := out.push (envHexDigit (b >>> 4))
    out := out.push (envHexDigit (b &&& 0x0F))
  return out

private def envErrKindTag : EnvVars.EnvVarsErrorKind → String
  | .invalidKey => "invalidKey"
  | .notFound => "notFound"
  | .invalidEncoding => "invalidEncoding"
  | .ioError => "ioError"

private def execEnvLauncherC : String :=
  "#include <stdio.h>\n" ++
  "#include <stdlib.h>\n" ++
  "#include <string.h>\n" ++
  "#include <unistd.h>\n" ++
  "static int hexv(char c) {\n" ++
  "  if (c >= '0' && c <= '9') return c - '0';\n" ++
  "  if (c >= 'a' && c <= 'f') return c - 'a' + 10;\n" ++
  "  if (c >= 'A' && c <= 'F') return c - 'A' + 10;\n" ++
  "  return -1;\n" ++
  "}\n" ++
  "static char *dechex(const char *s) {\n" ++
  "  size_t n = strlen(s);\n" ++
  "  if (n % 2 != 0) return NULL;\n" ++
  "  char *out = (char *)malloc(n / 2 + 1);\n" ++
  "  if (!out) return NULL;\n" ++
  "  for (size_t i = 0; i < n; i += 2) {\n" ++
  "    int hi = hexv(s[i]), lo = hexv(s[i + 1]);\n" ++
  "    if (hi < 0 || lo < 0) { free(out); return NULL; }\n" ++
  "    out[i / 2] = (char)((hi << 4) | lo);\n" ++
  "  }\n" ++
  "  out[n / 2] = '\\0';\n" ++
  "  return out;\n" ++
  "}\n" ++
  "int main(int argc, char **argv) {\n" ++
  "  int sep = -1;\n" ++
  "  for (int i = 2; i < argc; i++) {\n" ++
  "    if (strcmp(argv[i], \"--sep\") == 0) { sep = i; break; }\n" ++
  "  }\n" ++
  "  if (sep < 0) return 10;\n" ++
  "  int child_argc = sep - 1;\n" ++
  "  char **child_argv = (char **)calloc((size_t)child_argc + 1, sizeof(char *));\n" ++
  "  child_argv[0] = argv[1];\n" ++
  "  for (int i = 2; i < sep; i++) child_argv[i - 1] = argv[i];\n" ++
  "  int envc = argc - sep - 1;\n" ++
  "  char **envp = (char **)calloc((size_t)envc + 1, sizeof(char *));\n" ++
  "  for (int i = 0; i < envc; i++) {\n" ++
  "    envp[i] = dechex(argv[sep + 1 + i]);\n" ++
  "    if (!envp[i]) return 11;\n" ++
  "  }\n" ++
  "  execve(argv[1], child_argv, envp);\n" ++
  "  perror(\"execve\");\n" ++
  "  return 12;\n" ++
  "}\n"

private def runEnvHexProbe (probeArgs hexEnv : Array String) : IO IO.Process.Output := do
  let exe := (← IO.appPath).toString
  let tmpDir ← IO.FS.createTempDir
  try
    let src := tmpDir / "env_probe.c"
    let bin := tmpDir / "env_probe"
    IO.FS.writeFile src execEnvLauncherC
    let ccOut ← IO.Process.output {
      cmd := "cc"
      args := #["-O2", "-Wall", "-Wextra", "-Werror", src.toString, "-o", bin.toString]
    }
    assertEnvTrue (ccOut.exitCode == 0) s!"failed to compile env probe: {ccOut.stderr}"
    IO.Process.output {
      cmd := bin.toString
      args := #[exe, "--envvars-probe"] ++ probeArgs ++ #["--sep"] ++ hexEnv
    }
  finally
    let _ ← try IO.FS.removeDirAll tmpDir; pure () catch _ => pure ()

/-- Subprocess entrypoint for testing `EnvVars` with controlled raw `environ` bytes. -/
def probeMain (args : List String) : IO UInt32 := do
  match args with
  | ["get", key] =>
    match ← EnvVars.getEnv key with
    | .ok none => IO.println "OK:NONE"; return 0
    | .ok (some v) => IO.println s!"OK:SOME:{v}"; return 0
    | .error e =>
      IO.println s!"ERR:{envErrKindTag e.kind}:{e.key.getD ""}:{e.message}"
      return 2
  | ["list"] =>
    match ← EnvVars.listEnv with
    | .ok entries => IO.println s!"OK:{entries.size}"; return 0
    | .error e =>
      IO.println s!"ERR:{envErrKindTag e.kind}:{e.key.getD ""}:{e.message}"
      return 2
  | ["home"] =>
    match ← EnvVars.homeDir with
    | .ok h => IO.println s!"OK:{h}"; return 0
    | .error e =>
      IO.println s!"ERR:{envErrKindTag e.kind}:{e.key.getD ""}:{e.message}"
      return 2
  | _ =>
    IO.eprintln "unknown --envvars-probe mode"
    return 3

/-- Verify `EnvVars.getEnv` rejects invalid keys (empty, containing `'='`, or containing NUL) with `.invalidKey`. -/
def err_envvars_getEnv_invalidKey : IO Unit := do
  for badKey in ["", "A=B", String.ofList ['A', Char.ofNat 0, 'B']] do
    match ← EnvVars.getEnv badKey with
    | .ok v => throw (IO.userError s!"expected .invalidKey for {repr badKey}, got ok {repr v}")
    | .error e =>
      assertEnvTrue (e.kind == .invalidKey && e.key == some badKey && !e.message.isEmpty)
        s!"unexpected error for invalid key {repr badKey}: {repr e}"

/-- Verify `EnvVars.getEnv` returns `.invalidEncoding` when the queried variable holds invalid UTF-8 bytes. -/
def err_envvars_getEnv_invalidEncoding : IO Unit := do
  match ← EnvVars.getEnv "__LEANSWE_UNSET_ENV_ERR_CHECK__" with
  | .ok none => pure ()
  | other => throw (IO.userError s!"expected ok none on unset key, got {repr other}")
  let out ← runEnvHexProbe #["get", "BAD_ENV"] #[envUtf8ToHex "BAD_ENV=" ++ "ff"]
  assertEnvTrue (out.exitCode == 2 && out.stdout.startsWith "ERR:invalidEncoding:BAD_ENV:")
    s!"expected EnvVars.getEnv invalidEncoding error, got rc={out.exitCode} out={repr out.stdout}"

/-- Verify `EnvVars.listEnv` returns `.invalidEncoding` when any non-malformed `environ` entry holds invalid UTF-8 bytes. -/
def err_envvars_listEnv_invalidEncoding : IO Unit := do
  let _ ← match ← EnvVars.listEnv with
    | .ok xs => pure xs
    | .error e => throw (IO.userError s!"in-process EnvVars.listEnv failed: {repr e}")
  let out ← runEnvHexProbe #["list"] #[envUtf8ToHex "OK=1", envUtf8ToHex "BAD=" ++ "80"]
  assertEnvTrue (out.exitCode == 2 && out.stdout.startsWith "ERR:invalidEncoding:BAD:")
    s!"expected EnvVars.listEnv invalidEncoding error, got rc={out.exitCode} out={repr out.stdout}"

/-- Verify `EnvVars.homeDir` returns `.invalidEncoding` when `HOME` holds invalid UTF-8 bytes. -/
def err_envvars_homeDir_invalidEncoding : IO Unit := do
  match ← EnvVars.homeDir with
  | .ok h => assertEnvTrue (!h.isEmpty) "in-process homeDir is non-empty when set"
  | .error e => assertEnvTrue (e.kind == .notFound) s!"expected notFound when HOME unset, got {repr e}"
  let out ← runEnvHexProbe #["home"] #[envUtf8ToHex "HOME=" ++ "ff"]
  assertEnvTrue (out.exitCode == 2 && out.stdout.startsWith "ERR:invalidEncoding:HOME:")
    s!"expected EnvVars.homeDir invalidEncoding error, got rc={out.exitCode} out={repr out.stdout}"

/-- Verify `EnvVars.homeDir` returns `.notFound` when `HOME` is unset or empty. -/
def err_envvars_homeDir_notFound : IO Unit := do
  match ← EnvVars.homeDir with
  | .ok h => assertEnvTrue (!h.isEmpty) "in-process homeDir is non-empty when set"
  | .error e => assertEnvTrue (e.kind == .notFound) s!"expected notFound when HOME unset, got {repr e}"
  let unsetOut ← runEnvHexProbe #["home"] #[envUtf8ToHex "OTHER=1"]
  assertEnvTrue (unsetOut.exitCode == 2 && unsetOut.stdout.startsWith "ERR:notFound:HOME:")
    s!"expected EnvVars.homeDir notFound when unset, got rc={unsetOut.exitCode} out={repr unsetOut.stdout}"
  let emptyOut ← runEnvHexProbe #["home"] #[envUtf8ToHex "HOME="]
  assertEnvTrue (emptyOut.exitCode == 2 && emptyOut.stdout.startsWith "ERR:notFound:HOME:")
    s!"expected EnvVars.homeDir notFound when empty, got rc={emptyOut.exitCode} out={repr emptyOut.stdout}"

/-- Registry of error-coverage runtime tests for `LeanSwe.EnvVars`. -/
def registeredErrorTests : Array Core.RegisteredErrorTest := #[
  ⟨"LeanSwe.EnvVars.RuntimeTests.err_envvars_getEnv_invalidKey", .real,
    err_envvars_getEnv_invalidKey⟩,
  ⟨"LeanSwe.EnvVars.RuntimeTests.err_envvars_getEnv_invalidEncoding", .real,
    err_envvars_getEnv_invalidEncoding⟩,
  ⟨"LeanSwe.EnvVars.RuntimeTests.err_envvars_listEnv_invalidEncoding", .real,
    err_envvars_listEnv_invalidEncoding⟩,
  ⟨"LeanSwe.EnvVars.RuntimeTests.err_envvars_homeDir_invalidEncoding", .real,
    err_envvars_homeDir_invalidEncoding⟩,
  ⟨"LeanSwe.EnvVars.RuntimeTests.err_envvars_homeDir_notFound", .real,
    err_envvars_homeDir_notFound⟩
]

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

  Core.runRegisteredErrorTests registeredErrorTests
  IO.println "PASS: LeanSwe.EnvVars runtime tests"

end LeanSwe.EnvVars.RuntimeTests
