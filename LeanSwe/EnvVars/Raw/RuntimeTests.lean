import Core.Assumptions
import LeanSwe.EnvVars.Raw.Impl
import LeanSwe.EnvVars.Raw.Interface

namespace LeanSwe.EnvVars.Raw.RuntimeTests

open LeanSwe.EnvVars

private def assertRawTrue (cond : Bool) (msg : String) : IO Unit := do
  if !cond then
    throw (IO.userError s!"ASSERTION FAILED: {msg}")

private def hexDigit (n : UInt8) : Char :=
  if n < 10 then Char.ofNat (48 + n.toNat) else Char.ofNat (87 + n.toNat)

private def toHexString (bs : ByteArray) : String := Id.run do
  let mut out : String := ""
  for b in bs.data do
    out := out.push (hexDigit (b >>> 4))
    out := out.push (hexDigit (b &&& 0x0F))
  return out

private def utf8ToHex (s : String) : String :=
  toHexString s.toUTF8

private def envRawErrKindTag : EnvVarsRawErrorKind → String
  | .invalidEncoding => "invalidEncoding"
  | .invalidArgument => "invalidArgument"
  | .otherError => "otherError"
  | .userError => "userError"

private def execHexEnvC : String :=
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

private def runRawHexProbe (probeArgs hexEnv : Array String) : IO IO.Process.Output := do
  let exe := (← IO.appPath).toString
  let tmpDir ← IO.FS.createTempDir
  try
    let src := tmpDir / "env_launcher.c"
    let bin := tmpDir / "env_launcher"
    IO.FS.writeFile src execHexEnvC
    let ccOut ← IO.Process.output {
      cmd := "cc"
      args := #["-O2", "-Wall", "-Wextra", "-Werror", src.toString, "-o", bin.toString]
    }
    assertRawTrue (ccOut.exitCode == 0) s!"failed to compile env probe launcher: {ccOut.stderr}"
    IO.Process.output {
      cmd := bin.toString
      args := #[exe, "--envvars-raw-probe"] ++ probeArgs ++ #["--sep"] ++ hexEnv
    }
  finally
    let _ ← try IO.FS.removeDirAll tmpDir; pure () catch _ => pure ()

private def envRawErrLine (e : EnvVarsRawError) : String :=
  let (key?, msg) := match e with
    | .invalidEncoding k? m => (k?, m)
    | .invalidArgument k? _ m => (k?, m)
    | .otherError _ m => (none, m)
    | .userError m => (none, m)
  s!"ERR:{envRawErrKindTag e.kind}:{key?.getD ""}:{msg}"

private def assertRawGetEnvUnset (key : String) : IO Unit := do
  match ← Raw.getEnv key with
  | .ok none => pure ()
  | other => throw (IO.userError s!"expected unset in-process raw getEnv to return ok none for {key}, got {repr other}")

/-- Subprocess entrypoint for testing `EnvVars.Raw` with controlled raw `environ` bytes. -/
def probeMain (args : List String) : IO UInt32 := do
  match args with
  | ["get", key] =>
    match ← Raw.getEnv key with
    | .ok none =>
      IO.println "OK:NONE"
      return 0
    | .ok (some v) =>
      IO.println s!"OK:SOME:{v}"
      return 0
    | .error e =>
      IO.println (envRawErrLine e)
      return 2
  | ["list"] =>
    match ← Raw.listEnv with
    | .error e =>
      IO.println (envRawErrLine e)
      return 2
    | .ok entries =>
      for (k, v) in entries do
        IO.println s!"ITEM:{k}={v}"
      return 0
  | _ =>
    IO.eprintln "unknown --envvars-raw-probe mode"
    return 3

/-- Verify `Raw.getEnv` returns `none` when an environment variable is unset. -/
def assume_envvarsraw_getEnv_unsetReturnsNone : IO Unit := do
  assertRawGetEnvUnset "__LEANSWE_UNSET_RAW_PROBE_9999__"
  let out ← runRawHexProbe #["get", "MISSING_KEY"] #[utf8ToHex "OTHER=1"]
  assertRawTrue (out.exitCode == 0 && out.stdout == "OK:NONE\n")
    s!"expected raw getEnv unset probe to print OK:NONE, got rc={out.exitCode} out={repr out.stdout}"

/-- Verify `Raw.getEnv` preserves valid UTF-8 value bytes and rejects invalid UTF-8 bytes. -/
def assume_envvarsraw_getEnv_preservesSetBytesAndRejectsInvalidUtf8 : IO Unit := do
  assertRawGetEnvUnset "__LEANSWE_UNSET_RAW_PROBE_2__"
  let okOut ← runRawHexProbe #["get", "VAL"] #[utf8ToHex "VAL=hello=world"]
  assertRawTrue (okOut.exitCode == 0 && okOut.stdout == "OK:SOME:hello=world\n")
    s!"expected raw getEnv to preserve valid bytes, got rc={okOut.exitCode} out={repr okOut.stdout}"
  let emptyOut ← runRawHexProbe #["get", "EMPTY"] #[utf8ToHex "EMPTY="]
  assertRawTrue (emptyOut.exitCode == 0 && emptyOut.stdout == "OK:SOME:\n")
    s!"expected raw getEnv to preserve empty string, got rc={emptyOut.exitCode} out={repr emptyOut.stdout}"
  let badOut ← runRawHexProbe #["get", "BAD"] #[utf8ToHex "BAD=" ++ "ff"]
  assertRawTrue (badOut.exitCode == 2 && badOut.stdout.startsWith "ERR:invalidEncoding:BAD:")
    s!"expected raw getEnv invalidEncoding on invalid UTF-8, got rc={badOut.exitCode} out={repr badOut.stdout}"

/-- Verify `Raw.listEnv` copies `environ` order and skips malformed entries without `'='` or with empty names. -/
def assume_envvarsraw_listEnv_copiesEnvironOrderAndSkipsMalformed : IO Unit := do
  let _ ← match ← Raw.listEnv with
    | .ok xs => pure xs
    | .error e => throw (IO.userError s!"in-process Raw.listEnv failed: {repr e}")
  let out ← runRawHexProbe #["list"]
    #[utf8ToHex "MALFORMED_NO_EQ", utf8ToHex "=empty", utf8ToHex "FIRST=1=a", utf8ToHex "SECOND=2", utf8ToHex "FIRST=3"]
  let expected := "ITEM:FIRST=1=a\nITEM:SECOND=2\nITEM:FIRST=3\n"
  assertRawTrue (out.exitCode == 0 && out.stdout == expected)
    s!"expected exact ordered filtered items {repr expected}, got rc={out.exitCode} out={repr out.stdout}"

/-- Verify `Raw.listEnv` agrees with `Raw.getEnv` on first occurrence and absent keys. -/
def assume_envvarsraw_listEnv_consistentWithGetEnv : IO Unit := do
  let entries ← match ← Raw.listEnv with
    | .ok xs => pure xs
    | .error e => throw (IO.userError s!"in-process Raw.listEnv failed: {repr e}")
  assertRawGetEnvUnset "__LEANSWE_UNSET_CONSISTENCY__"
  assertRawTrue (!entries.any (fun (k, _) => k == "__LEANSWE_UNSET_CONSISTENCY__"))
    "absent key consistent with listEnv"
  let dupEnv := #[utf8ToHex "DUP=first", utf8ToHex "DUP=second", utf8ToHex "SOLO=val"]
  let listOut ← runRawHexProbe #["list"] dupEnv
  assertRawTrue (listOut.exitCode == 0 && listOut.stdout == "ITEM:DUP=first\nITEM:DUP=second\nITEM:SOLO=val\n")
    s!"unexpected listEnv dup output: {repr listOut.stdout}"
  let getDup ← runRawHexProbe #["get", "DUP"] dupEnv
  assertRawTrue (getDup.exitCode == 0 && getDup.stdout == "OK:SOME:first\n")
    s!"unexpected getEnv DUP output: {repr getDup.stdout}"
  let getMissing ← runRawHexProbe #["get", "ABSENT"] dupEnv
  assertRawTrue (getMissing.exitCode == 0 && getMissing.stdout == "OK:NONE\n")
    s!"unexpected getEnv ABSENT output: {repr getMissing.stdout}"

/-- Registry of runtime assumption checks for `LeanSwe.EnvVars.Raw`. -/
def registeredAssumptions : Array Core.RegisteredAssumption := #[
  ⟨"LeanSwe.EnvVars.Raw.assume_envvarsraw_getEnv_unsetReturnsNone",
    assume_envvarsraw_getEnv_unsetReturnsNone⟩,
  ⟨"LeanSwe.EnvVars.Raw.assume_envvarsraw_getEnv_preservesSetBytesAndRejectsInvalidUtf8",
    assume_envvarsraw_getEnv_preservesSetBytesAndRejectsInvalidUtf8⟩,
  ⟨"LeanSwe.EnvVars.Raw.assume_envvarsraw_listEnv_copiesEnvironOrderAndSkipsMalformed",
    assume_envvarsraw_listEnv_copiesEnvironOrderAndSkipsMalformed⟩,
  ⟨"LeanSwe.EnvVars.Raw.assume_envvarsraw_listEnv_consistentWithGetEnv",
    assume_envvarsraw_listEnv_consistentWithGetEnv⟩
]

/-- Verify `Raw.getEnv` returns `.invalidEncoding` for invalid UTF-8 bytes in `environ`. -/
def err_envvarsraw_getEnv_invalidEncoding : IO Unit := do
  assertRawGetEnvUnset "__LEANSWE_UNSET_RAW_ERR_CHECK__"
  let out ← runRawHexProbe #["get", "BAD_VAL"] #[utf8ToHex "BAD_VAL=" ++ "fffe"]
  assertRawTrue (out.exitCode == 2 && out.stdout.startsWith "ERR:invalidEncoding:BAD_VAL:")
    s!"expected Raw.getEnv invalidEncoding error, got rc={out.exitCode} out={repr out.stdout}"

/-- Verify `Raw.listEnv` returns `.invalidEncoding` for invalid UTF-8 bytes in `environ`. -/
def err_envvarsraw_listEnv_invalidEncoding : IO Unit := do
  let _ ← match ← Raw.listEnv with
    | .ok xs => pure xs
    | .error e => throw (IO.userError s!"in-process Raw.listEnv failed: {repr e}")
  let badValOut ← runRawHexProbe #["list"] #[utf8ToHex "OK=1", utf8ToHex "BAD=" ++ "80"]
  assertRawTrue (badValOut.exitCode == 2 && badValOut.stdout.startsWith "ERR:invalidEncoding:BAD:")
    s!"expected Raw.listEnv invalidEncoding on value bytes, got rc={badValOut.exitCode} out={repr badValOut.stdout}"
  let badKeyOut ← runRawHexProbe #["list"] #["ff" ++ utf8ToHex "=val"]
  assertRawTrue (badKeyOut.exitCode == 2 && badKeyOut.stdout.startsWith "ERR:invalidEncoding::")
    s!"expected Raw.listEnv invalidEncoding on key bytes, got rc={badKeyOut.exitCode} out={repr badKeyOut.stdout}"

/-- Registry of error-coverage runtime tests for `LeanSwe.EnvVars.Raw`. -/
def registeredErrorTests : Array Core.RegisteredErrorTest := #[
  ⟨"LeanSwe.EnvVars.Raw.RuntimeTests.err_envvarsraw_getEnv_invalidEncoding", .real,
    err_envvarsraw_getEnv_invalidEncoding⟩,
  ⟨"LeanSwe.EnvVars.Raw.RuntimeTests.err_envvarsraw_listEnv_invalidEncoding", .real,
    err_envvarsraw_listEnv_invalidEncoding⟩
]

private def assertTrue (cond : Bool) (msg : String) : IO Unit := do
  if !cond then
    throw (IO.userError s!"ASSERTION FAILED: {msg}")

private def assertOk {α : Type} (res : Except Raw.EnvVarsRawError α) (msg : String) : IO α := do
  match res with
  | .ok v => return v
  | .error e => throw (IO.userError s!"ASSERTION FAILED: {msg} (unexpected error: {repr e})")

/-- Execute primitive OS environment grounding tests for `LeanSwe.EnvVars.Raw`. -/
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

  Core.runRegisteredAssumptions registeredAssumptions
  Core.runRegisteredErrorTests registeredErrorTests
  IO.println "PASS: LeanSwe.EnvVars.Raw runtime tests"

end LeanSwe.EnvVars.Raw.RuntimeTests
