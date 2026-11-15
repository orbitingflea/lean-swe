import LeanSwe.CmdLine.Interface
import LeanSwe.Process.Interface

namespace LeanSwe.CmdLine.RuntimeTests

open LeanSwe.CmdLine
open LeanSwe.Process

private def probeBasicSpec : CommandSpec :=
  { name := "probe"
    version := some "2.1.0"
    about := "Probe CLI"
    options :=
      [ { name := "flag", long := some "flag", short := some 'f', kind := .bool, help := "Boolean flag", global := true },
        { name := "count", long := some "count", short := some 'n', kind := .nat, default := some "3", envVar := some "PROBE_COUNT", help := "Count" },
        { name := "port", long := some "port", kind := .int, envVar := some "PROBE_PORT", help := "Port" },
        { name := "mode", long := some "mode", kind := .choice ["dev", "prod"], default := some "dev", help := "Mode" },
        { name := "tag", long := some "tag", short := some 't', kind := .string, repeatable := true, help := "Tag" } ]
    args :=
      [ { name := "input", required := false, help := "Input file" },
        { name := "extras", required := false, variadic := true, help := "Extra files" } ] }

private def probeSubSpec : CommandSpec :=
  { name := "probe"
    version := some "2.1.0"
    about := "Probe CLI"
    options :=
      [ { name := "flag", long := some "flag", short := some 'f', kind := .bool, help := "Boolean flag", global := true } ]
    subcommands :=
      [ { name := "sub"
          about := "Subcommand"
          options := [ { name := "subopt", long := some "subopt", short := some 's', kind := .string, help := "Sub option" } ]
          args := [ { name := "target", required := true, help := "Target" } ] } ] }

private def probeValidatedSpec : CommandSpec :=
  { name := "vprobe"
    version := some "1.0"
    options :=
      [ { name := "num", long := some "num", kind := .custom "even", envVar := some "PROBE_NUM", required := true, help := "Even number" } ] }

private def evenValidator (s : String) : Except String Unit :=
  match s.toNat? with
  | some n =>
    if n % 2 == 0 then
      .ok ()
    else
      .error "must be even"
  | none => .error "must be a natural number"

private def formatTags (cmd : ParsedCmd) : String :=
  String.intercalate "," ((cmd.getList "tag").filterMap fun
    | .string s => some s
    | _ => none)

private def formatBasicSummary (cmd : ParsedCmd) : String :=
  let sub := String.intercalate "/" cmd.subcommandPath
  let cnt := match cmd.getNat "count" with | some n => toString n | none => ""
  let port := match cmd.getInt "port" with | some i => toString i | none => ""
  let mode := cmd.getChoice "mode" |>.getD ""
  let flag := match cmd.getBool "flag" with | some b => toString b | none => ""
  let subopt := cmd.getString "subopt" |>.getD ""
  let target := cmd.getString "target" |>.getD ""
  let input := cmd.getString "input" |>.getD ""
  let tags := formatTags cmd
  let pos := String.intercalate "," cmd.rawPositionals
  s!"OK:{sub}:{cnt}:{port}:{mode}:{flag}:{subopt}:{target}:{input}:{tags}:{pos}"

/-- Subprocess probe entrypoint invoked via `--cmdline-probe` from `runAll`. -/
def probeMain (args : List String) : IO UInt32 := do
  match args with
  | "basic" :: rest =>
    CmdLine.runCli probeBasicSpec rest fun cmd => do
      IO.println (formatBasicSummary cmd)
      return 42
  | "withsub" :: rest =>
    CmdLine.runCli probeSubSpec rest fun cmd => do
      IO.println (formatBasicSummary cmd)
      return 42
  | "validated" :: rest =>
    CmdLine.runCliWith probeValidatedSpec rest [("even", evenValidator)] fun cmd => do
      match cmd.getCustom "num" (fun s => match s.toNat? with | some n => .ok n | none => .error "bad") with
      | .ok (some n) =>
        IO.println s!"VAL:{n}"
        return 7
      | .ok none =>
        IO.eprintln "missing num"
        return 2
      | .error e =>
        IO.eprintln e.message
        return 2
  | ["prompt"] =>
    match ← CmdLine.promptLine "Enter name" (some "anon") with
    | .error e =>
      IO.eprintln s!"ERR:{reprStr e.kind}:{e.message}"
      return 2
    | .ok name =>
      match ← CmdLine.confirm "Proceed?" (some false) 3 with
      | .error e =>
        IO.eprintln s!"ERR:{reprStr e.kind}:{e.message}"
        return 2
      | .ok ok =>
        IO.println s!"PROMPT:{name}:{ok}"
        return 0
  | ["prompt-strict"] =>
    match ← CmdLine.promptLine "Token" none with
    | .error e =>
      IO.eprintln s!"ERR:{reprStr e.kind}:{e.message}"
      return 2
    | .ok tok =>
      match ← CmdLine.confirm "OK?" none 2 with
      | .error e =>
        IO.eprintln s!"ERR:{reprStr e.kind}:{e.message}"
        return 2
      | .ok ok =>
        IO.println s!"STRICT:{tok}:{ok}"
        return 0
  | _ =>
    IO.eprintln "unknown --cmdline-probe mode"
    return 3

private def assertTrue (cond : Bool) (msg : String) : IO Unit := do
  if !cond then
    throw (IO.userError s!"ASSERTION FAILED: {msg}")

private def containsSubstr (haystack needle : String) : Bool :=
  (haystack.splitOn needle).length > 1

private def runProbe (exe : String) (args : Array String)
    (envOverrides : Array (String × Option String) := #[])
    (stdinText : Option String := none) : IO ExecResult := do
  let baseEnv : Array (String × Option String) :=
    #[("PROBE_COUNT", none), ("PROBE_PORT", none), ("PROBE_NUM", none)] ++ envOverrides
  let req0 := { Process.mkCommandRequest exe (#["--cmdline-probe"] ++ args) with env := baseEnv }
  let req := match stdinText with
    | some txt => Process.withTextInput req0 txt
    | none => req0
  match ← Process.run req with
  | .ok res => return res
  | .error e => throw (IO.userError s!"ASSERTION FAILED: Process.run failed: {repr e}")

/-- Execute real OS subprocess, environment-variable, and stdio grounding tests for `LeanSwe.CmdLine`. -/
def runAll : IO Unit := do
  let exe := (← IO.appPath).toString

  let rHelp ← runProbe exe #["basic", "--help"]
  assertTrue (rHelp.exitCode == 0) s!"--help exit code expected 0 got {rHelp.exitCode}"
  let helpOut := String.fromUTF8! rHelp.stdout
  assertTrue (containsSubstr helpOut "Usage: probe") s!"--help stdout missing usage: {helpOut}"
  assertTrue (!containsSubstr helpOut "OK:") "handler must not run on --help"
  assertTrue ((String.fromUTF8! rHelp.stderr) == "") "--help stderr must be empty"

  let rSubHelp ← runProbe exe #["withsub", "sub", "--help"]
  assertTrue (rSubHelp.exitCode == 0) "sub --help exit code"
  let subHelpOut := String.fromUTF8! rSubHelp.stdout
  assertTrue (containsSubstr subHelpOut "Usage: probe sub") s!"sub --help missing usage: {subHelpOut}"
  assertTrue (containsSubstr subHelpOut "--subopt") s!"sub --help missing --subopt: {subHelpOut}"

  let rVer ← runProbe exe #["basic", "--version"]
  assertTrue (rVer.exitCode == 0) "--version exit code"
  assertTrue (String.fromUTF8! rVer.stdout == "probe 2.1.0\n") s!"--version stdout mismatch: {String.fromUTF8! rVer.stdout}"
  assertTrue ((String.fromUTF8! rVer.stderr) == "") "--version stderr empty"

  let rUnk ← runProbe exe #["basic", "--unknown"]
  assertTrue (rUnk.exitCode == 2) s!"unknown option exit code expected 2 got {rUnk.exitCode}"
  assertTrue (String.fromUTF8! rUnk.stdout == "") "unknown option stdout empty"
  assertTrue (containsSubstr (String.fromUTF8! rUnk.stderr) "unknown option") "unknown option stderr"

  let rTypo ← runProbe exe #["basic", "--flga"]
  assertTrue (rTypo.exitCode == 2) "typo exit code"
  assertTrue (containsSubstr (String.fromUTF8! rTypo.stderr) "did you mean '--flag'") s!"typo suggestion missing: {String.fromUTF8! rTypo.stderr}"

  let rOk ← runProbe exe #["basic", "--flag", "-t", "a", "-t", "b", "file.txt"]
  assertTrue (rOk.exitCode == 42) s!"handler exit code expected 42 got {rOk.exitCode}"
  assertTrue (String.fromUTF8! rOk.stdout == "OK::3::dev:true:::file.txt:a,b:file.txt\n")
    s!"basic stdout mismatch: {repr (String.fromUTF8! rOk.stdout)}"

  let rSub ← runProbe exe #["withsub", "sub", "-s", "hi", "tgt"]
  assertTrue (rSub.exitCode == 42) "subcommand exit code"
  assertTrue (String.fromUTF8! rSub.stdout == "OK:sub::::false:hi:tgt:::tgt\n")
    s!"subcommand stdout mismatch: {repr (String.fromUTF8! rSub.stdout)}"

  let rEnv ← runProbe exe #["basic"]
    #[("PROBE_COUNT", some "9"), ("PROBE_PORT", some "-12")]
  assertTrue (rEnv.exitCode == 42) "env fallback exit code"
  assertTrue (String.fromUTF8! rEnv.stdout == "OK::9:-12:dev:false:::::\n")
    s!"env fallback stdout mismatch: {repr (String.fromUTF8! rEnv.stdout)}"

  let rCliOverEnv ← runProbe exe #["basic", "--count", "15", "--no-flag", "--mode", "prod"]
    #[("PROBE_COUNT", some "9")]
  assertTrue (rCliOverEnv.exitCode == 42) "CLI override env exit code"
  assertTrue (String.fromUTF8! rCliOverEnv.stdout == "OK::15::prod:false:::::\n")
    s!"CLI override stdout mismatch: {repr (String.fromUTF8! rCliOverEnv.stdout)}"

  let rEmptyEnv ← runProbe exe #["basic"] #[("PROBE_COUNT", some "")]
  assertTrue (rEmptyEnv.exitCode == 42) "empty env var falls back to default"
  assertTrue (String.fromUTF8! rEmptyEnv.stdout == "OK::3::dev:false:::::\n")
    s!"empty env fallback stdout mismatch: {repr (String.fromUTF8! rEmptyEnv.stdout)}"

  let rBadEnv ← runProbe exe #["basic"] #[("PROBE_COUNT", some "abc")]
  assertTrue (rBadEnv.exitCode == 2) "invalid env var rejected"
  assertTrue (containsSubstr (String.fromUTF8! rBadEnv.stderr) "invalid unsigned integer value 'abc'")
    s!"invalid env var stderr mismatch: {repr (String.fromUTF8! rBadEnv.stderr)}"

  let rValOk ← runProbe exe #["validated", "--num", "8"]
  assertTrue (rValOk.exitCode == 7) "validated success exit code 7"
  assertTrue (String.fromUTF8! rValOk.stdout == "VAL:8\n") "validated stdout"

  let rValBad ← runProbe exe #["validated", "--num", "3"]
  assertTrue (rValBad.exitCode == 2) "validated failure exit code 2"
  assertTrue (containsSubstr (String.fromUTF8! rValBad.stderr) "must be even") "validated stderr"

  let rValEnv ← runProbe exe #["validated"] #[("PROBE_NUM", some "10")]
  assertTrue (rValEnv.exitCode == 7) "validated env exit code 7"
  assertTrue (String.fromUTF8! rValEnv.stdout == "VAL:10\n") "validated env stdout"

  let rPromptOk ← runProbe exe #["prompt"] #[] (some "  alice  \nmaybe\nyes\n")
  assertTrue (rPromptOk.exitCode == 0) s!"prompt ok exit code got {rPromptOk.exitCode}"
  assertTrue (containsSubstr (String.fromUTF8! rPromptOk.stdout) "PROMPT:alice:true\n")
    s!"prompt ok stdout mismatch: {repr (String.fromUTF8! rPromptOk.stdout)}"
  assertTrue (containsSubstr (String.fromUTF8! rPromptOk.stderr) "Please answer yes or no.")
    "prompt reprompt writes hint to stderr"

  let rPromptDef ← runProbe exe #["prompt"] #[] (some "\n\n")
  assertTrue (rPromptDef.exitCode == 0) "prompt defaults exit code"
  assertTrue (containsSubstr (String.fromUTF8! rPromptDef.stdout) "PROMPT:anon:false\n")
    s!"prompt defaults stdout: {repr (String.fromUTF8! rPromptDef.stdout)}"

  let rPromptEof ← runProbe exe #["prompt-strict"] #[] (some "")
  assertTrue (rPromptEof.exitCode == 2) "strict prompt EOF exit code 2"
  assertTrue (containsSubstr (String.fromUTF8! rPromptEof.stderr) "ERR:LeanSwe.CmdLine.CmdLineErrorKind.eof")
    s!"strict prompt EOF stderr: {repr (String.fromUTF8! rPromptEof.stderr)}"

  let rConfirmExhaust ← runProbe exe #["prompt-strict"] #[] (some "tok\nfoo\nbar\n")
  assertTrue (rConfirmExhaust.exitCode == 2) "confirm maxAttempts exhausted exit code 2"
  assertTrue (containsSubstr (String.fromUTF8! rConfirmExhaust.stderr) "ERR:LeanSwe.CmdLine.CmdLineErrorKind.invalidValue")
    s!"confirm exhaustion stderr: {repr (String.fromUTF8! rConfirmExhaust.stderr)}"

  IO.println "PASS: LeanSwe.CmdLine runtime tests"

end LeanSwe.CmdLine.RuntimeTests
