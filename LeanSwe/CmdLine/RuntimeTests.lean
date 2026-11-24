import Core.Assumptions
import LeanSwe.CmdLine.Interface
import LeanSwe.LinuxSyscall.Files.Types
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
  | ["confirm-ioerr"] =>
    match ← CmdLine.confirm "OK?" none 2 with
    | .error e =>
      IO.eprintln s!"ERR:{reprStr e.kind}:{e.message}"
      return 2
    | .ok ok =>
      IO.println s!"CONFIRM:{ok}"
      return 0
  | ["prompt-eof"] =>
    match ← CmdLine.promptLine "Token" none with
    | .error e =>
      IO.eprintln s!"ERR:{reprStr e.kind}:{e.message}"
      return 2
    | .ok tok =>
      IO.println s!"TOK:{tok}"
      return 0
  | ["prompt-default"] =>
    match ← CmdLine.promptLine "Def" (some "d") with
    | .error e =>
      IO.eprintln s!"ERR:{reprStr e.kind}:{e.message}"
      return 2
    | .ok val =>
      IO.println s!"DEF:{val}"
      return 0
  | ["confirm-exhaust"] =>
    match ← CmdLine.confirm "OK?" none 2 with
    | .error e =>
      IO.eprintln s!"ERR:{reprStr e.kind}:{e.message}"
      return 2
    | .ok ok =>
      IO.println s!"CONFIRM:{ok}"
      return 0
  | ["parse-env-err"] =>
    match ← CmdLine.parseWithEnv probeBasicSpec [] with
    | .error e =>
      IO.eprintln s!"ERR:{reprStr e.kind}:{e.target.getD ""}:{e.message}"
      return 2
    | .ok p =>
      IO.println s!"OK:{repr p.options}"
      return 0
  | ["default-get-env", key] =>
    match ← CmdLine.defaultOps.getEnv key with
    | .error e =>
      IO.eprintln s!"ERR:{reprStr e.kind}:{e.target.getD ""}:{e.message}"
      return 2
    | .ok none =>
      IO.println "OK:NONE"
      return 0
    | .ok (some v) =>
      IO.println s!"OK:SOME:{v}"
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

private def cmdHexDigit (n : UInt8) : Char :=
  if n < 10 then Char.ofNat (48 + n.toNat) else Char.ofNat (87 + n.toNat)

private def cmdUtf8ToHex (s : String) : String := Id.run do
  let mut out : String := ""
  for b in s.toUTF8.data do
    out := out.push (cmdHexDigit (b >>> 4))
    out := out.push (cmdHexDigit (b &&& 0x0F))
  return out

private def execCmdProbeC : String :=
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
  "  int close_stdin = (argc >= 2 && strcmp(argv[1], \"--close-stdin\") == 0);\n" ++
  "  int start = close_stdin ? 2 : 1;\n" ++
  "  int sep = -1;\n" ++
  "  for (int i = start + 1; i < argc; i++) {\n" ++
  "    if (strcmp(argv[i], \"--sep\") == 0) { sep = i; break; }\n" ++
  "  }\n" ++
  "  if (sep < 0) return 10;\n" ++
  "  int child_argc = sep - start;\n" ++
  "  char **child_argv = (char **)calloc((size_t)child_argc + 1, sizeof(char *));\n" ++
  "  child_argv[0] = argv[start];\n" ++
  "  for (int i = start + 1; i < sep; i++) child_argv[i - start] = argv[i];\n" ++
  "  if (close_stdin) close(0);\n" ++
  "  int envc = argc - sep - 1;\n" ++
  "  char **envp = (char **)calloc((size_t)envc + 1, sizeof(char *));\n" ++
  "  for (int i = 0; i < envc; i++) {\n" ++
  "    envp[i] = dechex(argv[sep + 1 + i]);\n" ++
  "    if (!envp[i]) return 11;\n" ++
  "  }\n" ++
  "  execve(argv[start], child_argv, envp);\n" ++
  "  perror(\"execve\");\n" ++
  "  return 12;\n" ++
  "}\n"

private def runCmdCProbe (closeStdin : Bool) (probeArgs hexEnv : Array String) : IO IO.Process.Output := do
  let exe := (← IO.appPath).toString
  let tmpDir ← IO.FS.createTempDir
  try
    let src := tmpDir / "cmd_probe.c"
    let bin := tmpDir / "cmd_probe"
    IO.FS.writeFile src execCmdProbeC
    let ccOut ← IO.Process.output {
      cmd := "cc"
      args := #["-O2", "-Wall", "-Wextra", "-Werror", src.toString, "-o", bin.toString]
    }
    assertTrue (ccOut.exitCode == 0) s!"failed to compile cmd probe: {ccOut.stderr}"
    let preArgs := if closeStdin then #["--close-stdin"] else #[]
    IO.Process.output {
      cmd := bin.toString
      args := preArgs ++ #[exe, "--cmdline-probe"] ++ probeArgs ++ #["--sep"] ++ hexEnv
    }
  finally
    let _ ← try IO.FS.removeDirAll tmpDir; pure () catch _ => pure ()

private def readUntilByte (h : IO.FS.Handle) (target : UInt8) (limit : Nat := 256) : IO String := do
  let mut bytes : ByteArray := ByteArray.empty
  for _ in List.range limit do
    let chunk ← h.read 1
    if chunk.isEmpty then
      return String.fromUTF8! bytes
    bytes := bytes ++ chunk
    if chunk.get! 0 == target then
      return String.fromUTF8! bytes
  return String.fromUTF8! bytes

private def assertPureErrKind {α : Type} (res : Except CmdLineError α) (expected : CmdLineErrorKind)
    (msg : String) : IO Unit := do
  match res with
  | .ok _ => throw (IO.userError s!"ASSERTION FAILED: {msg} (expected {repr expected}, got ok)")
  | .error e =>
    assertTrue (e.kind == expected && !e.message.isEmpty)
      s!"{msg} (got {repr e}, expected {repr expected})"

private def assertIoErrKind {α : Type} (act : IO (Except CmdLineError α)) (expected : CmdLineErrorKind)
    (msg : String) : IO Unit := do
  assertPureErrKind (← act) expected msg

private def assertDefaultGetEnvUnset (key : String) : IO Unit := do
  match ← CmdLine.defaultOps.getEnv key with
  | .ok none => pure ()
  | .ok (some v) =>
    throw (IO.userError s!"ASSERTION FAILED: expected ok none for {key}, got some {repr v}")
  | .error e =>
    throw (IO.userError s!"ASSERTION FAILED: expected ok none for {key}, got error {repr e}")

private def covBadSpec : CommandSpec := {
  name := "bad"
  options := [
    { name := "dup", short := some 'd', long := some "dup" },
    { name := "dup", short := some 'x', long := some "dup2" }
  ]
}

private def covCustomValidators : CustomValidators :=
  [("even", fun s =>
    match s.toNat? with
    | some n => if n % 2 == 0 then .ok () else .error "must be even"
    | none => .error "expected nat")]

private def covSpec : CommandSpec := {
  name := "cov"
  version := some "1.0.0"
  options := [{ name := "flag", short := some 'f', long := some "flag", kind := .bool, global := true }]
  subcommands := [{
    name := "sub"
    options := [{ name := "target", long := some "target", kind := .string, required := true }]
    args := [{ name := "item", kind := .nat, required := true }]
  }]
}

private def covLeafSpec : CommandSpec := {
  name := "covleaf"
  version := some "1.0.0"
  options := [
    { name := "count", short := some 'c', long := some "count", kind := .nat, required := true },
    { name := "even", long := some "even", kind := .custom "even" },
    { name := "flag", short := some 'f', long := some "flag", kind := .bool }
  ]
  args := [{ name := "input", kind := .string, required := true }]
}

private def testDefaultOpsReadLineEof : IO Unit := do
  assertDefaultGetEnvUnset "__LEANSWE_UNSET_CMDLINE_ENV__"
  let exe := (← IO.appPath).toString
  let res ← runProbe exe #["prompt-eof"] #[] (some "")
  let err := String.fromUTF8! res.stderr
  assertTrue (res.exitCode == 2 && containsSubstr err "CmdLineErrorKind.eof")
    s!"expected eof on closed stdin, got rc={res.exitCode} err={repr err}"

private def testDefaultOpsReadLineStripsNewlines : IO Unit := do
  assertDefaultGetEnvUnset "__LEANSWE_UNSET_CMDLINE_ENV__"
  let exe := (← IO.appPath).toString
  let lfRes ← runProbe exe #["prompt-default"] #[] (some "alpha\n")
  let lfOut := String.fromUTF8! lfRes.stdout
  assertTrue (lfRes.exitCode == 0 && containsSubstr lfOut "DEF:alpha\n" && !containsSubstr lfOut "\r")
    s!"expected LF stripped, got rc={lfRes.exitCode} out={repr lfOut}"
  let crlfRes ← runProbe exe #["prompt-default"] #[] (some "beta\r\n")
  let crlfOut := String.fromUTF8! crlfRes.stdout
  assertTrue (crlfRes.exitCode == 0 && containsSubstr crlfOut "DEF:beta\n" && !containsSubstr crlfOut "\r")
    s!"expected CRLF stripped, got rc={crlfRes.exitCode} out={repr crlfOut}"

private def testDefaultOpsWriteOutFlushesBeforeRead : IO Unit := do
  assertDefaultGetEnvUnset "__LEANSWE_UNSET_CMDLINE_ENV__"
  let exe := (← IO.appPath).toString
  let child ← IO.Process.spawn {
    cmd := exe
    args := #["--cmdline-probe", "prompt-strict"]
    stdin := .piped
    stdout := .piped
    stderr := .piped
  }
  let (cIn, child) ← child.takeStdin
  let firstPrompt ← readUntilByte child.stdout 0x6E
  assertTrue (firstPrompt == "Token")
    s!"expected flushed stdout prompt before stdin write, got {repr firstPrompt}"
  cIn.putStr "abc\n"
  cIn.flush
  let secondPrompt ← readUntilByte child.stdout 0x3F
  assertTrue (secondPrompt == "OK?")
    s!"expected flushed confirm prompt before stdin write, got {repr secondPrompt}"
  cIn.putStr "yes\n"
  cIn.flush
  let rc ← child.wait
  let restOut ← child.stdout.readToEnd
  assertTrue (rc == 0 && containsSubstr restOut "STRICT:abc:true")
    s!"expected prompt-strict exit 0 with STRICT:abc:true, got rc={rc} out={repr restOut}"

private def testDefaultOpsWriteErrFlushesBeforeRead : IO Unit := do
  assertDefaultGetEnvUnset "__LEANSWE_UNSET_CMDLINE_ENV__"
  let exe := (← IO.appPath).toString
  let child ← IO.Process.spawn {
    cmd := exe
    args := #["--cmdline-probe", "prompt-strict"]
    stdin := .piped
    stdout := .piped
    stderr := .piped
  }
  let (cIn, child) ← child.takeStdin
  let p1 ← readUntilByte child.stdout 0x6E
  assertTrue (p1 == "Token") s!"expected Token prompt, got {repr p1}"
  cIn.putStr "xyz\n"
  cIn.flush
  let p2 ← readUntilByte child.stdout 0x3F
  assertTrue (p2 == "OK?") s!"expected confirm prompt, got {repr p2}"
  cIn.putStr "maybe\n"
  cIn.flush
  let errLine ← readUntilByte child.stderr 0x0A
  assertTrue (errLine == "Please answer yes or no.\n")
    s!"expected flushed stderr retry prompt before next stdin write, got {repr errLine}"
  let p3 ← readUntilByte child.stdout 0x3F
  assertTrue (p3 == "OK?") s!"expected second confirm prompt, got {repr p3}"
  cIn.putStr "yes\n"
  cIn.flush
  let rc ← child.wait
  let restOut ← child.stdout.readToEnd
  assertTrue (rc == 0 && containsSubstr restOut "STRICT:xyz:true")
    s!"expected prompt-strict exit 0 after retry, got rc={rc} out={repr restOut}"

private def testDefaultOpsGetEnvMapsEnvVars : IO Unit := do
  assertDefaultGetEnvUnset "__LEANSWE_UNSET_CMDLINE_ENV__"
  let okOut ← runCmdCProbe false #["default-get-env", "MY_VAR"] #[cmdUtf8ToHex "MY_VAR=ok_val"]
  assertTrue (okOut.exitCode == 0 && okOut.stdout == "OK:SOME:ok_val\n")
    s!"expected defaultOps.getEnv ok some, got rc={okOut.exitCode} out={repr okOut.stdout}"
  let badOut ← runCmdCProbe false #["default-get-env", "BAD_VAR"] #[cmdUtf8ToHex "BAD_VAR=" ++ "ff"]
  assertTrue (badOut.exitCode == 2 && containsSubstr badOut.stderr "CmdLineErrorKind.ioError:BAD_VAR:")
    s!"expected defaultOps.getEnv ioError on invalid UTF-8, got rc={badOut.exitCode} err={repr badOut.stderr}"

private structure MockStdioState where
  inBytes : ByteArray := ByteArray.empty
  inOff : Nat := 0
  readEintrLeft : Nat := 0
  writeEintrLeft : Nat := 0
  writeZeroOnce : Bool := false
  dupFailErr? : Option LinuxSyscall.Errno := none
  outBytes : ByteArray := ByteArray.empty
  errBytes : ByteArray := ByteArray.empty
  openCount : Nat := 0

private def mkMockStdioFilesOps (stRef : IO.Ref MockStdioState) :
    LinuxSyscall.Files.FilesOpsM IO LinuxSyscall.Files.StdioFd :=
  let sentinel := LinuxSyscall.Errno.ENOSYS
  { openat := fun _ _ _ _ => pure (.error sentinel)
    openat2 := fun _ _ _ => pure (.error sentinel)
    close := fun _ => stRef.modifyGet fun st => (.ok (), { st with openCount := st.openCount - 1 })
    read := fun _ n => stRef.modifyGet fun st =>
      if st.readEintrLeft > 0 then
        (.error LinuxSyscall.Errno.EINTR, { st with readEintrLeft := st.readEintrLeft - 1 })
      else if n == 0 || st.inOff >= st.inBytes.size then
        (.ok ByteArray.empty, st)
      else
        let b := st.inBytes[st.inOff]!
        (.ok (ByteArray.mk #[b]), { st with inOff := st.inOff + 1 })
    write := fun slot slice => stRef.modifyGet fun st =>
      if st.writeEintrLeft > 0 then
        (.error LinuxSyscall.Errno.EINTR, { st with writeEintrLeft := st.writeEintrLeft - 1 })
      else if st.writeZeroOnce then
        (.ok 0, { st with writeZeroOnce := false })
      else
        let takeN := min 2 slice.size
        let part := slice.extract 0 takeN
        let st' := match slot with
          | .stdout => { st with outBytes := st.outBytes ++ part }
          | .stderr => { st with errBytes := st.errBytes ++ part }
          | .stdin => st
        (.ok (UInt32.ofNat takeN), st')
    fstat := fun _ => pure (.error sentinel)
    fstatat := fun _ _ _ => pure (.error sentinel)
    faccessat := fun _ _ _ _ => pure (.error sentinel)
    mkdirat := fun _ _ _ => pure (.error sentinel)
    unlinkat := fun _ _ _ => pure (.error sentinel)
    renameat2 := fun _ _ _ _ _ => pure (.error sentinel)
    symlinkat := fun _ _ _ => pure (.error sentinel)
    readlinkat := fun _ _ _ => pure (.error sentinel)
    getdents64 := fun _ _ => pure (.error sentinel)
    fchmodat := fun _ _ _ => pure (.error sentinel)
    fchmod := fun _ _ => pure (.error sentinel)
    flock := fun _ _ => pure (.error sentinel)
    fcntl := fun _ _ => pure (.error sentinel)
    fsync := fun _ => pure (.error sentinel)
    getcwd := fun _ => pure (.error sentinel)
    lseek := fun _ _ _ => pure (.error sentinel)
    reopenReadOnly := fun _ => pure (.error sentinel)
    dupStdio := fun slot => stRef.modifyGet fun st =>
      match st.dupFailErr? with
      | some e => (.error e, st)
      | none => (.ok slot, { st with openCount := st.openCount + 1 }) }

private def testMkFilesCliOpsLive : IO Unit := do
  let stRef ← IO.mkRef
    { inBytes := "  yes \r\nnext\n".toUTF8
      readEintrLeft := 2
      writeEintrLeft := 2 : MockStdioState }
  let cliOps := CmdLine.SysBridge.mkFilesCliOps (mkMockStdioFilesOps stRef)
    (fun k => pure (.ok (if k == "CLI_OPT" then some "env_val" else none)))
  let cRes ← CmdLine.confirmM cliOps "Proceed? " none 3
  assertTrue (match cRes with | .ok true => true | _ => false) "confirmM eintr+shortwrite"
  let pRes ← CmdLine.promptLineM cliOps "Next: " none
  assertTrue (match pRes with | .ok "next" => true | _ => false) "promptLineM second line"
  let eofRes ← CmdLine.promptLineM cliOps "Eof: " (some "defv")
  assertTrue (match eofRes with | .error e => e.kind == .eof | _ => false) "promptLineM eof"
  let sp : CmdLine.CommandSpec :=
    { name := "demo"
      version := some "2.0"
      options := [{ name := "opt", long := some "opt", kind := .string, envVar := some "CLI_OPT", default := some "fb" }] }
  let rcHelp ← CmdLine.runCliM cliOps sp ["--help"] (fun _ => pure 0)
  let rcVer ← CmdLine.runCliM cliOps sp ["--version"] (fun _ => pure 0)
  let rcBad ← CmdLine.runCliM cliOps sp ["--unknown"] (fun _ => pure 0)
  let rcOk ← CmdLine.runCliM cliOps sp [] (fun p => pure (if p.getString "opt" == some "env_val" then 0 else 9))
  assertTrue (rcHelp == 0 && rcVer == 0 && rcBad == 2 && rcOk == 0) "runCliM exit codes"
  let stMid ← stRef.get
  assertTrue (stMid.openCount == 0 && !stMid.outBytes.isEmpty && !stMid.errBytes.isEmpty) "stdio fds closed"
  stRef.set { inBytes := "ok\n".toUTF8, readEintrLeft := CmdLine.SysBridge.stdioEintrFuel }
  let readAtLimit ← cliOps.readLine
  assertTrue (readAtLimit == some "ok" && (← stRef.get).openCount == 0)
    "readLine absorbs exact stdioEintrFuel (64) consecutive EINTRs"
  stRef.set { inBytes := "ok\n".toUTF8, readEintrLeft := CmdLine.SysBridge.stdioEintrFuel + 1 }
  let readIntr ← try let _ ← cliOps.readLine; pure false catch e => pure (match e with | .interrupted _ 4 _ => true | _ => false)
  assertTrue (readIntr && (← stRef.get).openCount == 0) "readLine fails EINTR after stdioEintrFuel + 1 (65) and closes fd"
  stRef.set { writeEintrLeft := CmdLine.SysBridge.stdioEintrFuel }
  cliOps.writeOut "xy"
  let stWrLim ← stRef.get
  assertTrue (stWrLim.outBytes == "xy".toUTF8 && stWrLim.openCount == 0)
    "writeOut absorbs exact stdioEintrFuel (64) consecutive EINTRs"
  stRef.set { writeEintrLeft := CmdLine.SysBridge.stdioEintrFuel + 1 }
  let writeIntr ← try cliOps.writeOut "x"; pure false catch e => pure (match e with | .interrupted _ 4 _ => true | _ => false)
  assertTrue (writeIntr && (← stRef.get).openCount == 0) "writeOut fails EINTR after stdioEintrFuel + 1 (65) and closes fd"
  stRef.set { writeZeroOnce := true }
  let writeZero ← try cliOps.writeErr "x"; pure false catch e => pure (match e with | .hardwareFault 5 _ => true | _ => false)
  assertTrue (writeZero && (← stRef.get).openCount == 0) "writeErr 0-byte write returns EIO and closes fd"
  stRef.set { dupFailErr? := some LinuxSyscall.Errno.EBADF }
  let dupErr ← try let _ ← cliOps.readLine; pure false catch e => pure (match e with | .invalidArgument _ 9 _ => true | _ => false)
  assertTrue (dupErr && (← stRef.get).openCount == 0) "dupStdio EBADF throws invalidArgument 9"
  cliOps.writeOut ""
  cliOps.writeErr ""
  assertTrue ((← stRef.get).openCount == 0) "empty writeOut/writeErr bypasses dupStdio"

/-- Error test for `CmdLine.parse` returning `.helpRequested`. -/
def err_cmdline_parse_helpRequested : IO Unit :=
  assertPureErrKind (CmdLine.parse covSpec ["--help"]) .helpRequested "parse helpRequested"

/-- Error test for `CmdLine.parse` returning `.versionRequested`. -/
def err_cmdline_parse_versionRequested : IO Unit :=
  assertPureErrKind (CmdLine.parse covSpec ["--version"]) .versionRequested "parse versionRequested"

/-- Error test for `CmdLine.parse` returning `.unknownOption`. -/
def err_cmdline_parse_unknownOption : IO Unit :=
  assertPureErrKind (CmdLine.parse covLeafSpec ["--nope"]) .unknownOption "parse unknownOption"

/-- Error test for `CmdLine.parse` returning `.missingOption`. -/
def err_cmdline_parse_missingOption : IO Unit :=
  assertPureErrKind (CmdLine.parse covLeafSpec ["in.txt"]) .missingOption "parse missingOption"

/-- Error test for `CmdLine.parse` returning `.missingArgument`. -/
def err_cmdline_parse_missingArgument : IO Unit :=
  assertPureErrKind (CmdLine.parse covLeafSpec ["--count", "1"]) .missingArgument "parse missingArgument"

/-- Error test for `CmdLine.parse` returning `.unexpectedArgument`. -/
def err_cmdline_parse_unexpectedArgument : IO Unit :=
  assertPureErrKind (CmdLine.parse covLeafSpec ["--count", "1", "a", "b"]) .unexpectedArgument "parse unexpectedArgument"

/-- Error test for `CmdLine.parse` returning `.invalidValue`. -/
def err_cmdline_parse_invalidValue : IO Unit :=
  assertPureErrKind (CmdLine.parse covLeafSpec ["--count", "abc", "in.txt"]) .invalidValue "parse invalidValue"

/-- Error test for `CmdLine.parse` returning `.unknownSubcommand`. -/
def err_cmdline_parse_unknownSubcommand : IO Unit :=
  assertPureErrKind (CmdLine.parse covSpec ["ghost"]) .unknownSubcommand "parse unknownSubcommand"

/-- Error test for `CmdLine.parse` returning `.invalidSpec`. -/
def err_cmdline_parse_invalidSpec : IO Unit :=
  assertPureErrKind (CmdLine.parse covBadSpec []) .invalidSpec "parse invalidSpec"

/-- Error test for `CmdLine.parseWith` returning `.helpRequested`. -/
def err_cmdline_parseWith_helpRequested : IO Unit :=
  assertPureErrKind (CmdLine.parseWith covLeafSpec ["-h"] covCustomValidators) .helpRequested "parseWith helpRequested"

/-- Error test for `CmdLine.parseWith` returning `.versionRequested`. -/
def err_cmdline_parseWith_versionRequested : IO Unit :=
  assertPureErrKind (CmdLine.parseWith covLeafSpec ["-V"] covCustomValidators) .versionRequested "parseWith versionRequested"

/-- Error test for `CmdLine.parseWith` returning `.unknownOption`. -/
def err_cmdline_parseWith_unknownOption : IO Unit :=
  assertPureErrKind (CmdLine.parseWith covLeafSpec ["-z"] covCustomValidators) .unknownOption "parseWith unknownOption"

/-- Error test for `CmdLine.parseWith` returning `.missingOption`. -/
def err_cmdline_parseWith_missingOption : IO Unit :=
  assertPureErrKind (CmdLine.parseWith covLeafSpec ["in.txt"] covCustomValidators) .missingOption "parseWith missingOption"

/-- Error test for `CmdLine.parseWith` returning `.missingArgument`. -/
def err_cmdline_parseWith_missingArgument : IO Unit :=
  assertPureErrKind (CmdLine.parseWith covLeafSpec ["--count=2"] covCustomValidators) .missingArgument "parseWith missingArgument"

/-- Error test for `CmdLine.parseWith` returning `.unexpectedArgument`. -/
def err_cmdline_parseWith_unexpectedArgument : IO Unit :=
  assertPureErrKind (CmdLine.parseWith covLeafSpec ["--count=2", "a", "b"] covCustomValidators) .unexpectedArgument "parseWith unexpectedArgument"

/-- Error test for `CmdLine.parseWith` returning `.invalidValue`. -/
def err_cmdline_parseWith_invalidValue : IO Unit :=
  assertPureErrKind (CmdLine.parseWith covLeafSpec ["--count=2", "--even=3", "in.txt"] covCustomValidators) .invalidValue "parseWith invalidValue"

/-- Error test for `CmdLine.parseWith` returning `.unknownSubcommand`. -/
def err_cmdline_parseWith_unknownSubcommand : IO Unit :=
  assertPureErrKind (CmdLine.parseWith covSpec ["ghost"] covCustomValidators) .unknownSubcommand "parseWith unknownSubcommand"

/-- Error test for `CmdLine.parseWith` returning `.invalidSpec`. -/
def err_cmdline_parseWith_invalidSpec : IO Unit :=
  assertPureErrKind (CmdLine.parseWith covBadSpec [] covCustomValidators) .invalidSpec "parseWith invalidSpec"

/-- Error test for `CmdLine.parseWithEnv` returning `.helpRequested`. -/
def err_cmdline_parseWithEnv_helpRequested : IO Unit :=
  assertIoErrKind (CmdLine.parseWithEnv covLeafSpec ["--help"] covCustomValidators) .helpRequested "parseWithEnv helpRequested"

/-- Error test for `CmdLine.parseWithEnv` returning `.versionRequested`. -/
def err_cmdline_parseWithEnv_versionRequested : IO Unit :=
  assertIoErrKind (CmdLine.parseWithEnv covLeafSpec ["--version"] covCustomValidators) .versionRequested "parseWithEnv versionRequested"

/-- Error test for `CmdLine.parseWithEnv` returning `.unknownOption`. -/
def err_cmdline_parseWithEnv_unknownOption : IO Unit :=
  assertIoErrKind (CmdLine.parseWithEnv covLeafSpec ["--nope"] covCustomValidators) .unknownOption "parseWithEnv unknownOption"

/-- Error test for `CmdLine.parseWithEnv` returning `.missingOption`. -/
def err_cmdline_parseWithEnv_missingOption : IO Unit :=
  assertIoErrKind (CmdLine.parseWithEnv covLeafSpec ["in.txt"] covCustomValidators) .missingOption "parseWithEnv missingOption"

/-- Error test for `CmdLine.parseWithEnv` returning `.missingArgument`. -/
def err_cmdline_parseWithEnv_missingArgument : IO Unit :=
  assertIoErrKind (CmdLine.parseWithEnv covLeafSpec ["--count=1"] covCustomValidators) .missingArgument "parseWithEnv missingArgument"

/-- Error test for `CmdLine.parseWithEnv` returning `.unexpectedArgument`. -/
def err_cmdline_parseWithEnv_unexpectedArgument : IO Unit :=
  assertIoErrKind (CmdLine.parseWithEnv covLeafSpec ["--count=1", "a", "b"] covCustomValidators) .unexpectedArgument "parseWithEnv unexpectedArgument"

/-- Error test for `CmdLine.parseWithEnv` returning `.invalidValue`. -/
def err_cmdline_parseWithEnv_invalidValue : IO Unit :=
  assertIoErrKind (CmdLine.parseWithEnv covLeafSpec ["--count=1", "--even=5", "in.txt"] covCustomValidators) .invalidValue "parseWithEnv invalidValue"

/-- Error test for `CmdLine.parseWithEnv` returning `.unknownSubcommand`. -/
def err_cmdline_parseWithEnv_unknownSubcommand : IO Unit :=
  assertIoErrKind (CmdLine.parseWithEnv covSpec ["ghost"] covCustomValidators) .unknownSubcommand "parseWithEnv unknownSubcommand"

/-- Error test for `CmdLine.parseWithEnv` returning `.invalidSpec`. -/
def err_cmdline_parseWithEnv_invalidSpec : IO Unit :=
  assertIoErrKind (CmdLine.parseWithEnv covBadSpec [] covCustomValidators) .invalidSpec "parseWithEnv invalidSpec"

/-- Error test for `CmdLine.parseWithEnv` returning `.ioError` on non-UTF-8 environment bytes. -/
def err_cmdline_parseWithEnv_ioError : IO Unit := do
  assertIoErrKind (CmdLine.parseWithEnv covBadSpec [] covCustomValidators) .invalidSpec "parseWithEnv baseline"
  let out ← runCmdCProbe false #["parse-env-err"] #[cmdUtf8ToHex "PROBE_PORT=" ++ "ff"]
  assertTrue (out.exitCode == 2 && containsSubstr out.stderr "CmdLineErrorKind.ioError:PROBE_PORT:")
    s!"expected parseWithEnv ioError on invalid UTF-8 env, got rc={out.exitCode} err={repr out.stderr}"

/-- Error test for `CmdLine.renderHelp` returning `.unknownSubcommand`. -/
def err_cmdline_renderHelp_unknownSubcommand : IO Unit :=
  assertPureErrKind (CmdLine.renderHelp covSpec ["ghost"]) .unknownSubcommand "renderHelp unknownSubcommand"

/-- Error test for `CmdLine.renderHelp` returning `.invalidSpec`. -/
def err_cmdline_renderHelp_invalidSpec : IO Unit :=
  assertPureErrKind (CmdLine.renderHelp covBadSpec) .invalidSpec "renderHelp invalidSpec"

/-- Error test for `CmdLine.renderArgs` returning `.missingArgument`. -/
def err_cmdline_renderArgs_missingArgument : IO Unit :=
  assertPureErrKind (CmdLine.renderArgs covSpec {}) .missingArgument "renderArgs missingArgument"

/-- Error test for `CmdLine.renderArgs` returning `.invalidValue`. -/
def err_cmdline_renderArgs_invalidValue : IO Unit :=
  assertPureErrKind (CmdLine.renderArgs covLeafSpec { options := [("flag", [.bool true, .bool false])], args := [("input", [.string "x"])] }) .invalidValue "renderArgs invalidValue"

/-- Error test for `CmdLine.renderArgs` returning `.unknownSubcommand`. -/
def err_cmdline_renderArgs_unknownSubcommand : IO Unit :=
  assertPureErrKind (CmdLine.renderArgs covSpec { subcommandPath := ["ghost"] }) .unknownSubcommand "renderArgs unknownSubcommand"

/-- Error test for `CmdLine.renderArgs` returning `.invalidSpec`. -/
def err_cmdline_renderArgs_invalidSpec : IO Unit :=
  assertPureErrKind (CmdLine.renderArgs covBadSpec {}) .invalidSpec "renderArgs invalidSpec"

/-- Error test for `CmdLine.promptLine` returning `.eof`. -/
def err_cmdline_promptLine_eof : IO Unit := do
  assertDefaultGetEnvUnset "__LEANSWE_UNSET_CMDLINE_ERR__"
  let exe := (← IO.appPath).toString
  let res ← runProbe exe #["prompt-eof"] #[] (some "")
  let err := String.fromUTF8! res.stderr
  assertTrue (res.exitCode == 2 && containsSubstr err "CmdLineErrorKind.eof")
    s!"expected promptLine eof, got rc={res.exitCode} err={repr err}"

/-- Error test for `CmdLine.promptLine` returning `.ioError` on closed stdin. -/
def err_cmdline_promptLine_ioError : IO Unit := do
  assertDefaultGetEnvUnset "__LEANSWE_UNSET_CMDLINE_ERR__"
  let out ← runCmdCProbe true #["prompt-eof"] #[]
  assertTrue (out.exitCode == 2 && containsSubstr out.stderr "CmdLineErrorKind.ioError")
    s!"expected promptLine ioError on closed fd 0, got rc={out.exitCode} err={repr out.stderr}"

/-- Error test for `CmdLine.confirm` returning `.invalidValue`. -/
def err_cmdline_confirm_invalidValue : IO Unit := do
  assertDefaultGetEnvUnset "__LEANSWE_UNSET_CMDLINE_ERR__"
  let exe := (← IO.appPath).toString
  let res ← runProbe exe #["confirm-exhaust"] #[] (some "maybe\nperhaps\n")
  let err := String.fromUTF8! res.stderr
  assertTrue (res.exitCode == 2 && containsSubstr err "CmdLineErrorKind.invalidValue")
    s!"expected confirm invalidValue, got rc={res.exitCode} err={repr err}"

/-- Error test for `CmdLine.confirm` returning `.eof`. -/
def err_cmdline_confirm_eof : IO Unit := do
  assertDefaultGetEnvUnset "__LEANSWE_UNSET_CMDLINE_ERR__"
  let exe := (← IO.appPath).toString
  let res ← runProbe exe #["prompt-strict"] #[] (some "name\n")
  let err := String.fromUTF8! res.stderr
  assertTrue (res.exitCode == 2 && containsSubstr err "CmdLineErrorKind.eof")
    s!"expected confirm eof, got rc={res.exitCode} err={repr err}"

/-- Error test for `CmdLine.confirm` returning `.ioError` on closed stdin. -/
def err_cmdline_confirm_ioError : IO Unit := do
  assertDefaultGetEnvUnset "__LEANSWE_UNSET_CMDLINE_ERR__"
  let out ← runCmdCProbe true #["confirm-ioerr"] #[]
  assertTrue (out.exitCode == 2 && containsSubstr out.stderr "CmdLineErrorKind.ioError")
    s!"expected confirm ioError on closed fd 0, got rc={out.exitCode} err={repr out.stderr}"

/-- Registry of error-coverage runtime tests for `LeanSwe.CmdLine`. -/
def registeredErrorTests : Array Core.RegisteredErrorTest := #[
  ⟨"LeanSwe.CmdLine.RuntimeTests.err_cmdline_parse_helpRequested", .real, err_cmdline_parse_helpRequested⟩,
  ⟨"LeanSwe.CmdLine.RuntimeTests.err_cmdline_parse_versionRequested", .real, err_cmdline_parse_versionRequested⟩,
  ⟨"LeanSwe.CmdLine.RuntimeTests.err_cmdline_parse_unknownOption", .real, err_cmdline_parse_unknownOption⟩,
  ⟨"LeanSwe.CmdLine.RuntimeTests.err_cmdline_parse_missingOption", .real, err_cmdline_parse_missingOption⟩,
  ⟨"LeanSwe.CmdLine.RuntimeTests.err_cmdline_parse_missingArgument", .real, err_cmdline_parse_missingArgument⟩,
  ⟨"LeanSwe.CmdLine.RuntimeTests.err_cmdline_parse_unexpectedArgument", .real, err_cmdline_parse_unexpectedArgument⟩,
  ⟨"LeanSwe.CmdLine.RuntimeTests.err_cmdline_parse_invalidValue", .real, err_cmdline_parse_invalidValue⟩,
  ⟨"LeanSwe.CmdLine.RuntimeTests.err_cmdline_parse_unknownSubcommand", .real, err_cmdline_parse_unknownSubcommand⟩,
  ⟨"LeanSwe.CmdLine.RuntimeTests.err_cmdline_parse_invalidSpec", .real, err_cmdline_parse_invalidSpec⟩,
  ⟨"LeanSwe.CmdLine.RuntimeTests.err_cmdline_parseWith_helpRequested", .real, err_cmdline_parseWith_helpRequested⟩,
  ⟨"LeanSwe.CmdLine.RuntimeTests.err_cmdline_parseWith_versionRequested", .real, err_cmdline_parseWith_versionRequested⟩,
  ⟨"LeanSwe.CmdLine.RuntimeTests.err_cmdline_parseWith_unknownOption", .real, err_cmdline_parseWith_unknownOption⟩,
  ⟨"LeanSwe.CmdLine.RuntimeTests.err_cmdline_parseWith_missingOption", .real, err_cmdline_parseWith_missingOption⟩,
  ⟨"LeanSwe.CmdLine.RuntimeTests.err_cmdline_parseWith_missingArgument", .real, err_cmdline_parseWith_missingArgument⟩,
  ⟨"LeanSwe.CmdLine.RuntimeTests.err_cmdline_parseWith_unexpectedArgument", .real, err_cmdline_parseWith_unexpectedArgument⟩,
  ⟨"LeanSwe.CmdLine.RuntimeTests.err_cmdline_parseWith_invalidValue", .real, err_cmdline_parseWith_invalidValue⟩,
  ⟨"LeanSwe.CmdLine.RuntimeTests.err_cmdline_parseWith_unknownSubcommand", .real, err_cmdline_parseWith_unknownSubcommand⟩,
  ⟨"LeanSwe.CmdLine.RuntimeTests.err_cmdline_parseWith_invalidSpec", .real, err_cmdline_parseWith_invalidSpec⟩,
  ⟨"LeanSwe.CmdLine.RuntimeTests.err_cmdline_parseWithEnv_helpRequested", .real, err_cmdline_parseWithEnv_helpRequested⟩,
  ⟨"LeanSwe.CmdLine.RuntimeTests.err_cmdline_parseWithEnv_versionRequested", .real, err_cmdline_parseWithEnv_versionRequested⟩,
  ⟨"LeanSwe.CmdLine.RuntimeTests.err_cmdline_parseWithEnv_unknownOption", .real, err_cmdline_parseWithEnv_unknownOption⟩,
  ⟨"LeanSwe.CmdLine.RuntimeTests.err_cmdline_parseWithEnv_missingOption", .real, err_cmdline_parseWithEnv_missingOption⟩,
  ⟨"LeanSwe.CmdLine.RuntimeTests.err_cmdline_parseWithEnv_missingArgument", .real, err_cmdline_parseWithEnv_missingArgument⟩,
  ⟨"LeanSwe.CmdLine.RuntimeTests.err_cmdline_parseWithEnv_unexpectedArgument", .real, err_cmdline_parseWithEnv_unexpectedArgument⟩,
  ⟨"LeanSwe.CmdLine.RuntimeTests.err_cmdline_parseWithEnv_invalidValue", .real, err_cmdline_parseWithEnv_invalidValue⟩,
  ⟨"LeanSwe.CmdLine.RuntimeTests.err_cmdline_parseWithEnv_unknownSubcommand", .real, err_cmdline_parseWithEnv_unknownSubcommand⟩,
  ⟨"LeanSwe.CmdLine.RuntimeTests.err_cmdline_parseWithEnv_invalidSpec", .real, err_cmdline_parseWithEnv_invalidSpec⟩,
  ⟨"LeanSwe.CmdLine.RuntimeTests.err_cmdline_parseWithEnv_ioError", .real, err_cmdline_parseWithEnv_ioError⟩,
  ⟨"LeanSwe.CmdLine.RuntimeTests.err_cmdline_renderHelp_unknownSubcommand", .real, err_cmdline_renderHelp_unknownSubcommand⟩,
  ⟨"LeanSwe.CmdLine.RuntimeTests.err_cmdline_renderHelp_invalidSpec", .real, err_cmdline_renderHelp_invalidSpec⟩,
  ⟨"LeanSwe.CmdLine.RuntimeTests.err_cmdline_renderArgs_missingArgument", .real, err_cmdline_renderArgs_missingArgument⟩,
  ⟨"LeanSwe.CmdLine.RuntimeTests.err_cmdline_renderArgs_invalidValue", .real, err_cmdline_renderArgs_invalidValue⟩,
  ⟨"LeanSwe.CmdLine.RuntimeTests.err_cmdline_renderArgs_unknownSubcommand", .real, err_cmdline_renderArgs_unknownSubcommand⟩,
  ⟨"LeanSwe.CmdLine.RuntimeTests.err_cmdline_renderArgs_invalidSpec", .real, err_cmdline_renderArgs_invalidSpec⟩,
  ⟨"LeanSwe.CmdLine.RuntimeTests.err_cmdline_promptLine_eof", .real, err_cmdline_promptLine_eof⟩,
  ⟨"LeanSwe.CmdLine.RuntimeTests.err_cmdline_promptLine_ioError", .real, err_cmdline_promptLine_ioError⟩,
  ⟨"LeanSwe.CmdLine.RuntimeTests.err_cmdline_confirm_invalidValue", .real, err_cmdline_confirm_invalidValue⟩,
  ⟨"LeanSwe.CmdLine.RuntimeTests.err_cmdline_confirm_eof", .real, err_cmdline_confirm_eof⟩,
  ⟨"LeanSwe.CmdLine.RuntimeTests.err_cmdline_confirm_ioError", .real, err_cmdline_confirm_ioError⟩
]

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

  testDefaultOpsReadLineEof
  testDefaultOpsReadLineStripsNewlines
  testDefaultOpsWriteOutFlushesBeforeRead
  testDefaultOpsWriteErrFlushesBeforeRead
  testDefaultOpsGetEnvMapsEnvVars
  testMkFilesCliOpsLive
  Core.runRegisteredErrorTests registeredErrorTests
  IO.println "PASS: LeanSwe.CmdLine runtime tests"

end LeanSwe.CmdLine.RuntimeTests
