import Tests.Common
import LeanSwe.RegExp.RuntimeTests
import LeanSwe.Glob.RuntimeTests
import LeanSwe.Time.RuntimeTests
import LeanSwe.Json.RuntimeTests
import LeanSwe.Uuid.RuntimeTests
import LeanSwe.CmdLine.Interface
import LeanSwe.CmdLine.RuntimeTests
import LeanSwe.NumParse.RuntimeTests
import LeanSwe.Toml.RuntimeTests
import LeanSwe.Base64.RuntimeTests
import LeanSwe.Tar.RuntimeTests

namespace Tests.Mutate.Codecs

open LeanSwe
open Tests.Common

private def runCmdLineMutateExtra : IO Unit := do
  let checkB (lbl : String) (ok : Bool) : IO Unit := do
    unless ok do throw (IO.userError s!"CMDLINE_MUTATE_EXTRA_FAIL: {lbl}")
  checkB "nat30" (CmdLine.Internal.parseNatCharsFast "123456789012345678901234567890".toList == some 123456789012345678901234567890)
  checkB "editDist subst" (CmdLine.Internal.editDistance "abc" "adc" == 1)
  checkB "editDist transp" (CmdLine.Internal.editDistance "ab" "ba" == 1)
  checkB "editDistBounded diff" (CmdLine.Internal.editDistanceBounded 1 "a" "abcd" == 2)
  checkB "editDistBounded del" (CmdLine.Internal.editDistanceBounded 2 "aa" "a" == 1)
  checkB "editDistBounded rowMin" (CmdLine.Internal.editDistanceBounded 2 "ab" "xyz" == 3)
  checkB "bestSuggestion diff" (CmdLine.Internal.bestSuggestion "foo" ["foobarbaz", "fob"] == some "fob")
  checkB "bestSuggestion best" (CmdLine.Internal.bestSuggestion "x" ["xyz", "xy"] == some "xy")
  checkB "bestSuggestion tie" (CmdLine.Internal.bestSuggestion "ac" ["bc", "ab"] == some "ab")
  let sp : CmdLine.CommandSpec := {
    «name» := "cli", version := some "1.0"
    options := [
      { «name» := "flag", long := some "flag", short := some 'f', kind := .bool, global := true },
      { «name» := "rep", long := some "rep", kind := .bool, repeatable := true, global := true, envVar := some "REP" },
      { «name» := "num", long := some "num", short := some 'n', kind := .nat, global := true },
      { «name» := "shortonly", short := some 's', kind := .nat, global := true }
    ]
    subcommands := [{ «name» := "build", args := [{ «name» := "items", kind := .string, variadic := true, required := false }] }]
  }
  let spReqArg : CmdLine.CommandSpec := {
    «name» := "reqcli"
    options := [{ «name» := "k", long := some "k", kind := .nat }]
    args := [{ «name» := "files", kind := .string, variadic := true, required := true }]
  }
  let spOptArg : CmdLine.CommandSpec := {
    «name» := "optcli"
    args := [{ «name» := "files", kind := .string, variadic := true, required := false, default := some "def" }]
  }
  let spNoVer : CmdLine.CommandSpec := {
    «name» := "nover", shortVersion := true
    options := [{ «name» := "x", short := some 'x', kind := .bool }]
  }
  let spBad : CmdLine.CommandSpec := { «name» := "bad cmd" }
  let helpTxt := match CmdLine.renderHelp sp [] with | .ok s => s | .error _ => ""
  checkB "renderHelp subcmds" ((helpTxt.splitOn "<SUBCOMMAND>").length > 1 && (helpTxt.splitOn "SUBCOMMANDS:").length > 1)
  checkB "renderHelp bool no val" ((helpTxt.splitOn "--flag <VALUE>").length == 1)
  checkB "renderHelp nat placeholder" ((helpTxt.splitOn "--num <VALUE>").length > 1)
  let spNegColl : CmdLine.CommandSpec := {
    «name» := "c", options := [{ «name» := "a", long := some "flag", kind := .bool }, { «name» := "b", long := some "no-flag", kind := .nat }]
  }
  let spRepNoColl : CmdLine.CommandSpec := {
    «name» := "c", options := [{ «name» := "a", long := some "rep", kind := .bool, repeatable := true }, { «name» := "b", long := some "no-rep", kind := .nat }]
  }
  checkB "collectLongsTR bool neg" (!CmdLine.isValidSpec spNegColl && CmdLine.isValidSpec spRepNoColl)
  let rDup := CmdLine.parse sp ["build", "--num=1", "--num=2"]
  checkB "non-repeatable dup" (match rDup with | .error e => e.kind == .invalidValue | _ => false)
  let repOpt : CmdLine.OptSpec := { «name» := "rep", long := some "rep", kind := .bool, repeatable := true, envVar := some "REP" }
  let rEnvFalse : Except CmdLine.CmdLineError (Option (List CmdLine.OptValue)) :=
    CmdLine.Internal.resolveSingleOptionFast (m := Id) (fun _ => (.ok (some "false") : Except CmdLine.CmdLineError (Option String))) repOpt [] []
  checkB "rep bool env false" (rEnvFalse == .ok none)
  let envMapOps (kVal : Option String) : CmdLine.CliOpsM Id := {
    readLine := pure none, writeOut := fun _ => pure (), writeErr := fun _ => pure (),
    getEnv := fun k => pure (.ok (if k == "REP" then kVal else none))
  }
  let checkBoth (s : CmdLine.CommandSpec) (args : List String) (pred : Except CmdLine.CmdLineError CmdLine.ParsedCmd → Bool) (lbl : String) : IO Unit := do
    let r1 := CmdLine.parse s args
    let r2 := CmdLine.Internal.parseWithEnvSpecM CmdLine.Internal.pureNoEnvOps s args []
    checkB s!"{lbl}_fast" (pred r1)
    checkB s!"{lbl}_spec" (pred r2)
  checkBoth spBad [] (fun r => match r with | .error e => e.kind == .invalidSpec | _ => false) "invalidSpec"
  checkBoth sp ["build", "--", "-dash"] (fun r => match r with | .ok p => p.rawPositionals == ["-dash"] | _ => false) "dashdash"
  checkBoth sp ["--help"] (fun r => match r with | .error e => e.kind == .helpRequested | _ => false) "help"
  checkBoth sp ["--version"] (fun r => match r with | .error e => e.kind == .versionRequested | _ => false) "ver"
  checkBoth spNoVer ["-V"] (fun r => match r with | .error e => e.kind == .unknownOption && e.message == "unknown option '-V'" | _ => false) "shortVerNone"
  checkBoth spNoVer ["--version"] (fun r => match r with | .error e => e.kind == .unknownOption && e.target == some "version" | _ => false) "longVerNone"
  checkBoth sp ["--="] (fun r => match r with | .error e => e.kind == .unknownOption && e.target == some "--=" && e.message == "unknown option '--='" | _ => false) "emptyLong"
  checkBoth sp ["-h"] (fun r => match r with | .error e => e.kind == .helpRequested | _ => false) "shortHelp"
  checkBoth sp ["--no-flga"] (fun r => match r with | .error e => e.kind == .unknownOption && e.message == "unknown option '--no-flga'; did you mean '--no-flag'?" | _ => false) "negFlagSug"
  checkBoth sp ["--no-nmu"] (fun r => match r with | .error e => e.kind == .unknownOption && (e.message.splitOn "--no-num").length == 1 | _ => false) "noNegNat"
  checkBoth sp ["build", "--rep", "--rep"] (fun r => match r with | .ok p => p.options.any (fun kv => kv.1 == "rep" && kv.2 == [.bool true, .bool true]) | _ => false) "repTwice"
  checkBoth sp ["--help=1"] (fun r => match r with | .error e => e.kind == .invalidValue | _ => false) "helpEq"
  checkBoth sp ["--version=1"] (fun r => match r with | .error e => e.kind == .invalidValue | _ => false) "verEq"
  checkBoth sp ["build", "--no-flag"] (fun r => match r with | .ok p => p.options.any (fun kv => kv.1 == "flag" && kv.2 == [.bool false]) | _ => false) "noFlag"
  checkBoth sp ["build", "--no-flag=1"] (fun r => match r with | .error e => e.kind == .invalidValue | _ => false) "noFlagEq"
  checkBoth sp ["build", "--flag=false"] (fun r => match r with | .ok p => p.options.any (fun kv => kv.1 == "flag" && kv.2 == [.bool false]) | _ => false) "flagFalse"
  checkBoth sp ["build", "--rep=false"] (fun r => match r with | .error e => e.kind == .invalidValue | _ => false) "repFalse"
  checkBoth sp ["build", "--rep"] (fun r => match r with | .ok p => p.getBool "rep" == true | _ => false) "repTrue"
  checkBoth sp ["build", "-f", "-n", "7"] (fun r => match r with | .ok p => p.getBool "flag" == true && p.getNat "num" == some 7 | _ => false) "shortBundle"
  checkBoth sp ["build", "-V"] (fun r => match r with | .error e => e.kind == .versionRequested | _ => false) "shortV_inherited"
  checkBoth sp ["biuld"] (fun r => match r with | .error e => e.kind == .unknownSubcommand | _ => false) "subTypo"
  checkBoth sp ["--", "unknown_pos"] (fun r => match r with | .error e => e.kind == .unexpectedArgument | _ => false) "subUnexp"
  checkBoth sp [] (fun r => match r with | .error e => e.kind == .missingArgument | _ => false) "subMiss"
  checkBoth spReqArg [] (fun r => match r with | .error e => e.kind == .missingArgument | _ => false) "varReqMiss"
  checkBoth spOptArg [] (fun r => match r with | .ok p => p.args.any (·.1 == "files") | _ => false) "varOptDef"
  checkBoth spOptArg ["a", "b"] (fun r => match r with | .ok p => p.args == [("files", [.string "a", .string "b"])] | _ => false) "varOptMany"
  checkB "specM env false" (Id.run (CmdLine.Internal.parseWithEnvSpecM (envMapOps (some "false")) sp ["build"] []) == .ok { subcommandPath := ["build"], options := [("flag", [.bool false])] })
  let parsedR : CmdLine.ParsedCmd := {
    subcommandPath := ["build"]
    options := [("flag", [.bool false]), ("num", [.nat 9]), ("shortonly", [.nat 4])]
    args := [("items", [.string "-neg"])]
    rawPositionals := ["-neg"]
  }
  let rRend := CmdLine.renderArgs sp parsedR
  checkB "renderArgs edge" (rRend == .ok ["build", "--no-flag", "--num=9", "-s", "4", "--", "-neg"])
  let spShortRepBool : CmdLine.CommandSpec := {
    «name» := "sr", options := [{ «name» := "r", short := some 'r', kind := .bool, repeatable := true }]
  }
  checkB "renderArgs short rep bool" (CmdLine.renderArgs spShortRepBool { options := [("r", [.bool true, .bool true])] } == .ok ["-r", "-r"])
  checkB "renderArgs rep bool false" (match CmdLine.renderArgs sp { subcommandPath := ["build"], options := [("rep", [.bool true, .bool false])] } with | .error e => e.kind == .invalidValue | _ => false)
  let rEnvParse := CmdLine.Internal.parseWithEnvSpecM (envMapOps (some "true")) sp ["build"] []
  checkB "specM env true" (match rEnvParse with | .ok p => p.getBool "rep" == true | _ => false)
  let mockOps : CmdLine.CliOpsM (StateM (List String)) := {
    readLine := do match ← get with | [] => pure none | l :: ls => set ls; pure (some l)
    writeOut := fun _ => pure (), writeErr := fun _ => pure (), getEnv := fun _ => pure (.ok none)
  }
  let mockPrompt := (CmdLine.Internal.promptLine mockOps "p:" none).run []
  checkB "promptLine eof msg" (mockPrompt.1 == .error { kind := .eof, message := "unexpected end of input" })
  let mockConf0 := (CmdLine.Internal.confirm mockOps "c?" none 0).run []
  checkB "confirm 0 msg" (mockConf0.1 == .error { kind := .invalidValue, message := "exceeded maximum confirmation attempts" })
  let mockConfEof := (CmdLine.Internal.confirm mockOps "c?" none 2).run []
  checkB "confirm eof msg" (mockConfEof.1 == .error { kind := .eof, message := "unexpected end of input" })
  let mockConfBlank := (CmdLine.Internal.confirm mockOps "c?" none 1).run [""]
  checkB "confirm blank 1 msg" (mockConfBlank.1 == .error { kind := .invalidValue, message := "exceeded maximum confirmation attempts" })
  let mockConfNo := (CmdLine.Internal.confirm mockOps "c?" none 2).run ["no"]
  checkB "confirm no" (mockConfNo.1 == .ok false)
  let mockConfBad := (CmdLine.Internal.confirm mockOps "c?" none 1).run ["bad"]
  checkB "confirm bad 1 msg" (mockConfBad.1 == .error { kind := .invalidValue, message := "exceeded maximum confirmation attempts" })
  checkB "stripCrLf" (CmdLine.Internal.stripTrailingNewline "ab\r\n" == "ab" && CmdLine.Internal.stripTrailingNewline "ab\r" == "ab" && CmdLine.Internal.stripTrailingNewline "ab\n" == "ab")

/-- Mutation test suite for `LeanSwe.RegExp`. -/
def regExpSuite : MutateSuite :=
  { name := "RegExp", runBase := do RegExp.RuntimeTests.runAll; smokeRegExp; return none }

/-- Mutation test suite for `LeanSwe.Glob`. -/
def globSuite : MutateSuite :=
  { name := "Glob", runBase := do Glob.RuntimeTests.runAll; return none }

/-- Mutation test suite for `LeanSwe.Time`. -/
def timeSuite : MutateSuite :=
  { name := "Time", runBase := do Time.RuntimeTests.runAll; return none }

/-- Mutation test suite for `LeanSwe.Json`. -/
def jsonSuite : MutateSuite :=
  { name := "Json", runBase := do Json.RuntimeTests.runAll; return none }

/-- Mutation test suite for `LeanSwe.Uuid`. -/
def uuidSuite : MutateSuite :=
  { name := "Uuid", runBase := do Uuid.RuntimeTests.runAll; return none }

/-- Mutation test suite for `LeanSwe.CmdLine`. -/
def cmdLineSuite : MutateSuite :=
  { name := "CmdLine", runBase := do CmdLine.RuntimeTests.runAll; return none, runExtra := runCmdLineMutateExtra }

/-- Mutation test suite for `LeanSwe.NumParse`. -/
def numParseSuite : MutateSuite :=
  { name := "NumParse", runBase := do NumParse.RuntimeTests.runAll; return none }

/-- Mutation test suite for `LeanSwe.Toml`. -/
def tomlSuite : MutateSuite :=
  { name := "Toml", runBase := do Toml.RuntimeTests.runAll; return none }

/-- Mutation test suite for `LeanSwe.Base64`. -/
def base64Suite : MutateSuite :=
  { name := "Base64", runBase := do Base64.RuntimeTests.runAll; return none }

/-- Mutation test suite for `LeanSwe.Tar`. -/
def tarSuite : MutateSuite :=
  { name := "Tar", runBase := do Tar.RuntimeTests.runAll; return none }

end Tests.Mutate.Codecs
