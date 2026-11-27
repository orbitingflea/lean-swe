import Core.Assumptions
import LeanSwe.RegExp.Interface
import LeanSwe.EnvVars.Raw.RuntimeTests
import LeanSwe.EnvVars.RuntimeTests
import LeanSwe.CmdLine.RuntimeTests
import LeanSwe.SlotPool.RuntimeTests
import LeanSwe.Compress.RuntimeTests
import LeanSwe.Process.RuntimeTests

namespace Tests.Common

/-- Scoped `BEq` instance comparing `Except` values structurally for test assertions. -/
scoped instance beqExcept {ε α : Type} [BEq ε] [BEq α] : BEq (Except ε α) where
  beq
    | .ok a, .ok b => a == b
    | .error e1, .error e2 => e1 == e2
    | _, _ => false

/-- Single mutation-test suite entry pairing `RuntimeTests` baseline checks with `--mode full` extras. -/
structure MutateSuite where
  /-- Canonical `--suite` CLI identifier matching `scripts/mutate_and_test.py`. -/
  name : String
  /-- Baseline runtime test action returning `none` on pass or `some reason` on environment skip. -/
  runBase : IO (Option String)
  /-- Extra unit, property, or fault-injection checks run when `--mode full` is selected. -/
  runExtra : IO Unit := pure ()

/-- Quick smoke check verifying `RegExp.findAll` extracts consecutive digit runs. -/
def smokeRegExp : IO Unit := do
  match LeanSwe.RegExp.findAll "[0-9]+" "a1b22" with
  | .ok xs =>
    if xs.map (·.matched) != #["1", "22"] then
      throw (IO.userError s!"unexpected RegExp.findAll result: {repr xs}")
  | .error e =>
    throw (IO.userError s!"unexpected RegExp.findAll error: {e.message}")

/-- Fail with `IO.userError` when `ok` is `false`. -/
def checkUnit (label : String) (ok : Bool) : IO Unit :=
  unless ok do
    throw (IO.userError s!"unit check failed: {label}")

/-- Split a comma-separated `--suite` CLI argument into trimmed non-empty suite names. -/
def parseSuiteCsv (raw : String) : Array String :=
  let parts := (raw.splitOn ",").filterMap fun item =>
    let t := item.trimAscii.toString
    if t.isEmpty then none else some t
  parts.toArray

/-- Validate requested `--suite` names (`all` or empty selects every suite) and filter in registry order. -/
def selectNamedSuites {α : Type} (all : Array α) (nameOf : α → String)
    (requested : Array String) : Except String (Array α) := do
  let filterAll := requested.isEmpty || requested.contains "all"
  if filterAll then
    return all
  let knownNames := all.map nameOf
  for s in requested do
    if !knownNames.contains s then
      throw s!"UNKNOWN_SUITE: {s}"
  return all.filter fun entry => requested.contains (nameOf entry)

/-- Match shared `--*-probe` subprocess worker flags used by both `lean-swe-test` and `lean-swe-mut-test`. -/
def findRuntimeProbe? : List String → Option (IO UInt32)
  | "--envvars-raw-probe" :: rest => some (LeanSwe.EnvVars.Raw.RuntimeTests.probeMain rest)
  | "--envvars-probe" :: rest => some (LeanSwe.EnvVars.RuntimeTests.probeMain rest)
  | "--cmdline-probe" :: rest => some (LeanSwe.CmdLine.RuntimeTests.probeMain rest)
  | "--slotpool-probe" :: rest => some (LeanSwe.SlotPool.RuntimeTests.probeMain rest)
  | "--compress-probe" :: rest => some (LeanSwe.Compress.RuntimeTests.probeMain rest)
  | "--process-probe" :: rest => some (LeanSwe.Process.RuntimeTests.probeMain rest)
  | _ => none

private def errorTestModeTag : Core.ErrorTestMode → String
  | .real => "real"
  | .mocked => "mocked"

private def pkgCoverageMeta : String → Option (String × String)
  | "LeanSwe.Base64" => some ("LeanSwe.Base64.Base64ErrorKind", "err_base64_")
  | "LeanSwe.CmdLine" => some ("LeanSwe.CmdLine.CmdLineErrorKind", "err_cmdline_")
  | "LeanSwe.Compress" => some ("LeanSwe.Compress.CompressErrorKind", "err_compress_")
  | "LeanSwe.CryptoHash.Raw" => some ("LeanSwe.CryptoHash.Raw.CryptoHashErrorKind", "err_cryptohashraw_")
  | "LeanSwe.CryptoHash" => some ("LeanSwe.CryptoHash.Raw.CryptoHashErrorKind", "err_cryptohash_")
  | "LeanSwe.EnvVars.Raw" => some ("LeanSwe.EnvVars.Raw.EnvVarsRawErrorKind", "err_envvarsraw_")
  | "LeanSwe.EnvVars" => some ("LeanSwe.EnvVars.Raw.EnvVarsErrorKind", "err_envvars_")
  | "LeanSwe.Fs" => some ("LeanSwe.Fs.FsErrorKind", "err_fs_")
  | "LeanSwe.Git" => some ("LeanSwe.Git.GitErrorKind", "err_git_")
  | "LeanSwe.Glob" => some ("LeanSwe.Glob.GlobErrorKind", "err_glob_")
  | "LeanSwe.Json" => some ("LeanSwe.Json.JsonErrorKind", "err_json_")
  | "LeanSwe.NumParse" => some ("LeanSwe.NumParse.NumParseErrorKind", "err_numparse_")
  | "LeanSwe.PostFork" => some ("LeanSwe.PostFork.PostForkErrorKind", "err_")
  | "LeanSwe.Process" => some ("LeanSwe.Process.ProcessErrorKind", "err_process_")
  | "LeanSwe.RegExp" => some ("LeanSwe.RegExp.RegexErrorKind", "err_regexp_")
  | "LeanSwe.SlotPool" => some ("LeanSwe.SlotPool.SlotPoolErrorKind", "err_slotpool_")
  | "LeanSwe.Sqlite.Raw" => some ("LeanSwe.Sqlite.Raw.SqliteErrorKind", "err_sqliteraw_")
  | "LeanSwe.Sqlite" => some ("LeanSwe.Sqlite.Raw.SqliteErrorKind", "err_sqlite_")
  | "LeanSwe.Tar" => some ("LeanSwe.Tar.TarErrorKind", "err_tar_")
  | "LeanSwe.TempDir" => some ("LeanSwe.TempDir.TempDirErrorKind", "err_tempdir_")
  | "LeanSwe.Time" => some ("LeanSwe.Time.TimeErrorKind", "err_time_")
  | "LeanSwe.Toml" => some ("LeanSwe.Toml.TomlErrorKind", "err_toml_")
  | "LeanSwe.Uuid" => some ("LeanSwe.Uuid.UuidErrorKind", "err_uuid_")
  | _ => none

private def resolveGitOpName (opBase : String) : String :=
  match opBase with
  | "headBranch" | "headCommit" | "mergeBase" | "showFile" => opBase ++ "?"
  | _ => opBase

private def splitLastUnderscore? (s : String) : Option (String × String) :=
  let parts := s.splitOn "_"
  match parts.reverse with
  | [] | [_] => none
  | last :: revInit =>
    let head := "_".intercalate revInit.reverse
    if head.isEmpty || last.isEmpty then none else some (head, last)

/-- Runtime callback invoked by `Core.runRegisteredErrorTests` immediately after each error test (or verified sub-case) executes and passes, emitting live `ERR_HIT` records without static coverage tables. -/
def onRegisteredErrorTestPass (testName : String) (mode : Core.ErrorTestMode) : IO Unit := do
  let parts := testName.splitOn ".RuntimeTests."
  let [pkgNs, fnShort] := parts | return ()
  let some (enumType, pfx) := pkgCoverageMeta pkgNs | return ()
  if !fnShort.startsWith pfx || fnShort.endsWith "_mocked" then
    return ()
  let body := (fnShort.drop pfx.length).toString
  if let some (opBase, kindShort) := splitLastUnderscore? body then
    let opName := if pkgNs == "LeanSwe.Git" then resolveGitOpName opBase else opBase
    Core.logErrHit s!"{pkgNs}.{opName}" s!"{enumType}.{kindShort}" (errorTestModeTag mode)

end Tests.Common
