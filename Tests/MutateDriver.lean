import Core.PropCheck
import LeanSwe.RegExp.Interface
import LeanSwe.RegExp.RuntimeTests
import LeanSwe.Glob.RuntimeTests
import LeanSwe.Fs.Raw.RuntimeTests
import LeanSwe.Fs.RuntimeTests
import LeanSwe.Process.Raw.RuntimeTests
import LeanSwe.Process.RuntimeTests
import LeanSwe.Time.RuntimeTests
import LeanSwe.Json.RuntimeTests
import LeanSwe.EnvVars.Raw.Interface
import LeanSwe.EnvVars.Raw.RuntimeTests
import LeanSwe.EnvVars.Interface
import LeanSwe.EnvVars.RuntimeTests
import LeanSwe.Uuid.Raw.RuntimeTests
import LeanSwe.Uuid.RuntimeTests
import LeanSwe.Sqlite.Raw.RuntimeTests
import LeanSwe.Sqlite.RuntimeTests
import LeanSwe.Git.RuntimeTests
import LeanSwe.CmdLine.RuntimeTests
import LeanSwe.NumParse.RuntimeTests
import LeanSwe.Toml.RuntimeTests
import LeanSwe.TempDir.RuntimeTests
import LeanSwe.Compress.RuntimeTests
import LeanSwe.Base64.RuntimeTests
import LeanSwe.CryptoHash.Raw.RuntimeTests
import LeanSwe.CryptoHash.RuntimeTests
import LeanSwe.Tar.RuntimeTests
import LeanSwe.ProcessSandbox.Raw.RuntimeTests
import LeanSwe.ProcessSandbox.RuntimeTests
import LeanSwe.ConnectProxy.Raw.RuntimeTests
import LeanSwe.ConnectProxy.RuntimeTests
import LeanSwe.SlotPool.RuntimeTests

open LeanSwe
open Core.PropCheck

private local instance {ε α : Type} [BEq ε] [BEq α] : BEq (Except ε α) where
  beq
    | .ok a, .ok b => a == b
    | .error e1, .error e2 => e1 == e2
    | _, _ => false

private def smokeRegExp : IO Unit := do
  match RegExp.findAll "[0-9]+" "a1b22" with
  | .ok xs =>
    if xs.map (·.matched) != #["1", "22"] then
      throw (IO.userError s!"unexpected RegExp.findAll result: {repr xs}")
  | .error e =>
    throw (IO.userError s!"unexpected RegExp.findAll error: {e.message}")

private def sampleKeys : Array String :=
  #["", "A", "PATH", "HOME", "A=B", "A=1=2", String.ofList ['A', Char.ofNat 0],
    String.ofList ['\x00'], "FOO_BAR", "x:y"]

private def samplePaths : Array String :=
  #["", ":", ":::", "/usr/bin", ":/usr/bin:", ":/a::/b:", "a:b:c", "/tmp/x:/var/y:"]

private def sampleRawErrors : Array EnvVars.Raw.EnvVarsRawError :=
  #[ .invalidEncoding none "",
     .invalidEncoding (some "K") "bad utf8",
     .invalidArgument none 22 "",
     .invalidArgument (some "A=B") 22 "einval",
     .otherError 12 "",
     .otherError 5 "eio",
     .userError "",
     .userError "boom" ]

private def sampleEnvLists : Array (List (String × String)) :=
  #[ [],
     [("PATH", "/bin")],
     [("HOME", "")],
     [("HOME", "/tmp/u")],
     [("PATH", "/usr/bin"), ("HOME", "/tmp/u"), ("PATH", "/bin")],
     [("A", "1"), ("B", "2")] ]

private def pick {α : Type} (fallback : α) (arr : Array α) (r : Rng) : α × Rng :=
  let (u, r') := r.next
  ((arr[(u.toNat % arr.size)]?).getD fallback, r')

private def runPropChecksEnvVarsRaw : IO Unit := do
  let _ ← checkFor "test_envvarsraw_mapRawError_returnsNonEmptyMessage" 32 fun r =>
    let (raw, r') := pick (.userError "") sampleRawErrors r
    let err := EnvVars.Raw.defaultOps.mapRawError raw
    (r', assertB "err.message != \"\"" (!err.message.isEmpty))

  let _ ← checkFor "test_envvarsraw_mapRawError_preservesKindAndMetadata" 32 fun r =>
    let (raw, r') := pick (.userError "") sampleRawErrors r
    let err := EnvVars.Raw.defaultOps.mapRawError raw
    let ok := match raw with
      | .invalidEncoding key? _ => err.kind == .invalidEncoding && err.key == key? && err.errnoCode == none
      | .invalidArgument key? code _ => err.kind == .invalidKey && err.key == key? && err.errnoCode == some code
      | .otherError code _ => err.kind == .ioError && err.key == none && err.errnoCode == some code
      | .userError _ => err.kind == .ioError && err.key == none && err.errnoCode == none
    (r', assertB "kind & metadata" ok)

private def runPropChecksEnvVars : IO Unit := do
  let _ ← checkFor "test_envvars_mapRawError_returnsNonEmptyMessage" 32 fun r =>
    let (raw, r') := pick (.userError "") sampleRawErrors r
    let err := EnvVars.mapRawError raw
    (r', assertB "top mapRawError msg != \"\"" (!err.message.isEmpty))

  let _ ← checkFor "test_envvars_getEnv_rejectsInvalidKey" 40 fun r =>
    let (key, r') := pick "" sampleKeys r
    let invalid := key == "" || ('=' ∈ key.toList) || (Char.ofNat 0 ∈ key.toList)
    if !invalid then (r', assumeB false)
    else
      let raw : EnvVars.Raw.RawEnvVarsOpsM Id :=
        { mapRawError := EnvVars.Raw.Internal.mapRawError
          getEnv := fun _ => pure (.ok (some "leaked"))
          listEnv := pure (.ok #[]) }
      let res : Except EnvVars.EnvVarsError (Option String) := (EnvVars.Internal.mkApiM raw).getEnv key
      let ok := match res with
        | .error e => e.kind == .invalidKey && e.key == some key && e.errnoCode == none && !e.message.isEmpty
        | .ok _ => false
      (r', assertB "rejects invalid key" ok)

  let _ ← checkFor "test_envvars_getEnv_foundInMockList" 40 fun r =>
    let (entries, r1) := pick [] sampleEnvLists r
    let (key, r2) := pick "" sampleKeys r1
    let valid := key != "" && !('=' ∈ key.toList) && !(Char.ofNat 0 ∈ key.toList)
    match entries.find? (fun p => p.1 == key) with
    | some (_, val) =>
      if !valid then (r2, assumeB false)
      else
        let raw : EnvVars.Raw.RawEnvVarsOpsM Id :=
          { mapRawError := EnvVars.Raw.Internal.mapRawError
            getEnv := fun k => pure (.ok ((entries.find? fun p => p.1 == k).map (·.2)))
            listEnv := pure (.ok entries.toArray) }
        let res : Except EnvVars.EnvVarsError (Option String) := (EnvVars.Internal.mkApiM raw).getEnv key
        let ok := match res with | .ok (some v) => v == val | _ => false
        (r2, assertB "found in mock list" ok)
    | none => (r2, assumeB false)

  let _ ← checkFor "test_envvars_getEnv_missingInMockList" 40 fun r =>
    let (entries, r1) := pick [] sampleEnvLists r
    let (key, r2) := pick "" sampleKeys r1
    let valid := key != "" && !('=' ∈ key.toList) && !(Char.ofNat 0 ∈ key.toList)
    if !valid || (entries.find? (fun p => p.1 == key)).isSome then (r2, assumeB false)
    else
      let raw : EnvVars.Raw.RawEnvVarsOpsM Id :=
        { mapRawError := EnvVars.Raw.Internal.mapRawError
          getEnv := fun k => pure (.ok ((entries.find? fun p => p.1 == k).map (·.2)))
          listEnv := pure (.ok entries.toArray) }
      let res : Except EnvVars.EnvVarsError (Option String) := (EnvVars.Internal.mkApiM raw).getEnv key
      (r2, assertB "missing in mock list" (res == .ok none))

  let _ ← checkFor "test_envvars_getEnv_propagatesRawError" 32 fun r =>
    let (rawErr, r1) := pick (.userError "") sampleRawErrors r
    let (key, r2) := pick "" sampleKeys r1
    let valid := key != "" && !('=' ∈ key.toList) && !(Char.ofNat 0 ∈ key.toList)
    if !valid then (r2, assumeB false)
    else
      let raw : EnvVars.Raw.RawEnvVarsOpsM Id :=
        { mapRawError := EnvVars.Raw.Internal.mapRawError
          getEnv := fun _ => pure (.error rawErr)
          listEnv := pure (.ok #[]) }
      let res : Except EnvVars.EnvVarsError (Option String) := (EnvVars.Internal.mkApiM raw).getEnv key
      (r2, assertB "propagates raw error" (res == .error (EnvVars.Raw.Internal.mapRawError rawErr)))

  let _ ← checkFor "test_envvars_listEnv_returnsMockEntries" 32 fun r =>
    let (entries, r1) := pick [] sampleEnvLists r
    let raw : EnvVars.Raw.RawEnvVarsOpsM Id :=
      { mapRawError := EnvVars.Raw.Internal.mapRawError
        getEnv := fun _ => pure (.ok none)
        listEnv := pure (.ok entries.toArray) }
    let res : Except EnvVars.EnvVarsError (Array (String × String)) := (EnvVars.Internal.mkApiM raw).listEnv
    (r1, assertB "listEnv returns entries" (res == .ok entries.toArray))

  let _ ← checkFor "test_envvars_listEnv_propagatesRawError" 32 fun r =>
    let (rawErr, r1) := pick (.userError "") sampleRawErrors r
    let raw : EnvVars.Raw.RawEnvVarsOpsM Id :=
      { mapRawError := EnvVars.Raw.Internal.mapRawError
        getEnv := fun _ => pure (.ok none)
        listEnv := pure (.error rawErr) }
    let res : Except EnvVars.EnvVarsError (Array (String × String)) := (EnvVars.Internal.mkApiM raw).listEnv
    (r1, assertB "listEnv propagates raw error" (res == .error (EnvVars.Raw.Internal.mapRawError rawErr)))

  let _ ← checkFor "test_envvars_homeDir_returnsNonEmptyHome" 32 fun r =>
    let (entries, r1) := pick [] sampleEnvLists r
    match entries.find? (fun p => p.1 == "HOME") with
    | some ("HOME", h) =>
      if h.isEmpty then (r1, assumeB false)
      else
        let raw : EnvVars.Raw.RawEnvVarsOpsM Id :=
          { mapRawError := EnvVars.Raw.Internal.mapRawError
            getEnv := fun k => pure (.ok ((entries.find? fun p => p.1 == k).map (·.2)))
            listEnv := pure (.ok entries.toArray) }
        let res : Except EnvVars.EnvVarsError String := (EnvVars.Internal.mkApiM raw).homeDir
        (r1, assertB "homeDir non-empty" (res == .ok h))
    | _ => (r1, assumeB false)

  let _ ← checkFor "test_envvars_homeDir_missingOrEmptyFails" 32 fun r =>
    let (entries, r1) := pick [] sampleEnvLists r
    let matchesGuard :=
      entries.find? (fun p => p.1 == "HOME") == none ||
      entries.find? (fun p => p.1 == "HOME") == some ("HOME", "")
    if !matchesGuard then (r1, assumeB false)
    else
      let raw : EnvVars.Raw.RawEnvVarsOpsM Id :=
        { mapRawError := EnvVars.Raw.Internal.mapRawError
          getEnv := fun k => pure (.ok ((entries.find? fun p => p.1 == k).map (·.2)))
          listEnv := pure (.ok entries.toArray) }
      let res : Except EnvVars.EnvVarsError String := (EnvVars.Internal.mkApiM raw).homeDir
      let ok := match res with
        | .error e => e.kind == .notFound && e.key == some "HOME" && !e.message.isEmpty
        | .ok _ => false
      (r1, assertB "homeDir missing/empty fails" ok)

  let _ ← checkFor "test_envvars_homeDir_propagatesRawError" 32 fun r =>
    let (rawErr, r1) := pick (.userError "") sampleRawErrors r
    let raw : EnvVars.Raw.RawEnvVarsOpsM Id :=
      { mapRawError := EnvVars.Raw.Internal.mapRawError
        getEnv := fun _ => pure (.error rawErr)
        listEnv := pure (.ok #[]) }
    let res : Except EnvVars.EnvVarsError String := (EnvVars.Internal.mkApiM raw).homeDir
    (r1, assertB "homeDir propagates raw error" (res == .error (EnvVars.Raw.Internal.mapRawError rawErr)))

  let _ ← checkFor "test_envvars_splitSearchPath_emptyReturnsEmpty" 8 fun r =>
    (r, assertB "splitSearchPath empty" (EnvVars.splitSearchPath "" == #[]))

  let _ ← checkFor "test_envvars_splitSearchPath_entriesNonEmptyAndColonFree" 40 fun r =>
    let (p, r1) := pick "" samplePaths r
    let parts := EnvVars.splitSearchPath p
    (r1, assertB "entries clean" (parts.toList.all fun seg => !seg.isEmpty && !(':' ∈ seg.toList)))

  let _ ← checkFor "test_envvars_splitSearchPath_roundTripsCleanSegments" 40 fun r =>
    let (p, r1) := pick "" samplePaths r
    let parts := EnvVars.splitSearchPath p
    let rt := EnvVars.splitSearchPath (String.intercalate ":" parts.toList) == parts
    (r1, assertB "splitSearchPath roundTrip" rt)

private def runIoErrorToRawUnitTests : IO Unit := do
  let cases : Array (IO.Error × EnvVars.Raw.EnvVarsRawError) := #[
    (.invalidArgument (some "K") 22 "invalid UTF-8 in environment entry", .invalidEncoding (some "K") "invalid UTF-8 in environment entry"),
    (.invalidArgument (some "K") 22 "bad arg", .invalidArgument (some "K") 22 "bad arg"),
    (.otherError 12 "nomem", .otherError 12 "nomem"),
    (.userError "invalid UTF-8 in environment entry", .invalidEncoding none "invalid UTF-8 in environment entry"),
    (.userError "oops", .userError "oops"),
    (.noFileOrDirectory "p" 2 "noent", .otherError 2 "noent"),
    (.alreadyExists none 17 "eexist", .otherError 17 "eexist"),
    (.permissionDenied none 13 "eacces", .otherError 13 "eacces"),
    (.inappropriateType none 20 "enotdir", .otherError 20 "enotdir"),
    (.unsupportedOperation 95 "enotsup", .otherError 95 "enotsup"),
    (.unsatisfiedConstraints 1 "constr", .otherError 1 "constr"),
    (.illegalOperation 1 "illegal", .otherError 1 "illegal"),
    (.resourceBusy 16 "ebusy", .otherError 16 "ebusy"),
    (.resourceVanished 1 "vanish", .otherError 1 "vanish"),
    (.hardwareFault 5 "eio", .otherError 5 "eio"),
    (.protocolError 71 "eproto", .otherError 71 "eproto"),
    (.timeExpired 110 "etimedout", .otherError 110 "etimedout"),
    (.interrupted "p" 4 "eintr", .otherError 4 "p: eintr"),
    (.resourceExhausted none 24 "emfile", .otherError 24 "emfile"),
    (.noSuchThing none 2 "nosuch", .otherError 2 "nosuch"),
    (.unexpectedEof, .userError "unexpected end of file")
  ]
  for (ioErr, expected) in cases do
    let got := EnvVars.Raw.Internal.ioErrorToRaw ioErr
    if got != expected then
      throw (IO.userError s!"ioErrorToRaw mismatch for {ioErr}: got {repr got}, expected {repr expected}")

private def allSuites : Array (String × IO (Option String) × IO Unit) := #[
  ("RegExp", do RegExp.RuntimeTests.runAll; smokeRegExp; return none, pure ()),
  ("Glob", do Glob.RuntimeTests.runAll; return none, pure ()),
  ("Fs.Raw", do Fs.Raw.RuntimeTests.runAll; return none, pure ()),
  ("Fs", do Fs.RuntimeTests.runAll; return none, pure ()),
  ("Process.Raw", do Process.Raw.RuntimeTests.runAll; return none, pure ()),
  ("Process", do Process.RuntimeTests.runAll; return none, pure ()),
  ("Time", do Time.RuntimeTests.runAll; return none, pure ()),
  ("Json", do Json.RuntimeTests.runAll; return none, pure ()),
  ("EnvVars.Raw", do EnvVars.Raw.RuntimeTests.runAll; return none, do runPropChecksEnvVarsRaw; runIoErrorToRawUnitTests),
  ("EnvVars", do EnvVars.RuntimeTests.runAll; return none, runPropChecksEnvVars),
  ("Uuid.Raw", do Uuid.Raw.RuntimeTests.runAll; return none, pure ()),
  ("Uuid", do Uuid.RuntimeTests.runAll; return none, pure ()),
  ("Sqlite.Raw", do Sqlite.Raw.RuntimeTests.runAll; return none, pure ()),
  ("Sqlite", do Sqlite.RuntimeTests.runAll; return none, pure ()),
  ("Git", do Git.RuntimeTests.runAll; return none, pure ()),
  ("CmdLine", do CmdLine.RuntimeTests.runAll; return none, pure ()),
  ("NumParse", do NumParse.RuntimeTests.runAll; return none, pure ()),
  ("Toml", do Toml.RuntimeTests.runAll; return none, pure ()),
  ("TempDir", do TempDir.RuntimeTests.runAll; return none, pure ()),
  ("Compress", do Compress.RuntimeTests.runAll; return none, pure ()),
  ("Base64", do Base64.RuntimeTests.runAll; return none, pure ()),
  ("CryptoHash.Raw", do CryptoHash.Raw.RuntimeTests.runAll; return none, pure ()),
  ("CryptoHash", do CryptoHash.RuntimeTests.runAll; return none, pure ()),
  ("Tar", do Tar.RuntimeTests.runAll; return none, pure ()),
  ("ProcessSandbox.Raw", ProcessSandbox.Raw.RuntimeTests.runAllOutcome, pure ()),
  ("ProcessSandbox", ProcessSandbox.RuntimeTests.runAllOutcome, pure ()),
  ("ConnectProxy.Raw", do ConnectProxy.Raw.RuntimeTests.runAll; return none, pure ()),
  ("ConnectProxy", do ConnectProxy.RuntimeTests.runAll; return none, pure ()),
  ("SlotPool", do SlotPool.RuntimeTests.runAll; return none, pure ())
]

private structure MutateFlags where
  mode : String := "full"
  suites : Array String := #[]

private def parseFlags : List String → Except String MutateFlags
  | [] => .ok {}
  | "--mode" :: m :: rest => do
    let f ← parseFlags rest
    return { f with mode := m }
  | "--suite" :: s :: rest => do
    let f ← parseFlags rest
    let parts := (s.splitOn ",").filterMap fun item =>
      let t := item.trimAscii.toString
      if t.isEmpty then none else some t
    return { f with suites := parts.toArray ++ f.suites }
  | flag :: _ => .error s!"unknown flag {flag}"

/-- Mutation test driver supporting `--suite` filtering and omitting all `Proofs` imports. -/
def main (args : List String) : IO UInt32 := do
  match args with
  | "--cmdline-probe" :: rest =>
    return (← CmdLine.RuntimeTests.probeMain rest)
  | "--slotpool-probe" :: rest =>
    return (← SlotPool.RuntimeTests.probeMain rest)
  | _ =>
    let flags ← match parseFlags args with
      | .ok f => pure f
      | .error msg =>
        IO.eprintln msg
        return 2
    if flags.mode != "baseline" && flags.mode != "full" then
      IO.eprintln s!"unknown --mode {flags.mode}"
      return 2
    let knownNames := allSuites.map (fun (name, _, _) => name)
    let filterAll := flags.suites.isEmpty || flags.suites.contains "all"
    if !filterAll then
      for s in flags.suites do
        if !knownNames.contains s then
          IO.eprintln s!"UNKNOWN_SUITE: {s}"
          return 2
    let selected :=
      if filterAll then allSuites
      else allSuites.filter fun (name, _, _) => flags.suites.contains name
    for (name, runBase, runExtra) in selected do
      try
        match ← runBase with
        | none => pure ()
        | some reason => IO.println s!"SKIP: {name} ({reason})"
        if flags.mode == "full" then
          runExtra
      catch err =>
        IO.eprintln s!"FAIL: {name} ({err.toString})"
        return 1
    return 0
