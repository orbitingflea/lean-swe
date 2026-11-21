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
import LeanSwe.Uuid.RuntimeTests
import LeanSwe.Sqlite.Raw.Interface
import LeanSwe.Sqlite.Raw.RuntimeTests
import LeanSwe.Sqlite.RuntimeTests
import LeanSwe.Git.RuntimeTests
import LeanSwe.CmdLine.Interface
import LeanSwe.CmdLine.RuntimeTests
import LeanSwe.NumParse.RuntimeTests
import LeanSwe.Toml.RuntimeTests
import LeanSwe.TempDir.RuntimeTests
import LeanSwe.Compress.RuntimeTests
import LeanSwe.Base64.RuntimeTests
import LeanSwe.CryptoHash.Raw.RuntimeTests
import LeanSwe.CryptoHash.RuntimeTests
import LeanSwe.Tar.RuntimeTests
import LeanSwe.ProcessSandbox.Seccomp.RuntimeTests
import LeanSwe.ProcessSandbox.Raw.RuntimeTests
import LeanSwe.ProcessSandbox.RuntimeTests
import LeanSwe.ConnectProxy.Interface
import LeanSwe.ConnectProxy.RuntimeTests
import LeanSwe.SlotPool.RuntimeTests
import LeanSwe.LinuxSyscall.Sandbox.RuntimeTests
import LeanSwe.LinuxSyscall.TimeRand.RuntimeTests
import LeanSwe.LinuxSyscall.Files.Impl
import LeanSwe.LinuxSyscall.Files.RuntimeTests
import LeanSwe.LinuxSyscall.Passwd.RuntimeTests
import LeanSwe.LinuxSyscall.Dns.RuntimeTests
import LeanSwe.LinuxSyscall.Poll.Impl
import LeanSwe.LinuxSyscall.Poll.RuntimeTests
import LeanSwe.LinuxSyscall.Net.Impl
import LeanSwe.LinuxSyscall.Net.RuntimeTests
import LeanSwe.LinuxSyscall.Process.RuntimeTests
import LeanSwe.LinuxSyscall.Fuzz.ProcessFuzz

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
      let expectedMsg :=
        if entries.find? (fun p => p.1 == "HOME") == some ("HOME", "") then
          "HOME environment variable is empty"
        else
          "HOME environment variable is not set"
      let ok := match res with
        | .error e => e.kind == .notFound && e.key == some "HOME" && e.message == expectedMsg
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

private def runRawDecoderUnitTests : IO Unit := do
  let invalidUtf8 : ByteArray := ByteArray.mk #[0xFF, 0xFE]
  let okPair : ByteArray := "OK_KEY=val=ue".toUTF8
  let emptyValPair : ByteArray := "EMPTY_KEY=".toUTF8
  let noEqPair : ByteArray := "MALFORMED".toUTF8
  let emptyKeyPair : ByteArray := "=bad".toUTF8
  let badKeyUtf8 : ByteArray := invalidUtf8 ++ "=val".toUTF8
  let badValUtf8 : ByteArray := "K=".toUTF8 ++ invalidUtf8

  let mapCases : Array (EnvVars.Raw.EnvVarsRawError × EnvVars.EnvVarsError) := #[
    (.invalidEncoding (some "K") "bad utf8",
      { kind := .invalidEncoding, key := some "K", errnoCode := none, message := "bad utf8" }),
    (.invalidEncoding none "",
      { kind := .invalidEncoding, key := none, errnoCode := none, message := "invalid UTF-8 in environment" }),
    (.invalidArgument (some "A=B") 22 "bad key",
      { kind := .invalidKey, key := some "A=B", errnoCode := some 22, message := "bad key" }),
    (.invalidArgument none 22 "",
      { kind := .invalidKey, key := none, errnoCode := some 22, message := "invalid environment variable name" }),
    (.otherError 12 "nomem",
      { kind := .ioError, key := none, errnoCode := some 12, message := "nomem" }),
    (.otherError 5 "",
      { kind := .ioError, key := none, errnoCode := some 5, message := "os error 5" }),
    (.userError "oops",
      { kind := .ioError, key := none, errnoCode := none, message := "oops" }),
    (.userError "",
      { kind := .ioError, key := none, errnoCode := none, message := "environment error" })
  ]
  for (rawErr, expected) in mapCases do
    let got := EnvVars.Raw.mapRawError rawErr
    if got != expected then
      throw (IO.userError s!"mapRawError mismatch for {repr rawErr}: got {repr got}, expected {repr expected}")

  let fakeOps (getMap : String → Option ByteArray) (envList : Array ByteArray) : EnvVars.Raw.PosixRawOpsM Id :=
    { getEnvBytes := fun k => pure (getMap k)
      listEnvironBytes := pure envList }

  let ops : EnvVars.Raw.RawEnvVarsOpsM Id := EnvVars.Raw.Internal.mkRawOps (fakeOps
    (fun k =>
      if k == "VALID" then some "abc=123".toUTF8
      else if k == "EMPTY" then some ByteArray.empty
      else if k == "BAD" then some invalidUtf8
      else if k == "" || k == "A=B" then some "SHOULD_NOT_CALL".toUTF8
      else none)
    #[noEqPair, emptyKeyPair, okPair, emptyValPair])

  match (ops.getEnv "" : Except EnvVars.Raw.EnvVarsRawError (Option String)) with
  | .ok none => pure ()
  | other => throw (IO.userError s!"mkRawOps getEnv empty key failed: {repr other}")

  match (ops.getEnv "A=B" : Except EnvVars.Raw.EnvVarsRawError (Option String)) with
  | .ok none => pure ()
  | other => throw (IO.userError s!"mkRawOps getEnv '=' key failed: {repr other}")

  match (ops.getEnv "VALID" : Except EnvVars.Raw.EnvVarsRawError (Option String)) with
  | .ok (some "abc=123") => pure ()
  | other => throw (IO.userError s!"mkRawOps getEnv VALID failed: {repr other}")

  match (ops.getEnv "EMPTY" : Except EnvVars.Raw.EnvVarsRawError (Option String)) with
  | .ok (some "") => pure ()
  | other => throw (IO.userError s!"mkRawOps getEnv EMPTY failed: {repr other}")

  match (ops.getEnv "MISSING" : Except EnvVars.Raw.EnvVarsRawError (Option String)) with
  | .ok none => pure ()
  | other => throw (IO.userError s!"mkRawOps getEnv MISSING failed: {repr other}")

  match (ops.getEnv "BAD" : Except EnvVars.Raw.EnvVarsRawError (Option String)) with
  | .error (.invalidEncoding (some "BAD") _) => pure ()
  | other => throw (IO.userError s!"mkRawOps getEnv BAD failed: {repr other}")

  match (ops.listEnv : Except EnvVars.Raw.EnvVarsRawError (Array (String × String))) with
  | .ok #[("OK_KEY", "val=ue"), ("EMPTY_KEY", "")] => pure ()
  | other => throw (IO.userError s!"mkRawOps listEnv ok failed: {repr other}")

  let opsBadKey : EnvVars.Raw.RawEnvVarsOpsM Id :=
    EnvVars.Raw.Internal.mkRawOps (fakeOps (fun _ => none) #[okPair, badKeyUtf8])
  match (opsBadKey.listEnv : Except EnvVars.Raw.EnvVarsRawError (Array (String × String))) with
  | .error (.invalidEncoding none _) => pure ()
  | other => throw (IO.userError s!"mkRawOps listEnv badKey failed: {repr other}")

  let opsBadVal : EnvVars.Raw.RawEnvVarsOpsM Id :=
    EnvVars.Raw.Internal.mkRawOps (fakeOps (fun _ => none) #[okPair, badValUtf8])
  match (opsBadVal.listEnv : Except EnvVars.Raw.EnvVarsRawError (Array (String × String))) with
  | .error (.invalidEncoding (some "K") _) => pure ()
  | other => throw (IO.userError s!"mkRawOps listEnv badVal failed: {repr other}")

  if EnvVars.Raw.Internal.isValidPosixKey "" ||
     EnvVars.Raw.Internal.isValidPosixKey "A=B" ||
     EnvVars.Raw.Internal.isValidPosixKey (String.ofList ['A', Char.ofNat 0, 'B']) ||
     !EnvVars.Raw.Internal.isValidPosixKey "GOOD_KEY_1" then
    throw (IO.userError "isValidPosixKey check failed")

private structure FakeSqliteCState where
  tbl : Sqlite.Raw.RawHandleTable := {}
  preparedSqls : Array String := #[]
  nextTok : UInt64 := 100

private def runSqliteRawUnitTests : IO Unit := do
  let checkB (msg : String) (cond : Bool) : IO Unit := do
    if !cond then throw (IO.userError s!"Sqlite.Raw unit check failed: {msg}")
  let bytes (s : String) : List UInt8 := s.toUTF8.data.toList

  checkB "hex 0" (Sqlite.Raw.Internal.hexByteVal? 0x30 == some 0)
  checkB "hex 9" (Sqlite.Raw.Internal.hexByteVal? 0x39 == some 9)
  checkB "hex A" (Sqlite.Raw.Internal.hexByteVal? 0x41 == some 10)
  checkB "hex F" (Sqlite.Raw.Internal.hexByteVal? 0x46 == some 15)
  checkB "hex a" (Sqlite.Raw.Internal.hexByteVal? 0x61 == some 10)
  checkB "hex f" (Sqlite.Raw.Internal.hexByteVal? 0x66 == some 15)
  checkB "hex /" (Sqlite.Raw.Internal.hexByteVal? 0x2F == none)
  checkB "hex :" (Sqlite.Raw.Internal.hexByteVal? 0x3A == none)
  checkB "hex G" (Sqlite.Raw.Internal.hexByteVal? 0x47 == none)
  checkB "hex g" (Sqlite.Raw.Internal.hexByteVal? 0x67 == none)

  checkB "uri empty" (Sqlite.Raw.Internal.decodeUriComponent (bytes "") == bytes "")
  checkB "uri plain" (Sqlite.Raw.Internal.decodeUriComponent (bytes "abc") == bytes "abc")
  checkB "uri hex" (Sqlite.Raw.Internal.decodeUriComponent (bytes "%41%6a") == bytes "Aj")
  checkB "uri nul" (Sqlite.Raw.Internal.decodeUriComponent (bytes "a%00b") == bytes "a")
  checkB "uri trail %" (Sqlite.Raw.Internal.decodeUriComponent (bytes "%") == bytes "%")
  checkB "uri %%" (Sqlite.Raw.Internal.decodeUriComponent (bytes "%%41") == bytes "%A")
  checkB "uri %ZZ" (Sqlite.Raw.Internal.decodeUriComponent (bytes "%ZZ") == bytes "%ZZ")
  checkB "uri %4" (Sqlite.Raw.Internal.decodeUriComponent (bytes "%4") == bytes "%4")
  checkB "uri %4%41" (Sqlite.Raw.Internal.decodeUriComponent (bytes "%4%41") == bytes "%4A")
  checkB "uri %4Z" (Sqlite.Raw.Internal.decodeUriComponent (bytes "%4Z") == bytes "%4Z")

  checkB "takeBefore hit" (Sqlite.Raw.Internal.takeBeforeByte 0x23 [1, 0x23, 2] == [1])
  checkB "takeBefore miss" (Sqlite.Raw.Internal.takeBeforeByte 0x23 [1, 2] == [1, 2])
  checkB "splitFirst hit" (Sqlite.Raw.Internal.splitFirstByte 0x3F [1, 0x3F, 2, 0x3F] == ([1], some [2, 0x3F]))
  checkB "splitFirst miss" (Sqlite.Raw.Internal.splitFirstByte 0x3F [1] == ([1], none))
  checkB "splitOn" (Sqlite.Raw.Internal.splitOnByte 0x26 [1, 0x26, 2, 0x26] == [[1], [2], []])
  checkB "stripAuth" (Sqlite.Raw.Internal.stripAuthority (bytes "//localhost/a/b") == bytes "/a/b")
  checkB "stripAuth noslash" (Sqlite.Raw.Internal.stripAuthority (bytes "//localhost") == [])

  checkB "mem :memory:" (Sqlite.Raw.Internal.isMemoryTarget ":memory:" && !Sqlite.Raw.Internal.isUriReadOnly ":memory:")
  checkB "mem plain" (!Sqlite.Raw.Internal.isMemoryTarget "plain.db" && !Sqlite.Raw.Internal.isUriReadOnly "plain.db")
  checkB "mem file::memory:" (Sqlite.Raw.Internal.isMemoryTarget "file::memory:?mode=rwc")
  checkB "mem auth slash" (!Sqlite.Raw.Internal.isMemoryTarget "file://localhost/:memory:#frag")
  checkB "mem frag cuts query" (!Sqlite.Raw.Internal.isMemoryTarget "file:a.db#frag?mode=memory")
  checkB "mem auth+query+frag" (Sqlite.Raw.Internal.isMemoryTarget "file://localhost/a.db?mode=memory#frag")
  checkB "mem mode=memory" (Sqlite.Raw.Internal.isMemoryTarget "file:a.db?mode=memory")
  checkB "mem override ro" (!Sqlite.Raw.Internal.isMemoryTarget "file:a.db?mode=memory&mode=ro" &&
    Sqlite.Raw.Internal.isUriReadOnly "file:a.db?mode=memory&mode=ro")
  checkB "ro override rwc" (!Sqlite.Raw.Internal.isUriReadOnly "file:a.db?mode=ro&mode=rwc")
  checkB "mode bare" (!Sqlite.Raw.Internal.isUriReadOnly "file:a.db?mode")
  checkB "mem %00" (Sqlite.Raw.Internal.isMemoryTarget "file:a.db?x=1&mode=memory%00ro")

  checkB "sql tail ok" (Sqlite.Raw.Internal.isIgnorableSqlTail (bytes "  \t\n-- cmt\n /* a * b */ /* ** */ "))
  checkB "sql tail unclosed" (!Sqlite.Raw.Internal.isIgnorableSqlTail (bytes " /* unclosed "))
  checkB "sql tail slash" (!Sqlite.Raw.Internal.isIgnorableSqlTail (bytes " /* unclosed / "))
  checkB "sql tail star" (!Sqlite.Raw.Internal.isIgnorableSqlTail (bytes " /* unclosed *"))

  let stmts : List (Sqlite.Raw.StmtHandle × Sqlite.Raw.RawStmtHandle) :=
    [({ id := 1, dbId := 1 }, .mock 10), ({ id := 2, dbId := 2 }, .mock 11)]
  checkB "activeStmt db2" (Sqlite.Raw.Internal.hasActiveStmtForDb 2 stmts)
  checkB "activeStmt db3" (!Sqlite.Raw.Internal.hasActiveStmtForDb 3 stmts)

  let fakeCOps : Sqlite.Raw.CSqliteOpsM (StateM FakeSqliteCState) :=
    { openV2 := fun _ _ => modifyGet fun st => (.ok (.mock st.nextTok), { st with nextTok := st.nextTok + 1 })
      close := fun _ => pure (.ok ())
      extendedResultCodes := fun _ _ => pure (.ok ())
      busyTimeout := fun _ _ => pure (.ok ())
      prepareV2 := fun _ sql => modifyGet fun st =>
        let tok := st.nextTok
        (.ok (some (.mock tok), sql.toUTF8.size),
         { st with nextTok := tok + 1, preparedSqls := st.preparedSqls.push sql })
      step := fun _ => pure (.ok .done)
      reset := fun _ => pure (.ok ())
      clearBindings := fun _ => pure (.ok ())
      finalize := fun _ => pure (.finalized none)
      bindParamCount := fun _ => pure (.ok 0)
      bindNull := fun _ _ => pure (.ok ())
      bindInt64 := fun _ _ _ => pure (.ok ())
      bindDouble := fun _ _ _ => pure (.ok ())
      bindText := fun _ _ _ => pure (.ok ())
      bindBlob := fun _ _ _ => pure (.ok ())
      columnCount := fun _ => pure (.ok 0)
      columnType := fun _ _ => pure (.ok 5)
      columnInt64 := fun _ _ => pure (.ok 0)
      columnDouble := fun _ _ => pure (.ok 0.0)
      columnTextBytes := fun _ _ => pure (.ok ByteArray.empty)
      columnBlob := fun _ _ => pure (.ok ByteArray.empty)
      modifyTable := fun f => modifyGet fun st =>
        let (res, tbl') := f st.tbl
        (res, { st with tbl := tbl' }) }
  let rawOps := Sqlite.Raw.Internal.mkRawOps fakeCOps
  let errDummy : Sqlite.Raw.SqliteError := { kind := .ioError, message := "dummy" }
  let ((r1, r2, rClose1, rClose2, rClose2b), stEnd) := (do
    let db1 ← rawOps.openDb ":memory:" { foreignKeys := false, walMode := false }
    let db2 ← rawOps.openDb "disk.db" { foreignKeys := true, walMode := true }
    match db1, db2 with
    | .ok h1, .ok h2 =>
      let st2 ← rawOps.prepare h2 "SELECT 1"
      let c1 ← rawOps.closeDb h1
      let c2 ← rawOps.closeDb h2
      match st2 with
      | .ok s2 =>
        let _ ← rawOps.finalize s2
        let c2b ← rawOps.closeDb h2
        pure (Except.ok h1, Except.ok h2, c1, c2, c2b)
      | _ => pure (Except.error errDummy, Except.ok h2, c1, c2, Except.error errDummy)
    | e1, e2 => pure (e1, e2, Except.error errDummy, Except.error errDummy, Except.error errDummy)
    ).run {}
  checkB "mkRawOps open1" (r1 matches .ok _)
  checkB "mkRawOps open2" (r2 matches .ok _)
  checkB "mkRawOps pragmas" (stEnd.preparedSqls == #["PRAGMA foreign_keys = ON;", "PRAGMA journal_mode = WAL;", "SELECT 1"])
  checkB "mkRawOps close1" (rClose1 == .ok ())
  checkB "mkRawOps close2 busy" (match rClose2 with | .error e => e.kind == .busy | .ok _ => false)
  checkB "mkRawOps close2 after finalize" (rClose2b == .ok ())

private def runFilesMkOpsUnitTests : IO Unit := do
  let sentinelErr := LinuxSyscall.Errno.ENOSYS
  let raw : LinuxSyscall.Files.Internal.PosixFilesOps :=
    { openat := fun _ _ _ _ => pure (.error sentinelErr)
      openat2 := fun _ _ _ _ _ => pure (.error sentinelErr)
      close := fun _ => pure (.error sentinelErr)
      read := fun _ _ => pure (.error sentinelErr)
      write := fun _ _ => pure (.error sentinelErr)
      fstat := fun _ => pure (.error sentinelErr)
      fstatat := fun _ _ _ => pure (.error sentinelErr)
      faccessat := fun _ _ _ _ => pure (.error sentinelErr)
      mkdirat := fun _ _ _ => pure (.error sentinelErr)
      unlinkat := fun _ _ _ => pure (.error sentinelErr)
      renameat2 := fun _ _ _ _ _ => pure (.error sentinelErr)
      symlinkat := fun _ _ _ => pure (.error sentinelErr)
      readlinkat := fun _ _ _ => pure (.error sentinelErr)
      getdents64 := fun _ _ => pure (.error sentinelErr)
      fchmodat := fun _ _ _ => pure (.error sentinelErr)
      fchmod := fun _ _ => pure (.error sentinelErr)
      flock := fun _ _ => pure (.error sentinelErr)
      fcntl := fun _ _ _ => pure (.error sentinelErr)
      fsync := fun _ => pure (.error sentinelErr)
      getcwd := fun _ => pure (.error sentinelErr)
      lseek := fun _ _ _ => pure (.error sentinelErr)
      reopenReadOnly := fun _ => pure (.error sentinelErr)
      dupStdio := fun _ => pure (.error sentinelErr) }
  let ops := LinuxSyscall.Files.Internal.mkFilesOps raw
  let nul := ByteArray.mk #[97, 0, 98]
  let okP := "ok".toUTF8
  let expectEinval {α : Type} (label : String) (act : IO (Except LinuxSyscall.Errno α)) : IO Unit := do
    match ← act with
    | .error e =>
      if e != LinuxSyscall.Errno.EINVAL then
        throw (IO.userError s!"mkFilesOps {label}: expected EINVAL, got {e}")
    | .ok _ => throw (IO.userError s!"mkFilesOps {label}: expected EINVAL, got ok")
  let expectEnosys {α : Type} (label : String) (act : IO (Except LinuxSyscall.Errno α)) : IO Unit := do
    match ← act with
    | .error e =>
      if e != sentinelErr then
        throw (IO.userError s!"mkFilesOps {label}: expected ENOSYS, got {e}")
    | .ok _ => throw (IO.userError s!"mkFilesOps {label}: expected ENOSYS, got ok")
  expectEinval "openat" (ops.openat none nul {} 0)
  expectEnosys "openat pass" (ops.openat none okP {} 0)
  expectEinval "openat2" (ops.openat2 none nul {})
  expectEnosys "openat2 pass" (ops.openat2 none okP {})
  expectEinval "fstatat" (ops.fstatat none nul {})
  expectEinval "fstatat eaccess" (ops.fstatat none okP { eaccess := true })
  expectEnosys "fstatat pass" (ops.fstatat none okP {})
  expectEinval "faccessat" (ops.faccessat none nul {} {})
  expectEnosys "faccessat pass" (ops.faccessat none okP {} {})
  expectEinval "mkdirat" (ops.mkdirat none nul 0o755)
  expectEnosys "mkdirat pass" (ops.mkdirat none okP 0o755)
  expectEinval "unlinkat" (ops.unlinkat none nul false)
  expectEnosys "unlinkat pass" (ops.unlinkat none okP false)
  expectEinval "renameat2 old" (ops.renameat2 none nul none okP {})
  expectEinval "renameat2 new" (ops.renameat2 none okP none nul {})
  expectEnosys "renameat2 pass" (ops.renameat2 none okP none okP {})
  expectEinval "symlinkat target" (ops.symlinkat nul none okP)
  expectEinval "symlinkat link" (ops.symlinkat okP none nul)
  expectEnosys "symlinkat pass" (ops.symlinkat okP none okP)
  expectEinval "readlinkat" (ops.readlinkat none nul 64)
  expectEnosys "readlinkat pass" (ops.readlinkat none okP 64)
  expectEinval "fchmodat" (ops.fchmodat none nul 0o644)
  expectEnosys "fchmodat pass" (ops.fchmodat none okP 0o644)

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
    name := "cli", version := some "1.0"
    options := [
      { name := "flag", long := some "flag", short := some 'f', kind := .bool, global := true },
      { name := "rep", long := some "rep", kind := .bool, repeatable := true, global := true, envVar := some "REP" },
      { name := "num", long := some "num", short := some 'n', kind := .nat, global := true },
      { name := "shortonly", short := some 's', kind := .nat, global := true }
    ]
    subcommands := [{ name := "build", args := [{ name := "items", kind := .string, variadic := true, required := false }] }]
  }
  let spReqArg : CmdLine.CommandSpec := {
    name := "reqcli"
    options := [{ name := "k", long := some "k", kind := .nat }]
    args := [{ name := "files", kind := .string, variadic := true, required := true }]
  }
  let spOptArg : CmdLine.CommandSpec := {
    name := "optcli"
    args := [{ name := "files", kind := .string, variadic := true, required := false, default := some "def" }]
  }
  let spNoVer : CmdLine.CommandSpec := {
    name := "nover", shortVersion := true
    options := [{ name := "x", short := some 'x', kind := .bool }]
  }
  let spBad : CmdLine.CommandSpec := { name := "bad cmd" }
  let helpTxt := match CmdLine.renderHelp sp [] with | .ok s => s | .error _ => ""
  checkB "renderHelp subcmds" ((helpTxt.splitOn "<SUBCOMMAND>").length > 1 && (helpTxt.splitOn "SUBCOMMANDS:").length > 1)
  checkB "renderHelp bool no val" ((helpTxt.splitOn "--flag <VALUE>").length == 1)
  checkB "renderHelp nat placeholder" ((helpTxt.splitOn "--num <VALUE>").length > 1)
  let spNegColl : CmdLine.CommandSpec := {
    name := "c", options := [{ name := "a", long := some "flag", kind := .bool }, { name := "b", long := some "no-flag", kind := .nat }]
  }
  let spRepNoColl : CmdLine.CommandSpec := {
    name := "c", options := [{ name := "a", long := some "rep", kind := .bool, repeatable := true }, { name := "b", long := some "no-rep", kind := .nat }]
  }
  checkB "collectLongsTR bool neg" (!CmdLine.isValidSpec spNegColl && CmdLine.isValidSpec spRepNoColl)
  let rDup := CmdLine.parse sp ["build", "--num=1", "--num=2"]
  checkB "non-repeatable dup" (match rDup with | .error e => e.kind == .invalidValue | _ => false)
  let repOpt : CmdLine.OptSpec := { name := "rep", long := some "rep", kind := .bool, repeatable := true, envVar := some "REP" }
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
    name := "sr", options := [{ name := "r", short := some 'r', kind := .bool, repeatable := true }]
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

private def runDnsUnitTests : IO Unit := do
  let checkB (label : String) (cond : Bool) : IO Unit := do
    if !cond then throw (IO.userError s!"{label} failed")
  match ← LinuxSyscall.Dns.getaddrinfo "" with
  | .error e =>
    checkB "dns empty invalidHost" (e.kind == .invalidHost && e.gaiCode == LinuxSyscall.Dns.EAI_NONAME)
  | .ok _ => throw (IO.userError "dns empty unexpectedly succeeded")
  match ← LinuxSyscall.Dns.getaddrinfo "a\x00b" with
  | .error e =>
    checkB "dns nul invalidHost" (e.kind == .invalidHost && e.gaiCode == LinuxSyscall.Dns.EAI_NONAME)
  | .ok _ => throw (IO.userError "dns nul unexpectedly succeeded")
  checkB "dns 127.0.0.1" ((← LinuxSyscall.Dns.getaddrinfo "127.0.0.1") == .ok [.ipv4 127 0 0 1])
  checkB "dns ::1" ((← LinuxSyscall.Dns.getaddrinfo "::1") == .ok [.ipv6 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 1 0])
  checkB "dns ::ffff:127.0.0.1 any"
    ((← LinuxSyscall.Dns.getaddrinfo "::ffff:127.0.0.1" { family := .ipv4, sockType := .any }) ==
      .ok [.ipv4 127 0 0 1, .ipv4 127 0 0 1, .ipv4 127 0 0 1])
  match ← LinuxSyscall.Dns.getaddrinfo "fe80::1%lo" with
  | .ok addrs => checkB "dns scoped fe80::1%lo" (!addrs.isEmpty && addrs.all fun a => a.isIpv6 && !a.isUnscoped)
  | .error e => throw (IO.userError s!"dns fe80::1%lo failed: {repr e}")
  match ← LinuxSyscall.Dns.getaddrinfo "bad host" with
  | .error e => checkB "dns bad host" (e.kind == .nameNotFound)
  | .ok _ => throw (IO.userError "dns bad host unexpectedly succeeded")
  let addrs : List LinuxSyscall.Dns.DnsAddr :=
    [.ipv4 10 0 0 1, .ipv6 0xfe 0x80 0 0 0 0 0 0 0 0 0 0 0 0 0 1 7]
  checkB "dns codec roundtrip"
    (LinuxSyscall.Dns.Internal.decodeRecords (LinuxSyscall.Dns.Internal.encodeRecords addrs) == .ok addrs)
  let mockSys := LinuxSyscall.Dns.Internal.mkDnsOps
    { getaddrinfo := fun _ _ _ => pure (.error (LinuxSyscall.Dns.EAI_SYSTEM, LinuxSyscall.Errno.ENOENT, "mock sys".toUTF8)) }
  match ← mockSys.getaddrinfo "example.invalid" {} with
  | .error e =>
    checkB "dns mock EAI_SYSTEM" (e.kind == .systemError && e.errno? == some LinuxSyscall.Errno.ENOENT && e.message == "mock sys")
  | .ok _ => throw (IO.userError "dns mock EAI_SYSTEM unexpectedly succeeded")
  let mockBadUtf8 := LinuxSyscall.Dns.Internal.mkDnsOps
    { getaddrinfo := fun _ _ _ => pure (.error (LinuxSyscall.Dns.EAI_FAIL, 0, ByteArray.mk #[0xff, 0xfe])) }
  match ← mockBadUtf8.getaddrinfo "example.invalid" {} with
  | .error e => checkB "dns mock non-utf8" (e.kind == .nameNotFound && e.gaiCode == LinuxSyscall.Dns.EAI_FAIL && e.message == "<non-utf8:2B>")
  | .ok _ => throw (IO.userError "dns mock non-utf8 unexpectedly succeeded")

private def checkUnit (label : String) (ok : Bool) : IO Unit :=
  unless ok do
    throw (IO.userError s!"unit check failed: {label}")

private def runPollOpsUnitTests : IO Unit := do
  let mkMock (revBytes : ByteArray) (failPpoll? : Option LinuxSyscall.Errno := none) :
      LinuxSyscall.Poll.PosixPollOpsM (StateM Nat) Nat :=
    { ppoll := fun _ _ _ _ _ => do
        modify (· + 1)
        return match failPpoll? with
          | some e => .error e
          | none => .ok revBytes
      eventfd2 := fun _ _ => do
        modify (· + 1)
        return .ok 7 }
  let opsOk := LinuxSyscall.Poll.Internal.mkPollOpsM (mkMock (ByteArray.mk #[0x1f]))
  let opsShort := LinuxSyscall.Poll.Internal.mkPollOpsM (mkMock ByteArray.empty)
  let opsErr := LinuxSyscall.Poll.Internal.mkPollOpsM (mkMock ByteArray.empty (some LinuxSyscall.Errno.ENOSYS))
  let (rNeg, cNeg) := (opsOk.ppoll #[(1, { pollin := true })] (some { sec := -1, nsec := 0 })).run 0
  checkUnit "mkPollOpsM neg sec" (rNeg == .error LinuxSyscall.Errno.EINVAL && cNeg == 0)
  let (rNsec, cNsec) := (opsOk.ppoll #[(1, { pollin := true })] (some { sec := 0, nsec := 1000000000 })).run 0
  checkUnit "mkPollOpsM big nsec" (rNsec == .error LinuxSyscall.Errno.EINVAL && cNsec == 0)
  let bigEntries := Array.replicate (LinuxSyscall.Poll.MAX_POLL_NFDS + 1) (1, { pollin := true })
  let (rBig, cBig) := (opsOk.ppoll bigEntries none).run 0
  checkUnit "mkPollOpsM max nfds" (rBig == .error LinuxSyscall.Errno.EINVAL && cBig == 0)
  let (rMismatch, cMismatch) := (opsShort.ppoll #[(1, { pollin := true })] none).run 0
  checkUnit "mkPollOpsM revBytes len mismatch" (rMismatch == .error LinuxSyscall.Errno.EIO && cMismatch == 1)
  let (rRawErr, cRawErr) := (opsErr.ppoll #[(1, { pollin := true })] (some { sec := 1, nsec := 5 })).run 0
  checkUnit "mkPollOpsM raw err prop" (rRawErr == .error LinuxSyscall.Errno.ENOSYS && cRawErr == 1)
  let (rOk, cOk) := (opsOk.ppoll #[(1, { pollin := true })] (some { sec := 0, nsec := 0 })).run 0
  checkUnit "mkPollOpsM ok" (rOk == .ok #[{ pollin := true, pollout := true, pollerr := true, pollhup := true, pollnval := true }] && cOk == 1)
  let (rEfd, cEfd) := (opsOk.eventfd2 3 { nonblock := true, cloexec := true, semaphore := false }).run 0
  checkUnit "mkPollOpsM eventfd2" (rEfd == .ok 7 && cEfd == 1)

private def runNetOpsUnitTests : IO Unit := do
  let sentinel := LinuxSyscall.Errno.ENOSYS
  let mockRaw : LinuxSyscall.Net.PosixNetOpsM (StateM Nat) Nat :=
    { socket := fun _ _ _ _ => modify (· + 1) *> pure (.error sentinel)
      socketpair := fun _ _ _ => modify (· + 1) *> pure (.error sentinel)
      bind := fun _ _ => modify (· + 1) *> pure (.error sentinel)
      listen := fun _ _ => modify (· + 1) *> pure (.error sentinel)
      accept4 := fun _ _ => modify (· + 1) *> pure (.ok (9, (0, LinuxSyscall.Net.INADDR_LOOPBACK, 0, 0, 8080, 0, 0, ByteArray.empty)))
      connect := fun _ _ => modify (· + 1) *> pure (.error sentinel)
      getsockopt := fun _ _ => modify (· + 1) *> pure (.ok 1)
      setsockopt := fun _ _ _ => modify (· + 1) *> pure (.ok ())
      getsockname := fun _ => modify (· + 1) *> pure (.ok (2, 0, 0, 0, 0, 0, 0, "u".toUTF8))
      recvfrom := fun _ _ _ => modify (· + 1) *> pure (.ok "hi".toUTF8)
      sendto := fun _ _ _ => modify (· + 1) *> pure (.ok 2)
      shutdown := fun _ _ => modify (· + 1) *> pure (.ok ())
      sendmsg := fun _ _ => modify (· + 1) *> pure (.error sentinel)
      recvmsg := fun _ _ => modify (· + 1) *> pure (.error sentinel)
      ioctl := fun _ _ _ _ => modify (· + 1) *> pure (.error sentinel) }
  let ops := LinuxSyscall.Net.Internal.mkNetOpsM mockRaw
  let (rSock1, cSock1) := (ops.socket .unix .stream {} 6).run 0
  checkUnit "mkNetOpsM socket unix proto" (rSock1 == .error LinuxSyscall.Errno.EPROTONOSUPPORT && cSock1 == 0)
  let (rSock2, cSock2) := (ops.socket .inet .stream {} 263).run 0
  checkUnit "mkNetOpsM socket inet proto>=263" (rSock2 == .error LinuxSyscall.Errno.EINVAL && cSock2 == 0)
  let (rSock3, cSock3) := (ops.socket .inet .stream {} 6).run 0
  checkUnit "mkNetOpsM socket valid passthrough" (rSock3 == .error sentinel && cSock3 == 1)
  let (rPair1, cPair1) := (ops.socketpair .inet .stream {}).run 0
  checkUnit "mkNetOpsM socketpair inet" (rPair1 == .error LinuxSyscall.Errno.EOPNOTSUPP && cPair1 == 0)
  let (rPair2, cPair2) := (ops.socketpair .unix .dgram {}).run 0
  checkUnit "mkNetOpsM socketpair unix passthrough" (rPair2 == .error sentinel && cPair2 == 1)
  let badUnix1 := LinuxSyscall.Net.SockAddr.unix ByteArray.empty
  let badUnix2 := LinuxSyscall.Net.SockAddr.unix (ByteArray.mk #[65, 0, 66])
  let badUnix3 := LinuxSyscall.Net.SockAddr.unix (ByteArray.mk (Array.replicate (LinuxSyscall.Net.UNIX_PATH_MAX + 1) 97))
  let goodAddr := LinuxSyscall.Net.SockAddr.ipv4 LinuxSyscall.Net.INADDR_LOOPBACK 8080
  let (rBind1, cBind1) := (ops.bind 1 badUnix1).run 0
  let (rBind2, cBind2) := (ops.bind 1 badUnix2).run 0
  let (rBind3, cBind3) := (ops.bind 1 badUnix3).run 0
  let (rBindOk, cBindOk) := (ops.bind 1 goodAddr).run 0
  checkUnit "mkNetOpsM bind guards" (rBind1 == .error LinuxSyscall.Errno.EINVAL && cBind1 == 0 &&
    rBind2 == .error LinuxSyscall.Errno.EINVAL && cBind2 == 0 &&
    rBind3 == .error LinuxSyscall.Errno.EINVAL && cBind3 == 0 &&
    rBindOk == .error sentinel && cBindOk == 1)
  let (rConn1, cConn1) := (ops.connect 1 badUnix1).run 0
  let (rConn2, cConn2) := (ops.connect 1 badUnix2).run 0
  let (rConnOk, cConnOk) := (ops.connect 1 goodAddr).run 0
  checkUnit "mkNetOpsM connect guards" (rConn1 == .error LinuxSyscall.Errno.EINVAL && cConn1 == 0 &&
    rConn2 == .error LinuxSyscall.Errno.EINVAL && cConn2 == 0 &&
    rConnOk == .error sentinel && cConnOk == 1)
  let (rSend0, cSend0) := (ops.sendmsg 1 #[]).run 0
  let (rSend33, cSend33) := (ops.sendmsg 1 (Array.replicate (LinuxSyscall.Net.MAX_SCM_FDS + 1) 2)).run 0
  let (rSendOk, cSendOk) := (ops.sendmsg 1 #[2]).run 0
  checkUnit "mkNetOpsM sendmsg guards" (rSend0 == .error LinuxSyscall.Errno.EINVAL && cSend0 == 0 &&
    rSend33 == .error LinuxSyscall.Errno.EINVAL && cSend33 == 0 &&
    rSendOk == .error sentinel && cSendOk == 1)
  let (rRecv0, cRecv0) := (ops.recvmsg 1 0).run 0
  let (rRecv33, cRecv33) := (ops.recvmsg 1 (UInt32.ofNat (LinuxSyscall.Net.MAX_SCM_FDS + 1))).run 0
  let (rRecvOk, cRecvOk) := (ops.recvmsg 1 4).run 0
  checkUnit "mkNetOpsM recvmsg guards" (rRecv0 == .error LinuxSyscall.Errno.EINVAL && cRecv0 == 0 &&
    rRecv33 == .error LinuxSyscall.Errno.EINVAL && cRecv33 == 0 &&
    rRecvOk == .error sentinel && cRecvOk == 1)
  let badIf1 := ByteArray.mk (Array.replicate LinuxSyscall.Net.IFNAMSIZ 97)
  let badIf2 := ByteArray.mk #[108, 0, 111]
  let (rIoctl1, cIoctl1) := (ops.ioctl 1 .getIfFlags badIf1).run 0
  let (rIoctl2, cIoctl2) := (ops.ioctl 1 .getIfFlags badIf2).run 0
  let (rIoctlOk, cIoctlOk) := (ops.ioctl 1 (.setIfFlags LinuxSyscall.Net.IFF_UP) "lo".toUTF8).run 0
  checkUnit "mkNetOpsM ioctl guards" (rIoctl1 == .error LinuxSyscall.Errno.EINVAL && cIoctl1 == 0 &&
    rIoctl2 == .error LinuxSyscall.Errno.EINVAL && cIoctl2 == 0 &&
    rIoctlOk == .error sentinel && cIoctlOk == 1)
  let (rAcc, cAcc) := (ops.accept4 1 {}).run 0
  let (rGsn, cGsn) := (ops.getsockname 1).run 0
  checkUnit "mkNetOpsM accept4/getsockname" (rAcc == .ok (9, goodAddr) && cAcc == 1 &&
    rGsn == .ok (LinuxSyscall.Net.SockAddr.unix "u".toUTF8) && cGsn == 1)

private def runProcessMutExtra : IO Unit := do
  let checkB (msg : String) (cond : Bool) : IO Unit := do
    if !cond then
      throw (IO.userError s!"process mutate-driver check failed: {msg}")
  let pf0 : LinuxSyscall.Process.PipeFlags := { cloexec := false, nonblock := true, direct := true, notificationPipe := true }
  checkB "PipeFlags.isValid valid" pf0.isValid
  checkB "PipeFlags.toBits valid" (pf0.toBits == 0xe)
  let pfBad : LinuxSyscall.Process.PipeFlags := { extraBits := 1 }
  checkB "PipeFlags.isValid extraBits" (!pfBad.isValid)
  checkB "PipeFlags.toBits extraBits" (pfBad.toBits == 0x11)
  let wf0 : LinuxSyscall.Process.WaitFlags := { nohang := true, untraced := true, continued := true, wall := true, wclone := true, wnothread := true }
  checkB "WaitFlags.isValid valid" wf0.isValid
  checkB "WaitFlags.toBits valid" (wf0.toBits == 0x3f)
  let wfBad : LinuxSyscall.Process.WaitFlags := { extraBits := 2 }
  checkB "WaitFlags.isValid extraBits" (!wfBad.isValid)
  checkB "WaitFlags.toBits extraBits" (wfBad.toBits == 0x80)
  let pof0 : LinuxSyscall.Process.PidfdOpenFlags := { nonblock := true, thread := true }
  checkB "PidfdOpenFlags.isValid valid" pof0.isValid
  checkB "PidfdOpenFlags.toBits valid" (pof0.toBits == 0x3)
  let pofBad : LinuxSyscall.Process.PidfdOpenFlags := { extraBits := 1 }
  checkB "PidfdOpenFlags.isValid extraBits" (!pofBad.isValid)
  checkB "PidfdOpenFlags.toBits extraBits" (pofBad.toBits == 0x4)
  let psf0 : LinuxSyscall.Process.PidfdSignalFlags := { processGroup := true }
  checkB "PidfdSignalFlags.isValid valid" psf0.isValid
  checkB "PidfdSignalFlags.toBits valid" (psf0.toBits == 0x4)
  checkB "PidfdSignalFlags.isValid exclusive" (!(LinuxSyscall.Process.PidfdSignalFlags.mk true true false 0).isValid)
  let psfBad : LinuxSyscall.Process.PidfdSignalFlags := { extraBits := 1 }
  checkB "PidfdSignalFlags.isValid extraBits" (!psfBad.isValid)
  checkB "PidfdSignalFlags.toBits extraBits" (psfBad.toBits == 0x8)
  checkB "Signal.sigkill toRaw" (LinuxSyscall.Process.Signal.sigkill.toRaw == (3, 0))
  checkB "Signal.sigkill toLinuxNum" (LinuxSyscall.Process.Signal.sigkill.toLinuxNum == 9)
  checkB "Signal.sigzero valid" (LinuxSyscall.Process.Signal.sigzero.isValid)
  checkB "Signal.raw 32 nptl" (LinuxSyscall.Process.Signal.raw 32 |>.isNptlReserved)
  checkB "Signal.raw 33 nptl" (LinuxSyscall.Process.Signal.raw 33 |>.isNptlReserved)
  checkB "Signal.raw -1 invalid" (!(LinuxSyscall.Process.Signal.raw (-1)).isValid)
  checkB "Signal.raw 65 invalid" (!(LinuxSyscall.Process.Signal.raw 65).isValid)
  checkB "WaitResult.stillRunning" (LinuxSyscall.Process.WaitResult.ofRawWait4 (0, 0) == .stillRunning)
  checkB "WaitResult.exited" (LinuxSyscall.Process.WaitResult.ofRawWait4 (42, 0x0700) == .exited 42 7)
  checkB "WaitResult.signaled core" (LinuxSyscall.Process.WaitResult.ofRawWait4 (42, 0x8b) == .signaled 42 11 true)
  checkB "WaitResult.stopped" (LinuxSyscall.Process.WaitResult.ofRawWait4 (42, 0x137f) == .stopped 42 19)
  checkB "WaitResult.continued" (LinuxSyscall.Process.WaitResult.ofRawWait4 (42, 0xffff) == .continued 42)
  checkB "pipe2 invalid extraBits EINVAL"
    (match ← LinuxSyscall.Process.pipe2 pfBad with | .error e => e == LinuxSyscall.Errno.EINVAL | .ok _ => false)
  checkB "pipe2 high extraBits EINVAL"
    (match ← LinuxSyscall.Process.pipe2 { extraBits := 0x80000000 } with | .error e => e == LinuxSyscall.Errno.EINVAL | .ok _ => false)
  if !(← LinuxSyscall.Fuzz.ProcessEnv.probeKernelWatchQueue) then
    let notifOk ←
      match ← LinuxSyscall.Process.pipe2 { notificationPipe := true } with
      | .error e => pure (e == LinuxSyscall.Process.errnoENOPKG)
      | .ok (r, w) =>
        let _ ← LinuxSyscall.Fuzz.ProcessEnv.closeFd r
        let _ ← LinuxSyscall.Fuzz.ProcessEnv.closeFd w
        pure false
    checkB "pipe2 notificationPipe ENOPKG" notifOk
  checkB "waitpid invalid extraBits EINVAL" ((← LinuxSyscall.Process.waitpid 0 wfBad) == .error LinuxSyscall.Errno.EINVAL)
  checkB "waitpid high extraBits EINVAL" ((← LinuxSyscall.Process.waitpid 0 { extraBits := 0x80000000 }) == .error LinuxSyscall.Errno.EINVAL)
  match ← LinuxSyscall.Process.getpid with
  | .ok selfPid =>
    checkB "pidfd_open invalid extraBits EINVAL"
      (match ← LinuxSyscall.Process.pidfd_open selfPid pofBad with | .error e => e == LinuxSyscall.Errno.EINVAL | .ok _ => false)
    checkB "pidfd_open high extraBits EINVAL"
      (match ← LinuxSyscall.Process.pidfd_open selfPid { extraBits := 0x80000000 } with | .error e => e == LinuxSyscall.Errno.EINVAL | .ok _ => false)
    match ← LinuxSyscall.Process.pidfd_open selfPid {} with
    | .ok pfd =>
      checkB "pidfd_send_signal invalid extraBits EINVAL" ((← LinuxSyscall.Process.pidfd_send_signal pfd .sigzero psfBad) == .error LinuxSyscall.Errno.EINVAL)
      checkB "pidfd_send_signal high extraBits EINVAL" ((← LinuxSyscall.Process.pidfd_send_signal pfd .sigzero { extraBits := 0x80000000 }) == .error LinuxSyscall.Errno.EINVAL)
      checkB "pidfd_send_signal valid sigzero ok" ((← LinuxSyscall.Process.pidfd_send_signal pfd .sigzero {}) == .ok ())
      checkB "pidfd_open self close ok" ((← LinuxSyscall.Fuzz.ProcessEnv.closeFd pfd) == .ok ())
      checkB "pidfd_open double close EBADF" ((← LinuxSyscall.Fuzz.ProcessEnv.closeFd pfd) == .error LinuxSyscall.Errno.EBADF)
      checkB "pidfd_send_signal closed EBADF" ((← LinuxSyscall.Process.pidfd_send_signal pfd .sigzero {}) == .error LinuxSyscall.Errno.EBADF)
    | .error e => throw (IO.userError s!"pidfd_open self in MutateDriver failed: {e}")
  | .error e => throw (IO.userError s!"getpid in MutateDriver failed: {e}")
  match ← LinuxSyscall.Process.pipe2 { cloexec := true } with
  | .ok (rd, wr) =>
    match ← LinuxSyscall.Fuzz.ProcessEnv.getFdFlags rd, ← LinuxSyscall.Fuzz.ProcessEnv.getFdFlags wr with
    | .ok (_, flR), .ok (_, flW) =>
      checkB "pipe2 rd O_RDONLY" ((flR &&& 3) == 0)
      checkB "pipe2 wr O_WRONLY" ((flW &&& 3) == 1)
    | _, _ => throw (IO.userError "getFdFlags failed on pipe2 in MutateDriver")
    checkB "pipe2 rd close ok" ((← LinuxSyscall.Fuzz.ProcessEnv.closeFd rd) == .ok ())
    checkB "pipe2 wr close ok" ((← LinuxSyscall.Fuzz.ProcessEnv.closeFd wr) == .ok ())
  | .error e => throw (IO.userError s!"pipe2 in MutateDriver failed: {e}")
  match ← LinuxSyscall.Fuzz.ProcessEnv.spawnControlled (-1) false with
  | .ok (cPid, _) =>
    try
      checkB "waitpid live child stillRunning" ((← LinuxSyscall.Process.waitpid cPid.toInt32 { nohang := true }) == .ok .stillRunning)
      checkB "waitpid __WCLONE ECHILD on SIGCHLD child" ((← LinuxSyscall.Process.waitpid cPid.toInt32 { nohang := true, wclone := true }) == .error LinuxSyscall.Errno.ECHILD)
    finally
      LinuxSyscall.Fuzz.ProcessEnv.cleanupChild cPid
  | .error e => throw (IO.userError s!"spawnControlled in MutateDriver failed: {e}")
  for secErr in #[(1 : UInt32), 4, 5, 7, 9, 12, 28, 104, 116, 122, 4095] do
    match ← LinuxSyscall.Fuzz.ProcessEnv.checkFdCloseSeccomp secErr with
    | .ok true => pure ()
    | other => throw (IO.userError s!"checkFdCloseSeccomp {secErr} failed in MutateDriver: {repr other}")
  match ← LinuxSyscall.Fuzz.ProcessEnv.checkSeccompEfaultAbort with
  | .ok true => pure ()
  | other => throw (IO.userError s!"checkSeccompEfaultAbort failed in MutateDriver: {repr other}")

private def cproxySendAll (fd : LinuxSyscall.RawFd) (bs : ByteArray) : IO Unit := do
  let mut off : Nat := 0
  let mut guard : Nat := 0
  while off < bs.size && guard < bs.size + 64 do
    guard := guard + 1
    let slice := if off == 0 then bs else bs.extract off bs.size
    match ← LinuxSyscall.Net.sendto fd slice { nosignal := true } with
    | .ok n =>
      if n == 0 then
        throw (IO.userError "cproxySendAll unexpected 0-byte send")
      off := off + n.toNat
    | .error e =>
      if e != LinuxSyscall.Errno.EINTR then
        throw (IO.userError s!"cproxySendAll sendto failed: {e}")

private def cproxyWaitPollin (fd : LinuxSyscall.RawFd) (timeoutMs : Nat) : IO Bool := do
  let ts : LinuxSyscall.Poll.Timespec :=
    { sec := Int64.ofNat (timeoutMs / 1000)
      nsec := UInt32.ofNat ((timeoutMs % 1000) * 1000000) }
  let mut retries : Nat := 8
  while retries > 0 do
    retries := retries - 1
    match ← LinuxSyscall.Poll.ppoll #[(fd, { pollin := true })] (some ts) with
    | .ok rev =>
      let ev := rev[0]?.getD ({} : LinuxSyscall.Poll.PollEvents)
      return (ev.pollin || ev.pollhup || ev.pollerr)
    | .error e =>
      if e != LinuxSyscall.Errno.EINTR then
        return false
  return false

private def cproxyRecvAllUntilEof (fd : LinuxSyscall.RawFd) (timeoutMs : Nat) (maxBytes : Nat := 131072) : IO ByteArray := do
  let mut acc := ByteArray.empty
  let mut done := false
  let mut steps : Nat := 0
  while !done && steps < 4096 && acc.size < maxBytes do
    steps := steps + 1
    if !(← cproxyWaitPollin fd timeoutMs) then
      throw (IO.userError s!"cproxyRecvAllUntilEof timed out at {acc.size} bytes")
    match ← LinuxSyscall.Net.recvfrom fd 8192 {} with
    | .ok chunk =>
      if chunk.size == 0 then
        done := true
      else
        acc := acc ++ chunk
    | .error e =>
      if e == LinuxSyscall.Errno.ECONNRESET then
        done := true
      else if e != LinuxSyscall.Errno.EINTR then
        throw (IO.userError s!"cproxyRecvAllUntilEof recvfrom failed: {e}")
  return acc

private def cproxyRecvUntilSubstr (fd : LinuxSyscall.RawFd) (needle : ByteArray) (timeoutMs : Nat) : IO ByteArray := do
  let mut acc := ByteArray.empty
  let mut steps : Nat := 0
  while steps < 256 do
    steps := steps + 1
    if !(← cproxyWaitPollin fd timeoutMs) then
      throw (IO.userError "cproxyRecvUntilSubstr timed out")
    match ← LinuxSyscall.Net.recvfrom fd 1024 {} with
    | .ok chunk =>
      if chunk.size == 0 then
        return acc
      acc := acc ++ chunk
      if (ConnectProxy.SysBridge.findCrlfCrlf acc 0).isSome && needle.size == 4 then
        return acc
    | .error e =>
      if e != LinuxSyscall.Errno.EINTR then
        return acc
  return acc

private def cproxyBindLoopbackServer : IO (LinuxSyscall.RawFd × UInt16) := do
  let sfd ← match ← LinuxSyscall.Net.socket .inet .stream { cloexec := true } 0 with
    | .ok fd => pure fd
    | .error e => throw (IO.userError s!"server socket failed: {e}")
  let _ ← LinuxSyscall.Net.setsockopt sfd .reuseAddr 1
  match ← LinuxSyscall.Net.bind sfd (.ipv4 LinuxSyscall.Net.INADDR_LOOPBACK 0) with
  | .ok () => pure ()
  | .error e =>
    let _ ← LinuxSyscall.Files.close sfd
    throw (IO.userError s!"server bind failed: {e}")
  match ← LinuxSyscall.Net.listen sfd 16 with
  | .ok () => pure ()
  | .error e =>
    let _ ← LinuxSyscall.Files.close sfd
    throw (IO.userError s!"server listen failed: {e}")
  match ← LinuxSyscall.Net.getsockname sfd with
  | .ok (.ipv4 _ port) => return (sfd, port)
  | _ =>
    let _ ← LinuxSyscall.Files.close sfd
    throw (IO.userError "server getsockname unexpected sockaddr")

private def cproxyDialLoopback (port : UInt16) : IO LinuxSyscall.RawFd := do
  let cfd ← match ← LinuxSyscall.Net.socket .inet .stream { cloexec := true } 0 with
    | .ok fd => pure fd
    | .error e => throw (IO.userError s!"client socket failed: {e}")
  match ← LinuxSyscall.Net.connect cfd (.ipv4 LinuxSyscall.Net.INADDR_LOOPBACK port) with
  | .ok () => return cfd
  | .error e =>
    let _ ← LinuxSyscall.Files.close cfd
    throw (IO.userError s!"client connect failed: {e}")

private structure ScriptedCProxyState where
  rxQueue : List (Except LinuxSyscall.Errno ByteArray) := []
  txQueue : List (Except LinuxSyscall.Errno UInt32) := []
  accQueue : List (Except LinuxSyscall.Errno (Nat × LinuxSyscall.Net.SockAddr)) := []
  pollQueue : List (Except LinuxSyscall.Errno (Array LinuxSyscall.Poll.PollEvents)) := []
  soErrQueue : List (Except LinuxSyscall.Errno UInt32) := []
  connQueue : List (Except LinuxSyscall.Errno Unit) := []
  sentLog : ByteArray := ByteArray.empty
  closedFds : Array Nat := #[]
  dialed : Array LinuxSyscall.Net.SockAddr := #[]
  nextSock : Nat := 50

private def scriptedCProxySys : ConnectProxy.SysBridge.CProxySysOpsM (StateM ScriptedCProxyState) Nat :=
  let popRx : StateM ScriptedCProxyState (Except LinuxSyscall.Errno ByteArray) := do
    let s ← get
    match s.rxQueue with
    | hd :: tl => set { s with rxQueue := tl }; return hd
    | [] => return .error LinuxSyscall.Errno.EAGAIN
  let popTx (bs : ByteArray) : StateM ScriptedCProxyState (Except LinuxSyscall.Errno UInt32) := do
    let s ← get
    match s.txQueue with
    | hd :: tl =>
      let sent' := match hd with
        | .ok n => s.sentLog ++ bs.extract 0 (Nat.min n.toNat bs.size)
        | .error _ => s.sentLog
      set { s with txQueue := tl, sentLog := sent' }
      return hd
    | [] => return .error LinuxSyscall.Errno.EAGAIN
  { files :=
      { openat := fun _ _ _ _ => pure (.error LinuxSyscall.Errno.ENOSYS)
        openat2 := fun _ _ _ => pure (.error LinuxSyscall.Errno.ENOSYS)
        close := fun fd => do modify (fun s => { s with closedFds := s.closedFds.push fd }); return .ok ()
        read := fun _ _ => pure (.error LinuxSyscall.Errno.ENOSYS)
        write := fun _ _ => pure (.error LinuxSyscall.Errno.ENOSYS)
        fstat := fun _ => pure (.error LinuxSyscall.Errno.ENOSYS)
        fstatat := fun _ _ _ => pure (.error LinuxSyscall.Errno.ENOSYS)
        faccessat := fun _ _ _ _ => pure (.error LinuxSyscall.Errno.ENOSYS)
        mkdirat := fun _ _ _ => pure (.error LinuxSyscall.Errno.ENOSYS)
        unlinkat := fun _ _ _ => pure (.error LinuxSyscall.Errno.ENOSYS)
        renameat2 := fun _ _ _ _ _ => pure (.error LinuxSyscall.Errno.ENOSYS)
        symlinkat := fun _ _ _ => pure (.error LinuxSyscall.Errno.ENOSYS)
        readlinkat := fun _ _ _ => pure (.error LinuxSyscall.Errno.ENOSYS)
        getdents64 := fun _ _ => pure (.error LinuxSyscall.Errno.ENOSYS)
        fchmodat := fun _ _ _ => pure (.error LinuxSyscall.Errno.ENOSYS)
        fchmod := fun _ _ => pure (.error LinuxSyscall.Errno.ENOSYS)
        flock := fun _ _ => pure (.error LinuxSyscall.Errno.ENOSYS)
        fcntl := fun _ _ => pure (.error LinuxSyscall.Errno.ENOSYS)
        fsync := fun _ => pure (.error LinuxSyscall.Errno.ENOSYS)
        getcwd := fun _ => pure (.error LinuxSyscall.Errno.ENOSYS)
        lseek := fun _ _ _ => pure (.error LinuxSyscall.Errno.ENOSYS)
        reopenReadOnly := fun _ => pure (.error LinuxSyscall.Errno.ENOSYS)
        dupStdio := fun _ => pure (.error LinuxSyscall.Errno.ENOSYS) }
    net :=
      { socket := fun _ _ _ _ => do
          let s ← get
          set { s with nextSock := s.nextSock + 1 }
          return .ok s.nextSock
        socketpair := fun _ _ _ => pure (.ok (60, 61))
        bind := fun _ _ => pure (.ok ())
        listen := fun _ _ => pure (.ok ())
        accept4 := fun _ _ => do
          let s ← get
          match s.accQueue with
          | hd :: tl => set { s with accQueue := tl }; return hd
          | [] => return .error LinuxSyscall.Errno.EAGAIN
        connect := fun _ sa => do
          let s ← get
          set { s with dialed := s.dialed.push sa }
          match s.connQueue with
          | hd :: tl => modify (fun st => { st with connQueue := tl }); return hd
          | [] => return .error LinuxSyscall.Errno.EINPROGRESS
        getsockopt := fun _ _ => do
          let s ← get
          match s.soErrQueue with
          | hd :: tl => set { s with soErrQueue := tl }; return hd
          | [] => return .ok 0
        setsockopt := fun _ _ _ => pure (.ok ())
        getsockname := fun _ => pure (.ok (.ipv4 LinuxSyscall.Net.INADDR_LOOPBACK 18080))
        recvfrom := fun _ _ _ => popRx
        sendto := fun _ bs _ => popTx bs
        shutdown := fun _ _ => pure (.ok ())
        sendmsg := fun _ _ => pure (.error LinuxSyscall.Errno.ENOSYS)
        recvmsg := fun _ _ => pure (.error LinuxSyscall.Errno.ENOSYS)
        ioctl := fun _ _ _ => pure (.error LinuxSyscall.Errno.ENOSYS) }
    poll :=
      { ppoll := fun _ _ => do
          let s ← get
          match s.pollQueue with
          | hd :: tl => set { s with pollQueue := tl }; return hd
          | [] => return .ok #[]
        eventfd2 := fun _ _ => pure (.error LinuxSyscall.Errno.ENOSYS) }
    dns :=
      { getaddrinfo := fun _ _ => pure (.ok []) }
    timeRand :=
      { clock_gettime := fun _ => pure (.ok { sec := 1, nsec := 0 })
        clock_nanosleep := fun _ _ _ => pure (.ok ())
        getrandom := fun _ _ => pure (.ok ByteArray.empty) } }

private def runConnectProxyScriptedTests : IO Unit := do
  checkUnit "cproxy listenPollEvents cap"
    ((ConnectProxy.SysBridge.listenPollEvents 0 2).pollin == true &&
     (ConnectProxy.SysBridge.listenPollEvents 1 2).pollin == true &&
     (ConnectProxy.SysBridge.listenPollEvents 2 2).pollin == false &&
     (ConnectProxy.SysBridge.listenPollEvents 3 2).pollin == false)
  let rxInit : ScriptedCProxyState :=
    { rxQueue := [.ok (ByteArray.mk #[65]), .error LinuxSyscall.Errno.EINTR,
                  .ok (ByteArray.mk #[66, 67]), .error LinuxSyscall.Errno.ECONNRESET] }
  let (rxOut, _) := (ConnectProxy.Relay.recvIntoRing scriptedCProxySys.net 7 8 {}).run rxInit
  match rxOut with
  | some (rb', eof) =>
    checkUnit "cproxy recvIntoRing EINTR + ECONNRESET preserves bytes"
      (eof == true && rb'.toList == [65, 66, 67])
  | none =>
    throw (IO.userError "recvIntoRing unexpectedly dropped bytes on EINTR/ECONNRESET")
  let txInit : ScriptedCProxyState :=
    { txQueue := [.error LinuxSyscall.Errno.EINTR, .ok 2, .error LinuxSyscall.Errno.EINTR, .ok 2] }
  let rb0 := ({} : ConnectProxy.Relay.RingBuf).push ("ABCD".toUTF8)
  let (txOut, txSt) := (ConnectProxy.Relay.flushRingNonblock scriptedCProxySys.net 7 8 rb0).run txInit
  checkUnit "cproxy flushRingNonblock EINTR + short writes"
    (txOut.map (·.isEmpty) == some true && txSt.sentLog == "ABCD".toUTF8)
  let pipeInit : ScriptedCProxyState :=
    { txQueue := [.error LinuxSyscall.Errno.EINTR, .ok 2, .ok 3] }
  let st0 := ConnectProxy.Relay.RelayState.init 10 11 ("HELLO".toUTF8)
  let (stPipe, stPipeW) :=
    (ConnectProxy.Relay.stepBidirectionalRelay scriptedCProxySys.net scriptedCProxySys.closeFd
      st0 {} { pollout := true }).run pipeInit
  checkUnit "cproxy relay pipelined prefix flush + 200 preserved"
    (stPipe.prefixFlushed == true && stPipeW.sentLog == "HELLO".toUTF8 &&
     stPipe.u2c.toList == ConnectProxy.Relay.reply200Bytes.data.toList)
  let accInit : ScriptedCProxyState :=
    { accQueue := [
        .error LinuxSyscall.Errno.EINTR,
        .ok (21, .ipv4 LinuxSyscall.Net.INADDR_LOOPBACK 40001),
        .error LinuxSyscall.Errno.EINTR,
        .ok (22, .ipv4 LinuxSyscall.Net.INADDR_LOOPBACK 40002),
        .ok (23, .ipv4 LinuxSyscall.Net.INADDR_LOOPBACK 40003)
      ] }
  let lim2 : ConnectProxy.ProxyLimits := { maxConcurrentTunnels := 2 }
  let (accSlots, _) :=
    (ConnectProxy.SysBridge.acceptNewClients (dnsJob := Unit) scriptedCProxySys lim2 3 100 #[]).run accInit
  checkUnit "cproxy acceptNewClients EINTR + maxConcurrentTunnels"
    (accSlots.size == 2)
  let hsCapInit : ScriptedCProxyState := { rxQueue := [.ok ("0123456789ABCDEF".toUTF8)] }
  let lim16 : ConnectProxy.ProxyLimits := { maxHeaderBytes := 16 }
  let hsSlot0 : ConnectProxy.SysBridge.ClientSlot Nat Unit := { phase := .handshake 40 ByteArray.empty 5000 }
  let ((hsSlot1, hsEvs1), _) :=
    (ConnectProxy.SysBridge.stepHandshakeReadAux scriptedCProxySys lim16
      (ConnectProxy.Model.decideConnectHead { limits := lim16 })
      (ConnectProxy.Model.decideResolvedIps {})
      (ConnectProxy.SysBridge.startDnsSync scriptedCProxySys lim16 (ConnectProxy.Model.decideResolvedIps {}))
      hsSlot0 #[] 40 5000 1 ByteArray.empty).run hsCapInit
  checkUnit "cproxy stepHandshakeReadAux fuel-1 maxHeaderBytes cap"
    (hsEvs1.size == 1 && !(match hsSlot1.phase with | .handshake .. => true | _ => false))
  let fbCands : Array ConnectProxy.IpAddr := #[.v4 0x7f000001, .v4 0x7f000002]
  let connInit : ScriptedCProxyState :=
    { soErrQueue := [.error LinuxSyscall.Errno.EINTR, .ok LinuxSyscall.Errno.ECONNREFUSED]
      connQueue := [.ok ()] }
  let connSlot0 : ConnectProxy.SysBridge.ClientSlot Nat Unit :=
    { phase := .connecting 30 31 "up.local" 8443 fbCands 1 none 5000
      pipelined := "TAIL".toUTF8
      target? := some ("up.local", 8443) }
  let ((connSlot1, connEvs1), connSt1) :=
    (ConnectProxy.SysBridge.stepConnecting scriptedCProxySys {} connSlot0 #[]
      30 31 "up.local" 8443 fbCands 1 none 5000 {} { pollout := true } 1000).run connInit
  let connRelayOk := match connSlot1.phase with
    | .relay rst => rst.pendingPrefix == "TAIL".toUTF8 && rst.u2c.toList == ConnectProxy.Relay.reply200Bytes.data.toList
    | _ => false
  checkUnit "cproxy stepConnecting SO_ERROR fallback dial + pipelined handoff"
    (connRelayOk && connEvs1.size == 1 && connSt1.closedFds == #[31] &&
     connSt1.dialed == #[.ipv4 0x7f000002 8443])
  let tickInit : ScriptedCProxyState :=
    { pollQueue := [.error LinuxSyscall.Errno.EINTR] }
  let (tickOut, _) :=
    (ConnectProxy.SysBridge.pollAndStepTickSync scriptedCProxySys {}
      (ConnectProxy.Model.decideConnectHead {})
      (ConnectProxy.Model.decideResolvedIps {})
      false 4 3 #[] #[]).run tickInit
  let isRetry := match tickOut with | .retryEintr => true | _ => false
  checkUnit "cproxy pollAndStepTickSync retries ppoll EINTR" isRetry

private def runConnectProxyUnitTests : IO Unit := do
  checkUnit "cproxy parseIpAddr" (ConnectProxy.parseIpAddr "127.0.0.1" == .ok (.v4 0x7f000001))
  checkUnit "cproxy parseIpAddr bad" (!(ConnectProxy.parseIpAddr "10.1*").isOk)
  checkUnit "cproxy parseIpPrefix" (ConnectProxy.parseIpPrefix "10.1.0.0/16" == .ok (.v4 0x0a010000 16))
  checkUnit "cproxy isGlobalIp" (ConnectProxy.isGlobalIp (.v4 0x08080808) && !ConnectProxy.isGlobalIp (.v4 0x7f000001))
  let pol : ConnectProxy.IpPolicy := { base := .empty, extraAllows := #[.v4 0x0a000000 8], extraBans := #[.v4 0x0a000100 24] }
  checkUnit "cproxy allowsIp" (ConnectProxy.allowsIp pol (.v4 0x0a000201) && !ConnectProxy.allowsIp pol (.v4 0x0a000101))
  checkUnit "cproxy parseConnectRequest"
    (ConnectProxy.parseConnectRequest "CONNECT Example.COM:443 HTTP/1.1\r\n\r\n".toUTF8 ==
      .ok { host := "example.com", port := 443 })
  checkUnit "cproxy validateConfig"
    ((ConnectProxy.validateConfig { allowedTargets := #[{ host := "Example.COM", port := 443 }] }).isOk &&
     !(ConnectProxy.validateConfig { limits := { maxHeaderBytes := 0 } }).isOk)
  let mockApi := ConnectProxy.Internal.mkApiM ConnectProxy.Model.mockRawProxyOps
  let (mockRes, mockSt) := (mockApi.withProxy { allowedTargets := #[{ host := "example.com", port := 443 }] }
    fun p => pure (.ok p.port)).run { ephemeralPort := 54321 }
  checkUnit "cproxy mkApiM mock" (mockRes == .ok (54321, #[]) && mockSt.activeHandles == [])
  runConnectProxyScriptedTests
  let (rstSrv, rstPort) ← cproxyBindLoopbackServer
  let rstPayload := ByteArray.mk (Array.replicate 4096 0x5a)
  let rstTask ← IO.asTask (prio := .dedicated) do
    if ← cproxyWaitPollin rstSrv 1500 then
      match ← LinuxSyscall.Net.accept4 rstSrv { cloexec := true } with
      | .ok (ufd, _) =>
        cproxySendAll ufd rstPayload
        let _ ← LinuxSyscall.Files.close ufd
      | .error _ => pure ()
    let _ ← LinuxSyscall.Files.close rstSrv
  let liveCfg : ConnectProxy.ProxyConfig :=
    { listenPort := 0
      allowedTargets := #[
        { host := "127.0.0.1", port := rstPort },
        { host := "allowed.example.com", port := 443 }
      ]
      ipPolicy := { base := .empty, extraAllows := #[.v4 0x7f000000 8] } }
  let liveRes ← ConnectProxy.withProxy liveCfg fun proxy => do
    let cfdDeny ← cproxyDialLoopback proxy.port
    cproxySendAll cfdDeny "CONNECT blocked.example.com:443 HTTP/1.1\r\nHost: blocked.example.com:443\r\n\r\n".toUTF8
    let denyBytes ← cproxyRecvUntilSubstr cfdDeny "\r\n\r\n".toUTF8 800
    let _ ← LinuxSyscall.Files.close cfdDeny
    if ((String.fromUTF8! denyBytes).splitOn "403").length <= 1 then
      return .error { kind := .ioError, message := "expected 403 on blocked target" }
    let cfdRst ← cproxyDialLoopback proxy.port
    let reqRst := s!"CONNECT 127.0.0.1:{rstPort} HTTP/1.1\r\nHost: 127.0.0.1:{rstPort}\r\n\r\nUNREAD_CLIENT_TAIL".toUTF8
    cproxySendAll cfdRst reqRst
    let allRst ← cproxyRecvAllUntilEof cfdRst 1200 16384
    let _ ← LinuxSyscall.Files.close cfdRst
    if allRst.size != ConnectProxy.Relay.reply200Bytes.size + rstPayload.size then
      return .error { kind := .ioError, message := s!"TCP RST lost bytes: got {allRst.size}" }
    return .ok proxy.port
  let _ ← IO.wait rstTask
  match liveRes with
  | .ok (boundPort, evs) =>
    checkUnit "cproxy live loopback + RST conservation"
      (boundPort != 0 && evs.size == 2 &&
       evs[0]?.map (·.outcome) == some .denied &&
       evs[1]?.map (·.outcome) == some .allowed)
  | .error e =>
    throw (IO.userError s!"ConnectProxy live loopback failed: {repr e}")

private def countSelfOpenFds : IO Nat := do
  return (← (System.FilePath.mk "/proc/self/fd").readDir).size

private def cproxyReserveUnlisteningLoopback : IO (LinuxSyscall.RawFd × UInt16) := do
  let sfd ← match ← LinuxSyscall.Net.socket .inet .stream { cloexec := true } 0 with
    | .ok fd => pure fd
    | .error e => throw (IO.userError s!"reserve socket failed: {e}")
  match ← LinuxSyscall.Net.bind sfd (.ipv4 LinuxSyscall.Net.INADDR_LOOPBACK 0) with
  | .ok () => pure ()
  | .error e =>
    let _ ← LinuxSyscall.Files.close sfd
    throw (IO.userError s!"reserve bind failed: {e}")
  match ← LinuxSyscall.Net.getsockname sfd with
  | .ok (.ipv4 _ port) => return (sfd, port)
  | _ =>
    let _ ← LinuxSyscall.Files.close sfd
    throw (IO.userError "reserve getsockname unexpected sockaddr")

private def runConnectProxyMutateExtra : IO Unit := do
  let fdsBefore ← countSelfOpenFds
  let (echoSrv, echoPort) ← cproxyBindLoopbackServer
  let (deadSock, deadPort) ← cproxyReserveUnlisteningLoopback
  let echoTask ← IO.asTask (prio := .dedicated) do
    for _ in [0 : 2] do
      if ← cproxyWaitPollin echoSrv 2000 then
        match ← LinuxSyscall.Net.accept4 echoSrv { cloexec := true } with
        | .ok (ufd, _) =>
          let rx ← cproxyRecvAllUntilEof ufd 1500 65536
          cproxySendAll ufd ("ACK:".toUTF8 ++ rx)
          let _ ← LinuxSyscall.Net.shutdown ufd .wr
          let _ ← LinuxSyscall.Files.close ufd
        | .error _ => pure ()
    let _ ← LinuxSyscall.Files.close echoSrv
  let cfg : ConnectProxy.ProxyConfig :=
    { listenPort := 0
      allowedTargets := #[
        { host := "127.0.0.1", port := echoPort },
        { host := "localhost", port := echoPort },
        { host := "127.0.0.1", port := deadPort }
      ]
      ipPolicy := { base := .empty, extraAllows := #[.v4 0x7f000000 8, .v6 0 1 128] }
      limits :=
        { maxHeaderBytes := 128
          headerTimeoutMs := 120
          connectTimeoutMs := 300
          maxConcurrentTunnels := 2 } }
  let streamBody := ByteArray.mk ((List.range 36000).toArray.map fun i => UInt8.ofNat (i % 251))
  let sessRes ← ConnectProxy.withProxy cfg fun proxy => do
    let cStream ← cproxyDialLoopback proxy.port
    let headWithPipe := s!"CONNECT 127.0.0.1:{echoPort} HTTP/1.1\r\n\r\nPIPE!".toUTF8
    cproxySendAll cStream headWithPipe
    cproxySendAll cStream streamBody
    let _ ← LinuxSyscall.Net.shutdown cStream .wr
    let gotStream ← cproxyRecvAllUntilEof cStream 1500 65536
    let _ ← LinuxSyscall.Files.close cStream
    let expectedStream := ConnectProxy.Relay.reply200Bytes ++ "ACK:PIPE!".toUTF8 ++ streamBody
    if gotStream != expectedStream then
      return .error { kind := .ioError, message := s!"stream mismatch: got={gotStream.size} expected={expectedStream.size}" }
    let cDns ← cproxyDialLoopback proxy.port
    cproxySendAll cDns s!"CONNECT localhost:{echoPort} HTTP/1.1\r\n\r\nDNSOK".toUTF8
    let _ ← LinuxSyscall.Net.shutdown cDns .wr
    let gotDns ← cproxyRecvAllUntilEof cDns 1500 4096
    let _ ← LinuxSyscall.Files.close cDns
    if gotDns != ConnectProxy.Relay.reply200Bytes ++ "ACK:DNSOK".toUTF8 then
      return .error { kind := .ioError, message := s!"localhost DNS relay mismatch: {gotDns.size}" }
    let cOver ← cproxyDialLoopback proxy.port
    let overBytes := ByteArray.mk (Array.replicate 132 65)
    cproxySendAll cOver overBytes
    let gotOver ← cproxyRecvUntilSubstr cOver "\r\n\r\n".toUTF8 800
    let _ ← LinuxSyscall.Files.close cOver
    if ((String.fromUTF8! gotOver).splitOn "403").length <= 1 then
      return .error { kind := .ioError, message := "oversized header did not return 403" }
    let cSlow ← cproxyDialLoopback proxy.port
    cproxySendAll cSlow s!"CONNECT 127.0.0.1:{echoPort} HTTP/1.1\r\n".toUTF8
    let gotSlow ← cproxyRecvUntilSubstr cSlow "\r\n\r\n".toUTF8 800
    let _ ← LinuxSyscall.Files.close cSlow
    if ((String.fromUTF8! gotSlow).splitOn "403").length <= 1 then
      return .error { kind := .ioError, message := "slow header timeout did not return 403" }
    let cDead ← cproxyDialLoopback proxy.port
    cproxySendAll cDead s!"CONNECT 127.0.0.1:{deadPort} HTTP/1.1\r\n\r\n".toUTF8
    let gotDead ← cproxyRecvUntilSubstr cDead "\r\n\r\n".toUTF8 800
    let _ ← LinuxSyscall.Files.close cDead
    if ((String.fromUTF8! gotDead).splitOn "502").length <= 1 then
      return .error { kind := .ioError, message := "refused upstream did not return 502" }
    return .ok ()
  let _ ← IO.wait echoTask
  let _ ← LinuxSyscall.Files.close deadSock
  match sessRes with
  | .error e => throw (IO.userError s!"runConnectProxyMutateExtra session failed: {repr e}")
  | .ok ((), evs) =>
    checkUnit "cproxy extra events" (evs.size == 5)
  let banCfg : ConnectProxy.ProxyConfig :=
    { listenPort := 0
      allowedTargets := #[{ host := "localhost", port := 443 }]
      ipPolicy :=
        { base := .empty
          extraAllows := #[.v4 0x7f000000 8, .v6 0 1 128]
          extraBans := #[.v4 0x7f000000 8, .v6 0 1 128] } }
  let banRes ← ConnectProxy.withProxy banCfg fun proxy => do
    let cBan ← cproxyDialLoopback proxy.port
    cproxySendAll cBan "CONNECT localhost:443 HTTP/1.1\r\n\r\n".toUTF8
    let gotBan ← cproxyRecvUntilSubstr cBan "\r\n\r\n".toUTF8 800
    let _ ← LinuxSyscall.Files.close cBan
    if ((String.fromUTF8! gotBan).splitOn "403").length <= 1 then
      return .error { kind := .ioError, message := "banned resolved IP did not return 403" }
    return .ok ()
  match banRes with
  | .error e => throw (IO.userError s!"cproxy DNS IP ban failed: {repr e}")
  | .ok ((), banEvs) =>
    checkUnit "cproxy DNS IP ban event"
      (banEvs.size == 1 && banEvs[0]?.map (·.outcome) == some .denied)
  let fdsAfter ← countSelfOpenFds
  checkUnit "cproxy zero FD leaks across sessions" (fdsAfter == fdsBefore)

private def allSuites : Array (String × IO (Option String) × IO Unit) := #[
  ("RegExp", do RegExp.RuntimeTests.runAll; smokeRegExp; return none, pure ()),
  ("Glob", do Glob.RuntimeTests.runAll; return none, pure ()),
  ("Fs.Raw", do Fs.Raw.RuntimeTests.runAll; return none, pure ()),
  ("Fs", do Fs.RuntimeTests.runAll; return none, pure ()),
  ("Process.Raw", do Process.Raw.RuntimeTests.runAll; return none, pure ()),
  ("Process", do Process.RuntimeTests.runAll; return none, pure ()),
  ("Time", do Time.RuntimeTests.runAll; return none, pure ()),
  ("Json", do Json.RuntimeTests.runAll; return none, pure ()),
  ("EnvVars.Raw", do EnvVars.Raw.RuntimeTests.runAll; return none, do runPropChecksEnvVarsRaw; runRawDecoderUnitTests),
  ("EnvVars", do EnvVars.RuntimeTests.runAll; return none, runPropChecksEnvVars),
  ("Uuid", do Uuid.RuntimeTests.runAll; return none, pure ()),
  ("Sqlite.Raw", do Sqlite.Raw.RuntimeTests.runAll; return none, runSqliteRawUnitTests),
  ("Sqlite", do Sqlite.RuntimeTests.runAll; return none, pure ()),
  ("Git", do Git.RuntimeTests.runAll; return none, pure ()),
  ("CmdLine", do CmdLine.RuntimeTests.runAll; return none, runCmdLineMutateExtra),
  ("NumParse", do NumParse.RuntimeTests.runAll; return none, pure ()),
  ("Toml", do Toml.RuntimeTests.runAll; return none, pure ()),
  ("TempDir", do TempDir.RuntimeTests.runAll; return none, pure ()),
  ("Compress", do Compress.RuntimeTests.runAll; return none, pure ()),
  ("Base64", do Base64.RuntimeTests.runAll; return none, pure ()),
  ("CryptoHash.Raw", do CryptoHash.Raw.RuntimeTests.runAll; return none, pure ()),
  ("CryptoHash", do CryptoHash.RuntimeTests.runAll; return none, pure ()),
  ("Tar", do Tar.RuntimeTests.runAll; return none, pure ()),
  ("ProcessSandbox.Seccomp", do ProcessSandbox.Seccomp.RuntimeTests.runAll; return none, pure ()),
  ("ProcessSandbox.Raw", ProcessSandbox.Raw.RuntimeTests.runAllOutcome, pure ()),
  ("ProcessSandbox", ProcessSandbox.RuntimeTests.runAllOutcome, pure ()),
  ("ConnectProxy", do ConnectProxy.RuntimeTests.runAll; return none, do runConnectProxyUnitTests; runConnectProxyMutateExtra),
  ("SlotPool", do SlotPool.RuntimeTests.runAll; return none, pure ()),
  ("LinuxSyscall.Sandbox", do LinuxSyscall.Sandbox.RuntimeTests.runAll; return none, pure ()),
  ("LinuxSyscall.TimeRand", do LinuxSyscall.TimeRand.RuntimeTests.runAll; return none, pure ()),
  ("LinuxSyscall.Passwd", do LinuxSyscall.Passwd.RuntimeTests.runAll; return none, pure ()),
  ("LinuxSyscall.Dns", do LinuxSyscall.Dns.RuntimeTests.runAll; return none, runDnsUnitTests),
  ("LinuxSyscall.Poll", do LinuxSyscall.Poll.RuntimeTests.runAll; return none, do LinuxSyscall.Poll.RuntimeTests.runStraceFaultCheck; runPollOpsUnitTests),
  ("LinuxSyscall.Net", do LinuxSyscall.Net.RuntimeTests.runAll; return none, do LinuxSyscall.Net.RuntimeTests.runStraceFaultCheck; runNetOpsUnitTests),
  ("LinuxSyscall.Process", do LinuxSyscall.Process.RuntimeTests.runAll; return none, runProcessMutExtra),
  ("LinuxSyscall.Files", do LeanSwe.LinuxSyscall.Files.RuntimeTests.runAll; return none, runFilesMkOpsUnitTests)
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
  | "--envvars-raw-probe" :: rest =>
    return (← EnvVars.Raw.RuntimeTests.probeMain rest)
  | "--envvars-probe" :: rest =>
    return (← EnvVars.RuntimeTests.probeMain rest)
  | "--cmdline-probe" :: rest =>
    return (← CmdLine.RuntimeTests.probeMain rest)
  | "--slotpool-probe" :: rest =>
    return (← SlotPool.RuntimeTests.probeMain rest)
  | "--compress-probe" :: rest =>
    return (← Compress.RuntimeTests.probeMain rest)
  | "--timerand-strace-fault-check" :: rest =>
    return (← LinuxSyscall.TimeRand.RuntimeTests.probeMain rest)
  | "--passwd-probe" :: rest =>
    return (← LinuxSyscall.Passwd.RuntimeTests.probeMain rest)
  | "--uuid-probe" :: rest =>
    return (← Uuid.RuntimeTests.probeMain rest)
  | "--time-probe" :: rest =>
    return (← Time.RuntimeTests.probeMain rest)
  | "--poll-strace-fault-check" :: rest =>
    return (← LinuxSyscall.Poll.RuntimeTests.probeMain rest)
  | "--poll-strace-worker" :: rest =>
    return (← LinuxSyscall.Poll.RuntimeTests.probeMain ("--worker" :: rest))
  | "--poll-strace-efd-worker" :: rest =>
    return (← LinuxSyscall.Poll.RuntimeTests.probeMain ("--efd-worker" :: rest))
  | "--net-strace-fault-check" :: rest =>
    return (← LinuxSyscall.Net.RuntimeTests.probeMain rest)
  | "--net-strace-worker" :: rest =>
    return (← LinuxSyscall.Net.RuntimeTests.probeMain ("--worker" :: rest))
  | "--suite" :: "process" :: "--ns-worker" :: mode :: arg :: rest =>
    return (← LinuxSyscall.Fuzz.ProcessFuzz.nsWorkerMain mode arg rest)
  | "--process-strace-worker" :: opName :: errName :: _ =>
    return (← LinuxSyscall.Process.RuntimeTests.probeMain ["--worker", opName, errName])
  | "--files-strace-worker" :: rest =>
    return (← LinuxSyscall.Files.RuntimeTests.probeMain ("--worker" :: rest))
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
