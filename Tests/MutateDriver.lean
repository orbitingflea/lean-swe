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
import LeanSwe.ConnectProxy.Raw.RuntimeTests
import LeanSwe.ConnectProxy.RuntimeTests
import LeanSwe.SlotPool.RuntimeTests
import LeanSwe.LinuxSyscall.Sandbox.RuntimeTests
import LeanSwe.LinuxSyscall.TimeRand.RuntimeTests
import LeanSwe.LinuxSyscall.Passwd.RuntimeTests
import LeanSwe.LinuxSyscall.Dns.RuntimeTests

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
  ("ConnectProxy.Raw", do ConnectProxy.Raw.RuntimeTests.runAll; return none, pure ()),
  ("ConnectProxy", do ConnectProxy.RuntimeTests.runAll; return none, pure ()),
  ("SlotPool", do SlotPool.RuntimeTests.runAll; return none, pure ()),
  ("LinuxSyscall.Sandbox", do LinuxSyscall.Sandbox.RuntimeTests.runAll; return none, pure ()),
  ("LinuxSyscall.TimeRand", do LinuxSyscall.TimeRand.RuntimeTests.runAll; return none, pure ()),
  ("LinuxSyscall.Passwd", do LinuxSyscall.Passwd.RuntimeTests.runAll; return none, pure ()),
  ("LinuxSyscall.Dns", do LinuxSyscall.Dns.RuntimeTests.runAll; return none, runDnsUnitTests)
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
