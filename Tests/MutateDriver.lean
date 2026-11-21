import Core.PropCheck
import LeanSwe.RegExp.Interface
import LeanSwe.RegExp.RuntimeTests
import LeanSwe.Glob.RuntimeTests
import LeanSwe.Fs.Raw.RuntimeTests
import LeanSwe.Fs.RuntimeTests
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
import LeanSwe.Sqlite.Interface
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
import LeanSwe.LinuxSyscall.Files.Impl
import LeanSwe.LinuxSyscall.Files.Interface
import LeanSwe.LinuxSyscall.Dns.Impl
import LeanSwe.LinuxSyscall.Dns.Interface
import LeanSwe.LinuxSyscall.Poll.Impl
import LeanSwe.LinuxSyscall.Net.Impl
import LeanSwe.LinuxSyscall.Process.Interface
import Fuzz.Passwd.Suite
import Fuzz.Passwd.Checks
import Fuzz.Dns.Suite
import Fuzz.LinuxSyscall.Sandbox.Strace
import Fuzz.LinuxSyscall.TimeRand.Strace
import Fuzz.LinuxSyscall.Files.Strace
import Fuzz.LinuxSyscall.Poll.Strace
import Fuzz.LinuxSyscall.Net.Strace
import Fuzz.LinuxSyscall.ProcessEnv
import Fuzz.LinuxSyscall.Process.Fuzz
import Fuzz.LinuxSyscall.Process.Strace
import LeanSwe.PostFork.Aeneas.Model
import LeanSwe.PostFork.Aeneas.Funs
import LeanSwe.PostFork.RuntimeTests

@[extern "leanswe_postfork_host_pipe_cloexec"]
private opaque mutPfPipeCloexec : BaseIO (Except LeanSwe.LinuxSyscall.Errno (LeanSwe.LinuxSyscall.RawFd × LeanSwe.LinuxSyscall.RawFd))

@[extern "leanswe_postfork_host_close_fd"]
private opaque mutPfCloseFd : @& LeanSwe.LinuxSyscall.RawFd → BaseIO (Except LeanSwe.LinuxSyscall.Errno Unit)

@[extern "leanswe_postfork_host_write_once"]
private opaque mutPfWriteOnce : @& LeanSwe.LinuxSyscall.RawFd → @& ByteArray → UInt64 → UInt64 → BaseIO (Except LeanSwe.LinuxSyscall.Errno UInt64)

@[extern "leanswe_postfork_host_read_once"]
private opaque mutPfReadOnce : @& LeanSwe.LinuxSyscall.RawFd → UInt64 → BaseIO (Except LeanSwe.LinuxSyscall.Errno ByteArray)

@[extern "leanswe_postfork_host_probe_fd"]
private opaque mutPfProbeFd : Int32 → BaseIO (Except LeanSwe.LinuxSyscall.Errno Unit)

@[extern "leanswe_postfork_host_setpgid"]
private opaque mutPfSetpgid : LeanSwe.PostFork.Pid → LeanSwe.PostFork.Pid → BaseIO (Except LeanSwe.LinuxSyscall.Errno Unit)

@[extern "leanswe_postfork_host_wait_once"]
private opaque mutPfWaitOnce : LeanSwe.PostFork.Pid → BaseIO (Except LeanSwe.LinuxSyscall.Errno LeanSwe.PostFork.ChildWaitStatus)

@[extern "leanswe_postfork_host_fork_run"]
private opaque mutPfForkRun :
    UInt32 → UInt32 →
    @& Array LeanSwe.LinuxSyscall.RawFd → @& ByteArray → @& ByteArray → @& ByteArray →
    @& Array String → @& Array String → @& ByteArray →
    @& Option String → @& String → @& Array String →
    BaseIO (Except LeanSwe.LinuxSyscall.Errno LeanSwe.PostFork.Pid)

@[extern "signal"]
private opaque mutPfCStdSignal : UInt32 → USize → BaseIO USize

@[extern "close"]
private opaque mutPfCStdClose : UInt32 → BaseIO UInt32

@[extern "dup2"]
private opaque mutPfCStdDup2 : Int32 → Int32 → BaseIO Int32

@[noinline]
private def mutPfAllocPipeDropWrite : IO LeanSwe.LinuxSyscall.RawFd := do
  match ← mutPfPipeCloexec with
  | .ok (r, _w) => pure r
  | .error e => throw (IO.userError s!"mutPfAllocPipeDropWrite failed: {e}")

private def mutPfReadProcThreads : IO Nat := do
  let txt ← IO.FS.readFile "/proc/self/status"
  for ln in txt.splitOn "\n" do
    if ln.startsWith "Threads:" then
      let numStr := (ln.drop 8).trimAscii.toString
      if let some n := numStr.toNat? then
        return n
  throw (IO.userError "Threads: missing in /proc/self/status")

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
  checkB "sql tail bom ok" (Sqlite.Raw.Internal.scanSqlTail .normal [0xEF, 0xBB, 0xBF])
  checkB "sql tail bom space ok" (Sqlite.Raw.Internal.scanSqlTail .normal [0xEF, 0xBB, 0xBF, 0x20])
  checkB "sql tail bom1 eof" (!Sqlite.Raw.Internal.scanSqlTail .normal [0xEF])
  checkB "sql tail bom1 bad" (!Sqlite.Raw.Internal.scanSqlTail .normal [0xEF, 0x00])
  checkB "sql tail bom2 eof" (!Sqlite.Raw.Internal.scanSqlTail .normal [0xEF, 0xBB])
  checkB "sql tail bom2 bad" (!Sqlite.Raw.Internal.scanSqlTail .normal [0xEF, 0xBB, 0x00])
  checkB "sql tail normal line cmt" (Sqlite.Raw.Internal.scanSqlTail .normal (bytes "-- tail\n  "))
  checkB "sql tail normal line cmt eof" (Sqlite.Raw.Internal.scanSqlTail .normal (bytes "-- tail"))
  checkB "sql tail normal dash" (!Sqlite.Raw.Internal.scanSqlTail .normal (bytes "-"))
  checkB "sql tail normal dash bad" (!Sqlite.Raw.Internal.scanSqlTail .normal (bytes "-x"))
  checkB "sql tail normal blk cmt" (Sqlite.Raw.Internal.scanSqlTail .normal (bytes "/* ok */"))
  checkB "sql tail normal slash" (!Sqlite.Raw.Internal.scanSqlTail .normal (bytes "/"))
  checkB "sql tail normal slash bad" (!Sqlite.Raw.Internal.scanSqlTail .normal (bytes "/x"))
  checkB "sql tail vt normal" (!Sqlite.Raw.Internal.scanSqlTail .normal [0x0B])
  checkB "sql tail vt inSpace" (Sqlite.Raw.Internal.scanSqlTail .inSpace [0x0B])
  let baBom := ByteArray.mk #[0xEF, 0xBB, 0xBF, 0x2D, 0x2D, 0x63]
  checkB "sql tail ba bom+line" (Sqlite.Raw.Internal.scanSqlTailBa .normal baBom 0)
  checkB "sql tail ba blk" (Sqlite.Raw.Internal.scanSqlTailBa .normal ("/* x */".toUTF8) 0)
  checkB "sql tail ba blk slash" (Sqlite.Raw.Internal.scanSqlTailBa .normal ("/* a/b */".toUTF8) 0)
  checkB "sql tail ba blk stars" (Sqlite.Raw.Internal.scanSqlTailBa .normal ("/* **/".toUTF8) 0)
  checkB "sql tail ba blk unclosed" (!Sqlite.Raw.Internal.scanSqlTailBa .normal ("/* a*x".toUTF8) 0)
  checkB "sql tail ba reject" (!Sqlite.Raw.Internal.scanSqlTailBa .normal ("x".toUTF8) 0)
  checkB "hasZeroByteBa empty" (!Sqlite.Raw.Internal.hasZeroByteBa ByteArray.empty 0)
  checkB "hasZeroByteBa hit0" (Sqlite.Raw.Internal.hasZeroByteBa (ByteArray.mk #[0, 1]) 0)
  checkB "hasZeroByteBa hitEnd" (Sqlite.Raw.Internal.hasZeroByteBa (ByteArray.mk #[1, 2, 0]) 0)
  checkB "hasZeroByteBa miss" (!Sqlite.Raw.Internal.hasZeroByteBa (ByteArray.mk #[1, 2, 3]) 0)
  let rOverTimeout ← Sqlite.Raw.openDb ":memory:" { busyTimeoutMs := 0x80000000 }
  checkB "raw openDb busy_timeout > max" (match rOverTimeout with | .error e => e.kind == .invalidInput | .ok _ => false)
  let rExactTimeout ← Sqlite.Raw.openDb ":memory:" { busyTimeoutMs := 0x7fffffff, walMode := false, foreignKeys := false }
  match rExactTimeout with
  | .error e => throw (IO.userError s!"Sqlite.Raw exact INT_MAX timeout failed: {repr e}")
  | .ok hExact =>
    let rCloseExact ← Sqlite.Raw.closeDb hExact
    checkB "raw closeDb exact timeout" (rCloseExact == .ok ())
  let rDb ← Sqlite.Raw.openDb ":memory:" { walMode := false, foreignKeys := false }
  match rDb with
  | .error e => throw (IO.userError s!"Sqlite.Raw openDb failed: {repr e}")
  | .ok h =>
    let rStmt ← Sqlite.Raw.prepare h "SELECT X'', ?"
    match rStmt with
    | .error e =>
      let _ ← Sqlite.Raw.closeDb h
      throw (IO.userError s!"Sqlite.Raw prepare failed: {repr e}")
    | .ok sh =>
      let rB ← Sqlite.Raw.bind sh #[.bytes ByteArray.empty]
      checkB "shim bind empty blob" (rB == .ok ())
      let rSt ← Sqlite.Raw.step sh
      checkB "shim empty blob not null" (rSt == .ok (.row #[.bytes ByteArray.empty, .bytes ByteArray.empty]))
      let rBusyClose ← Sqlite.Raw.closeDb h
      checkB "shim close with active stmt" (match rBusyClose with | .error e => e.kind == .busy | .ok _ => false)
      let rBusyDefaultClose ← Sqlite.Raw.defaultOps.closeDb h
      checkB "defaultOps close with active stmt"
        (match rBusyDefaultClose with | .error e => e.kind == .busy | .ok _ => false)
      let rFin1 ← Sqlite.Raw.finalize sh
      checkB "shim finalize ok" (rFin1 == .ok ())
      let rFin2 ← Sqlite.Raw.finalize sh
      checkB "shim double finalize misuse" (match rFin2 with | .error e => e.kind == .misuse | .ok _ => false)
      let rCl1 ← Sqlite.Raw.closeDb h
      checkB "shim close ok" (rCl1 == .ok ())
      let rCl2 ← Sqlite.Raw.defaultOps.closeDb h
      checkB "shim double close misuse" (match rCl2 with | .error e => e.kind == .misuse | .ok _ => false)

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
        let consumed :=
          if sql == "SELECT 1; SELECT 2" then 9
          else if sql == "OVERCONSUME" then 999
          else sql.toUTF8.size
        (.ok (some (.mock tok), consumed),
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
  checkB "uri ba %%" (Sqlite.Raw.Internal.decodeUriMatchBa "%%41".toUTF8 0 4 (bytes "%A"))
  checkB "uri ba %4%41" (Sqlite.Raw.Internal.decodeUriMatchBa "%4%41".toUTF8 0 5 (bytes "%4A"))
  checkB "uri ba over normal ok" (Sqlite.Raw.Internal.decodeUriMatchBa "a".toUTF8 0 5 (bytes "a"))
  checkB "uri ba over normal no" (!Sqlite.Raw.Internal.decodeUriMatchBa "a".toUTF8 0 5 (bytes "ab"))
  checkB "uri ba over pct ok" (Sqlite.Raw.Internal.decodeUriMatchBa "%".toUTF8 0 5 (bytes "%"))
  checkB "uri ba over pct no" (!Sqlite.Raw.Internal.decodeUriMatchBa "%".toUTF8 0 5 (bytes "%%"))
  checkB "uri ba over pcthex ok" (Sqlite.Raw.Internal.decodeUriMatchBa "%4".toUTF8 0 5 (bytes "%4"))
  checkB "uri ba over pcthex no" (!Sqlite.Raw.Internal.decodeUriMatchBa "%4".toUTF8 0 5 (bytes "%41"))
  checkB "classifyBytes :memory:" (Sqlite.Raw.Internal.classifyPathBytes (bytes ":memory:") == (true, false))
  checkB "classifyBytes plain" (Sqlite.Raw.Internal.classifyPathBytes (bytes "plain.db") == (false, false))
  checkB "classifyBytes file::memory:" (Sqlite.Raw.Internal.classifyPathBytes (bytes "file::memory:") == (true, false))
  checkB "classifyBytes mode=memory" (Sqlite.Raw.Internal.classifyPathBytes (bytes "file:a.db?mode=memory") == (true, false))
  checkB "classifyBytes mode=ro" (Sqlite.Raw.Internal.classifyPathBytes (bytes "file:a.db?mode=ro") == (false, true))
  checkB "classifyBytes mode keep" (Sqlite.Raw.Internal.classifyPathBytes (bytes "file:a.db?mode=memory&x=1") == (true, false))
  checkB "classifyBytes mode override ro" (Sqlite.Raw.Internal.classifyPathBytes (bytes "file:a.db?mode=memory&mode=ro") == (false, true))
  checkB "classifyBytes mode override rwc" (Sqlite.Raw.Internal.classifyPathBytes (bytes "file:a.db?mode=ro&mode=rwc") == (false, false))
  checkB "classifyBytes mode bare" (Sqlite.Raw.Internal.classifyPathBytes (bytes "file:a.db?mode") == (false, false))
  checkB "hasZeroByte empty" (!Sqlite.Raw.Internal.hasZeroByte [])
  checkB "hasZeroByte hit0" (Sqlite.Raw.Internal.hasZeroByte [0, 1])
  checkB "hasZeroByte hitEnd" (Sqlite.Raw.Internal.hasZeroByte [1, 2, 0])
  checkB "hasZeroByte miss" (!Sqlite.Raw.Internal.hasZeroByte [1, 2, 3])
  checkB "hasZeroByteBa oob" (!Sqlite.Raw.Internal.hasZeroByteBa (ByteArray.mk #[1, 2]) 5)
  checkB "mapRawError empty cantOpen"
    ((Sqlite.Raw.mapRawError (.cantOpen (some "p") 14 "")).message == "unable to open sqlite database")
  checkB "mapRawError custom cantOpen"
    ((Sqlite.Raw.mapRawError (.cantOpen none 14 "custom")).message == "custom")
  checkB "mapRawError empty busy"
    ((Sqlite.Raw.mapRawError (.busy 5 "")).message == "sqlite database is busy")
  checkB "mapRawError empty constraint"
    ((Sqlite.Raw.mapRawError (.constraint 19 "")).message == "sqlite constraint failed")
  checkB "mapRawError empty misuse"
    ((Sqlite.Raw.mapRawError (.misuse 21 "")).message == "sqlite library misuse")
  checkB "mapRawError empty invalidArg"
    ((Sqlite.Raw.mapRawError (.invalidArgument "")).message == "invalid sqlite argument")
  checkB "mapRawError empty ioFailure"
    ((Sqlite.Raw.mapRawError (.ioFailure 8 "")).message == "sqlite io failure (8)")
  checkB "mapRawError empty codeErr"
    ((Sqlite.Raw.mapRawError (.sqliteCodeError 1 "")).message == "sqlite error (1)")
  checkB "mapRawError empty userErr"
    ((Sqlite.Raw.mapRawError (.userError "")).message == "sqlite error")
  checkB "attachOpenPath none"
    (Sqlite.Raw.Internal.attachOpenPath "x.db" (.cantOpen none 14 "d") == .cantOpen (some "x.db") 14 "d")
  checkB "attachOpenPath some"
    (Sqlite.Raw.Internal.attachOpenPath "x.db" (.cantOpen (some "y.db") 14 "d") == .cantOpen (some "y.db") 14 "d")
  checkB "sql tail ba inSpace vt" (Sqlite.Raw.Internal.scanSqlTailBa .normal (ByteArray.mk #[0x20, 0x0B]) 0)
  checkB "sql tail ba normal vt no" (!Sqlite.Raw.Internal.scanSqlTailBa .normal (ByteArray.mk #[0x0B]) 0)
  checkB "sql tail ba inSpace bom" (Sqlite.Raw.Internal.scanSqlTailBa .normal (ByteArray.mk #[0x20, 0xEF, 0xBB, 0xBF]) 0)
  checkB "sql tail ba inSpace bom1 bad" (!Sqlite.Raw.Internal.scanSqlTailBa .normal (ByteArray.mk #[0x20, 0xEF, 0x00]) 0)
  checkB "sql tail ba inSpace bom2 bad" (!Sqlite.Raw.Internal.scanSqlTailBa .normal (ByteArray.mk #[0x20, 0xEF, 0xBB, 0x00]) 0)
  checkB "sql tail ba inSpace cmt" (Sqlite.Raw.Internal.scanSqlTailBa .normal (ByteArray.mk #[0x20, 0x2F, 0x2A, 0x2A, 0x2F]) 0)
  checkB "sql tail ba inSpace bad" (!Sqlite.Raw.Internal.scanSqlTailBa .normal " x".toUTF8 0)
  checkB "sql tail ba over ok" (Sqlite.Raw.Internal.scanSqlTailBaAux .normal " ".toUTF8 0 5)
  checkB "sql tail ba over unclosed" (!Sqlite.Raw.Internal.scanSqlTailBaAux .normal "/*".toUTF8 0 5)
  let (emptyOpenRes, _) := (rawOps.openDb "" {}).run {}
  checkB "mkRawOps empty path" (match emptyOpenRes with | .error e => e.kind == .invalidInput | .ok _ => false)
  let (nulOpenRes, _) := (rawOps.openDb "a\x00b" {}).run {}
  checkB "mkRawOps nul path" (match nulOpenRes with | .error e => e.kind == .invalidInput | .ok _ => false)
  let (roCreateRes, _) := (rawOps.openDb ":memory:" { readOnly := true, createIfMissing := true }).run {}
  checkB "mkRawOps ro+create" (match roCreateRes with | .error e => e.kind == .invalidInput | .ok _ => false)
  let (overToRes, _) := (rawOps.openDb ":memory:" { busyTimeoutMs := 0x80000000 }).run {}
  checkB "mkRawOps over timeout" (match overToRes with | .error e => e.kind == .invalidInput | .ok _ => false)
  let ((nulPrepRes, badBindRes, multiPrepRes, overConPrepRes), _) := (do
    let .ok h ← rawOps.openDb ":memory:" { walMode := false, foreignKeys := false }
      | pure (Except.error errDummy, Except.error errDummy, Except.error errDummy, Except.error errDummy)
    let pNul ← rawOps.prepare h "SELECT \x001"
    let pMulti ← rawOps.prepare h "SELECT 1; SELECT 2"
    let pOverCon ← rawOps.prepare h "OVERCONSUME"
    let .ok s0 ← rawOps.prepare h "SELECT 1"
      | pure (pNul, Except.error errDummy, pMulti, pOverCon)
    let bMis ← rawOps.bind s0 #[.int 1]
    let _ ← rawOps.finalize s0
    let _ ← rawOps.closeDb h
    pure (pNul, bMis, pMulti, pOverCon)).run {}
  checkB "mkRawOps prepare NUL" (match nulPrepRes with | .error e => e.kind == .invalidInput | .ok _ => false)
  checkB "mkRawOps bind arity" (match badBindRes with | .error e => e.kind == .invalidInput | .ok _ => false)
  checkB "mkRawOps prepare multi" (match multiPrepRes with | .error e => e.kind == .misuse && e.sqliteCode == some 21 | .ok _ => false)
  checkB "mkRawOps prepare overconsume" (match overConPrepRes with | .error e => e.kind == .misuse && e.sqliteCode == some 21 | .ok _ => false)
  let rPermUri ← Sqlite.Raw.openDb "file::memory:?mode=rw" { readOnly := true, createIfMissing := false }
  checkB "raw openDb mode=rw ro SQLITE_PERM"
    (match rPermUri with | .error e => e.kind == .ioError && e.sqliteCode == some 3 | .ok _ => false)
  let bigSql := String.pushn "" ' ' (Sqlite.Raw.maxSqlByteLen + 1)
  let (overRes, _) := (do
    let dbRes ← rawOps.openDb ":memory:" { walMode := false, foreignKeys := false }
    match dbRes with
    | .ok h =>
      let pRes ← rawOps.prepare h bigSql
      let _ ← rawOps.closeDb h
      pure pRes
    | .error e => pure (.error e)).run {}
  checkB "mkRawOps prepare > maxSqlByteLen" (match overRes with | .error e => e.kind == .invalidInput | .ok _ => false)
  match ← Sqlite.Raw.openDb ":memory:" { walMode := false, foreignKeys := false } with
  | .error e => throw (IO.userError s!"Sqlite.Raw openDb for bigSql failed: {repr e}")
  | .ok hBig =>
    let defOverRes ← Sqlite.Raw.prepare hBig bigSql
    let _ ← Sqlite.Raw.closeDb hBig
    checkB "defaultOps prepare > maxSqlByteLen" (match defOverRes with | .error e => e.kind == .invalidInput | .ok _ => false)

  let hCloseCnt ← IO.mkRef 0
  let hFinCnt ← IO.mkRef 0
  let hClearCnt ← IO.mkRef 0
  let hResetCnt ← IO.mkRef 0
  let hFailSetup ← IO.mkRef true
  let tblRef ← IO.mkRef ({} : Sqlite.Raw.RawHandleTable)
  let isolatedMockC : Sqlite.Raw.CSqliteOps :=
    { modifyTable := fun f => tblRef.modifyGet f
      openV2 := fun _ _ => pure (.ok (.mock 501))
      close := fun _ => do hCloseCnt.modify (· + 1); pure (.ok ())
      extendedResultCodes := fun _ _ => pure (.ok ())
      busyTimeout := fun _ _ => do
        if ← hFailSetup.get then pure (.error (.busy 5 "setup busy")) else pure (.ok ())
      prepareV2 := fun _ sql =>
        let consumed := if sql == "SELECT 1; SELECT 2" then 9 else sql.toUTF8.size
        pure (.ok (some (.mock 601), consumed))
      step := fun _ => pure (.ok .done)
      reset := fun _ => do hResetCnt.modify (· + 1); pure (.ok ())
      clearBindings := fun _ => do hClearCnt.modify (· + 1); pure (.ok ())
      finalize := fun _ => do hFinCnt.modify (· + 1); pure (.finalized none)
      bindParamCount := fun _ => pure (.ok 1)
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
      columnBlob := fun _ _ => pure (.ok ByteArray.empty) }
  let isolatedOps := Sqlite.Raw.Internal.mkRawOps isolatedMockC
  let rSetupErr ← isolatedOps.openDb ":memory:" { walMode := false, foreignKeys := false }
  checkB "mkRawOps setup err closes rawDb"
    ((match rSetupErr with | .error e => e.kind == .busy | .ok _ => false) &&
      (← hCloseCnt.get) == 1 && (← isolatedOps.activeDbCount) == 0)
  hFailSetup.set false
  match ← isolatedOps.openDb ":memory:" { walMode := false, foreignKeys := false } with
  | .error e => throw (IO.userError s!"mkRawOps openDb failed: {repr e}")
  | .ok hIsoDb =>
    let rMulti ← isolatedOps.prepare hIsoDb "SELECT 1; SELECT 2"
    checkB "mkRawOps multi-stmt finalizes rawStmt"
      ((match rMulti with | .error e => e.kind == .misuse && e.sqliteCode == some 21 | .ok _ => false) &&
        (← hFinCnt.get) == 1 && (← isolatedOps.activeStmtCount) == 0)
    match ← isolatedOps.prepare hIsoDb "SELECT ?" with
    | .error e =>
      let _ ← isolatedOps.closeDb hIsoDb
      throw (IO.userError s!"mkRawOps prepare SELECT ? failed: {repr e}")
    | .ok hIsoSt =>
      let rBindIso ← isolatedOps.bind hIsoSt #[.int 7]
      checkB "mkRawOps bind resets and clears bindings"
        (rBindIso == .ok () && (← hResetCnt.get) == 1 && (← hClearCnt.get) == 1)
      let rFinIso ← isolatedOps.finalize hIsoSt
      let rClIso ← isolatedOps.closeDb hIsoDb
      checkB "mkRawOps finalize+close clean"
        (rFinIso == .ok () && rClIso == .ok () &&
          (← isolatedOps.activeDbCount) == 0 && (← isolatedOps.activeStmtCount) == 0)

private def runSqliteUnitTests : IO Unit := do
  let checkB (msg : String) (cond : Bool) : IO Unit := do
    if !cond then throw (IO.userError s!"Sqlite unit check failed: {msg}")
  let eInv := Sqlite.mapRawError (.invalidArgument "bad")
  checkB "mapRawError invalid" (eInv.kind == .invalidInput && !eInv.message.isEmpty)
  let vBad := Sqlite.validateConfig { readOnly := true, createIfMissing := true }
  checkB "validateConfig ro+create" (match vBad with | .error e => e.kind == .invalidInput | .ok _ => false)
  let dbBad ← Sqlite.withDb "" {} (fun _ => pure (.ok ()))
  checkB "withDb empty path" (match dbBad with | .error e => e.kind == .invalidInput | .ok _ => false)
  let rTxRbFail ← Sqlite.withDb ":memory:" { walMode := false, foreignKeys := false } fun db =>
    Sqlite.withTransaction (α := Unit) db fun h => do
      let _ ← Sqlite.exec h "COMMIT"
      pure (.error { kind := Sqlite.Raw.SqliteErrorKind.busy, message := "body fail" })
  checkB "withTransaction preserves body fail over rollback fail"
    (match rTxRbFail with
     | .error e => e.kind == Sqlite.Raw.SqliteErrorKind.busy && e.message == "body fail"
     | .ok _ => false)
  let rTxComRbFail ← Sqlite.withDb ":memory:" { walMode := false, foreignKeys := false } fun db =>
    Sqlite.withTransaction (α := Unit) db fun h => do
      let _ ← Sqlite.exec h "COMMIT"
      pure (.ok ())
  checkB "withTransaction propagates commit->rollback fail"
    (match rTxComRbFail with
     | .error e => e.kind == Sqlite.Raw.SqliteErrorKind.ioError && e.sqliteCode == some 1
     | .ok _ => false)
  let rQuery ← Sqlite.withDb ":memory:" { walMode := false, foreignKeys := false } fun db => do
    match ← Sqlite.exec db "CREATE TABLE t(id INTEGER PRIMARY KEY, v INT)" with
    | .error e => pure (.error e)
    | .ok () =>
      match ← Sqlite.exec db "INSERT INTO t(id, v) VALUES (1, ?)" #[.int 42] with
      | .error e => pure (.error e)
      | .ok () =>
        match ← Sqlite.query db "SELECT v FROM t ORDER BY id ASC" with
        | .error e => pure (.error e)
        | .ok rows =>
          match ← Sqlite.queryOne db "SELECT v FROM t WHERE id = ?" #[.int 1] with
          | .error e => pure (.error e)
          | .ok one => pure (.ok (rows, one))
  checkB "query+queryOne" (match rQuery with | .ok (rs, some r) => rs == #[#[.int 42]] && r == #[.int 42] | _ => false)
  let nDb ← Sqlite.activeDbCount
  let nSt ← Sqlite.activeStmtCount
  checkB "no leaked handles" (nDb == 0 && nSt == 0)

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
  if !(← Fuzz.LinuxSyscall.ProcessEnv.probeKernelWatchQueue) then
    let notifOk ←
      match ← LinuxSyscall.Process.pipe2 { notificationPipe := true } with
      | .error e => pure (e == LinuxSyscall.Process.errnoENOPKG)
      | .ok (r, w) =>
        let _ ← Fuzz.LinuxSyscall.ProcessEnv.closeFd r
        let _ ← Fuzz.LinuxSyscall.ProcessEnv.closeFd w
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
      checkB "pidfd_open self close ok" ((← Fuzz.LinuxSyscall.ProcessEnv.closeFd pfd) == .ok ())
      checkB "pidfd_open double close EBADF" ((← Fuzz.LinuxSyscall.ProcessEnv.closeFd pfd) == .error LinuxSyscall.Errno.EBADF)
      checkB "pidfd_send_signal closed EBADF" ((← LinuxSyscall.Process.pidfd_send_signal pfd .sigzero {}) == .error LinuxSyscall.Errno.EBADF)
    | .error e => throw (IO.userError s!"pidfd_open self in MutateDriver failed: {e}")
  | .error e => throw (IO.userError s!"getpid in MutateDriver failed: {e}")
  match ← LinuxSyscall.Process.pipe2 { cloexec := true } with
  | .ok (rd, wr) =>
    match ← Fuzz.LinuxSyscall.ProcessEnv.getFdFlags rd, ← Fuzz.LinuxSyscall.ProcessEnv.getFdFlags wr with
    | .ok (_, flR), .ok (_, flW) =>
      checkB "pipe2 rd O_RDONLY" ((flR &&& 3) == 0)
      checkB "pipe2 wr O_WRONLY" ((flW &&& 3) == 1)
    | _, _ => throw (IO.userError "getFdFlags failed on pipe2 in MutateDriver")
    checkB "pipe2 rd close ok" ((← Fuzz.LinuxSyscall.ProcessEnv.closeFd rd) == .ok ())
    checkB "pipe2 wr close ok" ((← Fuzz.LinuxSyscall.ProcessEnv.closeFd wr) == .ok ())
  | .error e => throw (IO.userError s!"pipe2 in MutateDriver failed: {e}")
  match ← Fuzz.LinuxSyscall.ProcessEnv.spawnControlled (-1) false with
  | .ok (cPid, _) =>
    try
      checkB "waitpid live child stillRunning" ((← LinuxSyscall.Process.waitpid cPid.toInt32 { nohang := true }) == .ok .stillRunning)
      checkB "waitpid __WCLONE ECHILD on SIGCHLD child" ((← LinuxSyscall.Process.waitpid cPid.toInt32 { nohang := true, wclone := true }) == .error LinuxSyscall.Errno.ECHILD)
    finally
      Fuzz.LinuxSyscall.ProcessEnv.cleanupChild cPid
  | .error e => throw (IO.userError s!"spawnControlled in MutateDriver failed: {e}")
  for secErr in #[(1 : UInt32), 4, 5, 7, 9, 12, 28, 104, 116, 122, 4095] do
    match ← Fuzz.LinuxSyscall.ProcessEnv.checkFdCloseSeccomp secErr with
    | .ok true => pure ()
    | other => throw (IO.userError s!"checkFdCloseSeccomp {secErr} failed in MutateDriver: {repr other}")
  match ← Fuzz.LinuxSyscall.ProcessEnv.checkSeccompEfaultAbort with
  | .ok true => pure ()
  | other => throw (IO.userError s!"checkSeccompEfaultAbort failed in MutateDriver: {repr other}")

private def runCompressMutateExtra : IO Unit := do
  let checkB (label : String) (cond : Bool) : IO Unit := do
    if !cond then throw (IO.userError s!"{label} failed")
  checkB "zstd compress args default"
    (Compress.Internal.mkCompressArgs .zstd {} == #["-c", "-q", "--no-progress"])
  checkB "zstd compress args explicit"
    (Compress.Internal.mkCompressArgs .zstd { level := some 19, threads := some 0 } ==
      #["-c", "-q", "--no-progress", "-19", "-T0"])
  checkB "xz compress args explicit"
    (Compress.Internal.mkCompressArgs .xz { level := some 0, threads := some 4 } ==
      #["-c", "-q", "-0", "-T4"])
  checkB "gzip compress args explicit"
    (Compress.Internal.mkCompressArgs .gzip { level := some 9 } == #["-c", "-n", "-9"])
  checkB "zstd decompress args"
    (Compress.Internal.mkDecompressArgs .zstd ==
      #["-d", "-c", "-q", "--no-progress", "--format=zstd"])
  checkB "xz decompress args memlimit"
    (Compress.Internal.mkDecompressArgs .xz ==
      #["-d", "-c", "-q", "-T1", "--format=xz"])
  checkB "gzip decompress args"
    (Compress.Internal.mkDecompressArgs .gzip == #["-d", "-c", "-n"])
  let cReq := Compress.Internal.mkCompressRequest .zstd { timeoutMs := 77, maxOutputBytes := 128 } ("ab".toUTF8)
  checkB "compress req slack+env"
    (cReq.program == "zstd" && cReq.cwd == none && cReq.env == Compress.codecSanitizedEnv &&
      cReq.inheritEnv == true && cReq.stdin == "ab".toUTF8 && cReq.timeoutMs == some 77 &&
      cReq.maxOutputBytes == some (128 + Compress.stderrPipeSlack))
  let dReq := Compress.Internal.mkDecompressRequest .xz { timeoutMs := 88, maxOutputBytes := 256 } ("cd".toUTF8)
  checkB "decompress req slack+env"
    (dReq.program == "xz" && dReq.cwd == none && dReq.env == Compress.codecSanitizedEnv &&
      dReq.inheritEnv == true && dReq.stdin == "cd".toUTF8 && dReq.timeoutMs == some 88 &&
      dReq.maxOutputBytes == some (256 + Compress.stderrPipeSlack))
  let vReq := Compress.Internal.mkToolVersionRequest .gzip
  checkB "version req env+limits"
    (vReq.program == "gzip" && vReq.args == #["--version"] && vReq.cwd == none &&
      vReq.env == Compress.codecSanitizedEnv && vReq.inheritEnv == true &&
      vReq.stdin == ByteArray.empty && vReq.timeoutMs == some 5000 && vReq.maxOutputBytes == some 65536)
  let isInvFor (c : Compress.Codec) (r : Except Compress.CompressError Unit) : Bool :=
    match r with
    | .error e =>
      e.kind == .invalidInput && e.codec == some c && e.exitCode == none && e.stderr == none && !e.message.isEmpty
    | .ok () => false
  checkB "validate zstd boundaries+codec"
    (isInvFor .zstd (Compress.Internal.validateCompressOptions .zstd { timeoutMs := 0 } ByteArray.empty) &&
      isInvFor .zstd (Compress.Internal.validateCompressOptions .zstd { maxOutputBytes := 0 } ByteArray.empty) &&
      isInvFor .zstd (Compress.Internal.validateCompressOptions .zstd { maxInputBytes := some 1 } ("ab".toUTF8)) &&
      isInvFor .zstd (Compress.Internal.validateCompressOptions .zstd { level := some 0 } ByteArray.empty) &&
      (Compress.Internal.validateCompressOptions .zstd { level := some 1, threads := some 0 } ByteArray.empty).isOk &&
      (Compress.Internal.validateCompressOptions .zstd { level := some 19, threads := some 4294967295 } ByteArray.empty).isOk &&
      isInvFor .zstd (Compress.Internal.validateCompressOptions .zstd { level := some 20 } ByteArray.empty) &&
      isInvFor .zstd (Compress.Internal.validateCompressOptions .zstd { threads := some 4294967296 } ByteArray.empty) &&
      isInvFor .zstd (Compress.Internal.validateDecompressOptions .zstd { timeoutMs := 0 } ByteArray.empty) &&
      isInvFor .xz (Compress.Internal.validateDecompressOptions .xz { maxOutputBytes := 0 } ByteArray.empty))
  checkB "validate xz+gzip+maxInput boundaries+codec"
    (isInvFor .xz (Compress.Internal.validateCompressOptions .xz { timeoutMs := 0 } ByteArray.empty) &&
      (Compress.Internal.validateCompressOptions .xz { level := some 0, threads := some 16384 } ByteArray.empty).isOk &&
      (Compress.Internal.validateCompressOptions .xz { level := some 9 } ByteArray.empty).isOk &&
      isInvFor .xz (Compress.Internal.validateCompressOptions .xz { level := some 10 } ByteArray.empty) &&
      isInvFor .xz (Compress.Internal.validateCompressOptions .xz { threads := some 16385 } ByteArray.empty) &&
      isInvFor .gzip (Compress.Internal.validateCompressOptions .gzip { level := some 0 } ByteArray.empty) &&
      (Compress.Internal.validateCompressOptions .gzip { level := some 9 } ByteArray.empty).isOk &&
      isInvFor .gzip (Compress.Internal.validateCompressOptions .gzip { threads := some 0 } ByteArray.empty) &&
      (Compress.Internal.validateCompressOptions .gzip { maxInputBytes := some 2 } ("ab".toUTF8)).isOk &&
      isInvFor .gzip (Compress.Internal.validateCompressOptions .gzip { maxInputBytes := some 1 } ("ab".toUTF8)) &&
      (Compress.Internal.validateDecompressOptions .gzip { maxInputBytes := some 2 } ("ab".toUTF8)).isOk &&
      isInvFor .gzip (Compress.Internal.validateDecompressOptions .gzip { maxInputBytes := some 1 } ("ab".toUTF8)))
  let badUtf8 := ByteArray.mk #[0xff, 0xfe]
  checkB "decodeStderr empty+invalidUtf8+valid"
    (Compress.Internal.decodeStderr ByteArray.empty == none &&
      Compress.Internal.decodeStderr badUtf8 == none &&
      Compress.Internal.decodeStderr ("ok".toUTF8) == some "ok")
  let errZero := Compress.Internal.classifyProcessError .zstd
    { kind := .nonZeroExit, exitCode := some 0, stderr := some ("e".toUTF8), message := "" }
  let errEmptySerr := Compress.Internal.classifyProcessError .zstd
    { kind := .ioError, stderr := some ByteArray.empty, message := "io" }
  let errBadUtf8Serr := Compress.Internal.classifyProcessError .zstd
    { kind := .ioError, stderr := some badUtf8, message := "io" }
  checkB "classifyProcessError zero exitCode + fallback msg + stderr norm"
    (errZero.kind == .commandFailed && errZero.codec == some .zstd && errZero.exitCode == none &&
      errZero.stderr == some "e" && !errZero.message.isEmpty &&
      errEmptySerr.stderr == none && errBadUtf8Serr.stderr == none)
  let errNf := Compress.Internal.classifyProcessError .xz
    { kind := .notFound, exitCode := some 127, stderr := some ("leak".toUTF8), message := "nf" }
  let errInv := Compress.Internal.classifyProcessError .gzip
    { kind := .invalidInput, errnoCode := some 22, stderr := some ("leak".toUTF8), message := "inv" }
  let errOom := Compress.Internal.classifyProcessError .gzip
    { kind := .invalidInput, errnoCode := some 12, stderr := some ("oom".toUTF8), message := "oom" }
  checkB "classifyProcessError stderr scrub + oom"
    (errNf.kind == .toolNotFound && errNf.codec == some .xz && errNf.exitCode == none && errNf.stderr == none &&
      errInv.kind == .invalidInput && errInv.codec == some .gzip && errInv.exitCode == none && errInv.stderr == none &&
      errOom.kind == .ioError && errOom.codec == some .gzip && errOom.exitCode == none && errOom.stderr == some "oom")
  let okExact := Compress.Internal.classifyExitResult .gzip false 3 ByteArray.empty
    { exitCode := 0, stdout := "abc".toUTF8, stderr := ByteArray.empty }
  let badFraming := Compress.Internal.classifyExitResult .gzip true 16 ("bad".toUTF8)
    { exitCode := 0, stdout := "abc".toUTF8, stderr := ByteArray.empty }
  let overMaxBadFraming := Compress.Internal.classifyExitResult .gzip true 2 ("bad".toUTF8)
    { exitCode := 0, stdout := "abcd".toUTF8, stderr := "leaked".toUTF8 }
  let gzBig ← match ← Compress.compress .gzip (ByteArray.mk (Array.replicate 270000 0)) with
    | .ok b => pure b
    | .error e => throw (IO.userError s!"gzip 270k zero compress failed: {e.message}")
  let calStream := gzBig ++ ByteArray.mk #[0x1F, 0x9D, 0x90, 0x00]
  let overMaxCal := Compress.Internal.classifyExitResult .gzip true 2 calStream
    { exitCode := 0, stdout := "abcd".toUTF8, stderr := "warn".toUTF8 }
  let compFailEmptySerr := Compress.Internal.classifyExitResult .zstd false 16 ByteArray.empty
    { exitCode := 2, stdout := ByteArray.empty, stderr := ByteArray.empty }
  let decFailBadUtf8Serr := Compress.Internal.classifyExitResult .xz true 16 ByteArray.empty
    { exitCode := 1, stdout := ByteArray.empty, stderr := badUtf8 }
  checkB "classifyExitResult exact maxOut + exit0 framing + bounded cal + exitCode/stderr"
    (okExact == .ok ("abc".toUTF8) &&
      (match badFraming with | .error e => e.kind == .corruptData && e.codec == some .gzip && e.exitCode == none && e.stderr == none | _ => false) &&
      (match overMaxBadFraming with | .error e => e.kind == .corruptData && e.codec == some .gzip && e.exitCode == none && e.stderr == none | _ => false) &&
      (match overMaxCal with | .error e => e.kind == .outputLimitExceeded && e.codec == some .gzip && e.exitCode == none && e.stderr == some "warn" | _ => false) &&
      (match compFailEmptySerr with | .error e => e.kind == .commandFailed && e.codec == some .zstd && e.exitCode == some 2 && e.stderr == none | _ => false) &&
      (match decFailBadUtf8Serr with | .error e => e.kind == .corruptData && e.codec == some .xz && e.exitCode == some 1 && e.stderr == none | _ => false))
  let mkMockRaw (out : Process.ExecOutcome) : Process.RawProcessOpsM Id :=
    { mapRawError := fun _ => { kind := .ioError, message := "mock" }
      spawn := fun _ => .ok { handleId := 1, pid := 1, pgid := 1 }
      awaitOutput := fun _ _ _ _ => .ok out
      killProcessGroup := fun _ => .ok ()
      reap := fun _ => .ok ()
      activeProcessCount := 0 }
  let avail0 : Bool := Compress.Internal.isToolAvailable
    (mkMockRaw (.exited { exitCode := 0, stdout := ByteArray.empty, stderr := ByteArray.empty })) .zstd
  let avail1 : Bool := Compress.Internal.isToolAvailable
    (mkMockRaw (.exited { exitCode := 1, stdout := ByteArray.empty, stderr := ByteArray.empty })) .zstd
  let avail127 : Bool := Compress.Internal.isToolAvailable
    (mkMockRaw (.exited { exitCode := 127, stdout := ByteArray.empty, stderr := ByteArray.empty })) .xz
  let decOomCal : Except Compress.CompressError ByteArray :=
    Compress.Internal.decompressWith (mkMockRaw (.outputLimitExceeded ("abc".toUTF8) ByteArray.empty)) .gzip { maxOutputBytes := 2 } calStream
  let decToCal : Except Compress.CompressError ByteArray :=
    Compress.Internal.decompressWith (mkMockRaw (.timedOut ByteArray.empty ByteArray.empty)) .gzip { maxOutputBytes := 2 } calStream
  let decNzOver : Except Compress.CompressError ByteArray :=
    Compress.Internal.decompressWith (mkMockRaw (.exited { exitCode := 1, stdout := ByteArray.mk #[0x41, 0x42, 0x43], stderr := ByteArray.empty })) .gzip { maxOutputBytes := 2 } calStream
  let compNzOver : Except Compress.CompressError ByteArray :=
    Compress.Internal.compressWith (mkMockRaw (.exited { exitCode := 1, stdout := ByteArray.mk #[0x41, 0x42, 0x43], stderr := ByteArray.empty })) .gzip { maxOutputBytes := 2 } ("ab".toUTF8)
  checkB "isToolAvailable nonzero exit + decompressWith bounded cal"
    (avail0 == true && avail1 == false && avail127 == false &&
      (match decOomCal with | .error e => e.kind == .outputLimitExceeded && e.codec == some .gzip && e.exitCode == none && e.stderr == none | _ => false) &&
      (match decToCal with | .error e => e.kind == .timedOut && e.codec == some .gzip && e.exitCode == none && e.stderr == none | _ => false) &&
      (match decNzOver with | .error e => e.kind == .corruptData && e.exitCode == some 1 | _ => false) &&
      (match compNzOver with | .error e => e.kind == .commandFailed && e.exitCode == some 1 | _ => false))

private def runPostForkMutExtra : IO Unit := do
  let checkM (lbl : String) (ok : Bool) : IO Unit := do
    if !ok then
      throw (IO.userError s!"PostFork mut extra failed: {lbl}")
  let (rPipe, wPipe) ← match ← mutPfPipeCloexec with
    | .ok p => pure p
    | .error e => throw (IO.userError s!"PostFork mut pipe2 failed errno={e}")
  try
    let rBounds ← mutPfWriteOnce wPipe (ByteArray.mk #[1]) 1 1
    checkM "write_once off==total len>0 EINVAL" (rBounds == .error LinuxSyscall.Errno.EINVAL)
    let _ ← mutPfCloseFd wPipe
    let rEbadf ← mutPfWriteOnce wPipe (ByteArray.mk #[1]) 0 1
    checkM "write_once closed RawFd EBADF" (rEbadf == .error LinuxSyscall.Errno.EBADF)
  finally
    let _ ← mutPfCloseFd rPipe
    let _ ← mutPfCloseFd wPipe

  let fakeWrite : Int32 → ByteArray → UInt64 → UInt64 → StateM (Nat × Nat × Nat × List Int32) (Except LinuxSyscall.Errno UInt64) :=
    fun _ _ _ len => do
      let (wCnt, rCnt, tCnt, closed) ← get
      set (wCnt + 1, rCnt, tCnt, closed)
      match wCnt with
      | 0 => pure (.error LinuxSyscall.Errno.EINTR)
      | 1 => pure (.ok 1)
      | _ => pure (.ok (if len > 0 then len else 0))
  let fakeOps (syncEpipe : Bool) (repBytes : ByteArray) :
      PostFork.Model.Internal.PosixHostOpsM (StateM (Nat × Nat × Nat × List Int32)) Int32 :=
    { probeFdOpen := fun _ => pure (.ok ())
      probeHandleOpen := fun _ => pure (.ok ())
      mkPipeCloexec := do
        let (wCnt, rCnt, tCnt, closed) ← get
        let base : Int32 := if closed.isEmpty then 10 else 12
        set (wCnt, rCnt, tCnt, closed)
        pure (.ok (base, base + 1))
      closeFd := fun fd => do
        let (wCnt, rCnt, tCnt, closed) ← get
        set (wCnt, rCnt, tCnt, fd :: closed)
        pure (.ok ())
      setpgidOnce := fun _ _ => pure (.ok ())
      writeOnce := fun fd _ _ len => do
        if syncEpipe && fd == 11 then pure (.error LinuxSyscall.Errno.EPIPE)
        else fakeWrite fd ByteArray.empty 0 len
      readOnce := fun _ _ => do
        let (wCnt, rCnt, tCnt, closed) ← get
        set (wCnt, rCnt + 1, tCnt, closed)
        match rCnt with
        | 0 => pure (.error LinuxSyscall.Errno.EINTR)
        | 1 => pure (.ok (repBytes.extract 0 (min 2 repBytes.size)))
        | 2 => pure (.ok (repBytes.extract (min 2 repBytes.size) repBytes.size))
        | _ => pure (.ok ByteArray.empty)
      waitOnce := fun _ => do
        let (wCnt, rCnt, tCnt, closed) ← get
        set (wCnt, rCnt, tCnt + 1, closed)
        if tCnt == 0 then pure (.error LinuxSyscall.Errno.EINTR) else pure (.ok (.exited 0))
      forkRun := fun _ _ _ _ _ _ _ _ _ _ _ => pure (.ok 100) }
  let ops1 := PostFork.Impl.Internal.mkHostOps (fakeOps false (PostFork.Model.encodeFailureReport .chdir LinuxSyscall.Errno.ENOENT)) 4
  let (p1, st1) := (ops1.spawn (PostFork.ChildSpecM.ofCommand "/bin/true")).run (0, 0, 0, [])
  checkM "spawn eintr+partial wire"
    (match p1 with
     | .error e => e.kind == .childFailed && e.childFailure == some { stage := .chdir, errno := LinuxSyscall.Errno.ENOENT, waitStatus := some (.exited 0) }
     | .ok _ => false)
  checkM "spawn wait count" (st1.2.2.1 == 2)

  let opsBar := PostFork.Impl.Internal.mkHostOps (fakeOps true (PostFork.Model.encodeFailureReport .execve LinuxSyscall.Errno.ENOENT)) 4
  let (bPendRes, bSt) := (opsBar.spawnWithBarrier (PostFork.ChildSpecM.ofCommand "/bin/true")).run (0, 0, 0, [])
  match bPendRes with
  | .error _ => throw (IO.userError "PostFork mut extra: spawnWithBarrier failed")
  | .ok pend =>
    let (rRel, _) := (opsBar.releaseBarrier pend).run bSt
    checkM "releaseBarrier epipe reports execve"
      (match rRel with
       | .error e => e.kind == .childFailed && e.errno == some LinuxSyscall.Errno.ENOENT
       | .ok _ => false)

  let fakeZero : PostFork.Model.Internal.PosixHostOpsM (StateM (Nat × Nat × Nat × List Int32)) Int32 :=
    { (fakeOps false ByteArray.empty) with writeOnce := fun _ _ _ _ => do
        let (wCnt, rCnt, tCnt, closed) ← get
        set (wCnt + 1, rCnt, tCnt, closed)
        pure (.ok 0) }
  let opsZero := PostFork.Impl.Internal.mkHostOps fakeZero 4
  let (bZRes, bZSt) := (opsZero.spawnWithBarrier (PostFork.ChildSpecM.ofCommand "/bin/true")).run (0, 0, 0, [])
  match bZRes with
  | .error _ => throw (IO.userError "PostFork mut extra: zero spawnWithBarrier failed")
  | .ok pendZ =>
    let (rZ, bZSt2) := (opsZero.releaseBarrier pendZ).run bZSt
    checkM "writeOnce 0 returns error immediately"
      (bZSt2.1 == 1 && (match rZ with | .error e => e.message == "host write returned zero bytes" | .ok _ => false))

  let fakeWriteEintr : PostFork.Model.Internal.PosixHostOpsM (StateM Nat) Int32 :=
    { writeOnce := fun _ _ _ len => do
        let n ← get
        set (n + 1)
        if n == 0 then pure (.error LinuxSyscall.Errno.EINTR) else pure (.ok len)
      probeFdOpen := fun _ => pure (.ok ())
      probeHandleOpen := fun _ => pure (.ok ())
      mkPipeCloexec := pure (.ok (10, 11))
      closeFd := fun _ => pure (.ok ())
      setpgidOnce := fun _ _ => pure (.ok ())
      readOnce := fun _ _ => pure (.ok ByteArray.empty)
      waitOnce := fun _ => pure (.ok (.exited 0))
      forkRun := fun _ _ _ _ _ _ _ _ _ _ _ => pure (.ok 100) }
  let (wrEintr, wrEintrCnt) := (PostFork.Impl.Internal.writeAllRetryEintr fakeWriteEintr 11 (ByteArray.mk #[1, 2, 3]) 0 4).run 0
  checkM "writeAllRetryEintr retries EINTR" (wrEintr.isOk && wrEintrCnt == 2)
  let (wrExactFuel, wrExactCnt) :=
    (PostFork.Impl.Internal.writeAllRetryEintr fakeWriteEintr 11 (ByteArray.mk #[7]) 0 1).run 0
  checkM "writeAllRetryEintr exact fuel finalOff succeeds" (wrExactFuel == .ok () && wrExactCnt == 2)

  let fakeReadAcc : PostFork.Model.Internal.PosixHostOpsM (StateM Nat) Int32 :=
    { fakeWriteEintr with
      readOnce := fun _ _ => do
        let n ← get
        set (n + 1)
        if n == 0 then pure (.ok (ByteArray.mk #[44])) else pure (.ok ByteArray.empty) }
  let (rdAcc, _) := (PostFork.Impl.Internal.readAllRetryEintr fakeReadAcc 10 64 (ByteArray.mk #[42, 43]) 4).run 0
  checkM "readAllRetryEintr keeps non-empty acc" (rdAcc == .ok (ByteArray.mk #[42, 43, 44]))

  let fakeAbortBusy : PostFork.Model.Internal.PosixHostOpsM (StateM Nat) Int32 :=
    { fakeWriteEintr with
      closeFd := fun _ => do modify (· + 1); pure (.error LinuxSyscall.Errno.EBUSY) }
  let (abBusyRes, abBusyCnt) :=
    ((PostFork.Impl.Internal.mkHostOps fakeAbortBusy 4).abortBarrier
      { pid := 100, pgid := none, syncWrite := 13, errRead := 10 }).run 0
  checkM "abortBarrier EBUSY fails fast"
    (abBusyCnt == 1 &&
      (match abBusyRes with
       | .error e => e.kind == .sysError && e.errno == some LinuxSyscall.Errno.EBUSY
       | .ok _ => false))

  let fakeAbortCloseEintr : PostFork.Model.Internal.PosixHostOpsM (StateM Nat) Int32 :=
    { fakeWriteEintr with
      closeFd := fun fd => do
        modify (· + 1)
        if fd == 13 then pure (.error LinuxSyscall.Errno.EINTR) else pure (.ok ())
      waitOnce := fun _ => pure (.ok (.exited 125)) }
  let (abEintrRes, _) :=
    ((PostFork.Impl.Internal.mkHostOps fakeAbortCloseEintr 4).abortBarrier
      { pid := 100, pgid := none, syncWrite := 13, errRead := 10 }).run 0
  checkM "abortBarrier closeFd EINTR still drains and reaps"
    (abEintrRes == .ok (.aborted (.exited 125)))

  let (spFkRes, spFkSt) :=
    ((PostFork.Impl.Internal.mkHostOps PostFork.Model.Internal.mockPosixHostOps 4).spawn
      { path := "/bin/true", argv := #[] }).run { failForkErrno := some LinuxSyscall.Errno.EAGAIN }
  checkM "spawn failForkErrno closes errW and errR"
    (spFkRes.isOk == false && spFkSt.closedHandles == [10, 11])

  checkM "ChildSpecM default sigpipe is resetDefault"
    (({ path := "/bin/true", argv := #[] } : PostFork.ChildSpecM Int32).sigpipe == .resetDefault)
  checkM "StdioPlan.redirect default closeSourcesAbove2 is true"
    ((PostFork.StdioPlan.redirect (.raw 0) (.raw 1) (.raw 2) : PostFork.StdioPlan Int32) ==
      PostFork.StdioPlan.redirect (.raw 0) (.raw 1) (.raw 2) true)
  checkM "Model.ArgToken.ref? extracts refs"
    (PostFork.Model.ArgToken.ref? (.lit "a" : PostFork.ArgToken Int32) == none &&
      PostFork.Model.ArgToken.ref? (.fdDecimal (.raw 5) : PostFork.ArgToken Int32) == some (.raw 5) &&
      PostFork.Model.ArgToken.ref? (.prefixedFd "p" (.handle 7) "s" : PostFork.ArgToken Int32) == some (.handle 7))
  checkM "Model.i32Le signed ordering"
    (PostFork.Model.i32Le (-5) 3 == true &&
      PostFork.Model.i32Le 3 3 == true &&
      PostFork.Model.i32Le 3 (-5) == false &&
      PostFork.Model.i32Le Int32.minValue Int32.maxValue == true &&
      PostFork.Model.i32Le Int32.maxValue Int32.minValue == false)

  let mkRelProbe (wrErr : LinuxSyscall.Errno) (cl13Res : Except LinuxSyscall.Errno Unit) :
      PostFork.Model.Internal.PosixHostOpsM (StateM (Nat × List Int32)) Int32 :=
    { probeFdOpen := fun _ => pure (.ok ())
      probeHandleOpen := fun _ => pure (.ok ())
      mkPipeCloexec := pure (.ok (10, 11))
      closeFd := fun fd => do
        modify fun (n, cs) => (n + 1, fd :: cs)
        if fd == 13 then pure cl13Res else pure (.ok ())
      setpgidOnce := fun _ _ => pure (.ok ())
      writeOnce := fun _ _ _ _ => do
        modify fun (n, cs) => (n + 1, cs)
        pure (.error wrErr)
      readOnce := fun _ _ => pure (.ok ByteArray.empty)
      waitOnce := fun _ => do
        modify fun (n, cs) => (n + 1, cs)
        pure (.ok (.exited 125))
      forkRun := fun _ _ _ _ _ _ _ _ _ _ _ => pure (.ok 100) }
  let relPend : PostFork.PendingChildM Int32 := { pid := 100, pgid := none, syncWrite := 13, errRead := 10 }
  let (rWrEbadf, stWrEbadf) := ((PostFork.Impl.Internal.mkHostOps (mkRelProbe LinuxSyscall.Errno.EBADF (.ok ())) 4).releaseBarrier relPend).run (0, [])
  checkM "releaseBarrier write EBADF fails fast" (rWrEbadf.isOk == false && stWrEbadf == (1, []))
  let (rWrEbusy, stWrEbusy) := ((PostFork.Impl.Internal.mkHostOps (mkRelProbe LinuxSyscall.Errno.EBUSY (.ok ())) 4).releaseBarrier relPend).run (0, [])
  checkM "releaseBarrier write EBUSY fails fast" (rWrEbusy.isOk == false && stWrEbusy == (1, []))
  let (rClEbadf, stClEbadf) := ((PostFork.Impl.Internal.mkHostOps (mkRelProbe LinuxSyscall.Errno.EIO (.error LinuxSyscall.Errno.EBADF)) 4).releaseBarrier relPend).run (0, [])
  checkM "releaseBarrier close EBADF fails fast" (rClEbadf.isOk == false && stClEbadf == (2, [13]))
  let (rClEbusy, stClEbusy) := ((PostFork.Impl.Internal.mkHostOps (mkRelProbe LinuxSyscall.Errno.EIO (.error LinuxSyscall.Errno.EBUSY)) 4).releaseBarrier relPend).run (0, [])
  checkM "releaseBarrier close EBUSY fails fast" (rClEbusy.isOk == false && stClEbusy == (2, [13]))
  let (rClEintr, stClEintr) := ((PostFork.Impl.Internal.mkHostOps (mkRelProbe LinuxSyscall.Errno.EIO (.error LinuxSyscall.Errno.EINTR)) 4).releaseBarrier relPend).run (0, [])
  checkM "releaseBarrier close EINTR still closes errRead and reaps" (rClEintr.isOk == false && stClEintr == (4, [10, 13]))
  let (rClOk, stClOk) := ((PostFork.Impl.Internal.mkHostOps (mkRelProbe LinuxSyscall.Errno.EIO (.ok ())) 4).releaseBarrier relPend).run (0, [])
  checkM "releaseBarrier write EIO closes both and reaps" (rClOk.isOk == false && stClOk == (4, [10, 13]))
  let (rWrEpipe0, stWrEpipe0) :=
    ((PostFork.Impl.Internal.mkHostOps (mkRelProbe LinuxSyscall.Errno.EPIPE (.ok ())) 4).releaseBarrier relPend).run (0, [])
  checkM "releaseBarrier write EPIPE empty errRead reaps and returns wireTruncated"
    (stWrEpipe0 == (4, [10, 13]) &&
      (match rWrEpipe0 with
       | .error e =>
         e.kind == .childFailed &&
           e.childFailure == some { stage := .wireTruncated, errno := LinuxSyscall.Errno.EIO, waitStatus := some (.exited 125) }
       | .ok _ => false))

  checkM "host setpgid(0, 1) EINVAL" ((← mutPfSetpgid 0 1) == .error LinuxSyscall.Errno.EINVAL)
  checkM "host setpgid(1, 0) EINVAL" ((← mutPfSetpgid 1 0) == .error LinuxSyscall.Errno.EINVAL)
  checkM "host waitOnce(0) EINVAL" ((← mutPfWaitOnce 0) == .error LinuxSyscall.Errno.EINVAL)
  checkM "host forkRun bad meta_ba EINVAL"
    ((← mutPfForkRun 0 0 #[] ByteArray.empty ByteArray.empty ByteArray.empty #[] #[] ByteArray.empty none "/bin/true" #[]) ==
      .error LinuxSyscall.Errno.EINVAL)

  let finR ← mutPfAllocPipeDropWrite
  try
    checkM "host pipe finalizer closes dropped write end" ((← mutPfReadOnce finR 1) == .ok ByteArray.empty)
  finally
    let _ ← mutPfCloseFd finR

  let immSpec : PostFork.ChildSpec :=
    { path := "/bin/true", argv := #[.lit "/bin/true"], forkMode := .immortalThread }
  match ← PostFork.spawn immSpec with
  | .error e => throw (IO.userError s!"PostFork mut immortal warmup failed: {repr e}")
  | .ok c0 =>
    let _ ← mutPfWaitOnce c0.pid
  let thrBase ← mutPfReadProcThreads
  for _ in List.range 4 do
    match ← PostFork.spawn immSpec with
    | .error e => throw (IO.userError s!"PostFork mut immortal loop failed: {repr e}")
    | .ok ci => let _ ← mutPfWaitOnce ci.pid
  let thrAfter ← mutPfReadProcThreads
  checkM s!"immortal spawner reuses single thread (base={thrBase} after={thrAfter})"
    (thrAfter ≤ thrBase + 1)

  match ← mutPfPipeCloexec with
  | .error e => throw (IO.userError s!"PostFork mut extra: host mkPipeCloexec failed: {repr e}")
  | .ok (pr, pw) =>
    try
      checkM "host writeOnce off=0 len=0" ((← mutPfWriteOnce pw (ByteArray.mk #[10, 20]) 0 0) == .ok 0)
      checkM "host writeOnce off=size len=0" ((← mutPfWriteOnce pw (ByteArray.mk #[10, 20]) 2 0) == .ok 0)
      checkM "host writeOnce oob off EINVAL" ((← mutPfWriteOnce pw (ByteArray.mk #[10, 20]) 5 1) == .error LinuxSyscall.Errno.EINVAL)
      checkM "host writeOnce oob len EINVAL" ((← mutPfWriteOnce pw (ByteArray.mk #[10, 20]) 1 5) == .error LinuxSyscall.Errno.EINVAL)
      checkM "host readOnce cap=0" ((← mutPfReadOnce pr 0) == .ok ByteArray.empty)
      checkM "host writeOnce 1B" ((← mutPfWriteOnce pw (ByteArray.mk #[99]) 0 1) == .ok 1)
      checkM "host readOnce 1B" ((← mutPfReadOnce pr 1) == .ok (ByteArray.mk #[99]))
      checkM "host probeFdOpen(-1) errors" (match ← mutPfProbeFd (-1) with | .error _ => true | .ok () => false)
    finally
      let _ ← mutPfCloseFd pr
      let _ ← mutPfCloseFd pw

  checkM "decodeChildFailure valid"
    (PostFork.Model.decodeChildFailure (ByteArray.mk #[0x50, 0x01, 6, 0, 2, 0, 0, 0]) ==
      some { stage := .chdir, errno := LinuxSyscall.Errno.ENOENT })
  checkM "decodeChildFailure bad magic"
    (PostFork.Model.decodeChildFailure (ByteArray.mk #[0x51, 0x01, 6, 0, 2, 0, 0, 0]) ==
      some { stage := .wireTruncated, errno := LinuxSyscall.Errno.EIO })
  checkM "decodeChildFailure bad version"
    (PostFork.Model.decodeChildFailure (ByteArray.mk #[0x50, 0x02, 6, 0, 2, 0, 0, 0]) ==
      some { stage := .wireTruncated, errno := LinuxSyscall.Errno.EIO })
  checkM "decodeChildFailure bad pad3"
    (PostFork.Model.decodeChildFailure (ByteArray.mk #[0x50, 0x01, 6, 1, 22, 0, 0, 0]) ==
      some { stage := .wireTruncated, errno := LinuxSyscall.Errno.EIO })
  checkM "decodeChildFailure bad tag"
    (PostFork.Model.decodeChildFailure (ByteArray.mk #[0x50, 0x01, 9, 0, 22, 0, 0, 0]) ==
      some { stage := .wireTruncated, errno := LinuxSyscall.Errno.EIO })
  checkM "decodeChildFailure short len"
    (PostFork.Model.decodeChildFailure (ByteArray.mk #[0x50, 0x01, 7, 0, 22, 0, 0]) ==
      some { stage := .wireTruncated, errno := LinuxSyscall.Errno.EIO })

  let wrSlice := PostFork.Aeneas.Model.mkSliceU8 1#usize [97#u8] rfl
  let brokenBase : PostFork.World.ChildState :=
    { status := .running
      fds := [(1, { desc := 11, cloexec := false })]
      descs := [(11, .stream false true true [])] }
  let resPid1 := _root_.sys.write { brokenBase with pid := 1, blockedSigs := [] } 1#i32 wrSlice
  checkM "sys.write pid=1 broken pipe survives"
    (match Aeneas.Std.Result.match resPid1 with
     | .ok (.Err _, st) => st.status == .running
     | _ => false)
  let resBlk := _root_.sys.write { brokenBase with pid := 42, blockedSigs := [13] } 1#i32 wrSlice
  checkM "sys.write blocked SIGPIPE survives"
    (match Aeneas.Std.Result.match resBlk with
     | .ok (.Err _, st) => st.status == .running
     | _ => false)
  let resDfl := _root_.sys.write { brokenBase with pid := 42, blockedSigs := [] } 1#i32 wrSlice
  checkM "sys.write unblocked pid!=1 SIGPIPE kills"
    (match Aeneas.Std.Result.match resDfl with
     | .ok (.Err _, st) => st.status == .signaled 13#i32
     | _ => false)

  let zeroBuf : Aeneas.Std.Array Aeneas.Std.U8 256#usize := Aeneas.Std.Array.repeat 256#usize 0#u8
  let dirState : PostFork.World.ChildState :=
    { status := .running
      fds := [(4, { desc := 30, cloexec := true })]
      descs := [(30, .directory 0)] }
  let (dRes1, dSt1, _) ← match Aeneas.Std.Result.match (_root_.sys.getdents64 dirState 4#i32 zeroBuf) with
    | .ok p => pure p
    | _ => throw (IO.userError "sys.getdents64 .directory batch1 failed")
  checkM "sys.getdents64 .directory batch1 > 0"
    (match dRes1 with | .Ok n => n.val > 0 | _ => false)
  let (dRes2, _, _) ← match Aeneas.Std.Result.match (_root_.sys.getdents64 dSt1 4#i32 zeroBuf) with
    | .ok p => pure p
    | _ => throw (IO.userError "sys.getdents64 .directory EOF failed")
  checkM "sys.getdents64 .directory EOF = 0"
    (match dRes2 with | .Ok n => n.val == 0 | _ => false)

  let sparseProcState : PostFork.World.ChildState :=
    { status := .running
      fds := [(3, { desc := 40, cloexec := true }), (10, { desc := 41, cloexec := false }), (200, { desc := 42, cloexec := false })]
      descs := [(40, .procSelfFd (-2)), (41, .stream true true false []), (42, .stream true true false [])]
      oracle := [.dentsBatch 0, .dentsBatch 0] }
  let (pRes1, pSt1, pBuf1) ← match Aeneas.Std.Result.match (_root_.sys.getdents64 sparseProcState 3#i32 zeroBuf) with
    | .ok p => pure p
    | _ => throw (IO.userError "sys.getdents64 sparse batch1 failed")
  let hasNonZeroDoff := (List.range 8).any fun i => (pBuf1.val[8 + i]!).val != 0
  checkM "sys.getdents64 procSelfFd batch1 non-zero d_off"
    ((match pRes1 with | .Ok n => n.val >= 20 | _ => false) && hasNonZeroDoff)
  let (pRes2, pSt2, _) ← match Aeneas.Std.Result.match (_root_.sys.getdents64 pSt1 3#i32 zeroBuf) with
    | .ok p => pure p
    | _ => throw (IO.userError "sys.getdents64 sparse batch2 failed")
  checkM "sys.getdents64 procSelfFd batch2 > 0"
    (match pRes2 with | .Ok n => n.val > 0 | _ => false)
  checkM "sys.getdents64 procSelfFd cursor advanced"
    (pSt2.getDesc 40 != sparseProcState.getDesc 40)

  checkM "Impl.pushI32Le all 4 byte lanes"
    (PostFork.Impl.Internal.pushI32Le ByteArray.empty 0x01020304 == ByteArray.mk #[0x04, 0x03, 0x02, 0x01] &&
      PostFork.Impl.Internal.pushI32Le ByteArray.empty (-0x01020304) == ByteArray.mk #[0xFC, 0xFC, 0xFD, 0xFE])
  checkM "Model.packI32Le all 4 byte lanes"
    (PostFork.Model.packI32Le 0x01020304 == ByteArray.mk #[0x04, 0x03, 0x02, 0x01] &&
      PostFork.Model.packI32Le (-0x01020304) == ByteArray.mk #[0xFC, 0xFC, 0xFD, 0xFE])
  checkM "Model.FailureStage.toTag? wireTruncated is none"
    (PostFork.Model.FailureStage.toTag? .wireTruncated == none &&
      PostFork.Model.encodeFailureReport .wireTruncated 0 == ByteArray.mk #[0x50, 0x01, 7, 0, 5, 0, 0, 0])
  checkM "Model.normalizeWireErrno out-of-range normalizes to EIO"
    (PostFork.Model.normalizeWireErrno 0 == LinuxSyscall.Errno.EIO &&
      PostFork.Model.normalizeWireErrno 4096 == LinuxSyscall.Errno.EIO)
  checkM "Types default parameter values"
    ((PostFork.ArgToken.prefixedFd "--fd=" (.raw 5) : PostFork.ArgToken Int32) ==
        PostFork.ArgToken.prefixedFd "--fd=" (.raw 5) "" &&
      (PostFork.FdPolicy.inheritNonCloexec : PostFork.FdPolicy Int32) ==
        PostFork.FdPolicy.inheritNonCloexec #[] &&
      (PostFork.FdPolicy.closeAllAbove2Except : PostFork.FdPolicy Int32) ==
        PostFork.FdPolicy.closeAllAbove2Except #[] &&
      (PostFork.ChildSpecM.ofCommand "/bin/true" : PostFork.ChildSpecM Int32) ==
        { path := "/bin/true", argv := #[.lit "/bin/true"] })

  let alwaysEintrOps : PostFork.Model.Internal.PosixHostOpsM (StateM Nat) Int32 :=
    { probeFdOpen := fun _ => pure (.ok ())
      probeHandleOpen := fun _ => pure (.ok ())
      mkPipeCloexec := pure (.ok (10, 11))
      closeFd := fun _ => pure (.ok ())
      setpgidOnce := fun _ _ => pure (.ok ())
      writeOnce := fun _ _ _ _ => do modify (· + 1); pure (.error LinuxSyscall.Errno.EINTR)
      readOnce := fun _ _ => do modify (· + 1); pure (.error LinuxSyscall.Errno.EINTR)
      waitOnce := fun _ => do modify (· + 1); pure (.error LinuxSyscall.Errno.EINTR)
      forkRun := fun _ _ _ _ _ _ _ _ _ _ _ => pure (.ok 100) }
  let (wrFuelRes, wrFuelCnt) :=
    (PostFork.Impl.Internal.writeAllRetryEintr alwaysEintrOps 11 (ByteArray.mk #[1]) 0 1).run 0
  checkM "writeAllRetryEintr fuel exhaustion errors"
    (wrFuelCnt == 2 && (match wrFuelRes with | .error e => e.errno == some LinuxSyscall.Errno.EIO | .ok () => false))
  let (rdFuelRes, rdFuelCnt) :=
    (PostFork.Impl.Internal.readAllRetryEintr alwaysEintrOps 10 16 ByteArray.empty 1).run 0
  checkM "readAllRetryEintr fuel exhaustion errors"
    (rdFuelCnt == 2 && (match rdFuelRes with | .error e => e.errno == some LinuxSyscall.Errno.EIO | .ok _ => false))
  let (wtFuelRes, wtFuelCnt) :=
    (PostFork.Impl.Internal.waitRetryEintr alwaysEintrOps 100 1).run 0
  checkM "waitRetryEintr fuel exhaustion errors"
    (wtFuelCnt == 2 && (match wtFuelRes with | .error e => e.errno == some LinuxSyscall.Errno.EINTR | .ok _ => false))

  let (spRdErr, spRdSt) :=
    ((PostFork.Impl.Internal.mkHostOps PostFork.Model.Internal.mockPosixHostOps 4).spawn
      { path := "/bin/cat", argv := #[] }).run { failReadErrno := some LinuxSyscall.Errno.ENOMEM }
  checkM "awaitExecOrFailure read error does not call blocking waitOnce"
    (!spRdErr.isOk && spRdSt.closedHandles == [10, 11] && spRdSt.callCount == 5)
  let (relClErr, relClSt) :=
    ((PostFork.Impl.Internal.mkHostOps PostFork.Model.Internal.mockPosixHostOps 4).releaseBarrier relPend).run
      { allocSyncWriteFd := 13, closedHandles := [10] }
  checkM "releaseBarrier closed errRead fails fast before syncWrite"
    (!relClErr.isOk && relClSt.syncWritten == ByteArray.empty && relClSt.callCount == 1)
  let (rWrEoverflow, stWrEoverflow) :=
    ((PostFork.Impl.Internal.mkHostOps (mkRelProbe 75 (.ok ())) 4).releaseBarrier relPend).run (0, [])
  checkM "releaseBarrier write EOVERFLOW fails fast without closing"
    (!rWrEoverflow.isOk && stWrEoverflow == (1, []))
  let (rClEperm, stClEperm) :=
    ((PostFork.Impl.Internal.mkHostOps (mkRelProbe LinuxSyscall.Errno.EIO (.error LinuxSyscall.Errno.EPERM)) 4).releaseBarrier relPend).run (0, [])
  checkM "releaseBarrier close EPERM fails fast without reaping"
    (!rClEperm.isOk && stClEperm == (2, [13]))
  let fakeAbortEperm : PostFork.Model.Internal.PosixHostOpsM (StateM Nat) Int32 :=
    { fakeWriteEintr with
      closeFd := fun _ => do modify (· + 1); pure (.error LinuxSyscall.Errno.EPERM) }
  let (abEpermRes, abEpermCnt) :=
    ((PostFork.Impl.Internal.mkHostOps fakeAbortEperm 4).abortBarrier
      { pid := 100, pgid := none, syncWrite := 13, errRead := 10 }).run 0
  checkM "abortBarrier EPERM fails fast"
    (abEpermCnt == 1 &&
      (match abEpermRes with
       | .error e => e.kind == .sysError && e.errno == some LinuxSyscall.Errno.EPERM
       | .ok _ => false))

  let selfBin := (← IO.appPath).toString
  match ← PostFork.spawn {
    path := "/bin/sh"
    argv := #[.lit "/bin/sh", .lit "-c", .lit "ulimit -n 24 && exec \"$1\" --postfork-probe", .lit "sh", .lit selfBin]
  } with
  | .error e => throw (IO.userError s!"PostFork mut subproc probe spawn failed: {repr e}")
  | .ok prChild =>
    let prWst ← mutPfWaitOnce prChild.pid
    checkM s!"PostFork subproc EMFILE + SIGPIPE probe exited 0 (got {repr prWst})"
      (prWst == .ok (.exited 0))

private def runPostForkSubprocProbe : IO UInt32 := do
  let prevDisp ← mutPfCStdSignal 13 0
  if prevDisp == USize.ofNat 18446744073709551615 then
    IO.eprintln "signal(SIGPIPE, SIG_DFL) failed"
    return 1
  match ← mutPfPipeCloexec with
  | .error _ =>
    return 1
  | .ok (sr, sw) =>
    let _ ← mutPfCloseFd sr
    let wrRes ← mutPfWriteOnce sw (ByteArray.mk #[1]) 0 1
    let _ ← mutPfCloseFd sw
    if wrRes != .error LinuxSyscall.Errno.EPIPE then
      return 1
  let mut openBefore : Array Int32 := #[]
  let mut closedHighBefore : Array Int32 := #[]
  for i in List.range 24 do
    let fd32 : Int32 := Int32.ofNat i
    match ← mutPfProbeFd fd32 with
    | .ok () => openBefore := openBefore.push fd32
    | .error _ =>
      if i ≥ 3 then
        closedHighBefore := closedHighBefore.push fd32
  if closedHighBefore.size < 2 then
    return 2
  match ← mutPfPipeCloexec with
  | .error _ => return 3
  | .ok (trR, trW) =>
    let trFd0 := closedHighBefore[0]!
    let trFd1 := closedHighBefore[1]!
    let pOpenOk ←
      if h : openBefore.size > 0 then
        pure ((← mutPfProbeFd openBefore[0]) == .ok ())
      else
        pure true
    let pTr0 ← mutPfProbeFd trFd0
    let pTr1 ← mutPfProbeFd trFd1
    let pushI32 := PostFork.Impl.Internal.pushI32Le
    let metaBa := pushI32 (pushI32 (pushI32 (pushI32 (pushI32 ByteArray.empty (-1)) (-2)) trFd0) trFd0) trFd0
    let argSlots := pushI32 ByteArray.empty (-1)
    let fkRawTr ← mutPfForkRun 8 0 #[trW] metaBa ByteArray.empty ByteArray.empty
      #["/bin/true"] #[""] argSlots none "/bin/true" #[]
    let _ ← mutPfCloseFd trR
    let dupRc ← mutPfCStdDup2 trFd1 trFd0
    let pAfterUntrack ← mutPfProbeFd trFd0
    if dupRc ≥ 0 then
      let _ ← mutPfCStdClose trFd0.toUInt32
    let _ ← mutPfCloseFd trW
    if !pOpenOk || pTr0 != .error LinuxSyscall.Errno.EBADF || pTr1 != .error LinuxSyscall.Errno.EBADF ||
        fkRawTr != .error LinuxSyscall.Errno.EBADF || dupRc != trFd0 || pAfterUntrack != .ok () then
      return 4
  let mut allocated : Array (LinuxSyscall.RawFd × LinuxSyscall.RawFd) := #[]
  let mut sawEmfile := false
  try
    for _ in List.range 32 do
      if !sawEmfile then
        match ← mutPfPipeCloexec with
        | .ok p => allocated := allocated.push p
        | .error e =>
          if e == LinuxSyscall.Errno.EMFILE then
            sawEmfile := true
          else
            throw (IO.userError s!"unexpected pipe2 errno={e}")
  finally
    for (r, w) in allocated do
      let _ ← mutPfCloseFd r
      let _ ← mutPfCloseFd w
  if !sawEmfile then
    return 5
  let _ ← mutPfCStdClose 0
  let _ ← mutPfCStdClose 1
  let _ ← mutPfCStdClose 2
  if (← LinuxSyscall.Sandbox.setrlimit .nofile 3 24) != .ok () then
    return 6
  match ← mutPfPipeCloexec with
  | .error e =>
    if e != LinuxSyscall.Errno.EMFILE then
      return 7
  | .ok (r, w) =>
    let _ ← mutPfCloseFd r
    let _ ← mutPfCloseFd w
    return 7
  if (← mutPfProbeFd 0) != .error LinuxSyscall.Errno.EBADF then
    return 8
  return 0

private structure GitMutProbeState where
  reqs : Array Git.GitRawRequest := #[]
  envs : Array (Array (String × Option String)) := #[]

private def runGitMutateExtra : IO Unit := do
  let checkB (label : String) (cond : Bool) : IO Unit := do
    if !cond then throw (IO.userError s!"GIT_MUTATE_EXTRA_FAIL: {label}")
  let mkReq (cwd : Option String) (args : Array String) (stdin : ByteArray := ByteArray.empty) : Git.GitRawRequest :=
    { cwd := cwd, args := args, stdin := stdin }
  let shaA := String.ofList (List.replicate 40 'a')
  let shaB := String.ofList (List.replicate 40 'b')
  let mockOps : Git.RawGitOpsM (StateM GitMutProbeState) :=
    { listEnv := pure (.ok #[("GIT_DIR", "/poison/.git"), ("LANG", "de_DE.UTF-8"), ("PATH", "/usr/bin")])
      execGit := fun env req => do
        modify fun s => { reqs := s.reqs.push req, envs := s.envs.push env }
        if req.args == #["merge-base", shaA, shaB] then
          return .ok { exitCode := 0, stdout := (shaA ++ "\n").toUTF8, stderr := ByteArray.empty }
        else if req.args.toList.contains "--verify" then
          return .ok { exitCode := 0, stdout := (shaA ++ "\n").toUTF8, stderr := ByteArray.empty }
        else
          return .ok { exitCode := 0, stdout := ByteArray.empty, stderr := ByteArray.empty } }
  let api := Git.Impl.mkApiM mockOps
  let (cRes, stCommit) := (api.commit "/repo" { message := "# hdr\nbody  \n", allowEmpty := true }).run {}
  checkB "commit ok + sanitized inherited env + exact flags"
    (cRes == .ok { hex := shaA } &&
      stCommit.envs.all (fun e =>
        e.toList.contains ("GIT_DIR", none) &&
        e.toList.contains ("LANG", none) &&
        e.toList.contains ("LC_ALL", some "C") &&
        e.toList.contains ("GIT_LITERAL_PATHSPECS", some "1") &&
        e.toList.contains ("GIT_TERMINAL_PROMPT", some "0") &&
        !e.toList.any (fun (k, v) =>
          k == "GIT_CONFIG_GLOBAL" || k == "GIT_CONFIG_NOSYSTEM" ||
          v == some "protocol.allow" || v == some "user.name" ||
          v == some "user.email" || v == some "core.hooksPath")) &&
      stCommit.reqs[0]? == some
        (mkReq (some "/repo") #["commit", "--no-gpg-sign", "-m", "# hdr\nbody  \n", "--allow-empty"]))
  let (clRes, stClone) :=
    (api.clone "/src" "/dst" { bare := true, singleBranch := true, depth? := some 1, branch? := some "feat" }).run {}
  checkB "clone exact flags"
    (clRes == .ok () &&
      stClone.reqs.back? == some
        (mkReq none #["clone", "--bare", "--single-branch", "--depth", "1", "--branch", "feat", "--", "/src", "/dst"]))
  let (coB, stCoB) := (api.checkout "/repo" (.branch { raw := "feat" }) false).run {}
  let (coR, stCoR) := (api.checkout "/repo" (.ref "feat") false).run {}
  let (swE, stSwE) := (api.switch "/repo" { raw := "feat" } false none false).run {}
  checkB "checkout + switch default flags (no --no-guess)"
    (coB == .ok () && stCoB.reqs.back? == some (mkReq (some "/repo") #["checkout", "feat", "--"]) &&
      coR == .ok () && stCoR.reqs.back? == some (mkReq (some "/repo") #["checkout", "feat", "--"]) &&
      swE == .ok () && stSwE.reqs.back? == some (mkReq (some "/repo") #["switch", "feat"]))
  let (waDef, stWaDef) := (api.worktreeAdd "/repo" { path := "/wt_def" }).run {}
  checkB "worktreeAdd default basename mode"
    (waDef == .ok () && stWaDef.reqs.back? == some (mkReq (some "/repo") #["worktree", "add", "--", "/wt_def"]))
  let (stRes, stStat) := (api.status "/repo").run {}
  let (dfRes, stDiff) := (api.diffNameStatus "/repo" "HEAD" (some "feat") #["p.txt"]).run {}
  checkB "status + diffNameStatus default rename detection and untracked-files=normal"
    (stRes == .ok #[] &&
      stStat.reqs.back? == some
        (mkReq (some "/repo") #["status", "--porcelain=v1", "--untracked-files=normal", "-z"]) &&
      dfRes == .ok #[] &&
      stDiff.reqs.back? == some
        (mkReq (some "/repo") #["diff", "--name-status", "-z", "HEAD", "feat", "--", "p.txt"]))
  let (wtRes, stWt) :=
    (api.withWorktree "/repo" { path := "/wt", detach := true, force := true } (fun p => pure (.ok p))).run {}
  checkB "withWorktree forwards opts.force to worktreeRemove"
    (wtRes == .ok "/wt" &&
      stWt.reqs.back? == some (mkReq (some "/repo") #["worktree", "remove", "--force", "--", "/wt"]))
  let (mbRes, _) := (api.mergeBase? "/repo" { hex := shaA } { hex := shaB }).run {}
  checkB "mergeBase direct git merge-base delegation" (mbRes == .ok (some { hex := shaA }))
  let peTimeout := Git.mapProcessError "fetch" { kind := .timedOut, exitCode := some 124, stderr := some ("t".toUTF8), message := "" }
  let peInv := Git.mapProcessError "fetch" { kind := .invalidInput, message := "bad" }
  let evErr := Git.mapEnvVarsError { kind := .ioError, message := "" }
  checkB "Interface error mapping"
    (peTimeout.kind == .timeout && peTimeout.command == some "fetch" && peTimeout.exitCode == some 124 &&
      peTimeout.stderr == some "t" && !peTimeout.message.isEmpty &&
      peInv.kind == .invalidInput && evErr.kind == .commandFailed && !evErr.message.isEmpty)

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

private def cproxyRecvUntilHeadEnd (fd : LinuxSyscall.RawFd) (timeoutMs : Nat) : IO ByteArray := do
  let mut acc := ByteArray.empty
  let mut steps : Nat := 0
  while steps < 256 do
    steps := steps + 1
    if !(← cproxyWaitPollin fd timeoutMs) then
      throw (IO.userError "cproxyRecvUntilHeadEnd timed out")
    match ← LinuxSyscall.Net.recvfrom fd 1024 {} with
    | .ok chunk =>
      if chunk.size == 0 then
        return acc
      acc := acc ++ chunk
      if (ConnectProxy.SysBridge.findCrlfCrlf acc 0).isSome then
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
    let denyBytes ← cproxyRecvUntilHeadEnd cfdDeny 800
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
    let gotOver ← cproxyRecvUntilHeadEnd cOver 800
    let _ ← LinuxSyscall.Files.close cOver
    if ((String.fromUTF8! gotOver).splitOn "403").length <= 1 then
      return .error { kind := .ioError, message := "oversized header did not return 403" }
    let cSlow ← cproxyDialLoopback proxy.port
    cproxySendAll cSlow s!"CONNECT 127.0.0.1:{echoPort} HTTP/1.1\r\n".toUTF8
    let gotSlow ← cproxyRecvUntilHeadEnd cSlow 800
    let _ ← LinuxSyscall.Files.close cSlow
    if ((String.fromUTF8! gotSlow).splitOn "403").length <= 1 then
      return .error { kind := .ioError, message := "slow header timeout did not return 403" }
    let cDead ← cproxyDialLoopback proxy.port
    cproxySendAll cDead s!"CONNECT 127.0.0.1:{deadPort} HTTP/1.1\r\n\r\n".toUTF8
    let gotDead ← cproxyRecvUntilHeadEnd cDead 800
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
    let gotBan ← cproxyRecvUntilHeadEnd cBan 800
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
  ("Process", do Process.RuntimeTests.runAll; return none, pure ()),
  ("Time", do Time.RuntimeTests.runAll; return none, pure ()),
  ("Json", do Json.RuntimeTests.runAll; return none, pure ()),
  ("EnvVars.Raw", do EnvVars.Raw.RuntimeTests.runAll; return none, do runPropChecksEnvVarsRaw; runRawDecoderUnitTests),
  ("EnvVars", do EnvVars.RuntimeTests.runAll; return none, runPropChecksEnvVars),
  ("Uuid", do Uuid.RuntimeTests.runAll; return none, pure ()),
  ("Sqlite.Raw", do Sqlite.Raw.RuntimeTests.runAll; return none, runSqliteRawUnitTests),
  ("Sqlite", do Sqlite.RuntimeTests.runAll; return none, runSqliteUnitTests),
  ("Git", do Git.RuntimeTests.runAll; return none, do Git.RuntimeTests.runMutateExtra; runGitMutateExtra),
  ("CmdLine", do CmdLine.RuntimeTests.runAll; return none, runCmdLineMutateExtra),
  ("NumParse", do NumParse.RuntimeTests.runAll; return none, pure ()),
  ("Toml", do Toml.RuntimeTests.runAll; return none, pure ()),
  ("TempDir", do TempDir.RuntimeTests.runAll; return none, pure ()),
  ("Compress", do Compress.RuntimeTests.runAll; return none, runCompressMutateExtra),
  ("Base64", do Base64.RuntimeTests.runAll; return none, pure ()),
  ("CryptoHash.Raw", do CryptoHash.Raw.RuntimeTests.runAll; return none, pure ()),
  ("CryptoHash", do CryptoHash.RuntimeTests.runAll; return none, pure ()),
  ("Tar", do Tar.RuntimeTests.runAll; return none, pure ()),
  ("ProcessSandbox.Seccomp", do ProcessSandbox.Seccomp.RuntimeTests.runAll; return none, pure ()),
  ("ProcessSandbox.Raw", ProcessSandbox.Raw.RuntimeTests.runAllOutcome, pure ()),
  ("ProcessSandbox", ProcessSandbox.RuntimeTests.runAllOutcome, pure ()),
  ("ConnectProxy", do ConnectProxy.RuntimeTests.runAll; return none, do runConnectProxyUnitTests; runConnectProxyMutateExtra),
  ("SlotPool", do SlotPool.RuntimeTests.runAll; return none, pure ()),
  ("LinuxSyscall.Sandbox", do Fuzz.LinuxSyscall.Sandbox.Strace.runChecks; return none, Fuzz.LinuxSyscall.Sandbox.Strace.runStraceFaultCheck),
  ("LinuxSyscall.TimeRand", do Fuzz.LinuxSyscall.TimeRand.Strace.runChecks; return none, Fuzz.LinuxSyscall.TimeRand.Strace.runStraceFaultCheck),
  ("LinuxSyscall.Passwd", do Fuzz.Passwd.suite.runSmoke { smoke := true }; return none, pure ()),
  ("LinuxSyscall.Dns", do Fuzz.Dns.suite.runSmoke { smoke := true }; return none, runDnsUnitTests),
  ("LinuxSyscall.Poll", do Fuzz.LinuxSyscall.Poll.Strace.runChecks; return none, do Fuzz.LinuxSyscall.Poll.Strace.runStraceFaultCheck; runPollOpsUnitTests),
  ("LinuxSyscall.Net", do Fuzz.LinuxSyscall.Net.Strace.runChecks; return none, do Fuzz.LinuxSyscall.Net.Strace.runStraceFaultCheck; runNetOpsUnitTests),
  ("LinuxSyscall.Process", do Fuzz.LinuxSyscall.Process.Strace.runChecks; return none, runProcessMutExtra),
  ("LinuxSyscall.Files", do Fuzz.LinuxSyscall.Files.Strace.runChecks; return none, runFilesMkOpsUnitTests),
  ("PostFork", do PostFork.RuntimeTests.runAll; return none, runPostForkMutExtra)
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
  | "--process-probe" :: rest =>
    return (← Process.RuntimeTests.probeMain rest)
  | "--uuid-probe" :: rest =>
    return (← Uuid.RuntimeTests.probeMain rest)
  | "--time-probe" :: rest =>
    return (← Time.RuntimeTests.probeMain rest)
  | "--passwd-probe" :: rest =>
    return (← Fuzz.Passwd.Checks.probeMain rest)
  | "--sandbox-strace-worker" :: mode :: [] =>
    Fuzz.LinuxSyscall.Sandbox.Strace.runStraceWorker mode
    return 0
  | "--sandbox-strace-fault-check" :: [] =>
    Fuzz.LinuxSyscall.Sandbox.Strace.runStraceFaultCheck
    IO.println "SANDBOX_STRACE_FAULT_CHECK_OK"
    return 0
  | "--timerand-strace-fault-check" :: rest =>
    return (← Fuzz.LinuxSyscall.TimeRand.Strace.probeMain rest)
  | "--poll-strace-fault-check" :: rest =>
    return (← Fuzz.LinuxSyscall.Poll.Strace.probeMain rest)
  | "--poll-strace-worker" :: rest =>
    return (← Fuzz.LinuxSyscall.Poll.Strace.probeMain ("--worker" :: rest))
  | "--poll-strace-efd-worker" :: rest =>
    return (← Fuzz.LinuxSyscall.Poll.Strace.probeMain ("--efd-worker" :: rest))
  | "--net-strace-fault-check" :: rest =>
    return (← Fuzz.LinuxSyscall.Net.Strace.probeMain rest)
  | "--net-strace-worker" :: rest =>
    return (← Fuzz.LinuxSyscall.Net.Strace.probeMain ("--worker" :: rest))
  | "--suite" :: "process" :: "--ns-worker" :: mode :: arg :: rest =>
    Fuzz.LinuxSyscall.ProcessEnv.ensureStdio
    return (← Fuzz.LinuxSyscall.ProcessFuzz.nsWorkerMain mode arg rest)
  | "--ns-worker" :: mode :: arg :: rest =>
    Fuzz.LinuxSyscall.ProcessEnv.ensureStdio
    return (← Fuzz.LinuxSyscall.ProcessFuzz.nsWorkerMain mode arg rest)
  | "--process-strace-worker" :: opName :: errName :: _ =>
    return (← Fuzz.LinuxSyscall.Process.Strace.probeMain ["--worker", opName, errName])
  | "--files-strace-worker" :: rest =>
    return (← Fuzz.LinuxSyscall.Files.Strace.probeMain ("--worker" :: rest))
  | "--postfork-probe" :: _ =>
    return (← runPostForkSubprocProbe)
  | ["--suite", "dns", "--steps", stepsStr, "--seed", seedStr] =>
    match stepsStr.toNat?, seedStr.toNat? with
    | some n, some s =>
      Fuzz.Dns.suite.runFuzz { steps := n, seed := UInt64.ofNat s }
      return 0
    | _, _ =>
      IO.eprintln s!"invalid dns subcheck args: {stepsStr} {seedStr}"
      return 2
  | _ =>
    let flags ← match parseFlags args with
      | .ok f => pure f
      | .error msg =>
        IO.eprintln msg
        return 2
    if flags.mode != "baseline" && flags.mode != "full" then
      IO.eprintln s!"unknown --mode {flags.mode}"
      return 2
    let knownNames := allSuites.map (fun (suiteName, _, _) => suiteName)
    let filterAll := flags.suites.isEmpty || flags.suites.contains "all"
    if !filterAll then
      for s in flags.suites do
        if !knownNames.contains s then
          IO.eprintln s!"UNKNOWN_SUITE: {s}"
          return 2
    let selected :=
      if filterAll then allSuites
      else allSuites.filter fun (suiteName, _, _) => flags.suites.contains suiteName
    for (suiteName, runBase, runExtra) in selected do
      try
        match ← runBase with
        | none => pure ()
        | some reason => IO.println s!"SKIP: {suiteName} ({reason})"
        if flags.mode == "full" then
          runExtra
      catch err =>
        IO.eprintln s!"FAIL: {suiteName} ({err.toString})"
        return 1
    return 0
