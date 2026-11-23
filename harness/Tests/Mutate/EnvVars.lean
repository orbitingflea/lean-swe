import Tests.Common
import Tests.PropCheck
import LeanSwe.EnvVars.Raw.Interface
import LeanSwe.EnvVars.Raw.RuntimeTests
import LeanSwe.EnvVars.Interface
import LeanSwe.EnvVars.RuntimeTests

namespace Tests.Mutate.EnvVars

open LeanSwe
open Tests.Common
open Tests.PropCheck

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

/-- Mutation test suite for `LeanSwe.EnvVars.Raw`. -/
def envVarsRawSuite : MutateSuite :=
  { name := "EnvVars.Raw"
    runBase := do EnvVars.Raw.RuntimeTests.runAll; return none
    runExtra := do runPropChecksEnvVarsRaw; runRawDecoderUnitTests }

/-- Mutation test suite for `LeanSwe.EnvVars`. -/
def envVarsSuite : MutateSuite :=
  { name := "EnvVars"
    runBase := do EnvVars.RuntimeTests.runAll; return none
    runExtra := runPropChecksEnvVars }

end Tests.Mutate.EnvVars
