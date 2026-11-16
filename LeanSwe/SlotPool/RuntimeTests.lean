import LeanSwe.Fs.Impl
import LeanSwe.Fs.Interface
import LeanSwe.Fs.Raw.Interface
import LeanSwe.Process.Interface
import LeanSwe.Process.Raw.Interface
import LeanSwe.SlotPool.Interface
import LeanSwe.SlotPool.Model
import LeanSwe.TempDir.Interface
import LeanSwe.Time.Interface

namespace LeanSwe.SlotPool.RuntimeTests

open LeanSwe
open LeanSwe.SlotPool

private def assertTrue (cond : Bool) (msg : String) : IO Unit := do
  if !cond then
    throw (IO.userError s!"ASSERTION FAILED: {msg}")

private def assertSlotOk {α : Type} (res : Except SlotPoolError α) (msg : String) : IO α := do
  match res with
  | .ok v => return v
  | .error e => throw (IO.userError s!"ASSERTION FAILED: {msg} (unexpected SlotPoolError: {repr e})")

private def assertSlotErrKind {α : Type} (res : Except SlotPoolError α) (expected : SlotPoolErrorKind)
    (msg : String) : IO SlotPoolError := do
  match res with
  | .ok _ => throw (IO.userError s!"ASSERTION FAILED: {msg} (expected SlotPoolError {repr expected}, got ok)")
  | .error e =>
    if e.kind != expected || e.message == "" then
      throw (IO.userError s!"ASSERTION FAILED: {msg} (got {repr e}, expected {repr expected})")
    return e

private def assertFsOk {α : Type} (res : Except Fs.FsError α) (msg : String) : IO α := do
  match res with
  | .ok v => return v
  | .error e => throw (IO.userError s!"ASSERTION FAILED: {msg} (unexpected FsError: {repr e})")

private def waitForFile (path : String) (maxPolls : Nat := 800) : IO Unit := do
  for _ in List.range maxPolls do
    match ← Fs.pathExists path with
    | .ok true => return ()
    | _ => IO.sleep 10
  throw (IO.userError s!"ASSERTION FAILED: timed out waiting for file {path}")

private def parseWaitPolicy : String → Nat → Option WaitPolicy
  | "nowait", _ => some .noWait
  | "forever", _ => some .waitForever
  | "upto", ms => some (.waitUpTo ms)
  | _, _ => none

private def runHoldProbe (poolDir : String) (totalSlots : Nat) (policy : WaitPolicy)
    (readyFile stopFile : String) : IO UInt32 := do
  let cfg : PoolConfig := { poolDir := poolDir, totalSlots := totalSlots, pollIntervalMs := 10 }
  let res ← SlotPool.withSlot cfg policy fun slotIdx => do
    match ← Fs.atomicWriteText readyFile (toString slotIdx) with
    | .error fe => return .error (Model.mapFsError fe)
    | .ok () =>
      let startNs ← Time.monoNanosNow
      let deadlineNs := startNs + 15000 * Model.nanosecondsPerMs
      for _ in List.range 1500 do
        match ← Fs.pathExists stopFile with
        | .ok true => return .ok slotIdx
        | _ =>
          let nowNs ← Time.monoNanosNow
          if nowNs ≥ deadlineNs then
            return .error { kind := .ioError, message := "hold probe timed out waiting for stopFile" }
          IO.sleep 10
      return .error { kind := .ioError, message := "hold probe exhausted poll limit" }
  match res with
  | .ok (.leased _ _) => return 0
  | .ok .noSlot =>
    IO.eprintln "NOSLOT"
    return 10
  | .error e =>
    IO.eprintln s!"SLOTERR:{reprStr e.kind}:{e.message}"
    return 11

private def runHoldSleepProbe (poolDir : String) (totalSlots : Nat) (readyFile : String) : IO UInt32 := do
  let cfg : PoolConfig := { poolDir := poolDir, totalSlots := totalSlots, pollIntervalMs := 10 }
  let res ← SlotPool.withSlot cfg .noWait fun slotIdx => do
    match ← Fs.atomicWriteText readyFile (toString slotIdx) with
    | .error fe => return .error (Model.mapFsError fe)
    | .ok () =>
      for _ in List.range 1500 do
        IO.sleep 10
      return .ok slotIdx
  match res with
  | .ok (.leased _ _) => return 0
  | .ok .noSlot =>
    IO.eprintln "NOSLOT"
    return 10
  | .error e =>
    IO.eprintln s!"SLOTERR:{reprStr e.kind}:{e.message}"
    return 11

private def runConcurrentWorkerProbe (poolDir : String) (totalSlots : Nat)
    (activeDir doneFile : String) : IO UInt32 := do
  let cfg : PoolConfig := { poolDir := poolDir, totalSlots := totalSlots, pollIntervalMs := 10 }
  let res ← SlotPool.withSlot cfg .waitForever fun slotIdx => do
    let activeMarker := Fs.join activeDir s!"slot-{slotIdx}.active"
    match ← Fs.Raw.createFileNew activeMarker (ByteArray.mk #[49]) with
    | .error fe =>
      return .error { kind := .ioError, path := some activeMarker, message := s!"mutual exclusion violation on slot {slotIdx}: {fe.message}" }
    | .ok () =>
      IO.sleep 35
      let _ ← Fs.unlink activeMarker false
      match ← Fs.atomicWriteText doneFile (toString slotIdx) with
      | .error fe => return .error (Model.mapFsError fe)
      | .ok () => return .ok slotIdx
  match res with
  | .ok (.leased _ _) => return 0
  | .ok .noSlot =>
    IO.eprintln "NOSLOT"
    return 10
  | .error e =>
    IO.eprintln s!"SLOTERR:{reprStr e.kind}:{e.message}"
    return 11

/-- Subprocess probe entrypoint invoked via `--slotpool-probe` from `runAll`. -/
def probeMain (args : List String) : IO UInt32 := do
  match args with
  | ["hold", poolDir, slotsStr, policyTag, timeoutStr, readyFile, stopFile] =>
    match slotsStr.toNat?, timeoutStr.toNat? with
    | some totalSlots, some timeoutMs =>
      match parseWaitPolicy policyTag timeoutMs with
      | some policy => runHoldProbe poolDir totalSlots policy readyFile stopFile
      | none =>
        IO.eprintln s!"unknown wait policy tag: {policyTag}"
        return 3
    | _, _ =>
      IO.eprintln "invalid numeric arguments for hold probe"
      return 3
  | ["hold-sleep", poolDir, slotsStr, readyFile] =>
    match slotsStr.toNat? with
    | some totalSlots => runHoldSleepProbe poolDir totalSlots readyFile
    | none =>
      IO.eprintln "invalid totalSlots for hold-sleep probe"
      return 3
  | ["worker", poolDir, slotsStr, activeDir, doneFile] =>
    match slotsStr.toNat? with
    | some totalSlots => runConcurrentWorkerProbe poolDir totalSlots activeDir doneFile
    | none =>
      IO.eprintln "invalid totalSlots for worker probe"
      return 3
  | ["race-worker", goFile, poolDir, slotsStr, activeDir, doneFile] =>
    match slotsStr.toNat? with
    | some totalSlots =>
      waitForFile goFile
      runConcurrentWorkerProbe poolDir totalSlots activeDir doneFile
    | none =>
      IO.eprintln "invalid totalSlots for race-worker probe"
      return 3
  | _ =>
    IO.eprintln "unknown --slotpool-probe arguments"
    return 3

private def spawnProbe (exe : String) (args : Array String) : IO Process.ProcessHandle := do
  match ← Process.Raw.spawn { program := exe, args := #["--slotpool-probe"] ++ args } with
  | .ok h => return h
  | .error e => throw (IO.userError s!"ASSERTION FAILED: spawn probe failed: {repr e}")

private def awaitProbeZero (h : Process.ProcessHandle) (label : String) : IO Unit := do
  let outcome ← Process.Raw.awaitOutput h ByteArray.empty (some 20000) none
  let _ ← Process.Raw.reap h
  match outcome with
  | .ok (.exited out) =>
    if out.exitCode != 0 then
      throw (IO.userError s!"ASSERTION FAILED: {label} exited {out.exitCode}, stderr={String.fromUTF8! out.stderr}")
  | .ok other =>
    throw (IO.userError s!"ASSERTION FAILED: {label} unexpected outcome: {repr other}")
  | .error e =>
    throw (IO.userError s!"ASSERTION FAILED: {label} awaitOutput error: {repr e}")

private def testInvalidConfigAndCollisions (sandbox : String) : IO Unit := do
  let ranRef ← IO.mkRef false
  let nulDir := String.ofList ['p', 'o', 'o', 'l', Char.ofNat 0]
  let badConfigs : Array PoolConfig :=
    #[ { poolDir := "", totalSlots := 1, pollIntervalMs := 10 },
       { poolDir := nulDir, totalSlots := 1, pollIntervalMs := 10 },
       { poolDir := Fs.join sandbox "bad-zero-slots", totalSlots := 0, pollIntervalMs := 10 },
       { poolDir := Fs.join sandbox "bad-zero-poll", totalSlots := 1, pollIntervalMs := 0 } ]
  for cfg in badConfigs do
    let err ← assertSlotErrKind
      (← SlotPool.withSlot cfg .noWait fun _ => do ranRef.set true; return .ok ())
      .invalidInput s!"reject invalid PoolConfig {repr cfg}"
    assertTrue (err.path == some cfg.poolDir) s!"invalid config preserves path {repr err}"
    assertTrue (!(← ranRef.get)) "invalid config never invokes callback"
  assertTrue (!(← assertFsOk (← Fs.pathExists (Fs.join sandbox "bad-zero-slots")) "exists"))
    "invalid totalSlots does not create poolDir"
  assertTrue (!(← assertFsOk (← Fs.pathExists (Fs.join sandbox "bad-zero-poll")) "exists"))
    "invalid pollIntervalMs does not create poolDir"

  let regularPoolFile := Fs.join sandbox "pool-regular-file"
  assertFsOk (← Fs.writeText regularPoolFile "not a directory") "create blocking regular file"
  let fileErr ← assertSlotErrKind
    (← SlotPool.withSlot { poolDir := regularPoolFile, totalSlots := 1, pollIntervalMs := 10 } .noWait fun _ => do
      ranRef.set true; return .ok ())
    .alreadyExists "regular file collision at poolDir rejected"
  assertTrue (fileErr.path == some regularPoolFile) "file collision preserves poolDir path"
  assertTrue (!(← ranRef.get)) "regular file collision never invokes callback"

  let dirPool := Fs.join sandbox "dir-slot-collision"
  assertFsOk (← Fs.mkdir dirPool false false) "mkdir dir-slot-collision"
  let slot0Dir := Fs.join dirPool "slot-0.lock"
  assertFsOk (← Fs.mkdir slot0Dir false false) "mkdir slot-0.lock directory collision"
  let dirErr ← assertSlotErrKind
    (← SlotPool.withSlot { poolDir := dirPool, totalSlots := 1, pollIntervalMs := 10 } .noWait fun _ => do
      ranRef.set true; return .ok ())
    .isADirectory "directory collision at slot-0.lock rejected"
  assertTrue (dirErr.path == some slot0Dir) "directory collision preserves lock path"
  assertTrue (!(← ranRef.get)) "directory collision never invokes callback"

  let symPool := Fs.join sandbox "sym-slot-collision"
  assertFsOk (← Fs.mkdir symPool false false) "mkdir sym-slot-collision"
  let symTarget := Fs.join sandbox "sym-victim.txt"
  assertFsOk (← Fs.writeText symTarget "victim") "create symlink victim file"
  let slot0Sym := Fs.join symPool "slot-0.lock"
  assertFsOk (← Fs.symlink symTarget slot0Sym) "plant symlink at slot-0.lock"
  let symErr ← assertSlotErrKind
    (← SlotPool.withSlot { poolDir := symPool, totalSlots := 1, pollIntervalMs := 10 } .noWait fun _ => do
      ranRef.set true; return .ok ())
    .invalidInput "symlink collision at slot-0.lock rejected via O_NOFOLLOW"
  assertTrue (symErr.path == some slot0Sym) "symlink collision preserves lock path"
  assertTrue (!(← ranRef.get)) "symlink collision never invokes callback"
  assertTrue ((← assertFsOk (← Fs.readText symTarget) "read victim") == "victim")
    "symlink target untouched after rejection"

private def testCallbackErrorAndUncaughtException (sandbox : String) : IO Unit := do
  let poolDir := Fs.join sandbox "nested/cb-pool"
  let cfg : PoolConfig := { poolDir := poolDir, totalSlots := 1, pollIntervalMs := 10 }
  let lock0 := Fs.join poolDir "slot-0.lock"

  let okOutcome ← assertSlotOk
    (← SlotPool.withSlot cfg (.waitUpTo 0) fun idx => return .ok (idx + 10))
    "waitUpTo 0 acquires free slot"
  assertTrue (okOutcome == .leased 0 10) "waitUpTo 0 leased slot 0"
  assertTrue (← assertFsOk (← Fs.isFile lock0) "isFile lock0") "lock0 file preserved after ok"

  let cbErr : SlotPoolError := { kind := .permissionDenied, path := some "cb/custom", message := "callback failed" }
  let gotErr ← assertSlotErrKind
    (← SlotPool.withSlot cfg .noWait fun _ => return (Except.error cbErr : Except SlotPoolError Nat))
    .permissionDenied "callback error returned"
  assertTrue (gotErr == cbErr) "callback error preserved verbatim"
  assertTrue (← assertFsOk (← Fs.isFile lock0) "isFile lock0") "lock0 file preserved after callback error"

  let reacquiredAfterCb ← assertSlotOk
    (← SlotPool.withSlot cfg .noWait fun idx => return .ok idx)
    "lock released after callback error"
  assertTrue (reacquiredAfterCb == .leased 0 0) "slot 0 reacquired immediately after callback error"

  let mut threw := false
  try
    let _ : Except SlotPoolError (LeaseOutcome Unit) ← SlotPool.withSlot cfg .noWait fun _ => do
      throw (IO.userError "boom")
  catch _ =>
    threw := true
  assertTrue threw "uncaught IO.Error propagated out of withSlot"
  assertTrue (← assertFsOk (← Fs.isFile lock0) "isFile lock0") "lock0 file preserved after IO.Error"

  let reacquiredAfterThrow ← assertSlotOk
    (← SlotPool.withSlot cfg .noWait fun idx => return .ok idx)
    "lock released after uncaught IO.Error"
  assertTrue (reacquiredAfterThrow == .leased 0 0) "slot 0 reacquired immediately after IO.Error"

private def testMultiProcessDisjointSlotsAndSaturation (exe sandbox : String) : IO Unit := do
  let poolDir := Fs.join sandbox "mp-disjoint-pool"
  let cfg : PoolConfig := { poolDir := poolDir, totalSlots := 3, pollIntervalMs := 10 }
  let ready0 := Fs.join sandbox "mp0.ready"
  let stop0 := Fs.join sandbox "mp0.stop"
  let ready1 := Fs.join sandbox "mp1.ready"
  let stop1 := Fs.join sandbox "mp1.stop"
  let ready2 := Fs.join sandbox "mp2.ready"
  let stop2 := Fs.join sandbox "mp2.stop"

  let h0 ← spawnProbe exe #["hold", poolDir, "3", "upto", "5000", ready0, stop0]
  try
    waitForFile ready0
    let h1 ← spawnProbe exe #["hold", poolDir, "3", "upto", "5000", ready1, stop1]
    try
      waitForFile ready1
      let h2 ← spawnProbe exe #["hold", poolDir, "3", "upto", "5000", ready2, stop2]
      try
        waitForFile ready2
        let s0 ← assertFsOk (← Fs.readText ready0) "read ready0"
        let s1 ← assertFsOk (← Fs.readText ready1) "read ready1"
        let s2 ← assertFsOk (← Fs.readText ready2) "read ready2"
        assertTrue (s0 == "0" && s1 == "1" && s2 == "2")
          s!"expected ascending disjoint slots 0,1,2 across 3 live processes, got {s0},{s1},{s2}"

        let ranRef ← IO.mkRef false
        let noWaitOut ← assertSlotOk
          (← SlotPool.withSlot cfg .noWait fun _ => do ranRef.set true; return .ok 1)
          "noWait while pool saturated"
        assertTrue (noWaitOut == .noSlot) "noWait returns .noSlot when all 3 slots busy"
        assertTrue (!(← ranRef.get)) "noWait saturated never invokes callback"

        let waitExpireOut ← assertSlotOk
          (← SlotPool.withSlot cfg (.waitUpTo 40) fun _ => do ranRef.set true; return .ok 1)
          "waitUpTo 40 while pool saturated"
        assertTrue (waitExpireOut == .noSlot) "waitUpTo returns .noSlot when all 3 slots stay busy"
        assertTrue (!(← ranRef.get)) "waitUpTo saturated never invokes callback"

        assertFsOk (← Fs.writeText stop1 "go") "stop child 1"
        awaitProbeZero h1 "hold child 1"

        let freedOut ← assertSlotOk
          (← SlotPool.withSlot cfg .noWait fun idx => return .ok idx)
          "parent acquires freed slot 1"
        assertTrue (freedOut == .leased 1 1) "parent acquired specifically slot 1 while 0 and 2 remained held"

        assertFsOk (← Fs.writeText stop0 "go") "stop child 0"
        assertFsOk (← Fs.writeText stop2 "go") "stop child 2"
        awaitProbeZero h0 "hold child 0"
        awaitProbeZero h2 "hold child 2"
      finally
        let _ ← Fs.writeText stop2 "go"
        let _ ← Process.Raw.killProcessGroup h2
        let _ ← Process.Raw.reap h2
    finally
      let _ ← Fs.writeText stop1 "go"
      let _ ← Process.Raw.killProcessGroup h1
      let _ ← Process.Raw.reap h1
  finally
    let _ ← Fs.writeText stop0 "go"
    let _ ← Process.Raw.killProcessGroup h0
    let _ ← Process.Raw.reap h0

  for i in List.range 3 do
    let lp := Model.slotLockPath Fs.join poolDir i
    assertTrue (← assertFsOk (← Fs.isFile lp) s!"isFile {lp}") s!"lock file {lp} preserved after exit"
  assertTrue ((← Process.activeProcessCount) == 0) "all hold processes reaped"

private def testMultiProcessConcurrentContention (exe sandbox : String) : IO Unit := do
  let poolDir := Fs.join sandbox "mp-concurrent-pool"
  let activeDir := Fs.join sandbox "mp-active"
  assertFsOk (← Fs.mkdir activeDir false false) "mkdir activeDir"

  let workerCount := 6
  let mut handles : Array (Nat × Process.ProcessHandle × String) := #[]
  try
    for i in List.range workerCount do
      let doneFile := Fs.join sandbox s!"worker-{i}.done"
      let h ← spawnProbe exe #["worker", poolDir, "2", activeDir, doneFile]
      handles := handles.push (i, h, doneFile)
    for (i, h, doneFile) in handles do
      awaitProbeZero h s!"concurrent worker {i}"
      let slotStr ← assertFsOk (← Fs.readText doneFile) s!"read worker {i} doneFile"
      assertTrue (slotStr == "0" || slotStr == "1")
        s!"worker {i} leased out-of-range slot {slotStr}"
  finally
    for (_, h, _) in handles do
      let _ ← Process.Raw.killProcessGroup h
      let _ ← Process.Raw.reap h

  for i in List.range 2 do
    let lp := Model.slotLockPath Fs.join poolDir i
    assertTrue (← assertFsOk (← Fs.isFile lp) s!"isFile {lp}") s!"concurrent lock file {lp} preserved"
  assertTrue ((← Process.activeProcessCount) == 0) "all concurrent workers reaped"

private def testSigkillWakeupWaitUpToAndWaitForever (exe sandbox : String) : IO Unit := do
  let poolDir := Fs.join sandbox "mp-sigkill-pool"
  let cfg : PoolConfig := { poolDir := poolDir, totalSlots := 1, pollIntervalMs := 10 }
  let lock0 := Fs.join poolDir "slot-0.lock"

  let k1Ready := Fs.join sandbox "sigkill1.ready"
  let peer1Ready := Fs.join sandbox "peer1.ready"
  let peer1Stop := Fs.join sandbox "peer1.stop"
  let hKill1 ← spawnProbe exe #["hold-sleep", poolDir, "1", k1Ready]
  try
    waitForFile k1Ready
    let sat1 ← assertSlotOk (← SlotPool.withSlot cfg .noWait fun _ => return .ok 1) "noWait while sigkill1 holds lock"
    assertTrue (sat1 == .noSlot) "sigkill1 holds exclusive lock"

    let hPeer1 ← spawnProbe exe #["hold", poolDir, "1", "forever", "0", peer1Ready, peer1Stop]
    try
      IO.sleep 60
      assertTrue (!(← assertFsOk (← Fs.pathExists peer1Ready) "peer1Ready check"))
        "waitForever peer stays blocked while sigkill1 holds slot 0"

      match ← Process.runCommand "kill" #["-9", toString hKill1.pid] with
      | .ok kout => assertTrue (kout.exitCode == 0) "kill -9 sigkill1 exit 0"
      | .error e => throw (IO.userError s!"kill -9 sigkill1 failed: {repr e}")
      let _ ← Process.Raw.reap hKill1

      waitForFile peer1Ready
      let peer1Slot ← assertFsOk (← Fs.readText peer1Ready) "read peer1Ready"
      assertTrue (peer1Slot == "0") s!"waitForever peer expected slot 0, got {peer1Slot}"
      assertFsOk (← Fs.writeText peer1Stop "go") "stop peer1"
      awaitProbeZero hPeer1 "waitForever peer1"
    finally
      let _ ← Fs.writeText peer1Stop "go"
      let _ ← Process.Raw.killProcessGroup hPeer1
      let _ ← Process.Raw.reap hPeer1
  finally
    let _ ← Process.Raw.killProcessGroup hKill1
    let _ ← Process.Raw.reap hKill1

  assertTrue (← assertFsOk (← Fs.isFile lock0) "isFile lock0") "lock0 preserved after SIGKILL + waitForever"

  let k2Ready := Fs.join sandbox "sigkill2.ready"
  let peer2Ready := Fs.join sandbox "peer2.ready"
  let peer2Stop := Fs.join sandbox "peer2.stop"
  let hKill2 ← spawnProbe exe #["hold-sleep", poolDir, "1", k2Ready]
  try
    waitForFile k2Ready
    let hPeer2 ← spawnProbe exe #["hold", poolDir, "1", "upto", "5000", peer2Ready, peer2Stop]
    try
      IO.sleep 60
      assertTrue (!(← assertFsOk (← Fs.pathExists peer2Ready) "peer2Ready check"))
        "waitUpTo peer stays blocked while sigkill2 holds slot 0"

      match ← Process.runCommand "kill" #["-9", toString hKill2.pid] with
      | .ok kout => assertTrue (kout.exitCode == 0) "kill -9 sigkill2 exit 0"
      | .error e => throw (IO.userError s!"kill -9 sigkill2 failed: {repr e}")
      let _ ← Process.Raw.reap hKill2

      waitForFile peer2Ready
      let peer2Slot ← assertFsOk (← Fs.readText peer2Ready) "read peer2Ready"
      assertTrue (peer2Slot == "0") s!"waitUpTo peer expected slot 0, got {peer2Slot}"
      assertFsOk (← Fs.writeText peer2Stop "go") "stop peer2"
      awaitProbeZero hPeer2 "waitUpTo peer2"
    finally
      let _ ← Fs.writeText peer2Stop "go"
      let _ ← Process.Raw.killProcessGroup hPeer2
      let _ ← Process.Raw.reap hPeer2
  finally
    let _ ← Process.Raw.killProcessGroup hKill2
    let _ ← Process.Raw.reap hKill2

  assertTrue (← assertFsOk (← Fs.isFile lock0) "isFile lock0") "lock0 preserved after SIGKILL + waitUpTo"
  assertTrue ((← Process.activeProcessCount) == 0) "all SIGKILL and peer processes reaped"

private def testUncreatedPoolDirRace (exe sandbox : String) : IO Unit := do
  let raw := Fs.Raw.defaultOps
  let raceDir := Fs.join sandbox "toctou-dir-pool"
  let raceFileDir := Fs.join sandbox "toctou-file-pool"
  let statCallsRef ← IO.mkRef (0 : Nat)
  let dirRacingOps : Fs.RawFsOps :=
    { raw with
      createDir := fun p => do
        if p == raceDir then
          let _ ← raw.createDir p
          return .error { kind := .alreadyExists, path := some p, message := "simulated concurrent mkdir" }
        else if p == raceFileDir then
          let _ ← Fs.writeText p "not-a-dir"
          return .error { kind := .alreadyExists, path := some p, message := "simulated concurrent file" }
        else
          raw.createDir p
      stat := fun follow p => do
        if p == raceDir then
          let n ← statCallsRef.modifyGet fun c => (c, c + 1)
          if n == 0 then
            return .error { kind := .notFound, path := some p, message := "initial stat before peer mkdir" }
        raw.stat follow p }
  let racingPoolApi := SlotPool.mkApiM (Fs.Internal.mkApiM dirRacingOps) Time.defaultOps
  let dirOut ← assertSlotOk
    (← racingPoolApi.withSlot { poolDir := raceDir, totalSlots := 1, pollIntervalMs := 10 } .noWait fun idx =>
      return .ok (idx + 7))
    "withSlot tolerates concurrent createDir alreadyExists on real dir"
  assertTrue (dirOut == .leased 0 7) "TOCTOU dir race returns .leased 0 7"
  assertTrue (← assertFsOk (← Fs.isDir raceDir) "raceDir isDir") "raceDir created as directory"
  let _ ← assertSlotErrKind
    (← racingPoolApi.withSlot { poolDir := raceFileDir, totalSlots := 1, pollIntervalMs := 10 } .noWait fun _ =>
      return .ok (1 : Nat))
    .alreadyExists
    "withSlot rejects concurrent file creation at poolDir"

  let mpPoolDir := Fs.join (Fs.join sandbox "mp-race-parent") "nested-pool"
  let activeDir := Fs.join sandbox "mp-race-active"
  let goFile := Fs.join sandbox "mp-race.go"
  assertFsOk (← Fs.mkdir activeDir false false) "mkdir mp-race-active"
  let mut handles : Array (Nat × Process.ProcessHandle × String) := #[]
  try
    for i in List.range 6 do
      let doneFile := Fs.join sandbox s!"race-worker-{i}.done"
      let h ← spawnProbe exe #["race-worker", goFile, mpPoolDir, "2", activeDir, doneFile]
      handles := handles.push (i, h, doneFile)
    IO.sleep 50
    assertFsOk (← Fs.writeText goFile "go") "release race-worker barrier"
    for (i, h, doneFile) in handles do
      awaitProbeZero h s!"race-worker {i}"
      let slotStr ← assertFsOk (← Fs.readText doneFile) s!"read race-worker {i} doneFile"
      assertTrue (slotStr == "0" || slotStr == "1")
        s!"race-worker {i} leased out-of-range slot {slotStr}"
  finally
    let _ ← Fs.writeText goFile "go"
    for (_, h, _) in handles do
      let _ ← Process.Raw.killProcessGroup h
      let _ ← Process.Raw.reap h
  assertTrue ((← Process.activeProcessCount) == 0) "all race-worker processes reaped"

/-- Execute all multi-process OS advisory-locking and boundary runtime checks for `LeanSwe.SlotPool`. -/
def runAll : IO Unit := do
  let exe := (← IO.appPath).toString
  let res ← TempDir.withTempDir none "lean-swe-slotpool-rt-" fun sandbox => do
    testInvalidConfigAndCollisions sandbox
    testCallbackErrorAndUncaughtException sandbox
    testMultiProcessDisjointSlotsAndSaturation exe sandbox
    testMultiProcessConcurrentContention exe sandbox
    testUncreatedPoolDirRace exe sandbox
    testSigkillWakeupWaitUpToAndWaitForever exe sandbox
    return .ok ()
  match res with
  | .ok () => IO.println "PASS: LeanSwe.SlotPool runtime tests"
  | .error e => throw (IO.userError s!"ASSERTION FAILED: outer temp sandbox error: {repr e}")

end LeanSwe.SlotPool.RuntimeTests
