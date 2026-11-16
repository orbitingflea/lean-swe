import LeanSwe.Fs.Types
import LeanSwe.SlotPool.Types
import LeanSwe.Time.Types

namespace LeanSwe.SlotPool.Model

open LeanSwe.Fs (FsApiM FsError FsErrorKind EntryKind FileStat LockMode)
open LeanSwe.Time (TimeOpsM)

/-- Nanoseconds in one millisecond (`1_000_000`). -/
def nanosecondsPerMs : Nat := 1000000

/-- Maximum milliseconds accepted by a single `UInt32` `TimeOpsM.sleep` call (`2 ^ 32 - 1`). -/
def maxSleepChunkMs : Nat := 4294967295

/-- Structural poll bound for `WaitPolicy.waitForever` (`2 ^ 64` polls). -/
def maxForeverPolls : Nat := 2 ^ 64

/-- Return `true` iff `cs` contains a NUL character (`'\x00'`). -/
def hasNulChar : List Char → Bool
  | [] => false
  | c :: cs => c == Char.ofNat 0 || hasNulChar cs

/-- Return `true` iff `poolDir` is non-empty and contains no NUL byte. -/
def validPoolDir (poolDir : String) : Bool :=
  !poolDir.isEmpty && !hasNulChar poolDir.toList

/-- Return `true` iff `cfg` has a valid `poolDir`, `totalSlots >= 1`, and `pollIntervalMs >= 1`. -/
def validPoolConfig (cfg : PoolConfig) : Bool :=
  validPoolDir cfg.poolDir && decide (1 ≤ cfg.totalSlots) && decide (1 ≤ cfg.pollIntervalMs)

/-- Validate `cfg` at the API boundary, returning `.invalidInput` when `validPoolConfig cfg` is `false`. -/
def validatePoolConfig (cfg : PoolConfig) : Except SlotPoolError PoolConfig :=
  if !validPoolDir cfg.poolDir then
    .error { kind := .invalidInput, path := some cfg.poolDir, message := "invalid pool directory path" }
  else if cfg.totalSlots == 0 then
    .error { kind := .invalidInput, path := some cfg.poolDir, message := "totalSlots must be at least 1" }
  else if cfg.pollIntervalMs == 0 then
    .error { kind := .invalidInput, path := some cfg.poolDir, message := "pollIntervalMs must be at least 1" }
  else
    .ok cfg

/-- Single ASCII decimal digit character `'0'` through `'9'` for `d < 10`. -/
def decDigitChar (d : Nat) : Char :=
  Char.ofNat (48 + d)

/-- Structurally recursive base-10 digit formatter prepending digits onto `acc`. -/
def natDecCharsAux : Nat → Nat → List Char → List Char
  | 0, _, acc => acc
  | fuel + 1, n, acc =>
    let d := decDigitChar (n % 10)
    let q := n / 10
    if q == 0 then
      d :: acc
    else
      natDecCharsAux fuel q (d :: acc)

/-- Format `n` as a base-10 ASCII decimal string using structural recursion. -/
def natDecString (n : Nat) : String :=
  String.ofList (natDecCharsAux (n + 1) n [])

/-- Canonical lock filename `"slot-<slotIndex>.lock"` for `slotIndex`. -/
def slotFileName (slotIndex : Nat) : String :=
  "slot-" ++ natDecString slotIndex ++ ".lock"

/-- Full lock path `<poolDir>/slot-<slotIndex>.lock` constructed via `join`. -/
def slotLockPath (join : String → String → String) (poolDir : String) (slotIndex : Nat) : String :=
  join poolDir (slotFileName slotIndex)

/-- Compute monotonic deadline `startNs + timeoutMs * 1_000_000` in nanoseconds. -/
def deadlineNanos (startNs timeoutMs : Nat) : Nat :=
  startNs + timeoutMs * nanosecondsPerMs

/-- Compute remaining wait budget in milliseconds, rounding positive sub-millisecond remainders up to `1`. -/
def remainingWaitMs (nowNs deadlineNs : Nat) : Nat :=
  if nowNs ≥ deadlineNs then
    0
  else
    (deadlineNs - nowNs + 999999) / nanosecondsPerMs

/-- Compute the next bounded sleep duration `min pollIntervalMs (remainingWaitMs nowNs deadlineNs)`. -/
def nextSleepMs (pollIntervalMs nowNs deadlineNs : Nat) : Nat :=
  Nat.min pollIntervalMs (remainingWaitMs nowNs deadlineNs)

/-- Structurally recursive worker splitting `ms` into positive `UInt32` chunks bounded by `maxSleepChunkMs`. -/
def sleepChunksAux : Nat → Nat → List UInt32
  | 0, _ => []
  | _ + 1, 0 => []
  | fuel + 1, ms =>
    let chunk := Nat.min ms maxSleepChunkMs
    UInt32.ofNat chunk :: sleepChunksAux fuel (ms - chunk)

/-- Split `ms` milliseconds into positive `UInt32` chunks summing to `ms`. -/
def sleepChunks (ms : Nat) : List UInt32 :=
  sleepChunksAux (ms / maxSleepChunkMs + 1) ms

/-- Execute a list of `UInt32` millisecond sleep chunks sequentially via `time.sleep`. -/
def runSleepChunks {m : Type → Type} [Monad m] (time : TimeOpsM m) : List UInt32 → m Unit
  | [] => pure ()
  | c :: cs => do
    time.sleep c
    runSleepChunks time cs

/-- Bundle of pure timing and `UInt32` sleep-chunking operations for `SpecTests` mutation testing. -/
structure TimingModelOps where
  /-- Compute monotonic deadline in nanoseconds from `(startNs, timeoutMs)`. -/
  deadlineNanos : Nat → Nat → Nat
  /-- Compute ceiling remaining milliseconds from `(nowNs, deadlineNs)`. -/
  remainingWaitMs : Nat → Nat → Nat
  /-- Compute next bounded sleep duration in milliseconds from `(pollIntervalMs, nowNs, deadlineNs)`. -/
  nextSleepMs : Nat → Nat → Nat → Nat
  /-- Split `ms` milliseconds into positive `UInt32` sleep chunks. -/
  sleepChunks : Nat → List UInt32

/-- Canonical `TimingModelOps` bundle backed by `Model` timing helpers. -/
def defaultTimingModelOps : TimingModelOps :=
  { deadlineNanos := deadlineNanos
    remainingWaitMs := remainingWaitMs
    nextSleepMs := nextSleepMs
    sleepChunks := sleepChunks }

/-- Map an `FsErrorKind` into the corresponding `SlotPoolErrorKind`. -/
def mapFsErrorKind : FsErrorKind → SlotPoolErrorKind
  | .invalidInput => .invalidInput
  | .notFound => .notFound
  | .alreadyExists => .alreadyExists
  | .permissionDenied => .permissionDenied
  | .isADirectory => .isADirectory
  | .notADirectory => .notADirectory
  | .unsupported => .unsupported
  | .notEmpty | .wouldBlock | .ioError => .ioError

/-- Convert an `FsError` into a `SlotPoolError` with a guaranteed non-empty diagnostic message. -/
def mapFsError (err : FsError) : SlotPoolError :=
  { kind := mapFsErrorKind err.kind
    path := err.path
    message := if err.message.isEmpty then "filesystem error in slot pool" else err.message }

/-- Strip trailing `'/'` characters from a reversed character list, keeping `['/']` for root. -/
def trimTrailingSlashesRev : List Char → List Char
  | [] => []
  | c :: rest =>
    if c == '/' then
      if rest.isEmpty then ['/'] else trimTrailingSlashesRev rest
    else
      c :: rest

/-- Normalize a mock path key by stripping non-root trailing `'/'` characters. -/
def normSimPath (p : String) : String :=
  String.ofList (trimTrailingSlashesRev p.toList.reverse).reverse

/-- Drop characters from a reversed path until the first `'/'`, returning the reversed prefix before that `'/'`. -/
def dropUntilSlashRev : List Char → Option (List Char)
  | [] => none
  | c :: rest => if c == '/' then some rest else dropUntilSlashRev rest

/-- Compute the normalized parent directory key of `p`, or `none` for root `"/"`, empty, or single-segment relative names. -/
def parentSimPath (p : String) : Option String :=
  let np := normSimPath p
  if np.isEmpty || np == "/" then
    none
  else
    match dropUntilSlashRev np.toList.reverse with
    | none => none
    | some [] => some "/"
    | some revPar => some (normSimPath (String.ofList revPar.reverse))

/-- Join two mock path strings cleanly under `normSimPath`. -/
def simJoin (base sub : String) : String :=
  let nb := normSimPath base
  let ns := normSimPath sub
  if ns.toList.head? == some '/' then
    ns
  else if nb.isEmpty then
    ns
  else if nb == "/" then
    "/" ++ ns
  else
    nb ++ "/" ++ ns

/-- Deterministic pure simulation state modeling directories, regular files, symlinks, locks, and monotonic time. -/
structure PoolSimState where
  /-- Normalized directory paths present in the simulated filesystem. -/
  dirs : List String := []
  /-- Normalized regular file paths (with UTF-8 text content) present in the simulated filesystem. -/
  files : List (String × String) := []
  /-- Normalized symbolic link paths present in the simulated filesystem. -/
  symlinks : List String := []
  /-- Active advisory locks `(normalizedPath, mode)` currently held by this process. -/
  heldLocks : List (String × LockMode) := []
  /-- Exclusive slot locks `(normalizedPath, releaseAtMonoNs)` held by external peer processes while `monoNanos < releaseAtMonoNs`. -/
  externalLeases : List (String × Nat) := []
  /-- Optional filesystem error injected on `mkdir`. -/
  failMkdirWith : Option FsError := none
  /-- Simulated monotonic clock in nanoseconds. -/
  monoNanos : Nat := 0
  /-- Recorded sequence of `UInt32` millisecond chunks passed to `TimeOpsM.sleep`. -/
  sleepLog : Array UInt32 := #[]
  deriving Repr, BEq, DecidableEq, Inhabited

/-- Return `true` iff normalized path `np` is a regular file in `s`. -/
def hasSimFile (s : PoolSimState) (np : String) : Bool :=
  s.files.any fun (fp, _) => fp == np

/-- Inspect simulated metadata without following symlinks (`lstat`). -/
def simLstatPure (s : PoolSimState) (p : String) : Except FsError FileStat :=
  let np := normSimPath p
  if np ∈ s.dirs then
    .ok { kind := .dir, byteSize := 0, mode := 0o755, modifiedSec := 0, modifiedNsec := 0, accessedSec := 0, accessedNsec := 0 }
  else
    match s.files.find? (fun (fp, _) => fp == np) with
    | some (_, content) =>
      .ok { kind := .file, byteSize := content.length, mode := 0o644, modifiedSec := 0, modifiedNsec := 0, accessedSec := 0, accessedNsec := 0 }
    | none =>
      if np ∈ s.symlinks then
        .ok { kind := .symlink, byteSize := 0, mode := 0o777, modifiedSec := 0, modifiedNsec := 0, accessedSec := 0, accessedNsec := 0 }
      else
        .error { kind := .notFound, path := some p, message := "path not found" }

/-- Recursively ensure normalized directory `np` and all of its ancestor directories exist in `s`. -/
def ensureSimDirChain : Nat → PoolSimState → String → Except FsError PoolSimState
  | 0, s, _ => .ok s
  | fuel + 1, s, np =>
    if hasSimFile s np || np ∈ s.symlinks then
      .error { kind := .notADirectory, path := some np, message := "ancestor is not a directory" }
    else if np ∈ s.dirs then
      .ok s
    else
      match parentSimPath np with
      | none => .ok { s with dirs := np :: s.dirs }
      | some par =>
        match ensureSimDirChain fuel s par with
        | .error e => .error e
        | .ok s' =>
          if np ∈ s'.dirs then .ok s'
          else .ok { s' with dirs := np :: s'.dirs }

/-- Pure state transition for `simFs.mkdir`. -/
def simMkdirPure (s : PoolSimState) (path : String) (parents existOk : Bool) : Except FsError PoolSimState :=
  match s.failMkdirWith with
  | some err => .error err
  | none =>
    if !validPoolDir path then
      .error { kind := .invalidInput, path := some path, message := "invalid directory path" }
    else
      let np := normSimPath path
      if hasSimFile s np || np ∈ s.symlinks then
        .error { kind := .alreadyExists, path := some path, message := "non-directory entry already exists" }
      else if np ∈ s.dirs then
        if existOk then
          .ok s
        else
          .error { kind := .alreadyExists, path := some path, message := "directory already exists" }
      else if !parents then
        match parentSimPath np with
        | none => .ok { s with dirs := np :: s.dirs }
        | some par =>
          if hasSimFile s par || par ∈ s.symlinks then
            .error { kind := .notADirectory, path := some par, message := "parent is not a directory" }
          else if par ∈ s.dirs then
            .ok { s with dirs := np :: s.dirs }
          else
            .error { kind := .notFound, path := some path, message := "parent directory does not exist" }
      else
        ensureSimDirChain (np.toList.length + 1) s np

/-- Return `true` iff `np` currently has a conflicting in-process or active external advisory lock. -/
def hasSimLockConflict (s : PoolSimState) (np : String) (mode : LockMode) : Bool :=
  (s.heldLocks.any fun (lp, lm) => lp == np && (mode == .exclusive || lm == .exclusive)) ||
    (s.externalLeases.any fun (lp, relNs) => lp == np && decide (s.monoNanos < relNs))

/-- Remove the first occurrence of `(np, mode)` from an active lock list. -/
def removeFirstSimLock (np : String) (mode : LockMode) : List (String × LockMode) → List (String × LockMode)
  | [] => []
  | x :: xs => if x == (np, mode) then xs else x :: removeFirstSimLock np mode xs

/-- Pure state transition attempting to open and non-blockingly or blockingly lock `lockPath`. -/
def simTryAcquirePure (s : PoolSimState) (lockPath : String) (mode : LockMode)
    (createIfMissing : Bool) : Except FsError (Option PoolSimState) :=
  if !validPoolDir lockPath then
    .error { kind := .invalidInput, path := some lockPath, message := "invalid lock path" }
  else
    let np := normSimPath lockPath
    if np ∈ s.dirs then
      .error { kind := .isADirectory, path := some lockPath, message := "lock target is a directory" }
    else if np ∈ s.symlinks then
      .error { kind := .invalidInput, path := some lockPath, message := "lock target is a symlink" }
    else if hasSimFile s np then
      if hasSimLockConflict s np mode then
        .ok none
      else
        .ok (some { s with heldLocks := (np, mode) :: s.heldLocks })
    else
      let parentOk : Bool :=
        match parentSimPath np with
        | none => true
        | some par => decide (par ∈ s.dirs)
      if !parentOk then
        .error { kind := .notFound, path := some lockPath, message := "lock parent directory does not exist" }
      else if !createIfMissing then
        .error { kind := .notFound, path := some lockPath, message := "lock file does not exist" }
      else if hasSimLockConflict s np mode then
        .ok none
      else
        .ok (some { s with
          files := (np, "") :: s.files
          heldLocks := (np, mode) :: s.heldLocks })

/-- Deterministic `FsApiM (StateM PoolSimState)` test and proof environment. -/
def simFs : FsApiM (StateM PoolSimState) :=
  { join := simJoin
    joinMany := fun parts => parts.foldl simJoin ""
    normPath := normSimPath
    parent := parentSimPath
    name := fun _ => none
    stem := fun _ => none
    suffix := fun _ => ""
    suffixes := fun _ => #[]
    withName := fun p _ => .ok p
    withSuffix := fun p _ => .ok p
    isAbsolute := fun p => p.startsWith "/"
    relativeTo := fun p _ => .ok p
    mapRawError := fun _ => { kind := .ioError, message := "sim raw error" }
    readText := fun p => do
      let s ← get
      let np := normSimPath p
      match s.files.find? (fun (fp, _) => fp == np) with
      | some (_, c) => return .ok c
      | none => return .error { kind := .notFound, path := some p, message := "file not found" }
    writeText := fun p c => do
      let s ← get
      let np := normSimPath p
      set { s with files := (np, c) :: s.files.filter (fun (fp, _) => fp != np) }
      return .ok ()
    appendText := fun p c => do
      let s ← get
      let np := normSimPath p
      set { s with files := (np, c) :: s.files.filter (fun (fp, _) => fp != np) }
      return .ok ()
    readBytes := fun _ => pure (.ok ByteArray.empty)
    writeBytes := fun _ _ => pure (.ok ())
    atomicWriteBytes := fun _ _ => pure (.ok ())
    atomicWriteText := fun _ _ => pure (.ok ())
    touch := fun p _ => do
      let s ← get
      let np := normSimPath p
      set { s with files := (np, "") :: s.files.filter (fun (fp, _) => fp != np) }
      return .ok ()
    mkdir := fun p parents existOk => do
      let s ← get
      match simMkdirPure s p parents existOk with
      | .error e => return .error e
      | .ok s' =>
        set s'
        return .ok ()
    unlink := fun p missingOk => do
      let s ← get
      let np := normSimPath p
      if np ∈ s.dirs then
        return .error { kind := .isADirectory, path := some p, message := "is a directory" }
      else if hasSimFile s np || np ∈ s.symlinks then
        set { s with
          files := s.files.filter (fun (fp, _) => fp != np)
          symlinks := s.symlinks.filter (· != np) }
        return .ok ()
      else if missingOk then
        return .ok ()
      else
        return .error { kind := .notFound, path := some p, message := "file not found" }
    rmdir := fun p => do
      let s ← get
      let np := normSimPath p
      if np ∈ s.dirs then
        set { s with dirs := s.dirs.filter (· != np) }
        return .ok ()
      else
        return .error { kind := .notFound, path := some p, message := "directory not found" }
    rmtree := fun p ignoreMissing => do
      let s ← get
      let np := normSimPath p
      if np ∈ s.dirs then
        set { s with dirs := s.dirs.filter (· != np) }
        return .ok ()
      else if ignoreMissing then
        return .ok ()
      else
        return .error { kind := .notFound, path := some p, message := "directory not found" }
    rename := fun _ _ => pure (.ok ())
    copyFile := fun _ _ => pure (.ok ())
    copyTree := fun _ _ _ => pure (.ok ())
    pathExists := fun p => do return .ok (simLstatPure (← get) p).isOk
    isFile := fun p => do
      match simLstatPure (← get) p with
      | .ok st => return .ok (st.kind == .file)
      | .error _ => return .ok false
    isDir := fun p => do
      match simLstatPure (← get) p with
      | .ok st => return .ok (st.kind == .dir)
      | .error _ => return .ok false
    isSymlink := fun p => do
      match simLstatPure (← get) p with
      | .ok st => return .ok (st.kind == .symlink)
      | .error _ => return .ok false
    stat := fun p => do return simLstatPure (← get) p
    lstat := fun p => do return simLstatPure (← get) p
    chmod := fun _ _ => pure (.ok ())
    symlink := fun _ linkPath => do
      let s ← get
      let np := normSimPath linkPath
      set { s with symlinks := np :: s.symlinks }
      return .ok ()
    readLink := fun _ => pure (.error { kind := .notFound, message := "no symlink" })
    resolve := fun p => pure (.ok (normSimPath p))
    cwd := pure (.ok "/")
    listDir := fun _ => pure (.ok #[])
    walk := fun _ => pure (.ok #[])
    glob := fun _ _ => pure (.ok #[])
    rglob := fun _ _ => pure (.ok #[])
    withFileLock := fun p mode createIfMissing action => do
      let s ← get
      match simTryAcquirePure s p mode createIfMissing with
      | .error e => return .error e
      | .ok none => return .error { kind := .wouldBlock, path := some p, message := "lock would block" }
      | .ok (some sLocked) =>
        let np := normSimPath p
        set sLocked
        let r ← action
        modify fun s' => { s' with heldLocks := removeFirstSimLock np mode s'.heldLocks }
        return r
    tryWithFileLock := fun p mode createIfMissing action => do
      let s ← get
      match simTryAcquirePure s p mode createIfMissing with
      | .error e => return .error e
      | .ok none => return .ok none
      | .ok (some sLocked) =>
        let np := normSimPath p
        set sLocked
        let r ← action
        modify fun s' => { s' with heldLocks := removeFirstSimLock np mode s'.heldLocks }
        return r.map some }

/-- Deterministic `TimeOpsM (StateM PoolSimState)` advancing `monoNanos` and recording `sleepLog` chunks on `sleep`. -/
def simTime : TimeOpsM (StateM PoolSimState) :=
  { nowTimestamp := pure (Std.Time.Timestamp.ofSecondsSinceUnixEpoch 0)
    monoNanosNow := do
      let s ← get
      return s.monoNanos
    sleep := fun ms =>
      modify fun s =>
        { s with
          monoNanos := s.monoNanos + ms.toNat * nanosecondsPerMs
          sleepLog := s.sleepLog.push ms } }

/-- Lifted `FsApiM (ExceptT String (StateM PoolSimState))` releasing held locks via `tryFinally'` on uncaught exceptions. -/
def simFsEx : FsApiM (ExceptT String (StateM PoolSimState)) :=
  { join := simFs.join
    joinMany := simFs.joinMany
    normPath := simFs.normPath
    parent := simFs.parent
    name := simFs.name
    stem := simFs.stem
    suffix := simFs.suffix
    suffixes := simFs.suffixes
    withName := simFs.withName
    withSuffix := simFs.withSuffix
    isAbsolute := simFs.isAbsolute
    relativeTo := simFs.relativeTo
    mapRawError := simFs.mapRawError
    readText := fun p => liftM (simFs.readText p)
    writeText := fun p c => liftM (simFs.writeText p c)
    appendText := fun p c => liftM (simFs.appendText p c)
    readBytes := fun p => liftM (simFs.readBytes p)
    writeBytes := fun p bs => liftM (simFs.writeBytes p bs)
    atomicWriteBytes := fun p bs => liftM (simFs.atomicWriteBytes p bs)
    atomicWriteText := fun p c => liftM (simFs.atomicWriteText p c)
    touch := fun p ex => liftM (simFs.touch p ex)
    mkdir := fun p par ex => liftM (simFs.mkdir p par ex)
    unlink := fun p m => liftM (simFs.unlink p m)
    rmdir := fun p => liftM (simFs.rmdir p)
    rmtree := fun p ign => liftM (simFs.rmtree p ign)
    rename := fun a b => liftM (simFs.rename a b)
    copyFile := fun a b => liftM (simFs.copyFile a b)
    copyTree := fun a b c => liftM (simFs.copyTree a b c)
    pathExists := fun p => liftM (simFs.pathExists p)
    isFile := fun p => liftM (simFs.isFile p)
    isDir := fun p => liftM (simFs.isDir p)
    isSymlink := fun p => liftM (simFs.isSymlink p)
    stat := fun p => liftM (simFs.stat p)
    lstat := fun p => liftM (simFs.lstat p)
    chmod := fun p m => liftM (simFs.chmod p m)
    symlink := fun a b => liftM (simFs.symlink a b)
    readLink := fun p => liftM (simFs.readLink p)
    resolve := fun p => liftM (simFs.resolve p)
    cwd := liftM simFs.cwd
    listDir := fun p => liftM (simFs.listDir p)
    walk := fun p => liftM (simFs.walk p)
    glob := fun a b => liftM (simFs.glob a b)
    rglob := fun a b => liftM (simFs.rglob a b)
    withFileLock := fun p mode createIfMissing action => do
      let s : PoolSimState ← get
      match simTryAcquirePure s p mode createIfMissing with
      | .error e => return .error e
      | .ok none => return .error { kind := .wouldBlock, path := some p, message := "lock would block" }
      | .ok (some sLocked) =>
        let np := normSimPath p
        liftM (set sLocked : StateM PoolSimState Unit)
        let (r, _) ← tryFinally' action (fun _ =>
          liftM (modify (fun (s' : PoolSimState) =>
            { s' with heldLocks := removeFirstSimLock np mode s'.heldLocks }) : StateM PoolSimState Unit))
        return r
    tryWithFileLock := fun p mode createIfMissing action => do
      let s : PoolSimState ← get
      match simTryAcquirePure s p mode createIfMissing with
      | .error e => return .error e
      | .ok none => return .ok none
      | .ok (some sLocked) =>
        let np := normSimPath p
        liftM (set sLocked : StateM PoolSimState Unit)
        let (r, _) ← tryFinally' action (fun _ =>
          liftM (modify (fun (s' : PoolSimState) =>
            { s' with heldLocks := removeFirstSimLock np mode s'.heldLocks }) : StateM PoolSimState Unit))
        return r.map some }

/-- Lifted `TimeOpsM (ExceptT String (StateM PoolSimState))` backed by `simTime`. -/
def simTimeEx : TimeOpsM (ExceptT String (StateM PoolSimState)) :=
  { nowTimestamp := liftM simTime.nowTimestamp
    monoNanosNow := liftM simTime.monoNanosNow
    sleep := fun ms => liftM (simTime.sleep ms) }

/-- Build external exclusive leases `(normSimPath (slotLockPath join poolDir i), releaseAtNs)` for all `i < count`. -/
def leasesBeforeSlot (join : String → String → String) (poolDir : String) (releaseAtNs : Nat) :
    Nat → List (String × Nat)
  | 0 => []
  | k + 1 =>
    (normSimPath (slotLockPath join poolDir k), releaseAtNs) ::
      leasesBeforeSlot join poolDir releaseAtNs k

/-- Build external leases for `0 .. count - 1` where `targetSlot` releases at `targetReleaseNs` and other slots release at `otherReleaseNs`. -/
def leasesWithTargetRelease (join : String → String → String) (poolDir : String)
    (targetSlot targetReleaseNs otherReleaseNs : Nat) : Nat → List (String × Nat)
  | 0 => []
  | k + 1 =>
    let rel := if k == targetSlot then targetReleaseNs else otherReleaseNs
    (normSimPath (slotLockPath join poolDir k), rel) ::
      leasesWithTargetRelease join poolDir targetSlot targetReleaseNs otherReleaseNs k

/-- Build external leases for `0 .. count - 1` where slots `< freeIdx` release at `lockedUntilNs` and slots `>= freeIdx` release at `targetReleaseNs`. -/
def leasesBeforeSlotUntil (join : String → String → String) (poolDir : String)
    (freeIdx targetReleaseNs lockedUntilNs : Nat) : Nat → List (String × Nat)
  | 0 => []
  | k + 1 =>
    let rel := if k < freeIdx then lockedUntilNs else targetReleaseNs
    (normSimPath (slotLockPath join poolDir k), rel) ::
      leasesBeforeSlotUntil join poolDir freeIdx targetReleaseNs lockedUntilNs k

/-- Expected ascending list of lock paths `<poolDir>/slot-<i>.lock` for `rem` slots starting at `nextIdx`. -/
def expectedSlotPaths (join : String → String → String) (poolDir : String) (nextIdx : Nat) : Nat → List String
  | 0 => []
  | rem + 1 => slotLockPath join poolDir nextIdx :: expectedSlotPaths join poolDir (nextIdx + 1) rem

/-- Expected sequence of `UInt32` sleep chunks emitted across `remMs` milliseconds in steps of `pollIntervalMs`. -/
def expectedWaitUpToChunks (pollIntervalMs : Nat) : Nat → Nat → List UInt32
  | 0, _ => []
  | _ + 1, 0 => []
  | fuel + 1, remMs =>
    let dur := Nat.min pollIntervalMs remMs
    sleepChunks dur ++ expectedWaitUpToChunks pollIntervalMs fuel (remMs - dur)

/-- Canonical `UInt32` sleep-chunk log for an expiring `WaitPolicy.waitUpTo timeoutMs` call on a contended pool. -/
def expectedPollSleepLog (pollIntervalMs timeoutMs : Nat) : List UInt32 :=
  expectedWaitUpToChunks pollIntervalMs (timeoutMs + 1) timeoutMs

/-- Concatenate `rounds` copies of `sleepChunks pollIntervalMs` for `WaitPolicy.waitForever` verification. -/
def repeatSleepChunks (pollIntervalMs : Nat) : Nat → List UInt32
  | 0 => []
  | r + 1 => sleepChunks pollIntervalMs ++ repeatSleepChunks pollIntervalMs r

/-- Lift a `StateM S` computation onto the first component of `StateM (S × Aux)`. -/
def liftStateFirst {S Aux α : Type} (act : StateM S α) : StateM (S × Aux) α :=
  StateT.mk fun (s, aux) =>
    let (a, s') := act.run s
    (a, (s', aux))

/-- Lift an `FsApiM (StateM S)` bundle onto the first component of `StateM (S × Aux)`. -/
def liftFsFirst {S Aux : Type} (fs : FsApiM (StateM S)) : FsApiM (StateM (S × Aux)) :=
  { join := fs.join
    joinMany := fs.joinMany
    normPath := fs.normPath
    parent := fs.parent
    name := fs.name
    stem := fs.stem
    suffix := fs.suffix
    suffixes := fs.suffixes
    withName := fs.withName
    withSuffix := fs.withSuffix
    isAbsolute := fs.isAbsolute
    relativeTo := fs.relativeTo
    mapRawError := fs.mapRawError
    readText := fun p => liftStateFirst (fs.readText p)
    writeText := fun p c => liftStateFirst (fs.writeText p c)
    appendText := fun p c => liftStateFirst (fs.appendText p c)
    readBytes := fun p => liftStateFirst (fs.readBytes p)
    writeBytes := fun p bs => liftStateFirst (fs.writeBytes p bs)
    atomicWriteBytes := fun p bs => liftStateFirst (fs.atomicWriteBytes p bs)
    atomicWriteText := fun p c => liftStateFirst (fs.atomicWriteText p c)
    touch := fun p ex => liftStateFirst (fs.touch p ex)
    mkdir := fun p par ex => liftStateFirst (fs.mkdir p par ex)
    unlink := fun p m => liftStateFirst (fs.unlink p m)
    rmdir := fun p => liftStateFirst (fs.rmdir p)
    rmtree := fun p ign => liftStateFirst (fs.rmtree p ign)
    rename := fun a b => liftStateFirst (fs.rename a b)
    copyFile := fun a b => liftStateFirst (fs.copyFile a b)
    copyTree := fun a b c => liftStateFirst (fs.copyTree a b c)
    pathExists := fun p => liftStateFirst (fs.pathExists p)
    isFile := fun p => liftStateFirst (fs.isFile p)
    isDir := fun p => liftStateFirst (fs.isDir p)
    isSymlink := fun p => liftStateFirst (fs.isSymlink p)
    stat := fun p => liftStateFirst (fs.stat p)
    lstat := fun p => liftStateFirst (fs.lstat p)
    chmod := fun p m => liftStateFirst (fs.chmod p m)
    symlink := fun a b => liftStateFirst (fs.symlink a b)
    readLink := fun p => liftStateFirst (fs.readLink p)
    resolve := fun p => liftStateFirst (fs.resolve p)
    cwd := liftStateFirst fs.cwd
    listDir := fun p => liftStateFirst (fs.listDir p)
    walk := fun p => liftStateFirst (fs.walk p)
    glob := fun a b => liftStateFirst (fs.glob a b)
    rglob := fun a b => liftStateFirst (fs.rglob a b)
    withFileLock := fun p mode createIfMissing action =>
      StateT.mk fun (s, aux) =>
        let (r, s') := (fs.withFileLock p mode createIfMissing
          (StateT.mk fun st =>
            let (ar, (st', _)) := action.run (st, aux)
            (ar, st'))).run s
        (r, (s', aux))
    tryWithFileLock := fun p mode createIfMissing action =>
      StateT.mk fun (s, aux) =>
        let (r, s') := (fs.tryWithFileLock p mode createIfMissing
          (StateT.mk fun st =>
            let (ar, (st', _)) := action.run (st, aux)
            (ar, st'))).run s
        (r, (s', aux)) }

/-- Lift a `TimeOpsM (StateM S)` bundle onto the first component of `StateM (S × Aux)`. -/
def liftTimeFirst {S Aux : Type} (time : TimeOpsM (StateM S)) : TimeOpsM (StateM (S × Aux)) :=
  { nowTimestamp := liftStateFirst time.nowTimestamp
    monoNanosNow := liftStateFirst time.monoNanosNow
    sleep := fun ms => liftStateFirst (time.sleep ms) }

end LeanSwe.SlotPool.Model
