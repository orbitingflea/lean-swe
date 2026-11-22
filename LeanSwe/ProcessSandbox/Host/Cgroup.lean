import LeanSwe.LinuxSyscall.Common.Types
import LeanSwe.LinuxSyscall.Files.Types
import LeanSwe.LinuxSyscall.TimeRand.Types
import LeanSwe.Process.SysBridge

namespace LeanSwe.ProcessSandbox.Host.Cgroup

open LeanSwe.LinuxSyscall
open LeanSwe.Process.SysBridge

/-- Maximum number of `cgroup.events` poll iterations (`200 × 2 ms`) during cgroup teardown. -/
def CGROUP_POLL_STEPS : Nat := 200

/-- Maximum number of `EBUSY`-retrying `rmdir` attempts (`200 × 2 ms`) during cgroup teardown. -/
def CGROUP_RMDIR_STEPS : Nat := 200

/-- Sleep interval in milliseconds between cgroup teardown poll/retry iterations. -/
def CGROUP_RETRY_SLEEP_MS : Nat := 2

/-- Maximum bytes read from `/proc/self/cgroup` or `cgroup.events`. -/
def CGROUP_READ_CAP : Nat := 4096

/-- Construct a child control file path beneath `cgDir`. -/
def cgroupSubfile (cgDir name : String) : String :=
  s!"{cgDir}/{name}"

/-- Construct a unique per-box sibling cgroup directory path beneath `parent`. -/
def cgroupDirName (parent : String) (pid : UInt32) (seq : Nat) : String :=
  s!"{parent}/leanswe-psandbox-{pid}-{seq}"

/-- Compute the `pids.max` value written to cgroup v2 (`pidsMax + 2` for `bwrap --as-pid-1` wrapper tasks, saturating at `2^64 - 1`). -/
def cappedPidsMax (pidsMax : Nat) : Nat :=
  Nat.min (pidsMax + 2) (UInt64.size - 1)

/-- Accumulator helper splitting a character list on `sep`. -/
def splitCharAux (sep : Char) (acc : List Char) : List Char → List (List Char)
  | [] => [acc.reverse]
  | c :: cs =>
    if c == sep then acc.reverse :: splitCharAux sep [] cs
    else splitCharAux sep (c :: acc) cs

/-- Split character list `cs` on separator `sep`. -/
def splitChar (sep : Char) (cs : List Char) : List (List Char) :=
  splitCharAux sep [] cs

/-- Return `true` iff `needle` occurs as a contiguous sublist of `haystack`. -/
def hasSublistChars (needle : List Char) : List Char → Bool
  | [] => needle.isEmpty
  | c :: cs => needle.isPrefixOf (c :: cs) || hasSublistChars needle cs

/-- Strip a single trailing ASCII `'\r'` from a line's character list. -/
def stripTrailingCrChars (cs : List Char) : List Char :=
  match cs.reverse with
  | '\r' :: rest => rest.reverse
  | _ => cs

/-- Strip trailing `'/'` characters from a character list while preserving `"/"`. -/
def stripTrailingSlashesChars (cs : List Char) : List Char :=
  let rec dropRev : List Char → List Char
    | ['/'] => ['/']
    | '/' :: rest => dropRev rest
    | other => other
  (dropRev cs.reverse).reverse

/-- Compute the parent relative path of an absolute slash-prefixed cgroup v2 path (`""` for top-level entries). -/
def parentRelPath (v2Rel : String) : String :=
  let trimmed := stripTrailingSlashesChars v2Rel.toList
  let segs := (splitChar '/' trimmed).map String.ofList
  match segs.reverse with
  | [] => ""
  | [_] => ""
  | _ :: restRev =>
    let joined := String.intercalate "/" restRev.reverse
    if joined == "" then "" else joined

/-- Parse `/proc/self/cgroup` text to locate the delegated parent directory under `/sys/fs/cgroup`. -/
def parseDelegatedCgroupParent (procCgroupText : String) : Option String :=
  let lines := splitChar '\n' procCgroupText.toList
  let v2Rel? := lines.findSome? fun rawLine =>
    let line := stripTrailingCrChars rawLine
    if ['0', ':', ':'].isPrefixOf line then
      some (String.ofList (line.drop 3))
    else
      none
  match v2Rel? with
  | none => none
  | some v2Rel =>
    if v2Rel.toList.head? != some '/' then
      none
    else
      let parentRel := parentRelPath v2Rel
      if parentRel.isEmpty then
        some "/sys/fs/cgroup"
      else
        some ("/sys/fs/cgroup" ++ parentRel)

/-- Return `true` iff `cgroup.events` text reports `"populated 0"`. -/
def isPopulatedZero (eventsText : String) : Bool :=
  hasSublistChars "populated 0".toList eventsText.toList

/-- Write all bytes of `data[off..]` to `h`, retrying `EINTR` and advancing across partial writes. -/
def writeAllFd {m : Type → Type} [Monad m] {fd : Type}
    (files : Files.FilesOpsM m fd) (h : fd) (data : ByteArray) :
    Nat → Nat → m (Except Errno Unit)
  | off, 0 =>
    if off ≥ data.size then pure (.ok ()) else pure (.error Errno.EIO)
  | off, fuel + 1 => do
    if off ≥ data.size then
      return .ok ()
    else
      let slice := if off == 0 then data else data.extract off data.size
      match ← files.write h slice with
      | .ok n =>
        if n == 0 then
          return .error Errno.EIO
        else
          writeAllFd files h data (off + n.toNat) fuel
      | .error e =>
        if e == Errno.EINTR then
          writeAllFd files h data off fuel
        else
          return .error e

/-- Open `path` write-only with `O_CLOEXEC`, write `text` completely, and close the descriptor. -/
def writeTextFile {m : Type → Type} [Monad m] {fd : Type}
    (files : Files.FilesOpsM m fd) (path text : String)
    (eintrFuel : Nat := DEFAULT_EINTR_FUEL) : m (Except Errno Unit) := do
  match ← retryEintr (files.openat none path.toUTF8 { access := .wronly, cloexec := true } 0) eintrFuel with
  | .error e => return .error e
  | .ok h =>
    let res ← writeAllFd files h text.toUTF8 0 eintrFuel
    closeOpt files (some h)
    return res

/-- Read up to `maxBytes` from open descriptor `h` until `EOF` or cap, retrying `EINTR`. -/
def readBoundedLoop {m : Type → Type} [Monad m] {fd : Type}
    (files : Files.FilesOpsM m fd) (h : fd) (maxBytes : Nat) :
    Array ByteArray → Nat → Nat → m (Except Errno ByteArray)
  | chunks, total, 0 => pure (.ok (concatChunks chunks total))
  | chunks, total, fuel + 1 => do
    if total ≥ maxBytes then
      return .ok (concatChunks chunks total)
    else
      let want := Nat.min (maxBytes - total) 4096
      match ← files.read h (UInt32.ofNat want) with
      | .ok bs =>
        if bs.size == 0 then
          return .ok (concatChunks chunks total)
        else
          readBoundedLoop files h maxBytes (chunks.push bs) (total + bs.size) fuel
      | .error e =>
        if e == Errno.EINTR then
          readBoundedLoop files h maxBytes chunks total fuel
        else
          return .error e

/-- Open `path` read-only with `O_CLOEXEC`, read up to `maxBytes`, and close the descriptor. -/
def readSmallFile {m : Type → Type} [Monad m] {fd : Type}
    (files : Files.FilesOpsM m fd) (path : String) (maxBytes : Nat := CGROUP_READ_CAP)
    (eintrFuel : Nat := DEFAULT_EINTR_FUEL) : m (Except Errno ByteArray) := do
  match ← retryEintr (files.openat none path.toUTF8 { access := .rdonly, cloexec := true } 0) eintrFuel with
  | .error e => return .error e
  | .ok h =>
    let res ← readBoundedLoop files h maxBytes #[] 0 eintrFuel
    closeOpt files (some h)
    return res

/-- Read `/proc/self/cgroup` and resolve the delegated parent directory under `/sys/fs/cgroup`. -/
def findDelegatedCgroupParent {m : Type → Type} [Monad m] {fd : Type}
    (files : Files.FilesOpsM m fd) (eintrFuel : Nat := DEFAULT_EINTR_FUEL) :
    m (Except Errno String) := do
  match ← readSmallFile files "/proc/self/cgroup" CGROUP_READ_CAP eintrFuel with
  | .error e => return .error e
  | .ok raw =>
    match String.fromUTF8? raw with
    | none => return .error Errno.ENOENT
    | some text =>
      match parseDelegatedCgroupParent text with
      | some parent => return .ok parent
      | none => return .error Errno.ENOENT

/-- Create a fresh sibling cgroup v2 directory under the caller's delegated `/sys/fs/cgroup` parent. -/
def createSiblingCgroup {m : Type → Type} [Monad m] {fd : Type}
    (files : Files.FilesOpsM m fd) (pid : UInt32) (seq : Nat)
    (eintrFuel : Nat := DEFAULT_EINTR_FUEL) : m (Except Errno String) := do
  match ← findDelegatedCgroupParent files eintrFuel with
  | .error e => return .error e
  | .ok parent =>
    let cgDir := cgroupDirName parent pid seq
    match ← retryEintr (files.mkdirat none cgDir.toUTF8 0o755) eintrFuel with
    | .error e => return .error e
    | .ok () => return .ok cgDir

/-- Configure `memory.max`, optional `memory.swap.max = "0"`, and optional `memory.oom.group = "1"` (ignoring `ENOENT` on the two optional control files). -/
def configureCgroupMemory {m : Type → Type} [Monad m] {fd : Type}
    (files : Files.FilesOpsM m fd) (cgDir memLimit : String)
    (eintrFuel : Nat := DEFAULT_EINTR_FUEL) : m (Except (String × Errno) Unit) := do
  match ← writeTextFile files (cgroupSubfile cgDir "memory.max") memLimit eintrFuel with
  | .error e => return .error ("memory.max", e)
  | .ok () =>
    match ← writeTextFile files (cgroupSubfile cgDir "memory.swap.max") "0" eintrFuel with
    | .error e =>
      if e != Errno.ENOENT then
        return .error ("memory.swap.max", e)
    | .ok () => pure ()
    match ← writeTextFile files (cgroupSubfile cgDir "memory.oom.group") "1" eintrFuel with
    | .error e =>
      if e != Errno.ENOENT then
        return .error ("memory.oom.group", e)
    | .ok () => pure ()
    return .ok ()

/-- Configure `pids.max` inside `cgDir`. -/
def configureCgroupPids {m : Type → Type} [Monad m] {fd : Type}
    (files : Files.FilesOpsM m fd) (cgDir pidsLimit : String)
    (eintrFuel : Nat := DEFAULT_EINTR_FUEL) : m (Except Errno Unit) :=
  writeTextFile files (cgroupSubfile cgDir "pids.max") pidsLimit eintrFuel

/-- Poll `cgroup.events` until `"populated 0"` is observed, `openat` fails, or `steps` elapse. -/
def pollCgroupUnpopulated {m : Type → Type} [Monad m] {fd : Type}
    (files : Files.FilesOpsM m fd) (timeRand : TimeRand.TimeRandOpsM m)
    (eventsPath : String) (eintrFuel : Nat) : Nat → m Unit
  | 0 => pure ()
  | steps + 1 => do
    match ← readSmallFile files eventsPath 256 eintrFuel with
    | .error _ => pure ()
    | .ok raw =>
      match String.fromUTF8? raw with
      | some text =>
        if isPopulatedZero text then
          pure ()
        else do
          sleepMonoMs timeRand CGROUP_RETRY_SLEEP_MS
          pollCgroupUnpopulated files timeRand eventsPath eintrFuel steps
      | none =>
        sleepMonoMs timeRand CGROUP_RETRY_SLEEP_MS
        pollCgroupUnpopulated files timeRand eventsPath eintrFuel steps

/-- Retry `rmdir` (`unlinkat removeDir := true`) on `EBUSY` or `EINTR` up to `steps` additional times. -/
def retryRmdirCgroup {m : Type → Type} [Monad m] {fd : Type}
    (files : Files.FilesOpsM m fd) (timeRand : TimeRand.TimeRandOpsM m)
    (cgDirBytes : ByteArray) : Nat → m (Except Errno Unit)
  | 0 => do
    match ← files.unlinkat none cgDirBytes true with
    | .ok () => return .ok ()
    | .error e => if e == Errno.ENOENT then return .ok () else return .error e
  | steps + 1 => do
    match ← files.unlinkat none cgDirBytes true with
    | .ok () => return .ok ()
    | .error e =>
      if e == Errno.ENOENT then
        return .ok ()
      else if e == Errno.EBUSY || e == Errno.EINTR then
        sleepMonoMs timeRand CGROUP_RETRY_SLEEP_MS
        retryRmdirCgroup files timeRand cgDirBytes steps
      else
        return .error e

/-- Write `cgroup.kill = "1"`, poll `cgroup.events` until `"populated 0"`, and `rmdir` `cgDir` with bounded `EBUSY` retries. -/
def cleanupCgroupDir {m : Type → Type} [Monad m] {fd : Type}
    (files : Files.FilesOpsM m fd) (timeRand : TimeRand.TimeRandOpsM m)
    (cgDir : String)
    (pollSteps : Nat := CGROUP_POLL_STEPS)
    (rmdirSteps : Nat := CGROUP_RMDIR_STEPS)
    (eintrFuel : Nat := DEFAULT_EINTR_FUEL) : m (Except Errno Unit) := do
  if cgDir.isEmpty then
    return .ok ()
  let _ ← writeTextFile files (cgroupSubfile cgDir "cgroup.kill") "1" eintrFuel
  pollCgroupUnpopulated files timeRand (cgroupSubfile cgDir "cgroup.events") eintrFuel pollSteps
  retryRmdirCgroup files timeRand cgDir.toUTF8 rmdirSteps

end LeanSwe.ProcessSandbox.Host.Cgroup
