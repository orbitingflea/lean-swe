import LeanSwe.LinuxSyscall.Common.Types
import LeanSwe.LinuxSyscall.Files.Types
import LeanSwe.LinuxSyscall.Files.Model
import LeanSwe.LinuxSyscall.Files.Seed
import LeanSwe.LinuxSyscall.Files.Interface
import LeanSwe.LinuxSyscall.Files.Impl
import Fuzz.LinuxSyscall.Files.Strace
import Fuzz.LinuxSyscall.Rng
import Fuzz.LinuxSyscall.Env
import Std.Data.HashMap

namespace Fuzz.LinuxSyscall.FilesFuzz

open LeanSwe.LinuxSyscall
open LeanSwe.LinuxSyscall.Files

local instance : Repr ByteArray where
  reprPrec b _ := f!"ByteArray.mk {repr b.data}"

/-- Symbolic handle identifier used inside shrinkable fuzz traces. -/
abbrev SymFd := Nat

/-- Symbolic file syscall request referencing `SymFd` slots instead of live `RawFd` values. -/
inductive SymReq where
  /-- Symbolic `openat` syscall request. -/
  | openat (dir : Option SymFd) (path : ByteArray) (flags : OpenFlags) (mode : Mode)
  /-- Symbolic `openat2` syscall request. -/
  | openat2 (dir : Option SymFd) (path : ByteArray) (how : OpenHow)
  /-- Symbolic `close` syscall request. -/
  | close (fd : SymFd)
  /-- Symbolic `read` syscall request. -/
  | read (fd : SymFd) (maxBytes : UInt32)
  /-- Symbolic `write` syscall request. -/
  | write (fd : SymFd) (data : ByteArray)
  /-- Symbolic `fstat` syscall request. -/
  | fstat (fd : SymFd)
  /-- Symbolic `fstatat` syscall request. -/
  | fstatat (dir : Option SymFd) (path : ByteArray) (flags : AtFlags)
  /-- Symbolic `faccessat` syscall request. -/
  | faccessat (dir : Option SymFd) (path : ByteArray) (mode : AccessModeMask) (flags : AtFlags)
  /-- Symbolic `mkdirat` syscall request. -/
  | mkdirat (dir : Option SymFd) (path : ByteArray) (mode : Mode)
  /-- Symbolic `unlinkat` syscall request. -/
  | unlinkat (dir : Option SymFd) (path : ByteArray) (removeDir : Bool)
  /-- Symbolic `renameat2` syscall request. -/
  | renameat2 (oldDir : Option SymFd) (oldPath : ByteArray)
      (newDir : Option SymFd) (newPath : ByteArray) (flags : RenameFlags)
  /-- Symbolic `symlinkat` syscall request. -/
  | symlinkat (target : ByteArray) (newDir : Option SymFd) (linkPath : ByteArray)
  /-- Symbolic `readlinkat` syscall request. -/
  | readlinkat (dir : Option SymFd) (path : ByteArray) (maxBytes : UInt32)
  /-- Symbolic `getdents64` syscall request. -/
  | getdents64 (fd : SymFd) (maxBytes : UInt32)
  /-- Symbolic `fchmodat` syscall request. -/
  | fchmodat (dir : Option SymFd) (path : ByteArray) (mode : Mode)
  /-- Symbolic `fchmod` syscall request. -/
  | fchmod (fd : SymFd) (mode : Mode)
  /-- Symbolic `flock` syscall request. -/
  | flock (fd : SymFd) (op : FlockOp)
  /-- Symbolic `fcntl` syscall request. -/
  | fcntl (fd : SymFd) (cmd : FcntlCmd)
  /-- Symbolic `fsync` syscall request. -/
  | fsync (fd : SymFd)
  /-- Symbolic `getcwd` syscall request. -/
  | getcwd (maxBytes : UInt32)
  /-- Symbolic `lseek` syscall request. -/
  | lseek (fd : SymFd) (offset : Int64) (whence : SeekWhence)
  /-- Symbolic `reopenReadOnly` syscall request. -/
  | reopenReadOnly (fd : SymFd)
  /-- Symbolic `dupStdio` syscall request. -/
  | dupStdio (slot : StdioFd)
  deriving Repr

/-- Whether executing this symbolic request allocates a new file descriptor on success. -/
def SymReq.isAlloc : SymReq → Bool
  | .openat .. | .openat2 .. | .reopenReadOnly _ | .dupStdio _ => true
  | _ => false

/-- Recorded step in a fuzzing episode with its symbolic handle allocation ID if opened. -/
structure SymStep where
  /-- Symbolic handle ID assigned when this step is an FD-allocating request. -/
  allocId : Option SymFd
  /-- Syscall request executed at this step. -/
  req : SymReq
  deriving Repr

/-- Canonical string name for a `FilesErrorKind` bucket. -/
def filesErrorKindName : FilesErrorKind -> String
  | .notFound => "notFound"
  | .badFd => "badFd"
  | .invalidArg => "invalidArg"
  | .stateConflict => "stateConflict"
  | .permissionDenied => "permissionDenied"
  | .transientOrResource => "transientOrResource"

/-- Per-(syscall, outcome) counter table accumulated across episodes. -/
structure HitStats where
  /-- Counts keyed by `"<syscall>:<ok|err(errno)>"`. -/
  counts : Std.HashMap String Nat := {}
  /-- Counts keyed by `"<syscall>:<ok|FilesErrorKind>"`. -/
  kindCounts : Std.HashMap String Nat := {}
  /-- Total syscalls executed. -/
  totalSteps : Nat := 0
  /-- Total episodes executed. -/
  totalEpisodes : Nat := 0

/-- Record one syscall outcome into `HitStats`. -/
def HitStats.record (st : HitStats) (syscallName : String) (out : FilesOutcome) : HitStats :=
  let (bucket, kindKey) := match out with
    | .err e =>
      (s!"{syscallName}:err({e})", s!"{syscallName}:{filesErrorKindName (FilesErrorKind.ofErrno e)}")
    | _ => (s!"{syscallName}:ok", s!"{syscallName}:ok")
  let prev := st.counts.getD bucket 0
  let prevKind := st.kindCounts.getD kindKey 0
  { counts := st.counts.insert bucket (prev + 1)
    kindCounts := st.kindCounts.insert kindKey (prevKind + 1)
    totalSteps := st.totalSteps + 1
    totalEpisodes := st.totalEpisodes }

/-- Merge two `HitStats` tables cleanly. -/
def HitStats.merge (a b : HitStats) : HitStats :=
  let counts' := b.counts.fold (fun acc k v => acc.insert k (acc.getD k 0 + v)) a.counts
  let kindCounts' := b.kindCounts.fold (fun acc k v => acc.insert k (acc.getD k 0 + v)) a.kindCounts
  { counts := counts'
    kindCounts := kindCounts'
    totalSteps := a.totalSteps + b.totalSteps
    totalEpisodes := a.totalEpisodes + b.totalEpisodes }

/-- Canonical syscall name for reporting and coverage assertions. -/
def symReqName : SymReq -> String
  | .openat .. => "openat"
  | .openat2 .. => "openat2"
  | .close .. => "close"
  | .read .. => "read"
  | .write .. => "write"
  | .fstat .. => "fstat"
  | .fstatat .. => "fstatat"
  | .faccessat .. => "faccessat"
  | .mkdirat .. => "mkdirat"
  | .unlinkat .. => "unlinkat"
  | .renameat2 .. => "renameat2"
  | .symlinkat .. => "symlinkat"
  | .readlinkat .. => "readlinkat"
  | .getdents64 .. => "getdents64"
  | .fchmodat .. => "fchmodat"
  | .fchmod .. => "fchmod"
  | .flock .. => "flock"
  | .fcntl .. => "fcntl"
  | .fsync .. => "fsync"
  | .getcwd .. => "getcwd"
  | .lseek .. => "lseek"
  | .reopenReadOnly .. => "reopenReadOnly"
  | .dupStdio .. => "dupStdio"

/-- List of all 23 syscall names expected in coverage checks. -/
def allSyscallNames : Array String := #[
  "openat", "openat2", "close", "read", "write",
  "fstat", "fstatat", "faccessat", "mkdirat", "unlinkat",
  "renameat2", "symlinkat", "readlinkat", "getdents64", "fchmodat",
  "fchmod", "flock", "fcntl", "fsync", "getcwd",
  "lseek", "reopenReadOnly", "dupStdio"
]

private def optSymFdToHid (m : Std.HashMap SymFd HandleId) : Option SymFd -> Option (Option HandleId)
  | none => some none
  | some s => (m.get? s).map some

private def symReqToFilesReq (m : Std.HashMap SymFd HandleId) : SymReq -> Option FilesReq
  | .openat dir p f mode => (optSymFdToHid m dir).map fun d => .openat d p f mode
  | .openat2 dir p how => (optSymFdToHid m dir).map fun d => .openat2 d p how
  | .close fd => (m.get? fd).map .close
  | .read fd n => (m.get? fd).map (FilesReq.read · n)
  | .write fd d => (m.get? fd).map (FilesReq.write · d)
  | .fstat fd => (m.get? fd).map .fstat
  | .fstatat dir p f => (optSymFdToHid m dir).map fun d => .fstatat d p f
  | .faccessat dir p mode f => (optSymFdToHid m dir).map fun d => .faccessat d p mode f
  | .mkdirat dir p mode => (optSymFdToHid m dir).map fun d => .mkdirat d p mode
  | .unlinkat dir p r => (optSymFdToHid m dir).map fun d => .unlinkat d p r
  | .renameat2 od op nd np f => do
    let od' ← optSymFdToHid m od
    let nd' ← optSymFdToHid m nd
    pure (.renameat2 od' op nd' np f)
  | .symlinkat t nd lp => (optSymFdToHid m nd).map fun d => .symlinkat t d lp
  | .readlinkat dir p n => (optSymFdToHid m dir).map fun d => .readlinkat d p n
  | .getdents64 fd n => (m.get? fd).map (FilesReq.getdents64 · n)
  | .fchmodat dir p mode => (optSymFdToHid m dir).map fun d => .fchmodat d p mode
  | .fchmod fd mode => (m.get? fd).map (FilesReq.fchmod · mode)
  | .flock fd op => (m.get? fd).map (FilesReq.flock · op)
  | .fcntl fd cmd => (m.get? fd).map (FilesReq.fcntl · cmd)
  | .fsync fd => (m.get? fd).map .fsync
  | .getcwd n => some (.getcwd n)
  | .lseek fd off w => (m.get? fd).map (FilesReq.lseek · off w)
  | .reopenReadOnly fd => (m.get? fd).map .reopenReadOnly
  | .dupStdio slot => some (.dupStdio slot)

private def procFdSymPrefix : ByteArray := "/proc/self/fd/@".toUTF8
private def procFdRealPrefix : String := "/proc/self/fd/"

private def decodeSymProcFd (p : ByteArray) : Option (SymFd × ByteArray) :=
  if p.data.size <= procFdSymPrefix.data.size || !startsWithBytes p procFdSymPrefix then
    none
  else Id.run do
    let mut i := procFdSymPrefix.data.size
    let mut sid : Nat := 0
    let mut digits : Nat := 0
    while h : i < p.data.size do
      let b := p.data[i]
      if b >= 48 && b <= 57 then
        sid := sid * 10 + (b.toNat - 48)
        digits := digits + 1
        i := i + 1
      else
        break
    if digits == 0 then
      return none
    else if i < p.data.size && p.data[i]! != 47 then
      return none
    else
      let suffix := ByteArray.mk (p.data.extract i p.data.size)
      return some (sid, suffix)

private def resolveSymProcFdPath (procFdMap : Std.HashMap SymFd Nat) (p : ByteArray) : ByteArray :=
  match decodeSymProcFd p with
  | none => p
  | some (sid, suffix) =>
    match procFdMap.get? sid with
    | some rawNum => (procFdRealPrefix ++ toString rawNum).toUTF8 ++ suffix
    | none => p

private def remapSymPath (m : Std.HashMap SymFd SymFd) (p : ByteArray) : Option ByteArray :=
  match decodeSymProcFd p with
  | none => some p
  | some (sid, suffix) =>
    (m.get? sid).map fun sid' => ("/proc/self/fd/@" ++ toString sid').toUTF8 ++ suffix

private def resolveSymProcFdReq (m : Std.HashMap SymFd Nat) : SymReq → SymReq
  | .openat dir p f mode => .openat dir (resolveSymProcFdPath m p) f mode
  | .openat2 dir p how => .openat2 dir (resolveSymProcFdPath m p) how
  | .fstatat dir p f => .fstatat dir (resolveSymProcFdPath m p) f
  | .faccessat dir p mode f => .faccessat dir (resolveSymProcFdPath m p) mode f
  | .mkdirat dir p mode => .mkdirat dir (resolveSymProcFdPath m p) mode
  | .unlinkat dir p r => .unlinkat dir (resolveSymProcFdPath m p) r
  | .renameat2 od op nd np f =>
    .renameat2 od (resolveSymProcFdPath m op) nd (resolveSymProcFdPath m np) f
  | .symlinkat t nd lp => .symlinkat (resolveSymProcFdPath m t) nd (resolveSymProcFdPath m lp)
  | .readlinkat dir p n => .readlinkat dir (resolveSymProcFdPath m p) n
  | .fchmodat dir p mode => .fchmodat dir (resolveSymProcFdPath m p) mode
  | r => r

private def remapOptSymFd (m : Std.HashMap SymFd SymFd) : Option SymFd -> Option (Option SymFd)
  | none => some none
  | some s => (m.get? s).map some

private def remapSymReq (m : Std.HashMap SymFd SymFd) : SymReq -> Option SymReq
  | .openat dir p f mode => do
    let d' ← remapOptSymFd m dir
    let p' ← remapSymPath m p
    pure (.openat d' p' f mode)
  | .openat2 dir p how => do
    let d' ← remapOptSymFd m dir
    let p' ← remapSymPath m p
    pure (.openat2 d' p' how)
  | .close fd => (m.get? fd).map SymReq.close
  | .read fd n => (m.get? fd).map (SymReq.read · n)
  | .write fd d => (m.get? fd).map (SymReq.write · d)
  | .fstat fd => (m.get? fd).map SymReq.fstat
  | .fstatat dir p f => do
    let d' ← remapOptSymFd m dir
    let p' ← remapSymPath m p
    pure (.fstatat d' p' f)
  | .faccessat dir p mode f => do
    let d' ← remapOptSymFd m dir
    let p' ← remapSymPath m p
    pure (.faccessat d' p' mode f)
  | .mkdirat dir p mode => do
    let d' ← remapOptSymFd m dir
    let p' ← remapSymPath m p
    pure (.mkdirat d' p' mode)
  | .unlinkat dir p r => do
    let d' ← remapOptSymFd m dir
    let p' ← remapSymPath m p
    pure (.unlinkat d' p' r)
  | .renameat2 od op nd np f => do
    let od' <- remapOptSymFd m od
    let nd' <- remapOptSymFd m nd
    let op' ← remapSymPath m op
    let np' ← remapSymPath m np
    pure (.renameat2 od' op' nd' np' f)
  | .symlinkat t nd lp => do
    let t' ← remapSymPath m t
    let nd' ← remapOptSymFd m nd
    let lp' ← remapSymPath m lp
    pure (.symlinkat t' nd' lp')
  | .readlinkat dir p n => do
    let d' ← remapOptSymFd m dir
    let p' ← remapSymPath m p
    pure (.readlinkat d' p' n)
  | .getdents64 fd n => (m.get? fd).map (SymReq.getdents64 · n)
  | .fchmodat dir p mode => do
    let d' ← remapOptSymFd m dir
    let p' ← remapSymPath m p
    pure (.fchmodat d' p' mode)
  | .fchmod fd mode => (m.get? fd).map (SymReq.fchmod · mode)
  | .flock fd op => (m.get? fd).map (SymReq.flock · op)
  | .fcntl fd cmd => (m.get? fd).map (SymReq.fcntl · cmd)
  | .fsync fd => (m.get? fd).map SymReq.fsync
  | .getcwd n => some (.getcwd n)
  | .lseek fd off w => (m.get? fd).map (SymReq.lseek · off w)
  | .reopenReadOnly fd => (m.get? fd).map SymReq.reopenReadOnly
  | .dupStdio slot => some (.dupStdio slot)

/-- Compact a trace after deletion, dropping dependent steps and renumbering `SymFd` sequentially from `preSeeded`. -/
def renumberTrace (steps : Array SymStep) (preSeeded : Nat := 0) : Array SymStep := Id.run do
  let mut out : Array SymStep := #[]
  let mut idMap : Std.HashMap SymFd SymFd := {}
  for s in [:preSeeded] do
    idMap := idMap.insert s s
  let mut nextId : SymFd := preSeeded
  for step in steps do
    match remapSymReq idMap step.req with
    | none => pure ()
    | some req' =>
      let isAlloc := req'.isAlloc
      if isAlloc then
        let newAlloc := nextId
        match step.allocId with
        | some oldId => idMap := idMap.insert oldId newAlloc
        | none => pure ()
        nextId := nextId + 1
        out := out.push { allocId := some newAlloc, req := req' }
      else
        out := out.push { allocId := none, req := req' }
  return out

private def shrinkPathCandidates (p : ByteArray) : Array ByteArray := Id.run do
  if p.size <= 1 then return #[]
  let mut out : Array ByteArray := #[]
  let short := "a".toUTF8
  if p != short then
    out := out.push short
  if let some idx := p.data.findIdx? (· == 47) then
    let tail := p.extract (idx + 1) p.size
    if !tail.isEmpty && tail != p && tail != short then
      out := out.push tail
  let mut k := p.size / 2
  while k >= 1 do
    let pref := p.extract 0 k
    if pref != p && pref != short then
      out := out.push pref
    if k == 1 then break
    k := k / 2
  return out

private def shrinkBytesCandidates (d : ByteArray) : Array ByteArray := Id.run do
  if d.isEmpty then return #[]
  let mut lens : Array Nat := #[0]
  let mut p := 1
  while p < d.size do
    lens := lens.push p
    p := p * 2
  let half := d.size / 2
  if half > 0 && !lens.contains half then
    lens := lens.push half
  return lens.map (d.extract 0 ·)

private def shrinkSizeCandidates (n : UInt32) : Array UInt32 :=
  #[0, 1, 8, 64].filter (· < n)

private def shrinkModeCandidates (m : Mode) : Array Mode :=
  #[0, 0o644, 0o755, m &&& 0o7000, m &&& 0o0777].filter (· < m)

private def shrinkOpenFlagsCandidates (f : OpenFlags) : Array OpenFlags := Id.run do
  let mut out : Array OpenFlags := #[]
  let baseRo : OpenFlags := { access := .rdonly, cloexec := false }
  if f != baseRo then out := out.push baseRo
  let keepCore : OpenFlags := {
    access := f.access, creat := f.creat, directory := f.directory,
    path := f.path, cloexec := false
  }
  if (f.excl || f.trunc || f.append || f.nofollow || f.nonblock || f.cloexec || f.noctty) &&
      keepCore != f && keepCore != baseRo then
    out := out.push keepCore
  let pushUniq := fun (arr : Array OpenFlags) (cand : OpenFlags) =>
    if cand != f && !arr.contains cand then arr.push cand else arr
  if f.access != .rdonly then out := pushUniq out { f with access := .rdonly }
  if f.access == .rdwr then out := pushUniq out { f with access := .wronly }
  if f.creat then out := pushUniq out { f with creat := false }
  if f.excl then out := pushUniq out { f with excl := false }
  if f.trunc then out := pushUniq out { f with trunc := false }
  if f.append then out := pushUniq out { f with append := false }
  if f.nofollow then out := pushUniq out { f with nofollow := false }
  if f.directory then out := pushUniq out { f with directory := false }
  if f.nonblock then out := pushUniq out { f with nonblock := false }
  if f.cloexec then out := pushUniq out { f with cloexec := false }
  if f.noctty then out := pushUniq out { f with noctty := false }
  if f.path then out := pushUniq out { f with path := false }
  return out

private def shrinkResolveFlagsCandidates (r : ResolveFlags) : Array ResolveFlags := Id.run do
  let mut out : Array ResolveFlags := #[]
  let emptyRes : ResolveFlags := {}
  if r != emptyRes then out := out.push emptyRes
  let pushUniq := fun (arr : Array ResolveFlags) (cand : ResolveFlags) =>
    if cand != r && !arr.contains cand then arr.push cand else arr
  if r.noXdev then out := pushUniq out { r with noXdev := false }
  if r.noMagiclinks then out := pushUniq out { r with noMagiclinks := false }
  if r.noSymlinks then out := pushUniq out { r with noSymlinks := false }
  if r.beneath then out := pushUniq out { r with beneath := false }
  if r.inRoot then out := pushUniq out { r with inRoot := false }
  if r.cached then out := pushUniq out { r with cached := false }
  return out

private def shrinkAtFlagsCandidates (f : AtFlags) : Array AtFlags := Id.run do
  let mut out : Array AtFlags := #[]
  let emptyAt : AtFlags := {}
  if f != emptyAt then out := out.push emptyAt
  let pushUniq := fun (arr : Array AtFlags) (cand : AtFlags) =>
    if cand != f && !arr.contains cand then arr.push cand else arr
  if f.symlinkNofollow then out := pushUniq out { f with symlinkNofollow := false }
  if f.emptyPath then out := pushUniq out { f with emptyPath := false }
  if f.eaccess then out := pushUniq out { f with eaccess := false }
  return out

private def shrinkAccessMaskCandidates (m : AccessModeMask) : Array AccessModeMask := Id.run do
  let mut out : Array AccessModeMask := #[]
  if m.read then out := out.push { m with read := false }
  if m.write then out := out.push { m with write := false }
  if m.exec then out := out.push { m with exec := false }
  return out

private def shrinkRenameFlagsCandidates (f : RenameFlags) : Array RenameFlags := Id.run do
  let mut out : Array RenameFlags := #[]
  let emptyRen : RenameFlags := {}
  if f != emptyRen then out := out.push emptyRen
  let pushUniq := fun (arr : Array RenameFlags) (cand : RenameFlags) =>
    if cand != f && !arr.contains cand then arr.push cand else arr
  if f.noreplace then out := pushUniq out { f with noreplace := false }
  if f.exchange then out := pushUniq out { f with exchange := false }
  if f.whiteout then out := pushUniq out { f with whiteout := false }
  return out

private def shrinkFcntlCandidates : FcntlCmd → Array FcntlCmd
  | .addSeals s => (#[0, 0x20, 0x0f].filter (· < s)).map .addSeals
  | .setFl true true => #[.setFl false true, .setFl true false, .setFl false false]
  | .setFl true false => #[.setFl false false]
  | .setFl false true => #[.setFl false false]
  | .setFd true => #[.setFd false]
  | _ => #[]

private def shrinkFlockCandidates : FlockOp → Array FlockOp
  | .shared true => #[.shared false]
  | .exclusive true => #[.exclusive false]
  | _ => #[]

private def shrinkOptDirCandidates : Option SymFd → Array (Option SymFd)
  | some _ => #[none]
  | none => #[]

private def shrinkStepArgCandidates (req : SymReq) : Array SymReq :=
  match req with
  | .write fd d => (shrinkBytesCandidates d).map (.write fd)
  | .read fd n => (shrinkSizeCandidates n).map (.read fd)
  | .getdents64 fd n => (shrinkSizeCandidates n).map (.getdents64 fd)
  | .getcwd n => (shrinkSizeCandidates n).map .getcwd
  | .lseek fd off w =>
    (if off != 0 then #[.lseek fd 0 w] else #[]) ++
    (if w != .seekSet then #[.lseek fd off .seekSet] else #[])
  | .openat d p f m =>
    (shrinkOptDirCandidates d).map (fun d' => .openat d' p f m) ++
    (shrinkPathCandidates p).map (fun p' => .openat d p' f m) ++
    (shrinkOpenFlagsCandidates f).map (fun f' => .openat d p f' m) ++
    (shrinkModeCandidates m).map (fun m' => .openat d p f m')
  | .openat2 d p h =>
    (shrinkOptDirCandidates d).map (fun d' => .openat2 d' p h) ++
    (shrinkPathCandidates p).map (fun p' => .openat2 d p' h) ++
    (shrinkOpenFlagsCandidates h.flags).map (fun fl' =>
      .openat2 d p { h with flags := fl', mode := if fl'.creat then h.mode else 0 }) ++
    (shrinkResolveFlagsCandidates h.resolve).map (fun r' => .openat2 d p { h with resolve := r' }) ++
    (shrinkModeCandidates h.mode).map (fun m' => .openat2 d p { h with mode := m' })
  | .fstatat d p f =>
    (shrinkOptDirCandidates d).map (fun d' => .fstatat d' p f) ++
    (shrinkPathCandidates p).map (fun p' => .fstatat d p' f) ++
    (shrinkAtFlagsCandidates f).map (fun f' => .fstatat d p f')
  | .faccessat d p m f =>
    (shrinkOptDirCandidates d).map (fun d' => .faccessat d' p m f) ++
    (shrinkPathCandidates p).map (fun p' => .faccessat d p' m f) ++
    (shrinkAccessMaskCandidates m).map (fun m' => .faccessat d p m' f) ++
    (shrinkAtFlagsCandidates f).map (fun f' => .faccessat d p m f')
  | .mkdirat d p m =>
    (shrinkOptDirCandidates d).map (fun d' => .mkdirat d' p m) ++
    (shrinkPathCandidates p).map (fun p' => .mkdirat d p' m) ++
    (shrinkModeCandidates m).map (fun m' => .mkdirat d p m')
  | .unlinkat d p r =>
    (shrinkOptDirCandidates d).map (fun d' => .unlinkat d' p r) ++
    (shrinkPathCandidates p).map (fun p' => .unlinkat d p' r) ++
    (if r then #[.unlinkat d p false] else #[])
  | .renameat2 od op nd np f =>
    (shrinkOptDirCandidates od).map (fun od' => .renameat2 od' op nd np f) ++
    (shrinkOptDirCandidates nd).map (fun nd' => .renameat2 od op nd' np f) ++
    (shrinkPathCandidates op).map (fun op' => .renameat2 od op' nd np f) ++
    (shrinkPathCandidates np).map (fun np' => .renameat2 od op nd np' f) ++
    (shrinkRenameFlagsCandidates f).map (fun f' => .renameat2 od op nd np f')
  | .symlinkat tgt nd lp =>
    (shrinkOptDirCandidates nd).map (fun nd' => .symlinkat tgt nd' lp) ++
    (shrinkPathCandidates tgt).map (fun tgt' => .symlinkat tgt' nd lp) ++
    (shrinkPathCandidates lp).map (fun lp' => .symlinkat tgt nd lp')
  | .fchmodat d p m =>
    (shrinkOptDirCandidates d).map (fun d' => .fchmodat d' p m) ++
    (shrinkPathCandidates p).map (fun p' => .fchmodat d p' m) ++
    (shrinkModeCandidates m).map (fun m' => .fchmodat d p m')
  | .fchmod fd m => (shrinkModeCandidates m).map (fun m' => .fchmod fd m')
  | .fcntl fd cmd => (shrinkFcntlCandidates cmd).map (.fcntl fd)
  | .flock fd op => (shrinkFlockCandidates op).map (.flock fd)
  | .readlinkat d p n =>
    (shrinkOptDirCandidates d).map (fun d' => .readlinkat d' p n) ++
    (shrinkPathCandidates p).map (fun p' => .readlinkat d p' n) ++
    (shrinkSizeCandidates n).map (fun n' => .readlinkat d p n')
  | _ => #[]

/-- Greedy delta-minimizer over `SymStep` traces with handle-ID renumbering, pair deletions, and step-argument shrinking. -/
def shrinkTrace (trace : Array SymStep) (reproduces : Array SymStep -> IO Bool)
    (preSeeded : Nat := 0) : IO (Array SymStep) := do
  let mut cur := renumberTrace trace preSeeded
  if cur.size == 0 then
    return cur
  if cur.size > 1 then
    let mut chunk := cur.size / 2
    while chunk >= 1 do
      let mut i : Nat := 0
      let mut improved := false
      while i < cur.size do
        let hi := min cur.size (i + chunk)
        let candidateRaw := cur.extract 0 i ++ cur.extract hi cur.size
        let candidate := renumberTrace candidateRaw preSeeded
        if candidate.size < cur.size then
          if ← reproduces candidate then
            cur := candidate
            improved := true
          else
            i := i + chunk
        else
          i := i + chunk
      if improved then
        chunk := min chunk (max 1 (cur.size / 2))
      else
        if chunk == 1 then
          break
        chunk := chunk / 2
    let mut pairImproved := true
    while pairImproved && cur.size >= 3 do
      pairImproved := false
      let mut i : Nat := 0
      while i + 1 < cur.size do
        let candidate := renumberTrace (cur.extract 0 i ++ cur.extract (i + 2) cur.size) preSeeded
        if candidate.size < cur.size then
          if ← reproduces candidate then
            cur := candidate
            pairImproved := true
          else
            i := i + 1
        else
          i := i + 1
  for idx in [:cur.size] do
    let mut improvedStep := true
    let mut fuel : Nat := 32
    while improvedStep && fuel > 0 do
      improvedStep := false
      fuel := fuel - 1
      let some step := cur[idx]? | break
      for req' in shrinkStepArgCandidates step.req do
        let candidate := cur.set! idx { step with req := req' }
        if ← reproduces candidate then
          cur := candidate
          improvedStep := true
          break
  if cur.size > 1 then
    let mut i : Nat := 0
    while i < cur.size do
      let candidate := renumberTrace (cur.extract 0 i ++ cur.extract (i + 1) cur.size) preSeeded
      if candidate.size < cur.size then
        if ← reproduces candidate then
          cur := candidate
        else
          i := i + 1
      else
        i := i + 1
  return cur

private def baseNames : Array String := #[
  "a", "b", "c", "d", "sub", "dir2", "empty_d", "hl1", "hl2",
  "p.fifo", "p444.fifo", "p000.fifo", "p.sock", "lnk_sub", "missing", "d255",
  "lf", "hl_lo1", "hl_lo2", "ldir", "empty_ldir", "sym_hla",
  "suid_lf", "sgid_lf", "sgid_nogrp_lf",
  "s1721", "s1721/reg666", "s1721/fifo666", "s1777/reg666", "s1777/fifo666", "s1777/u65534", "s1777/sym_other",
  "s1777/f640", "s1777/f604", "s1777/g640", "s1777/g604", "s1777/sock666",
  "s_unmap", "s_unmap/reg666", "s_unmap/fifo666", "s_unmap/sym_other", "s_unmap/sock666",
  "s1002", "s1002/reg666", "s1002/fifo666", "s1002/sym_other", "r_nogid", "r_nouid", "gd", "gd/sub", "gd/f", "gd/sgid2640"
]
private def subNames : Array String := #["a", "b", "x", "y", "lnk"]
private def specialNames : Array String := #[
  "p.fifo", "p444.fifo", "p000.fifo", "p.sock", "hl1", "hl2", "lnk_null", "lnk_zero", "lnk_full",
  "lnk_proc", "lnk_exe", "lnk_etc", "lnk_root", "lnk_sub", "lnk_cross", "d255",
  "lf", "hl_lo1", "hl_lo2", "ldir", "ldir/x", "empty_ldir", "sym_hla",
  "suid_lf", "sgid_lf", "sgid_nogrp_lf",
  "s1721", "s1721/reg666", "s1721/fifo666", "s1777/reg666", "s1777/fifo666", "s1777/u65534", "s1777/sym_other",
  "s1777/f640", "s1777/f604", "s1777/g640", "s1777/g604", "s1777/sock666",
  "s_unmap", "s_unmap/reg666", "s_unmap/fifo666", "s_unmap/sym_other", "s_unmap/sock666",
  "s1002", "s1002/reg666", "s1002/fifo666", "s1002/sym_other", "r_nogid", "r_nouid", "gd", "gd/sub", "gd/f", "gd/sgid2640"
]
private def safeHostProbePaths : Array String := #[
  "/dev/null", "/dev/zero", "/dev/full", "/proc/self/status",
  "/proc/self/cmdline", "/proc/self/exe", "/proc/self/fd/0",
  "/proc/1/fd/0", "/proc/1/cwd", "/proc/self/oom_score_adj",
  "/proc/self/fd/1", "/proc/self/fd/2", "/proc/self/cwd", "/proc/self/root",
  "/etc/passwd", "/sys/kernel/cpu_byteorder", "/",
  "../../../../etc/passwd", "../../../../sys/kernel/cpu_byteorder"
]

private def longSName : ByteArray :=
  ByteArray.mk (Array.replicate 255 (115 : UInt8))

private def maxNameComponent : ByteArray :=
  ByteArray.mk (Array.replicate 255 (97 : UInt8))

private def longComponent : ByteArray :=
  ByteArray.mk (Array.replicate 256 (97 : UInt8))

private def nearPathMax : ByteArray := Id.run do
  let mut bytes : Array UInt8 := #[]
  for _ in [:2047] do
    bytes := bytes.push 46
    bytes := bytes.push 47
  bytes := bytes.push 97
  return ByteArray.mk bytes

private def exactPathMax : ByteArray := Id.run do
  let mut bytes : Array UInt8 := #[]
  for _ in [:2047] do
    bytes := bytes.push 46
    bytes := bytes.push 47
  bytes := bytes.push 97
  bytes := bytes.push 98
  return ByteArray.mk bytes

private def overPathMax : ByteArray := Id.run do
  let mut bytes : Array UInt8 := #[]
  for idx in [:2050] do
    if idx > 0 then
      bytes := bytes.push 47
    bytes := bytes.push 97
  return ByteArray.mk bytes

private def badUtf8Name : ByteArray :=
  ByteArray.mk #[0xff, 0xfe, 0x80, 0x9f, 97]

private def badUtf8Sub : ByteArray :=
  ByteArray.mk #[0xed, 0xa0, 0x80, 47, 98]

private def overlayHotNames : Array String := #[
  "hl_lo1", "hl_lo2", "sym_hla", "lf", "ldir", "ldir/x", "empty_ldir", "suid_lf", "sgid_lf", "sgid_nogrp_lf"
]

private def asymHotNames : Array String := #[
  "gd", "gd/f", "gd/sgid2640", "s1777/reg666", "s1777/f640", "s1777/g640", "s_unmap/reg666"
]

private def genPath (rng : Rng) (allowSpecial : Bool) (allowAbs : Bool) (inSubdir : Bool)
    (crossDir? : Option String := none) (hasParentWork : Bool := false)
    (overlayHot : Bool := false) (openProcSids : Array SymFd := #[])
    (asymHot : Bool := false) : ByteArray × Rng :=
  let (pickDynProc, r0a) := if allowAbs && !openProcSids.isEmpty then rng.chance 1 8 else (false, rng)
  if pickDynProc then
    let (sid, r1) := r0a.pickArray openProcSids 0
    let (sfxKind, r2) := r1.nextNat 5
    let sfx := if sfxKind == 0 then "/" else if sfxKind == 1 then "/a" else ""
    (("/proc/self/fd/@" ++ toString sid ++ sfx).toUTF8, r2)
  else
  let (pickAsym, r0b) := if asymHot then r0a.chance 1 4 else (false, r0a)
  if pickAsym then
    let (n, r1) := r0b.pickArray asymHotNames "gd/sgid2640"
    (n.toUTF8, r1)
  else
  let (pickOvl, r0) := r0b.chance 1 3
  if overlayHot && pickOvl then
    let (n, r1) := r0.pickArray overlayHotNames "hl_lo1"
    (n.toUTF8, r1)
  else
  let (kind, r1) := r0.nextNat 44
  if allowSpecial && kind == 0 then
    (ByteArray.empty, r1)
  else if allowSpecial && kind == 1 then
    (ByteArray.mk #[97, 0, 98], r1)
  else if allowSpecial && kind == 2 then
    (longComponent, r1)
  else if allowSpecial && kind == 3 then
    (overPathMax, r1)
  else if allowSpecial && kind == 4 then
    (".".toUTF8, r1)
  else if allowSpecial && kind == 5 && (inSubdir || hasParentWork) then
    ("..".toUTF8, r1)
  else if allowAbs && kind == 6 then
    let (n, r2) := r1.pickArray baseNames "a"
    (("/" ++ n).toUTF8, r2)
  else if kind >= 7 && kind <= 10 then
    let (d, r2) := r1.pickArray #["sub", "dir2", "a", "lnk_sub", "d255", "ldir", "gd"] "sub"
    let (f, r3) := r2.pickArray subNames "x"
    if kind == 9 then
      ((d ++ "/" ++ f ++ "/").toUTF8, r3)
    else if kind == 10 then
      ((d ++ "//" ++ f).toUTF8, r3)
    else
      ((d ++ "/" ++ f).toUTF8, r3)
  else if kind >= 11 && kind <= 13 then
    let (d1, r2) := r1.pickArray #["sub", "dir2", "a", "lnk_sub", "ldir"] "sub"
    let (d2, r3) := r2.pickArray subNames "a"
    let (f, r4) := r3.pickArray subNames "x"
    if kind == 12 then
      ((d1 ++ "/" ++ d2 ++ "/" ++ f ++ "/").toUTF8, r4)
    else if kind == 13 then
      ((d1 ++ "/./" ++ d2 ++ "/../" ++ f).toUTF8, r4)
    else
      ((d1 ++ "/" ++ d2 ++ "/" ++ f).toUTF8, r4)
  else if kind == 14 then
    let (n, r2) := r1.pickArray baseNames "a"
    ((n ++ "/").toUTF8, r2)
  else if allowSpecial && kind == 15 then
    ("sub/../a".toUTF8, r1)
  else if allowSpecial && kind == 16 then
    ("./".toUTF8, r1)
  else if allowSpecial && kind == 17 && (inSubdir || hasParentWork) then
    ("../".toUTF8, r1)
  else if allowSpecial && kind == 18 then
    let (d, r2) := r1.pickArray #["sub", "dir2", "a", "lnk_sub", "ldir"] "sub"
    ((d ++ "/./").toUTF8, r2)
  else if allowSpecial && kind == 19 then
    let (d, r2) := r1.pickArray #["sub", "dir2", "a", "lnk_sub", "ldir"] "sub"
    ((d ++ "/../").toUTF8, r2)
  else if allowSpecial && kind == 20 then
    (maxNameComponent, r1)
  else if allowSpecial && kind == 21 then
    (nearPathMax, r1)
  else if allowSpecial && kind >= 22 && kind <= 25 then
    let (n, r2) := r1.pickArray specialNames "p.fifo"
    (n.toUTF8, r2)
  else if allowAbs && (kind == 26 || kind == 27) then
    let (p, r2) := r1.pickArray safeHostProbePaths "/dev/null"
    (p.toUTF8, r2)
  else if allowAbs && kind == 28 then
    match crossDir? with
    | some cd =>
      let (pickFile, r2) := r1.chance 1 2
      if pickFile then ((cd ++ "/cf").toUTF8, r2) else ((cd ++ "/new_c").toUTF8, r2)
    | none => ("../escape".toUTF8, r1)
  else if allowSpecial && kind == 29 then
    ("d255/".toUTF8 ++ longSName, r1)
  else if allowSpecial && kind == 30 then
    ("..".toUTF8, r1)
  else if allowSpecial && kind == 31 then
    (exactPathMax, r1)
  else if allowSpecial && kind == 32 then
    (badUtf8Name, r1)
  else if allowSpecial && kind == 33 then
    (badUtf8Sub, r1)
  else if allowAbs && kind == 34 then
    ("/".toUTF8, r1)
  else if hasParentWork && (kind == 35 || kind == 36) then
    let (p, r2) := r1.pickArray #["../work", "../dst", "../deep_d", "../deep_d/work"] "../work"
    (p.toUTF8, r2)
  else
    let (n, r2) := r1.pickArray baseNames "a"
    (n.toUTF8, r2)

private def genOpenFlags (rng : Rng) : OpenFlags × Rng :=
  let (accIdx, r1) := rng.nextNat 3
  let access : AccessMode := match accIdx with
    | 0 => .rdonly
    | 1 => .wronly
    | _ => .rdwr
  let (creat, r2) := r1.chance 1 3
  let (excl, r3) := r2.chance 1 4
  let (trunc, r4) := r3.chance 1 4
  let (append, r5) := r4.chance 1 4
  let (directory, r6) := r5.chance 1 3
  let (nofollow, r7) := r6.chance 1 5
  let (cloexec, r8) := r7.chance 3 4
  let (nonblock, r9) := r8.chance 1 4
  let (noctty, r10) := r9.chance 1 5
  let (path, r11) := r10.chance 1 4
  ({ access, creat, excl, trunc, append, nofollow, directory, nonblock, cloexec, noctty, path }, r11)

private def genResolveFlags (rng : Rng) : ResolveFlags × Rng :=
  let (beneath, r1) := rng.chance 1 3
  let (inRoot, r2) := r1.chance 1 4
  let (noMagiclinks, r3) := r2.chance 1 4
  let (noSymlinks, r4) := r3.chance 1 4
  let (noXdev, r5) := r4.chance 1 6
  let (cached, r6) := r5.chance 1 8
  ({ beneath, inRoot, noMagiclinks, noSymlinks, noXdev, cached }, r6)

private def genMode (rng : Rng) : Mode × Rng :=
  let modes : Array Mode := #[
    0o644, 0o600, 0o444, 0o200, 0o755, 0o555, 0o000, 0o700, 0o777,
    0o1002, 0o1755, 0o1777, 0o2644, 0o2755, 0o2750, 0o2010, 0o4755, 0o6644, 0o7000, 0o10644
  ]
  rng.pickArray modes 0o644

private def genAtFlags (rng : Rng) : AtFlags × Rng :=
  let (emptyPath, r1) := rng.chance 1 4
  let (symlinkNofollow, r2) := r1.chance 1 3
  let (eaccess, r3) := r2.chance 1 6
  ({ emptyPath, symlinkNofollow, eaccess }, r3)

private def genPayload (rng : Rng) : ByteArray × Rng :=
  let (idx, r1) := rng.nextNat 9
  match idx with
  | 0 => (ByteArray.empty, r1)
  | 1 => ("hello".toUTF8, r1)
  | 2 => (ByteArray.mk #[0, 1, 255, 10, 42], r1)
  | 3 => (ByteArray.mk (Array.replicate 128 (65 : UInt8)), r1)
  | 4 => (ByteArray.mk (Array.replicate 4096 (66 : UInt8)), r1)
  | 5 => (ByteArray.mk (Array.replicate 8192 (67 : UInt8)), r1)
  | 6 => (ByteArray.mk (Array.replicate 65537 (68 : UInt8)), r1)
  | 7 => (ByteArray.mk (Array.replicate 69632 (69 : UInt8)), r1)
  | _ => ("payload-data-0123456789".toUTF8, r1)

private structure GenEnv where
  allFds : Array (SymFd × HandleId) := #[]
  openFds : Array (SymFd × HandleId) := #[]
  procFdMap : Std.HashMap SymFd Nat := {}

private def GenEnv.openProcSids (env : GenEnv) : Array SymFd :=
  env.openFds.filterMap fun (sid, _) =>
    if env.procFdMap.contains sid then some sid else none

private def pickDirArg (rng : Rng) (env : GenEnv) : (Option SymFd × Bool) × Rng :=
  let (useDir, r1) := rng.chance 1 4
  if !useDir || env.allFds.isEmpty then
    ((none, false), r1)
  else
    let (preferOpen, r2) := r1.chance 5 6
    let pool := if preferOpen && !env.openFds.isEmpty then env.openFds else env.allFds
    let (pair, r3) := r2.pickArray pool (0, 0)
    ((some pair.1, true), r3)

private def pickTargetFd (rng : Rng) (env : GenEnv) : SymFd × Rng :=
  let (preferOpen, r1) := rng.chance 9 10
  let pool := if preferOpen && !env.openFds.isEmpty then env.openFds else env.allFds
  let (pair, r2) := r1.pickArray pool (0, 0)
  (pair.1, r2)

private def isOpenDirHandle (s : FilesState) (hid : HandleId) : Bool :=
  match assocGet s.fds hid with
  | some desc =>
    match assocGet s.inodes desc.ino with
    | some vn => vn.kind == .dir
    | none => false
  | none => false

private def isUnlinkedOpenDirHandle (s : FilesState) (hid : HandleId) : Bool :=
  match assocGet s.fds hid with
  | some desc =>
    match assocGet s.inodes desc.ino with
    | some vn => vn.kind == .dir && vn.nlink == 0
    | none => false
  | none => false

private def pickDirTargetFd (rng : Rng) (env : GenEnv) (s : FilesState) : SymFd × Rng :=
  let openDirFds := env.openFds.filter fun (_, hid) => isOpenDirHandle s hid
  let unlinkedDirFds := env.openFds.filter fun (_, hid) => isUnlinkedOpenDirHandle s hid
  let (preferUnlinked, r0) := rng.chance 1 2
  if preferUnlinked && !unlinkedDirFds.isEmpty then
    let (pair, r1) := r0.pickArray unlinkedDirFds (0, 0)
    (pair.1, r1)
  else
    let (preferDir, r1) := r0.chance 3 4
    if preferDir && !openDirFds.isEmpty then
      let (pair, r2) := r1.pickArray openDirFds (0, 0)
      (pair.1, r2)
    else
      pickTargetFd r1 env

private def symToHid (env : GenEnv) (s : SymFd) : Option HandleId :=
  env.allFds.findSome? fun (sym, hid) => if sym == s then some hid else none

private def isSubtreeOf (s : FilesState) (rootIno targetIno : InodeId) (fuel : Nat := 64) : Bool :=
  match fuel with
  | 0 => false
  | fuel' + 1 =>
    if targetIno == rootIno then true
    else match assocGet s.inodes rootIno with
      | none => false
      | some rvn =>
        if rvn.kind != .dir then false
        else rvn.children.any fun (_, cIno) =>
          cIno == targetIno || isSubtreeOf s cIno targetIno fuel'

private def isOwnedInode (s : FilesState) (ownedRootIno : InodeId) (crossIno? : Option InodeId) (ino : InodeId) : Bool :=
  isSubtreeOf s ownedRootIno ino || match crossIno? with
    | some ci => isSubtreeOf s ci ino
    | none => false

private def walkTargetStep (s : FilesState) (followFinal : Bool) (inRootBase? : Option InodeId := none)
    (beneathBase? : Option InodeId := none) :
    Nat → Nat → InodeId → List ByteArray → Bool → Option (InodeId × Option InodeId × Option VNode)
  | 0, _, _, _, _ => none
  | _, _, curIno, [], _ =>
    match assocGet s.inodes curIno with
    | some vn => some (vn.parentIno, some curIno, some vn)
    | none => none
  | stepFuel + 1, symFuel, curIno, seg :: rest, trailing =>
    match assocGet s.inodes curIno with
    | none => none
    | some dirVn =>
      if dirVn.kind != .dir then none
      else if bytesEq seg dotBytes then
        walkTargetStep s followFinal inRootBase? beneathBase? stepFuel symFuel curIno rest trailing
      else if bytesEq seg dotDotBytes then
        if some curIno == beneathBase? && inRootBase?.isNone then none
        else
          let nextIno := if some curIno == inRootBase? then curIno else dirVn.parentIno
          walkTargetStep s followFinal inRootBase? beneathBase? stepFuel symFuel nextIno rest trailing
      else
        let isFinal := rest.isEmpty
        match bytesAssocGet dirVn.children seg with
        | none =>
          if isFinal then some (curIno, none, none) else none
        | some childIno =>
          match assocGet s.inodes childIno with
          | none => none
          | some childVn =>
            match childVn.data with
            | .symlink (.procMagic tIno fdHid?) =>
              if isFinal && !followFinal && !trailing then
                some (curIno, some childIno, some childVn)
              else if symFuel == 0 then
                none
              else if beneathBase?.isSome || inRootBase?.isSome then none
              else
                let effIno := match fdHid? with
                  | some hid => match assocGet s.fds hid with
                    | some d => d.ino
                    | none => tIno
                  | none => tIno
                if isFinal && !trailing then
                  match fdHid? with
                  | some hid =>
                    match assocGet s.fds hid with
                    | some d =>
                      match assocGet s.inodes d.ino with
                      | some tvn => some (d.dentry?.map (·.1) |>.getD tvn.parentIno, some d.ino, some tvn)
                      | none => none
                    | none => none
                  | none =>
                    match assocGet s.inodes effIno with
                    | some tvn => some (tvn.parentIno, some effIno, some tvn)
                    | none => none
                else
                  walkTargetStep s followFinal inRootBase? beneathBase? stepFuel (symFuel - 1) effIno rest trailing
            | .symlink (.path targetBytes) =>
              if isFinal && !followFinal && !trailing then
                some (curIno, some childIno, some childVn)
              else if symFuel == 0 then
                none
              else match validatePathBytes targetBytes with
                | .error _ => none
                | .ok (tAbs, tSegs, tTrail) =>
                  if tAbs && beneathBase?.isSome then none
                  else
                    let targetStart := if tAbs then inRootBase?.getD s.rootIno else curIno
                    let combinedTrail := if isFinal then (tTrail || trailing) else trailing
                    walkTargetStep s followFinal inRootBase? beneathBase? stepFuel (symFuel - 1) targetStart (tSegs ++ rest) combinedTrail
            | _ =>
              if isFinal then
                some (curIno, some childIno, some childVn)
              else if childVn.kind != .dir then
                none
              else
                walkTargetStep s followFinal inRootBase? beneathBase? stepFuel symFuel childIno rest trailing

private def walkLastVisitedInode (s : FilesState) (inRootBase? : Option InodeId := none)
    (beneathBase? : Option InodeId := none) :
    Nat → Nat → InodeId → List ByteArray → Option InodeId
  | 0, _, curIno, _ => some curIno
  | _, _, curIno, [] => some curIno
  | stepFuel + 1, symFuel, curIno, seg :: rest =>
    match assocGet s.inodes curIno with
    | none => some curIno
    | some dirVn =>
      if dirVn.kind != .dir then some curIno
      else if bytesEq seg dotBytes then
        walkLastVisitedInode s inRootBase? beneathBase? stepFuel symFuel curIno rest
      else if bytesEq seg dotDotBytes then
        if some curIno == beneathBase? && inRootBase?.isNone then none
        else
          let nextIno := if some curIno == inRootBase? then curIno else dirVn.parentIno
          walkLastVisitedInode s inRootBase? beneathBase? stepFuel symFuel nextIno rest
      else
        let isFinal := rest.isEmpty
        match bytesAssocGet dirVn.children seg with
        | none => some curIno
        | some childIno =>
          match assocGet s.inodes childIno with
          | none => some curIno
          | some childVn =>
            match childVn.data with
            | .symlink (.procMagic tIno fdHid?) =>
              if symFuel == 0 then none
              else if beneathBase?.isSome || inRootBase?.isSome then none
              else
                let effIno := match fdHid? with
                  | some hid => match assocGet s.fds hid with
                    | some d => d.ino
                    | none => tIno
                  | none => tIno
                walkLastVisitedInode s inRootBase? beneathBase? stepFuel (symFuel - 1) effIno rest
            | .symlink (.path targetBytes) =>
              if symFuel == 0 then none
              else match validatePathBytes targetBytes with
                | .error _ => some curIno
                | .ok (tAbs, tSegs, _) =>
                  if tAbs && beneathBase?.isSome then none
                  else
                    let targetStart := if tAbs then inRootBase?.getD s.rootIno else curIno
                    walkLastVisitedInode s inRootBase? beneathBase? stepFuel (symFuel - 1) targetStart (tSegs ++ rest)
            | _ =>
              if isFinal then some childIno
              else if childVn.kind != .dir then some childIno
              else walkLastVisitedInode s inRootBase? beneathBase? stepFuel symFuel childIno rest

private def inspectPathTarget (s : FilesState) (env : GenEnv) (dir : Option SymFd)
    (path0 : ByteArray) (followFinal : Bool := true) (inRoot : Bool := false)
    (beneath : Bool := false) : Option (InodeId × Option InodeId × Option VNode) :=
  let path := resolveSymProcFdPath env.procFdMap path0
  if hasEmbeddedNul path then none
  else
    let (isAbs, segs, trailing) := splitPathBytes path
    if beneath && (isAbs || inRoot) then none
    else
      let dirIno? : Option InodeId :=
        match dir with
        | none => some s.cwdIno
        | some sid => match symToHid env sid with
          | none => none
          | some hid => match assocGet s.fds hid with
            | none => none
            | some desc => some desc.ino
      let startIno? : Option InodeId :=
        if isAbs && !inRoot then some s.rootIno
        else dirIno?
      match startIno? with
      | none => none
      | some startIno =>
        let inRootBase? := if inRoot then dirIno? else none
        let beneathBase? := if beneath then dirIno? else none
        walkTargetStep s followFinal inRootBase? beneathBase? (segs.length + 131072) 40 startIno segs trailing

private def isSafeCharDevTarget (s : FilesState) (env : GenEnv) (dir : Option SymFd)
    (path : ByteArray) (followFinal : Bool) (inRoot : Bool := false) (beneath : Bool := false) : Bool :=
  match inspectPathTarget s env dir path followFinal inRoot beneath with
  | some (_, _, some vn) =>
    match vn.data with
    | .charDev .nullDev | .charDev .zeroDev | .charDev .fullDev => true
    | _ => false
  | _ => false

private def targetMayBlock (s : FilesState) (env : GenEnv) (dir : Option SymFd)
    (path : ByteArray) (followFinal : Bool) (access : AccessMode) (inRoot : Bool := false)
    (beneath : Bool := false) : Bool :=
  let extDir := (dir.bind (symToHid env) |>.bind (assocGet s.fds ·)).map (·.isExternalStdio) == some true
  match inspectPathTarget s env dir path followFinal inRoot beneath with
  | some (_, _, some vn) =>
    match vn.data with
    | .fifo _ => access != .rdwr
    | .charDev .generic => true
    | _ => vn.isDynamic && vn.kind == .other
  | _ => extDir

private def isTargetExternalStdio (s : FilesState) (env : GenEnv) (dir : Option SymFd)
    (path : ByteArray) (followFinal : Bool) (inRoot : Bool := false) (beneath : Bool := false) : Bool :=
  let extDir := (dir.bind (symToHid env) |>.bind (assocGet s.fds ·)).map (·.isExternalStdio) == some true
  match inspectPathTarget s env dir path followFinal inRoot beneath with
  | some (_, _, some vn) => extDir || (vn.isDynamic && vn.kind == .other)
  | _ => extDir

private def isProcFd0Target (path : ByteArray) : Bool :=
  bytesEq path ("/proc/self/fd/0".toUTF8) ||
  bytesEq path ("/proc/1/fd/0".toUTF8)

private def isManagedProcFd0Target (s : FilesState) (path : ByteArray) : Bool :=
  if !isProcFd0Target path then false
  else
    let isSelfFd0 := bytesEq path ("/proc/self/fd/0".toUTF8) ||
      match inspectPathTarget s {} none "/proc/self".toUTF8 false with
      | some (_, _, some sv) => bytesEq sv.symlinkTarget ("1".toUTF8)
      | _ => false
    if isSelfFd0 && s.managedStdioMap.any (fun (slot, _) => slot == .stdin) then true
    else match inspectPathTarget s {} none path false with
      | some (_, _, some linkVn) =>
        match linkVn.data with
        | .symlink (.procMagic _ (some _)) => true
        | _ => false
      | _ => false

private def isExternalProcFd0Target (s : FilesState) (path : ByteArray) : Bool :=
  if !isProcFd0Target path || isManagedProcFd0Target s path then false
  else match inspectPathTarget s {} none path false with
    | some (_, _, some linkVn) =>
      match linkVn.data with
      | .symlink (.procMagic _ none) => true
      | _ => false
    | _ => false

private def isClosedProcFd0Target (s : FilesState) (path : ByteArray) : Bool :=
  if !isProcFd0Target path || isManagedProcFd0Target s path then false
  else match inspectPathTarget s {} none path false with
    | some (parentIno, none, none) =>
      match assocGet s.inodes parentIno with
      | some pvn => pvn.isPseudo
      | none => false
    | _ => false

private def isStdoutStderrTarget (path : ByteArray) : Bool :=
  let p1 := "/proc/self/fd/1".toUTF8
  let p2 := "/proc/self/fd/2".toUTF8
  let q1 := "/proc/1/fd/1".toUTF8
  let q2 := "/proc/1/fd/2".toUTF8
  bytesEq path p1 || bytesEq path p2 || bytesEq path q1 || bytesEq path q2 ||
  startsWithBytes path ("/proc/self/fd/1/".toUTF8) ||
  startsWithBytes path ("/proc/self/fd/2/".toUTF8) ||
  startsWithBytes path ("/proc/1/fd/1/".toUTF8) ||
  startsWithBytes path ("/proc/1/fd/2/".toUTF8)

private def isFdStdoutStderr (s : FilesState) (env : GenEnv) (sid : SymFd) : Bool :=
  match symToHid env sid with
  | none => false
  | some hid => match assocGet s.fds hid with
    | none => false
    | some desc =>
      let checkProcFd := fun (name : ByteArray) =>
        match inspectPathTarget s env none name true with
        | some (_, some ino, _) => ino == desc.ino
        | _ => false
      checkProcFd "/proc/self/fd/1".toUTF8 || checkProcFd "/proc/self/fd/2".toUTF8

private def isTargetStdoutStderr (s : FilesState) (env : GenEnv) (dir : Option SymFd)
    (path : ByteArray) (followFinal : Bool) (inRoot : Bool := false) (beneath : Bool := false) : Bool :=
  match inspectPathTarget s env dir path followFinal inRoot beneath with
  | some (_, some ti, _) =>
    let checkProcFd := fun (name : ByteArray) =>
      match inspectPathTarget s env none name true with
      | some (_, some ino, _) => ino == ti
      | _ => false
    checkProcFd "/proc/self/fd/1".toUTF8 || checkProcFd "/proc/self/fd/2".toUTF8
  | _ => false

private def mutTargetAllowed (s : FilesState) (env : GenEnv) (ownedRootIno : InodeId)
    (crossIno? : Option InodeId) (allowHostMut safeStdin : Bool) (dir : Option SymFd)
    (path0 : ByteArray) (followFinal : Bool) (allowSafeCharDev : Bool := false)
    (inRoot : Bool := false) (beneath : Bool := false) : Bool :=
  let path := resolveSymProcFdPath env.procFdMap path0
  if hasEmbeddedNul path then true
  else
    let (isAbs, segs, _) := splitPathBytes path
    if beneath && (isAbs || inRoot) then true
    else if segs.isEmpty && isAbs && !inRoot then allowHostMut
    else if isStdoutStderrTarget path || isTargetStdoutStderr s env dir path followFinal inRoot beneath then false
    else
      match inspectPathTarget s env dir path followFinal inRoot beneath with
      | none =>
        let dirIno? : Option InodeId := match dir with
          | none => some s.cwdIno
          | some sid => symToHid env sid |>.bind (assocGet s.fds ·) |>.map (·.ino)
        match dirIno? with
        | none => true
        | some dirIno =>
          let startIno := if isAbs && !inRoot then s.rootIno else dirIno
          let inRootBase? := if inRoot then some dirIno else none
          let beneathBase? := if beneath then some dirIno else none
          match walkLastVisitedInode s inRootBase? beneathBase? (segs.length + 131072) 40 startIno segs with
          | none => true
          | some lastIno => isOwnedInode s ownedRootIno crossIno? lastIno
      | some (parentIno, targetIno?, targetVn?) =>
        let inOwned :=
          (isSubtreeOf s ownedRootIno parentIno ||
            (match crossIno? with | some ci => isSubtreeOf s ci parentIno | none => false)) &&
          (match targetIno? with
          | some ti =>
            (ownedRootIno == s.cwdIno || ti != ownedRootIno) &&
            (isSubtreeOf s ownedRootIno ti ||
              (match crossIno? with | some ci => isSubtreeOf s ci ti | none => false))
          | none => true)
        if inOwned then true
        else if allowSafeCharDev && isSafeCharDevTarget s env dir path followFinal inRoot beneath then true
        else
          let isManagedFd0 := !inRoot && !beneath && isManagedProcFd0Target s path
          let isEpisodeProcFd :=
            (((decodeSymProcFd path0).bind fun (sid, _) => env.procFdMap.get? sid).isSome || isManagedFd0) &&
            dir.isNone && !inRoot && !beneath
          let isOwnedTarget := match targetVn? with
            | some vn =>
              !vn.isPseudo && !vn.isDynamic && vn.owner.ownedByUid &&
              (ownedRootIno == s.cwdIno || targetIno? != some ownedRootIno) &&
              ((mountProfileOf s vn.mountId).supportsSeals || isEpisodeProcFd || dir.isSome)
            | none =>
              isEpisodeProcFd &&
              match assocGet s.inodes parentIno with
              | some pvn =>
                !pvn.isPseudo && !pvn.isDynamic && pvn.owner.ownedByUid &&
                (ownedRootIno == s.cwdIno || parentIno != ownedRootIno)
              | none => false
          if isOwnedTarget then true
          else if allowHostMut then
            if !inRoot && !beneath && isExternalProcFd0Target s path then safeStdin
            else if !inRoot && !beneath && isClosedProcFd0Target s path then true
            else
              match targetVn? with
              | some vn =>
                !(vn.isDynamic && vn.kind == .other) &&
                (vn.isPseudo ||
                 targetIno? == some s.rootIno ||
                 !vn.owner.ownedByUid ||
                 isReadOnlyMount s vn.mountId)
              | none => false
          else false

private def freshNonexistentName (s : FilesState) : ByteArray :=
  let children := match assocGet s.inodes s.cwdIno with
    | some vn => vn.children
    | none => []
  let rec go (idx : Nat) : ByteArray :=
    if idx >= 256 then
      s!"__nonexistent_safe_{s.nextIno}__".toUTF8
    else
      let cand := s!"__nonexistent_safe_{idx}__".toUTF8
      match bytesAssocGet children cand with
      | none => cand
      | some _ => go (idx + 1)
  go 0

private def clampOwnedMutArgs (s : FilesState) (env : GenEnv) (ownedRootIno : InodeId)
    (crossIno? : Option InodeId) (allowHostMut safeStdin : Bool) (dir : Option SymFd)
    (path : ByteArray) (rng : Rng) (followFinal : Bool := true)
    (allowSafeCharDev : Bool := false) (inRoot : Bool := false) (beneath : Bool := false) : Option SymFd × ByteArray × Rng :=
  if mutTargetAllowed s env ownedRootIno crossIno? allowHostMut safeStdin dir path followFinal allowSafeCharDev inRoot beneath then
    (dir, path, rng)
  else
    let dir' := match dir with
      | none => none
      | some sid => match symToHid env sid with
        | none => dir
        | some hid => match assocGet s.fds hid with
          | none => dir
          | some desc =>
            if isSubtreeOf s ownedRootIno desc.ino ||
                (match crossIno? with | some ci => isSubtreeOf s ci desc.ino | none => false) then dir
            else none
    let cands : Array String := #["a", "b", "c", "d", "sub/a", "missing"]
    let safe := cands.filter fun c =>
      mutTargetAllowed s env ownedRootIno crossIno? allowHostMut safeStdin dir' c.toUTF8 followFinal allowSafeCharDev inRoot beneath
    if safe.isEmpty then
      (none, freshNonexistentName s, rng)
    else
      let (n, r1) := rng.pickArray safe "a"
      (dir', n.toUTF8, r1)

private def findOpenEmptyCwdChildName (s : FilesState) : Option ByteArray :=
  match assocGet s.inodes s.cwdIno with
  | none => none
  | some cwdVn =>
    cwdVn.children.findSome? fun (name, cino) =>
      match assocGet s.inodes cino with
      | some cvn =>
        if cvn.kind == .dir && cvn.children.isEmpty && cvn.nlink > 0 &&
            s.fds.any (fun (_, desc) => desc.ino == cino) then
          some name
        else none
      | none => none

private def findOpenMayCopyUpChild (s : FilesState) : Option (ByteArray × Bool) :=
  match assocGet s.inodes s.cwdIno with
  | none => none
  | some cwdVn =>
    cwdVn.children.findSome? fun (name, cino) =>
      match assocGet s.inodes cino with
      | some cvn =>
        let removable := cvn.kind != .dir || cvn.children.isEmpty
        if cvn.mayCopyUp && cvn.nlink > 0 && removable &&
            s.fds.any (fun (_, desc) => desc.ino == cino) then
          some (name, cvn.kind == .dir)
        else none
      | none => none

private def findWritableFifoChildName (s : FilesState) : Option ByteArray :=
  match assocGet s.inodes s.cwdIno with
  | none => none
  | some cwdVn =>
    if cwdVn.isDeadDir || isReadOnlyMount s cwdVn.mountId then none
    else cwdVn.children.findSome? fun (name, cino) =>
      match assocGet s.inodes cino with
      | some cvn =>
        if cvn.kind == .fifo && cvn.nlink > 0 && cvn.owner.ownedByUid &&
            (cvn.mode &&& 0o600) == 0o600 && !isReadOnlyMount s cvn.mountId then
          some name
        else none
      | none => none

private def isUnlinkedCopyUpDesc (s : FilesState) (od : OpenDesc) : Bool :=
  match assocGet s.inodes od.ino with
  | none => false
  | some vn =>
    vn.mayCopyUp &&
    match od.dentry? with
    | none => true
    | some (pIno, lf) =>
      match assocGet s.inodes pIno with
      | none => true
      | some pvn =>
        pvn.isDeadDir || pvn.nlink == 0 || bytesAssocGet pvn.children lf != some od.ino

private def wouldReadBlock (s : FilesState) (env : GenEnv) (sid : SymFd) (sz : UInt32) : Bool :=
  match symToHid env sid with
  | none => false
  | some hid => match assocGet s.fds hid with
    | none => false
    | some desc =>
      if desc.isExternalStdio then true
      else if desc.access == .wronly then false
      else match assocGet s.inodes desc.ino with
        | none => false
        | some vn =>
          match vn.data with
          | .charDev .generic => true
          | .fifo p =>
            if desc.nonblock then false
            else min sz.toNat MAX_READ_BYTES.toNat > 0 &&
              p.buf.data.size == 0 && (vn.isDynamic || p.writers > 0)
          | _ => false

private def wouldWriteBlock (s : FilesState) (env : GenEnv) (sid : SymFd) (sz : Nat) : Bool :=
  match symToHid env sid with
  | none => false
  | some hid => match assocGet s.fds hid with
    | none => false
    | some desc =>
      if desc.isExternalStdio then true
      else if sz == 0 || desc.access == .rdonly then false
      else match assocGet s.inodes desc.ino with
        | none => false
        | some vn =>
          match vn.data with
          | .charDev .generic => true
          | .fifo p =>
            if desc.nonblock then false
            else vn.isDynamic || (p.readers > 0 && p.buf.data.size + sz > 4096)
          | _ => false

private def canProbeProcSelfExe (s : FilesState) : Bool :=
  !s.cred.capDacOverride &&
  (match s.cwdPath with | .bound _ => true | .unbound _ => false) &&
  !isReadOnlyMount s 0 &&
  match assocGet s.inodes s.cwdIno with
  | some cvn => !isReadOnlyMount s cvn.mountId && !(mountProfileOf s cvn.mountId).isOverlay
  | none => false

private def genSymReq (rng : Rng) (env : GenEnv) (s : FilesState)
    (ownedRootIno : InodeId := s.cwdIno)
    (crossIno? : Option InodeId := none) (crossDir? : Option String := none)
    (allowHostMut : Bool := true) (safeStdin : Bool := true) : SymReq × Rng :=
  let hasParentWork := ownedRootIno != s.cwdIno
  let ovlHot := match assocGet s.inodes s.cwdIno with
    | some cvn => cvn.overlayMergedDir || cvn.mayCopyUp || (mountProfileOf s cvn.mountId).isOverlay
    | none => false
  let asymHot := match assocGet s.inodes s.cwdIno with
    | some cvn => (bytesAssocGet cvn.children "gd".toUTF8).isSome
    | none => false
  let (opSlot, r1a) := rng.nextNat 28
  let opIdx0 :=
    if opSlot < 23 then opSlot
    else if ovlHot then
      match opSlot with
      | 23 => 10
      | 24 => 14
      | 25 => 15
      | 26 => if (findOpenMayCopyUpChild s).isSome then 9 else 16
      | _ => 0
    else match opSlot with
      | 23 => 8
      | 24 => 9
      | 25 => 13
      | 26 => 20
      | _ => 0
  let (rebalanceOpen, r1b) := r1a.chance 1 2
  let (allocPick, r1c) := r1b.nextNat 6
  let (preferFreeDup, r1) :=
    if !s.freeStdioSlots.isEmpty then r1c.chance 1 3 else (false, r1c)
  let opIdx :=
    if preferFreeDup then 22
    else if env.allFds.isEmpty then
      let initOps := #[0, 1, 6, 7, 8, 9, 10, 11, 12, 14, 19, 22]
      initOps.getD (opIdx0 % initOps.size) 0
    else if env.openFds.size < 2 && (rebalanceOpen || opIdx0 == 2) then
      if env.openFds.isEmpty then
        if allocPick % 2 == 0 then 0 else 1
      else
        #[0, 1, 0, 1, 21, 22].getD allocPick 0
    else
      opIdx0
  let openProcSids := env.openProcSids
  match opIdx with
  | 0 =>
    let hasNonblockFifoFd := env.openFds.any fun (_, hid) =>
      match assocGet s.fds hid with
      | some desc =>
        desc.nonblock && desc.access != .rdonly &&
        match assocGet s.inodes desc.ino with
        | some vn => match vn.data with | .fifo p => p.readers > 0 | _ => false
        | none => false
      | none => false
    let hasOpathSockFd := env.openFds.any fun (_, hid) =>
      match assocGet s.fds hid with
      | some desc =>
        desc.isPathFd &&
        match assocGet s.inodes desc.ino with
        | some vn => vn.kind == .socket
        | none => false
      | none => false
    let cwdHasSock := match assocGet s.inodes s.cwdIno with
      | some cvn => (bytesAssocGet cvn.children "p.sock".toUTF8).isSome
      | none => false
    let (preferFifoOpen, r1f) := r1.chance 1 8
    let (preferOpathSock, r1s0) := r1f.chance 1 12
    let (preferExeBusy, r1s) := r1s0.chance 1 48
    if preferExeBusy && allowHostMut && canProbeProcSelfExe s then
      (.openat none "/proc/self/exe".toUTF8 { access := .wronly, cloexec := true } 0, r1s)
    else
    match !hasNonblockFifoFd && preferFifoOpen && isOwnedInode s ownedRootIno crossIno? s.cwdIno, findWritableFifoChildName s with
    | true, some fifoName =>
      (.openat none fifoName { access := .rdwr, nonblock := true } 0o644, r1s)
    | _, _ =>
      if !hasOpathSockFd && preferOpathSock && cwdHasSock then
        (.openat none "p.sock".toUTF8 { path := true, cloexec := true } 0, r1s)
      else
      let ((dir0, hasDir), r2) := pickDirArg r1s env
      let (flags0, r3) := genOpenFlags r2
      let (useSimple, r3b) := r3.chance 1 3
      let (p0, r4) := genPath r3b (!useSimple) true hasDir crossDir? hasParentWork ovlHot openProcSids asymHot
      let followLast := !flags0.nofollow && !(flags0.creat && flags0.excl)
      let needsOwned := flags0.creat || flags0.trunc || flags0.access != .rdonly
      let (dir, path, r5) :=
        if needsOwned then
          clampOwnedMutArgs s env ownedRootIno crossIno? allowHostMut safeStdin dir0 p0 r4 followLast true
        else (dir0, p0, r4)
      let effPath := resolveSymProcFdPath env.procFdMap path
      let flags1 :=
        if isStdoutStderrTarget effPath || isTargetStdoutStderr s env dir effPath followLast ||
            isTargetExternalStdio s env dir effPath followLast ||
            (isExternalProcFd0Target s effPath && !safeStdin) then
          { flags0 with access := .rdonly, creat := false, trunc := false, nonblock := true }
        else if targetMayBlock s env dir effPath followLast flags0.access then
          { flags0 with nonblock := true }
        else flags0
      let (mode, r6) := genMode r5
      (.openat dir path flags1 mode, r6)
  | 1 =>
    let (preferExeBusy2, r1e) := r1.chance 1 48
    if preferExeBusy2 && allowHostMut && canProbeProcSelfExe s then
      (.openat2 none "/proc/self/exe".toUTF8 { flags := { access := .wronly, cloexec := true } }, r1e)
    else
    let ((dir0, hasDir), r2) := pickDirArg r1e env
    let (probeOpath, r2a) := r2.chance 1 10
    let (flags0, r3) :=
      if probeOpath then
        let (noctty, ra) := r2a.chance 1 2
        let (cloexec, rb) := ra.chance 1 2
        let (nofollow, rc) := rb.chance 1 2
        let (directory, rd) := rc.chance 1 2
        ({ access := .rdonly, noctty, cloexec, nofollow, directory, path := true }, rd)
      else
        genOpenFlags r2a
    let (resolve, r4) := genResolveFlags r3
    let (modeRaw, r5) := if probeOpath then ((0 : Mode), r4) else genMode r4
    let (p0, r6) := genPath r5 true true hasDir crossDir? hasParentWork ovlHot openProcSids asymHot
    let followLast := !flags0.nofollow && !(flags0.creat && flags0.excl) && !resolve.noSymlinks
    let needsOwned := flags0.creat || flags0.trunc || flags0.access != .rdonly
    let (dir, path, r7) :=
      if needsOwned then
        clampOwnedMutArgs s env ownedRootIno crossIno? allowHostMut safeStdin dir0 p0 r6 followLast true resolve.inRoot resolve.beneath
      else (dir0, p0, r6)
    let effPath := resolveSymProcFdPath env.procFdMap path
    let flags1 :=
      if isStdoutStderrTarget effPath || isTargetStdoutStderr s env dir effPath followLast resolve.inRoot resolve.beneath ||
          isTargetExternalStdio s env dir effPath followLast resolve.inRoot resolve.beneath ||
          (!resolve.inRoot && !resolve.beneath && isExternalProcFd0Target s effPath && !safeStdin) then
        { flags0 with access := .rdonly, creat := false, trunc := false, nonblock := true }
      else if targetMayBlock s env dir effPath followLast flags0.access resolve.inRoot resolve.beneath then
        { flags0 with nonblock := true }
      else flags0
    (.openat2 dir path { flags := flags1, mode := modeRaw, resolve }, r7)
  | 2 =>
    let (fd, r2) := pickTargetFd r1 env
    (.close fd, r2)
  | 3 =>
    let emptyNonblockFifoFds := env.openFds.filter fun (_, hid) =>
      match assocGet s.fds hid with
      | some desc =>
        desc.nonblock && desc.access != .wronly &&
        match assocGet s.inodes desc.ino with
        | some vn => match vn.data with | .fifo p => p.writers > 0 && p.buf.data.isEmpty | _ => false
        | none => false
      | none => false
    let (preferFifoEagain, r1b) := r1.chance 1 2
    let (fd0, r2) :=
      if preferFifoEagain && !emptyNonblockFifoFds.isEmpty then
        let (pair, r2') := r1b.pickArray emptyNonblockFifoFds (0, 0)
        (pair.1, r2')
      else pickTargetFd r1b env
    let (sz0, r3) := r2.pickArray #[0, 1, 16, 4096, 65536, 16777216, 16777217, 33554432, 0xffffffff] 64
    if wouldReadBlock s env fd0 sz0 then
      let nonBlocking := env.openFds.filter fun (sid, _) => !wouldReadBlock s env sid sz0
      if !nonBlocking.isEmpty then
        let (pair, r4) := r3.pickArray nonBlocking (fd0, 0)
        (.read pair.1 sz0, r4)
      else if !wouldReadBlock s env fd0 0 then
        (.read fd0 0, r3)
      else
        (.fstat fd0, r3)
    else
      (.read fd0 sz0, r3)
  | 4 =>
    let fullNonblockFifoFds := env.openFds.filter fun (_, hid) =>
      match assocGet s.fds hid with
      | some desc =>
        desc.nonblock && desc.access != .rdonly &&
        match assocGet s.inodes desc.ino with
        | some vn => match vn.data with | .fifo p => p.readers > 0 && p.buf.data.size >= 65536 | _ => false
        | none => false
      | none => false
    let nonblockFifoFds := env.openFds.filter fun (_, hid) =>
      match assocGet s.fds hid with
      | some desc =>
        desc.nonblock && desc.access != .rdonly &&
        match assocGet s.inodes desc.ino with
        | some vn => match vn.data with | .fifo p => p.readers > 0 | _ => false
        | none => false
      | none => false
    let (preferFull, r1a) := r1.chance 4 5
    let (preferFifoOverflow, r1b) := r1a.chance 3 4
    let (fd0, data0, r3) :=
      if preferFull && !fullNonblockFifoFds.isEmpty then
        let (pair, r2) := r1b.pickArray fullNonblockFifoFds (0, 0)
        let (d0, r2b) := genPayload r2
        let d := if d0.data.isEmpty then ByteArray.mk #[70] else d0
        (pair.1, d, r2b)
      else if preferFifoOverflow && !nonblockFifoFds.isEmpty then
        let (pair, r2) := r1b.pickArray nonblockFifoFds (0, 0)
        let (pick69k, r2b) := r2.chance 1 2
        let sz := if pick69k then 69632 else 65537
        (pair.1, ByteArray.mk (Array.replicate sz (70 : UInt8)), r2b)
      else
        let (f0, r2) := pickTargetFd r1b env
        let (d0, r2b) := genPayload r2
        (f0, d0, r2b)
    let blockOut := isFdStdoutStderr s env fd0
    if blockOut || wouldWriteBlock s env fd0 data0.data.size then
      let okFds := env.openFds.filter fun (sid, _) =>
        !isFdStdoutStderr s env sid && !wouldWriteBlock s env sid data0.data.size
      if !okFds.isEmpty then
        let (pair, r4) := r3.pickArray okFds (fd0, 0)
        (.write pair.1 data0, r4)
      else
        let alt := env.openFds.filter fun (sid, _) => !isFdStdoutStderr s env sid
        match alt.toList.head? with
        | some (sid, _) => (.write sid ByteArray.empty, r3)
        | none => (.fstat fd0, r3)
    else
      (.write fd0 data0, r3)
  | 5 =>
    let (fd, r2) := pickTargetFd r1 env
    (.fstat fd, r2)
  | 6 =>
    let ((dir, hasDir), r2) := pickDirArg r1 env
    let (flags, r3) := genAtFlags r2
    let (path, r4) := genPath r3 true true hasDir crossDir? hasParentWork ovlHot openProcSids asymHot
    (.fstatat dir path flags, r4)
  | 7 =>
    let ((dir, hasDir), r2) := pickDirArg r1 env
    let (flags, r3) := genAtFlags r2
    let (rd, r4) := r3.chance 1 2
    let (wr, r5) := r4.chance 1 2
    let (ex, r6) := r5.chance 1 3
    let (path, r7) := genPath r6 true true hasDir crossDir? hasParentWork ovlHot openProcSids
    (.faccessat dir path { read := rd, write := wr, exec := ex } flags, r7)
  | 8 =>
    let ((dir0, hasDir), r2) := pickDirArg r1 env
    let (useSimple, r2b) := r2.chance 1 3
    let (p0, r3) := genPath r2b (!useSimple) true hasDir crossDir? hasParentWork ovlHot openProcSids
    let (dir, path, r4) := clampOwnedMutArgs s env ownedRootIno crossIno? allowHostMut safeStdin dir0 p0 r3 false
    let (mode, r5) := genMode r4
    (.mkdirat dir path mode, r5)
  | 9 =>
    let (preferEmptyOpen, r1b) := if ovlHot then r1.chance 2 3 else r1.chance 1 3
    match preferEmptyOpen, findOpenMayCopyUpChild s, findOpenEmptyCwdChildName s with
    | true, some (name, isDir), _ =>
      (.unlinkat none name isDir, r1b)
    | true, none, some emptyName =>
      (.unlinkat none emptyName true, r1b)
    | _, _, _ =>
      let ((dir0, hasDir), r2) := pickDirArg r1b env
      let (removeDir, r3) := r2.chance 2 3
      let (useSimple, r3b) := r3.chance 1 3
      let (p0, r4) := genPath r3b (!useSimple) true hasDir crossDir? hasParentWork ovlHot openProcSids asymHot
      let (dir, path, r5) := clampOwnedMutArgs s env ownedRootIno crossIno? allowHostMut safeStdin dir0 p0 r4 false
      (.unlinkat dir path removeDir, r5)
  | 10 =>
    let ((od0, hasOd), r2) := pickDirArg r1 env
    let ((nd0, hasNd), r3) := pickDirArg r2 env
    let (op0, r4) := genPath r3 true true hasOd crossDir? hasParentWork ovlHot openProcSids
    let (od, op, r5) := clampOwnedMutArgs s env ownedRootIno crossIno? allowHostMut safeStdin od0 op0 r4 false
    let (np0, r6) := genPath r5 true true hasNd crossDir? hasParentWork ovlHot openProcSids
    let (nd, np, r7) := clampOwnedMutArgs s env ownedRootIno crossIno? allowHostMut safeStdin nd0 np0 r6 false
    let (nr, r8) := r7.chance 1 4
    let (ex, r9) := r8.chance 1 4
    let (wh, r10) := r9.chance 1 8
    (.renameat2 od op nd np { noreplace := nr, exchange := ex, whiteout := wh }, r10)
  | 11 =>
    let ((nd0, hasNd), r2) := pickDirArg r1 env
    let (target, r3) := genPath r2 true true true crossDir? hasParentWork ovlHot
    let (lp0, r4) := genPath r3 true false hasNd crossDir? hasParentWork ovlHot openProcSids
    let (nd, lp, r5) := clampOwnedMutArgs s env ownedRootIno crossIno? allowHostMut safeStdin nd0 lp0 r4 false
    (.symlinkat target nd lp, r5)
  | 12 =>
    let ((dir, hasDir), r2) := pickDirArg r1 env
    let (path, r3) := genPath r2 true true hasDir crossDir? hasParentWork ovlHot openProcSids
    let (sz, r4) := r3.pickArray #[0, 1, 8, 256, 4096, 16777216, 16777217, 0xffffffff] 256
    (.readlinkat dir path sz, r4)
  | 13 =>
    let (fd, r2) := pickDirTargetFd r1 env s
    let (sz, r3) := r2.pickArray #[0, 16, 23, 24, 31, 32, 48, 64, 4096, 16777217, 0xffffffff] 4096
    (.getdents64 fd sz, r3)
  | 14 =>
    let ((dir0, hasDir), r2) := pickDirArg r1 env
    let (p0, r3) := genPath r2 true true hasDir crossDir? hasParentWork ovlHot openProcSids
    let (dir, path, r4) := clampOwnedMutArgs s env ownedRootIno crossIno? allowHostMut safeStdin dir0 p0 r3 true false
    let (mode, r5) := genMode r4
    (.fchmodat dir path mode, r5)
  | 15 =>
    let unlinkedCopyUpFds := env.openFds.filter fun (_, hid) =>
      match assocGet s.fds hid with
      | some od => isUnlinkedCopyUpDesc s od
      | none => false
    let (preferUnlinkedCopyUp, r1b) := r1.chance 4 5
    let (fd, r2) :=
      if preferUnlinkedCopyUp && !unlinkedCopyUpFds.isEmpty then
        let (pair, rTmp) := r1b.pickArray unlinkedCopyUpFds (0, 0)
        (pair.1, rTmp)
      else
        pickTargetFd r1b env
    let (mode, r3) := genMode r2
    let fchmodSafe : Bool := match symToHid env fd with
      | none => true
      | some hid => match assocGet s.fds hid with
        | none => true
        | some od =>
          if isFdStdoutStderr s env fd then false
          else if ownedRootIno != s.cwdIno && od.ino == ownedRootIno then false
          else if isSubtreeOf s ownedRootIno od.ino || (crossIno?.map (isSubtreeOf s · od.ino) |>.getD false) then true
          else match assocGet s.inodes od.ino with
            | some vn =>
              if !vn.isDynamic && !vn.isPseudo && vn.owner.ownedByUid && od.ino != s.rootIno && od.ino != 0 then true
              else if allowHostMut then vn.isPseudo || !vn.owner.ownedByUid || isReadOnlyMount s vn.mountId
              else false
            | none => false
    if fchmodSafe then (.fchmod fd mode, r3)
    else (.fstat fd, r3)
  | 16 =>
    let (fd, r2) := pickTargetFd r1 env
    let (opChoice, r3) := r2.nextNat 5
    let rawOp : FlockOp := match opChoice with
      | 0 => .shared false
      | 1 => .shared true
      | 2 => .exclusive false
      | 3 => .exclusive true
      | _ => .unlock
    let sop : FlockOp := match symToHid env fd with
      | none => rawOp
      | some hid => match assocGet s.fds hid with
        | none => rawOp
        | some od =>
          let forceNb := od.isExternalStdio || match assocGet s.inodes od.ino with
            | none => true
            | some vn => vn.isPseudo || vn.isDynamic || !vn.owner.ownedByUid || !isOwnedInode s ownedRootIno crossIno? od.ino
          match rawOp with
          | .shared false =>
            if forceNb || hasConflictingFlock s hid od.ino false then .shared true else .shared false
          | .exclusive false =>
            if forceNb || hasConflictingFlock s hid od.ino true then .exclusive true else .exclusive false
          | other => other
    (.flock fd sop, r3)
  | 17 =>
    let (cmdIdx, r3) := r1.nextNat 6
    let (fd, r2b) :=
      if cmdIdx == 4 || cmdIdx == 5 then
        let sealFds := env.openFds.filter fun (_, hid) =>
          match assocGet s.fds hid with
          | some desc => match assocGet s.inodes desc.ino with
            | some vn => !vn.isPseudo && (mountProfileOf s vn.mountId).supportsSeals
            | none => false
          | none => false
        let (preferSeal, rs) := r3.chance 3 4
        if preferSeal && !sealFds.isEmpty then
          let (pair, rs2) := rs.pickArray sealFds (0, 0)
          (pair.1, rs2)
        else
          pickTargetFd rs env
      else if cmdIdx == 2 then
        let extFds := env.openFds.filter fun (_, hid) =>
          match assocGet s.fds hid with
          | some desc => desc.isExternalStdio
          | none => false
        let (preferExt, re) := r3.chance 1 2
        if preferExt && !extFds.isEmpty then
          let (pair, re2) := re.pickArray extFds (0, 0)
          (pair.1, re2)
        else
          pickTargetFd re env
      else
        pickTargetFd r3 env
    let (cmd, r4) := match cmdIdx with
      | 0 => (.getFl, r2b)
      | 1 =>
        if isFdStdoutStderr s env fd then (.getFl, r2b)
        else
          let (ap, ra) := r2b.chance 1 2
          let (nb, rb) := ra.chance 1 2
          (.setFl nb ap, rb)
      | 2 => (.getFd, r2b)
      | 3 =>
        let (cl, ra) := r2b.chance 1 2
        (.setFd cl, ra)
      | 4 =>
        let (seals, ra) := r2b.pickArray #[0, 1, 2, 4, 8, 16, 32, 0x3f, 0x10000000] 1
        (.addSeals seals, ra)
      | _ => (.getSeals, r2b)
    (.fcntl fd cmd, r4)
  | 18 =>
    let (fd, r2) := pickTargetFd r1 env
    (.fsync fd, r2)
  | 19 =>
    let (sz, r2) := r1.pickArray #[0, 1, 8, 40, 44, 48, 52, 56, 256, 4096, 16777217, 0xffffffff] 256
    (.getcwd sz, r2)
  | 20 =>
    let fifoFds := env.openFds.filter fun (_, hid) =>
      match assocGet s.fds hid with
      | some desc =>
        !desc.isPathFd &&
        match assocGet s.inodes desc.ino with
        | some vn => match vn.data with | .fifo _ => true | _ => false
        | none => false
      | none => false
    let (preferFifo, r1b) := r1.chance 1 5
    let (fd, r2) :=
      if preferFifo && !fifoFds.isEmpty then
        let (pair, rTmp) := r1b.pickArray fifoFds (0, 0)
        (pair.1, rTmp)
      else
        pickTargetFd r1b env
    let (off, r3) := r2.pickArray #[(-9223372036854775808 : Int64), (-100 : Int64), (-5 : Int64), (-1 : Int64), 0, 1, 2, 7, 16, 4096, 65536, 9223372036854775807] 0
    let (wIdx, r4) := r3.nextNat 3
    let whence : SeekWhence := match wIdx with
      | 0 => .seekSet
      | 1 => .seekCur
      | _ => .seekEnd
    (.lseek fd off whence, r4)
  | 21 =>
    let hotReopenFds := env.openFds.filter fun (_, hid) =>
      match assocGet s.fds hid with
      | some desc => desc.isPathFd || desc.isExternalStdio
      | none => false
    let (preferHot, r1b) := r1.chance 3 5
    let (fd0, r2) :=
      if preferHot && !hotReopenFds.isEmpty then
        let (pair, rTmp) := r1b.pickArray hotReopenFds (0, 0)
        (pair.1, rTmp)
      else
        pickTargetFd r1b env
    (.reopenReadOnly fd0, r2)
  | _ =>
    let (preferFree, r1b) := r1.chance 3 4
    if preferFree && !s.freeStdioSlots.isEmpty then
      let (slot, r2) := r1b.pickArray s.freeStdioSlots.toArray .stdin
      (.dupStdio slot, r2)
    else
      let (slotIdx, r2) := r1b.nextNat 3
      let slot : StdioFd := match slotIdx with
        | 0 => .stdin
        | 1 => .stdout
        | _ => .stderr
      (.dupStdio slot, r2)

private def allocClosedDummy (ops : FilesOps) : IO (Option RawFd) := do
  match ← ops.openat none "/dev/null".toUTF8 { access := .rdonly } 0 with
  | .ok fd =>
    let _ ← ops.close fd
    return some fd
  | .error _ => return none

private def resolveOrClosedDummy (ops : FilesOps) (rawMap : Std.HashMap HandleId RawFd)
    (closedDummy? : Option RawFd) (hid : HandleId) : IO (Option RawFd) := do
  match rawMap.get? hid with
  | some rfd => return some rfd
  | none =>
    if let some d := closedDummy? then
      return some d
    allocClosedDummy ops

/-- Execute a single `FilesReq` against real `FilesOps`, returning `FilesOutcome` and any opened `RawFd`. -/
def execRealReq (ops : FilesOps) (rawMap : Std.HashMap HandleId RawFd)
    (nextHid : HandleId) (req : FilesReq) (closedDummy? : Option RawFd := none) :
    IO (FilesOutcome × Option (HandleId × RawFd)) :=
  let resolve := resolveOrClosedDummy ops rawMap closedDummy?
  match req with
  | .openat dir p f mode => do
    let d ← match dir with
      | none => pure none
      | some hid => resolve hid
    if dir.isSome && d.isNone then return (.err 9, none)
    match ← ops.openat d p f mode with
    | .ok rfd => return (.opened nextHid, some (nextHid, rfd))
    | .error e => return (.err e, none)
  | .openat2 dir p how => do
    let d ← match dir with
      | none => pure none
      | some hid => resolve hid
    if dir.isSome && d.isNone then return (.err 9, none)
    match ← ops.openat2 d p how with
    | .ok rfd => return (.opened nextHid, some (nextHid, rfd))
    | .error e => return (.err e, none)
  | .close hid => do
    match ← resolve hid with
    | none => return (.err 9, none)
    | some rfd =>
      match ← ops.close rfd with
      | .ok () => return (.unit, none)
      | .error e => return (.err e, none)
  | .read hid n => do
    match ← resolve hid with
    | none => return (.err 9, none)
    | some rfd =>
      match ← ops.read rfd n with
      | .ok b => return (.bytes b, none)
      | .error e => return (.err e, none)
  | .write hid d => do
    match ← resolve hid with
    | none => return (.err 9, none)
    | some rfd =>
      match ← ops.write rfd d with
      | .ok n => return (.u32 n, none)
      | .error e => return (.err e, none)
  | .fstat hid => do
    match ← resolve hid with
    | none => return (.err 9, none)
    | some rfd =>
      match ← ops.fstat rfd with
      | .ok st => return (.statted st, none)
      | .error e => return (.err e, none)
  | .fstatat dir p f => do
    let d ← match dir with
      | none => pure none
      | some hid => resolve hid
    if dir.isSome && d.isNone then return (.err 9, none)
    match ← ops.fstatat d p f with
    | .ok st => return (.statted st, none)
    | .error e => return (.err e, none)
  | .faccessat dir p mode f => do
    let d ← match dir with
      | none => pure none
      | some hid => resolve hid
    if dir.isSome && d.isNone then return (.err 9, none)
    match ← ops.faccessat d p mode f with
    | .ok () => return (.unit, none)
    | .error e => return (.err e, none)
  | .mkdirat dir p mode => do
    let d ← match dir with
      | none => pure none
      | some hid => resolve hid
    if dir.isSome && d.isNone then return (.err 9, none)
    match ← ops.mkdirat d p mode with
    | .ok () => return (.unit, none)
    | .error e => return (.err e, none)
  | .unlinkat dir p r => do
    let d ← match dir with
      | none => pure none
      | some hid => resolve hid
    if dir.isSome && d.isNone then return (.err 9, none)
    match ← ops.unlinkat d p r with
    | .ok () => return (.unit, none)
    | .error e => return (.err e, none)
  | .renameat2 od op nd np f => do
    let od' ← match od with
      | none => pure none
      | some hid => resolve hid
    let nd' ← match nd with
      | none => pure none
      | some hid => resolve hid
    if (od.isSome && od'.isNone) || (nd.isSome && nd'.isNone) then return (.err 9, none)
    match ← ops.renameat2 od' op nd' np f with
    | .ok () => return (.unit, none)
    | .error e => return (.err e, none)
  | .symlinkat t nd lp => do
    let d ← match nd with
      | none => pure none
      | some hid => resolve hid
    if nd.isSome && d.isNone then return (.err 9, none)
    match ← ops.symlinkat t d lp with
    | .ok () => return (.unit, none)
    | .error e => return (.err e, none)
  | .readlinkat dir p n => do
    let d ← match dir with
      | none => pure none
      | some hid => resolve hid
    if dir.isSome && d.isNone then return (.err 9, none)
    match ← ops.readlinkat d p n with
    | .ok b => return (.bytes b, none)
    | .error e => return (.err e, none)
  | .getdents64 hid n => do
    match ← resolve hid with
    | none => return (.err 9, none)
    | some rfd =>
      match ← ops.getdents64 rfd n with
      | .ok b => return (.bytes b, none)
      | .error e => return (.err e, none)
  | .fchmodat dir p mode => do
    let d ← match dir with
      | none => pure none
      | some hid => resolve hid
    if dir.isSome && d.isNone then return (.err 9, none)
    match ← ops.fchmodat d p mode with
    | .ok () => return (.unit, none)
    | .error e => return (.err e, none)
  | .fchmod hid mode => do
    match ← resolve hid with
    | none => return (.err 9, none)
    | some rfd =>
      match ← ops.fchmod rfd mode with
      | .ok () => return (.unit, none)
      | .error e => return (.err e, none)
  | .flock hid op => do
    match ← resolve hid with
    | none => return (.err 9, none)
    | some rfd =>
      match ← ops.flock rfd op with
      | .ok () => return (.unit, none)
      | .error e => return (.err e, none)
  | .fcntl hid cmd => do
    match ← resolve hid with
    | none => return (.err 9, none)
    | some rfd =>
      match ← ops.fcntl rfd cmd with
      | .ok v => return (.u32 v, none)
      | .error e => return (.err e, none)
  | .fsync hid => do
    match ← resolve hid with
    | none => return (.err 9, none)
    | some rfd =>
      match ← ops.fsync rfd with
      | .ok () => return (.unit, none)
      | .error e => return (.err e, none)
  | .getcwd n => do
    match ← ops.getcwd n with
    | .ok b => return (.bytes b, none)
    | .error e => return (.err e, none)
  | .lseek hid off whence => do
    match ← resolve hid with
    | none => return (.err 9, none)
    | some rfd =>
      match ← ops.lseek rfd off whence with
      | .ok pos => return (.u64 pos, none)
      | .error e => return (.err e, none)
  | .reopenReadOnly hid => do
    match ← resolve hid with
    | none => return (.err 9, none)
    | some rfd =>
      match ← ops.reopenReadOnly rfd with
      | .ok newFd => return (.opened nextHid, some (nextHid, newFd))
      | .error e => return (.err e, none)
  | .dupStdio slot => do
    match ← ops.dupStdio slot with
    | .ok newFd => return (.opened nextHid, some (nextHid, newFd))
    | .error e => return (.err e, none)

private def extractDirentNames (bs : ByteArray) : Array ByteArray := Id.run do
  let mut names : Array ByteArray := #[]
  let mut pos : Nat := 0
  let n := bs.data.size
  while pos + 20 <= n do
    let lo := bs.data[pos + 16]!.toNat
    let hi := bs.data[pos + 17]!.toNat
    let reclen := lo + hi * 256
    if reclen < 24 || pos + reclen > n then break
    let mut nameBytes : Array UInt8 := #[]
    let mut i := pos + 19
    while i < pos + reclen do
      let b := bs.data[i]!
      if b == 0 then break
      nameBytes := nameBytes.push b
      i := i + 1
    let nb := ByteArray.mk nameBytes
    if nb.data != #[46] && nb.data != #[46, 46] && nb.data.size > 0 then
      names := names.push nb
    pos := pos + reclen
  return names

private def unlinkChildrenRaw (dirFd : RawFd) : Nat → IO Unit
  | 0 => pure ()
  | depth + 1 => do
    let ops := defaultOps
    let _ ← ops.fchmod dirFd 0o700
    for _ in [:4096] do
      match ← ops.getdents64 dirFd 8192 with
      | .error _ => break
      | .ok chunk =>
        if chunk.data.size == 0 then break
        for name in extractDirentNames chunk do
          match ← ops.unlinkat (some dirFd) name false with
          | .ok _ => pure ()
          | .error _ =>
            match ← ops.openat (some dirFd) name { access := .rdonly, directory := true, nofollow := true } 0 with
            | .ok cfd =>
              unlinkChildrenRaw cfd depth
              let _ ← ops.close cfd
              let _ ← ops.unlinkat (some dirFd) name true
            | .error oe =>
              if oe == Errno.EACCES then
                let _ ← ops.fchmodat (some dirFd) name 0o700
                match ← ops.openat (some dirFd) name { access := .rdonly, directory := true, nofollow := true } 0 with
                | .ok cfd =>
                  unlinkChildrenRaw cfd depth
                  let _ ← ops.close cfd
                  let _ ← ops.unlinkat (some dirFd) name true
                | .error _ =>
                  let _ ← ops.unlinkat (some dirFd) name true
                  let _ ← ops.unlinkat (some dirFd) name false
              else
                let _ ← ops.unlinkat (some dirFd) name true
                let _ ← ops.unlinkat (some dirFd) name false

private def unlinkTreeRaw (dirBytes : ByteArray) : IO Unit := do
  let ops := defaultOps
  let openDir := ops.openat none dirBytes { access := .rdonly, directory := true, nofollow := true } 0
  match ← openDir with
  | .ok dfd =>
    unlinkChildrenRaw dfd 64
    let _ ← ops.close dfd
    let _ ← ops.unlinkat none dirBytes true
  | .error oe =>
    if oe == Errno.EACCES then
      let _ ← ops.fchmodat none dirBytes 0o700
      match ← openDir with
      | .ok dfd =>
        unlinkChildrenRaw dfd 64
        let _ ← ops.close dfd
        let _ ← ops.unlinkat none dirBytes true
      | .error _ =>
        let _ ← ops.unlinkat none dirBytes true
        let _ ← ops.unlinkat none dirBytes false
    else
      let _ ← ops.unlinkat none dirBytes false

private def removeDirForced (dir : System.FilePath) : IO Unit := do
  if ← dir.pathExists then
    try
      IO.FS.removeDirAll dir
    catch _ =>
      unlinkTreeRaw dir.toString.toUTF8
      if ← dir.pathExists then
        if ← (System.FilePath.mk "/bin/sh").pathExists then
          let _ ← IO.Process.output {
            cmd := "sh"
            args := #["-c", "chmod -R u+rwx \"$1\" 2>/dev/null || true; rm -rf \"$1\" 2>/dev/null || true", "_", dir.toString]
            stdin := .null
          }

private def cleanupEpisodeDir (ops : FilesOps) (openRfds : Array RawFd)
    (savedCwd epDir : System.FilePath) (crossDir? : Option System.FilePath := none)
    (keepEpDir : Bool := false) : IO Unit := do
  let _ ← Env.umask 0o022
  for rfd in openRfds do
    let _ ← ops.close rfd
  IO.Process.setCurrentDir savedCwd
  if !keepEpDir then
    removeDirForced epDir
  if let some cd := crossDir? then
    removeDirForced cd

/-- Result of replaying a symbolic trace against the real kernel and model oracle. -/
structure ReplayResult where
  /-- Index of the first step where `allowedStep` returned `none`, if any. -/
  mismatchIdx : Option Nat
  /-- Request at the mismatch step. -/
  mismatchReq : Option FilesReq
  /-- Real outcome observed at the mismatch step. -/
  mismatchOut : Option FilesOutcome
  /-- Model state before the mismatch step (or final state). -/
  finalState : FilesState

private def decodeProbeFdKind (code : UInt32) : FileKind × Option SpecialDevKind :=
  match code with
  | 1 => (.reg, none)
  | 2 => (.dir, none)
  | 4 => (.fifo, none)
  | 5 => (.socket, none)
  | 31 => (.charDev, some .nullDev)
  | 32 => (.charDev, some .zeroDev)
  | 33 => (.charDev, some .fullDev)
  | 30 => (.charDev, none)
  | 6 => (.other, none)
  | _ => (.charDev, some .nullDev)

private structure EpisodeRecipe where
  epUmask : Mode := 0o022
  sgidSub : Bool := false
  cwdSubdir : Bool := false
  fsizeLimit? : Option UInt64 := none
  seedFifo : Bool := true
  seedSock : Bool := true
  seedHardlinks : Bool := true
  seedSymlinks : Bool := true
  seedD255 : Bool := true
  seedCross : Bool := true

private def genEpisodeRecipe (rng : Rng) : EpisodeRecipe × Rng :=
  let (epUmask, r1) := rng.pickArray #[0o022, 0o077, 0o002, 0o200, 0o000] 0o022
  let (sgidSub, r2) := r1.chance 1 2
  let (cwdSubdir, r2b) := r2.chance 1 5
  let (useFsize, r2c) := r2b.chance 1 10
  let (fsizeVal, r2d) := r2c.pickArray #[2048, 8192] 2048
  let fsizeLimit? := if useFsize then some fsizeVal else none
  let (seedFifo, r3) := r2d.chance 3 4
  let (seedSock, r4) := r3.chance 3 4
  let (seedHardlinks, r5) := r4.chance 3 4
  let (seedSymlinks, r6) := r5.chance 4 5
  let (seedD255, r7) := r6.chance 1 3
  let (seedCross, r8) := r7.chance 3 4
  ({ epUmask, sgidSub, cwdSubdir, fsizeLimit?, seedFifo, seedSock, seedHardlinks, seedSymlinks, seedD255, seedCross }, r8)

private def mountProfileForPath (p : ByteArray) (_sealsHint : Bool) : IO MountProfile := do
  let fsType ← Env.statfsFsType p
  let ro ← Env.statfsIsReadOnly p
  let isTmpfs := fsType == (0x01021994 : UInt64)
  let isOverlay := fsType == (0x794c7630 : UInt64) || fsType == (0x65735546 : UInt64)
  let isVfat := fsType == (0x4d44 : UInt64)
  let isExfat := fsType == (0x2011bab0 : UInt64)
  let isFat := isVfat || isExfat
  return {
    readOnly := ro
    supportsSymlinks := !isFat
    posixModes := !isFat
    isOverlay := isOverlay
    supportsSeals := isTmpfs
  }

private structure MountIdEntry where
  mntId : UInt64
  dev : UInt64
  mid : Nat

private def sameMountKey (aMnt aDev bMnt bDev : UInt64) : Bool :=
  if aMnt != 0 && bMnt != 0 then aMnt == bMnt
  else aDev != 0 && aDev == bDev

private def internMountById (path : ByteArray) (mntId : UInt64) (dev : UInt64)
    (sealsHint : Bool) (nextMid : Nat) (entries : List MountIdEntry)
    (profiles : List (Nat × MountProfile)) :
    IO (Nat × Nat × List MountIdEntry × List (Nat × MountProfile)) := do
  match entries.find? (fun e => sameMountKey e.mntId e.dev mntId dev) with
  | some e => return (e.mid, nextMid, entries, profiles)
  | none =>
    let prof ← mountProfileForPath path sealsHint
    let entries' := entries ++ [{ mntId, dev, mid := nextMid }]
    let profiles' := profiles ++ [(nextMid, prof)]
    return (nextMid, nextMid + 1, entries', profiles')

private def strictAncestors (p : System.FilePath) : List System.FilePath :=
  let rec go (fuel : Nat) (cur : System.FilePath) (acc : List System.FilePath) : List System.FilePath :=
    match fuel with
    | 0 => acc
    | n + 1 =>
      match cur.parent with
      | none => acc
      | some par =>
        if par == cur then acc
        else go n par (par :: acc)
  go 64 p []

private def mappedFlags (uidRanges gidRanges : List (UInt32 × UInt32)) (selfGids : List UInt32)
    (ug : UInt64) : Bool × Bool × Bool × UInt32 :=
  let u := ug.toUInt32
  let g := (ug >>> 32).toUInt32
  let uMap := Env.isIdMapped uidRanges u
  let gMap := Env.isIdMapped gidRanges g
  (uMap, gMap, gMap && selfGids.contains g, u)

private def inspectExistingEntries (epWork : System.FilePath)
    (uidRanges gidRanges : List (UInt32 × UInt32)) (selfGids : List UInt32)
    (nextMid0 : Nat) (mountEntries0 : List MountIdEntry)
    (mountProfiles0 : List (Nat × MountProfile)) :
    IO (List SeedEntry × Nat × List MountIdEntry × List (Nat × MountProfile)) := do
  let ops := defaultOps
  let mut nextMid := nextMid0
  let mut mountEntries := mountEntries0
  let mut mountProfiles := mountProfiles0
  let mut entries : List SeedEntry := []
  if ← (epWork / "sub").pathExists then
    let subMode ← Env.statMode "sub".toUTF8
    entries := entries ++ [{ name := "sub".toUTF8, kind := .dir, mode := subMode, modeExact := true }]
    if ← (epWork / "sub" / "a").pathExists then
      let saMode ← Env.statMode "sub/a".toUTF8
      entries := entries ++ [{ relDir := ["sub".toUTF8], name := "a".toUTF8, kind := .reg, mode := saMode, modeExact := true, bytes := "init-a".toUTF8 }]
  if ← (epWork / "empty_d").pathExists then
    let emptyMode ← Env.statMode "empty_d".toUTF8
    entries := entries ++ [{ name := "empty_d".toUTF8, kind := .dir, mode := emptyMode, modeExact := true }]
  if ← (epWork / "d255").pathExists then
    let d255Mode ← Env.statMode "d255".toUTF8
    entries := entries ++ [{ name := "d255".toUTF8, kind := .dir, mode := d255Mode, modeExact := true }]
    let pLong := "d255/".toUTF8 ++ longSName
    if ← (epWork / "d255" / (String.fromUTF8! longSName)).pathExists then
      let lsMode ← Env.statMode pLong
      entries := entries ++ [{ relDir := ["d255".toUTF8], name := longSName, kind := .reg, mode := lsMode, modeExact := true }]
  if ← (epWork / "hl1").pathExists then
    let hlMode ← Env.statMode "hl1".toUTF8
    if ← (epWork / "hl2").pathExists then
      entries := entries ++ [
        { name := "hl1".toUTF8, kind := .reg, mode := hlMode, modeExact := true, bytes := "hl-data".toUTF8, hardlinkGroup? := some 1 },
        { name := "hl2".toUTF8, kind := .reg, mode := hlMode, modeExact := true, bytes := "hl-data".toUTF8, hardlinkGroup? := some 1 }
      ]
    else
      entries := entries ++ [{ name := "hl1".toUTF8, kind := .reg, mode := hlMode, modeExact := true, bytes := "hl-data".toUTF8 }]
  if ← (epWork / "p.fifo").pathExists then
    let fMode ← Env.statMode "p.fifo".toUTF8
    entries := entries ++ [{ name := "p.fifo".toUTF8, kind := .fifo, mode := fMode, modeExact := true }]
  if ← (epWork / "p444.fifo").pathExists then
    let f444Mode ← Env.statMode "p444.fifo".toUTF8
    entries := entries ++ [{ name := "p444.fifo".toUTF8, kind := .fifo, mode := f444Mode, modeExact := true }]
  if ← (epWork / "p000.fifo").pathExists then
    let f000Mode ← Env.statMode "p000.fifo".toUTF8
    entries := entries ++ [{ name := "p000.fifo".toUTF8, kind := .fifo, mode := f000Mode, modeExact := true }]
  if ← (epWork / "p.sock").pathExists then
    let kMode ← Env.statMode "p.sock".toUTF8
    entries := entries ++ [{ name := "p.sock".toUTF8, kind := .socket, mode := kMode, modeExact := true }]
  for (lname, target) in #[
    ("lnk_null", "/dev/null"), ("lnk_zero", "/dev/zero"), ("lnk_full", "/dev/full"),
    ("lnk_proc", "/proc/self/status"), ("lnk_exe", "/proc/self/exe"),
    ("lnk_etc", "/etc/passwd"), ("lnk_root", "/"), ("lnk_sub", "sub")
  ] do
    if ← (epWork / lname).pathExists then
      entries := entries ++ [{ name := lname.toUTF8, kind := .symlink, mode := 0o777, symlinkTarget := target.toUTF8 }]
  if ← (epWork / "f444").pathExists then
    let f4Mode ← Env.statMode "f444".toUTF8
    entries := entries ++ [{ name := "f444".toUTF8, kind := .reg, mode := f4Mode, modeExact := true, bytes := "ro444\n".toUTF8 }]
  let myUid ← Env.getUid
  for nm in #["r_nogid", "r_nouid"] do
    if ← (epWork / nm).pathExists then
      let p := nm.toUTF8
      let rm ← Env.statMode p
      let rug ← Env.statUidGid p
      let (ruMap, rgMap, rInGrp, ru) := mappedFlags uidRanges gidRanges selfGids rug
      let rDev ← Env.statDev p
      let rIno ← Env.statIno p
      entries := entries ++ [{
        name := p, kind := .reg, mode := rm, modeExact := true,
        bytes := "asym\n".toUTF8,
        kernelDev? := if rDev != 0 then some rDev else none,
        kernelIno? := if rIno != 0 then some rIno else none,
        ownedByUid := ruMap && (ru == myUid), inGroup := rInGrp,
        ownerUid? := if ru != 0xffffffff then some ru else none,
        uidMapped := ruMap, gidMapped := rgMap
      }]
  for dname in #["s1777", "s1721", "s1002", "s_unmap"] do
    if ← (epWork / dname).pathExists then
      let dm ← Env.statMode dname.toUTF8
      let dug ← Env.statUidGid dname.toUTF8
      let (duMap, dgMap, dInGrp, du) := mappedFlags uidRanges gidRanges selfGids dug
      entries := entries ++ [{
        name := dname.toUTF8, kind := .dir, mode := dm, modeExact := true,
        ownedByUid := duMap && (du == myUid), inGroup := dInGrp,
        ownerUid? := if du != 0xffffffff then some du else none,
        uidMapped := duMap, gidMapped := dgMap
      }]
      if ← (epWork / dname / "reg666").pathExists then
        let p := s!"{dname}/reg666".toUTF8
        let rm ← Env.statMode p
        let rug ← Env.statUidGid p
        let (ruMap, rgMap, rInGrp, ru) := mappedFlags uidRanges gidRanges selfGids rug
        entries := entries ++ [{
          relDir := [dname.toUTF8], name := "reg666".toUTF8, kind := .reg, mode := rm, modeExact := true,
          bytes := "sticky\n".toUTF8,
          ownedByUid := ruMap && (ru == myUid), inGroup := rInGrp,
          ownerUid? := if ru != 0xffffffff then some ru else none,
          uidMapped := ruMap, gidMapped := rgMap
        }]
      for fname in #["f640", "f604", "g640", "g604"] do
        if ← (epWork / dname / fname).pathExists then
          let p := s!"{dname}/{fname}".toUTF8
          let fm ← Env.statMode p
          let fug ← Env.statUidGid p
          let (fuMap, fgMap, fInGrp, fu) := mappedFlags uidRanges gidRanges selfGids fug
          entries := entries ++ [{
            relDir := [dname.toUTF8], name := fname.toUTF8, kind := .reg, mode := fm, modeExact := true,
            bytes := "sticky\n".toUTF8,
            ownedByUid := fuMap && (fu == myUid), inGroup := fInGrp,
            ownerUid? := if fu != 0xffffffff then some fu else none,
            uidMapped := fuMap, gidMapped := fgMap
          }]
      let sockP := s!"{dname}/sock666".toUTF8
      if let .ok st ← ops.fstatat none sockP { symlinkNofollow := true } then
        let sug ← Env.statUidGid sockP
        let (suMap, sgMap, sInGrp, su) := mappedFlags uidRanges gidRanges selfGids sug
        entries := entries ++ [{
          relDir := [dname.toUTF8], name := "sock666".toUTF8, kind := .socket, mode := st.mode, modeExact := true,
          ownedByUid := suMap && (su == myUid), inGroup := sInGrp,
          ownerUid? := if su != 0xffffffff then some su else none,
          uidMapped := suMap, gidMapped := sgMap
        }]
      if ← (epWork / dname / "fifo666").pathExists then
        let p := s!"{dname}/fifo666".toUTF8
        let fm ← Env.statMode p
        let fug ← Env.statUidGid p
        let (fuMap, fgMap, fInGrp, fu) := mappedFlags uidRanges gidRanges selfGids fug
        entries := entries ++ [{
          relDir := [dname.toUTF8], name := "fifo666".toUTF8, kind := .fifo, mode := fm, modeExact := true,
          ownedByUid := fuMap && (fu == myUid), inGroup := fInGrp,
          ownerUid? := if fu != 0xffffffff then some fu else none,
          uidMapped := fuMap, gidMapped := fgMap
        }]
      if ← (epWork / dname / "u65534").pathExists then
        let p := s!"{dname}/u65534".toUTF8
        let um ← Env.statMode p
        let uug ← Env.statUidGid p
        let (uuMap, ugMap, uInGrp, uu) := mappedFlags uidRanges gidRanges selfGids uug
        let uDev ← Env.statDev p
        let uIno ← Env.statIno p
        let uMnt ← Env.statMntId p
        let (uMid, nmU, meU, mpU) ← internMountById p uMnt uDev false nextMid mountEntries mountProfiles
        nextMid := nmU; mountEntries := meU; mountProfiles := mpU
        entries := entries ++ [{
          relDir := [dname.toUTF8], name := "u65534".toUTF8, kind := .reg, mode := um, modeExact := true,
          kernelDev? := if uDev != 0 then some uDev else none,
          kernelIno? := if uIno != 0 then some uIno else none,
          mountId? := some uMid,
          allowDevInoAlias := true,
          ownedByUid := uuMap && (uu == myUid), inGroup := uInGrp,
          ownerUid? := if uu != 0xffffffff then some uu else none,
          uidMapped := uuMap, gidMapped := ugMap, dynamicMeta := true
        }]
      let symP := s!"{dname}/sym_other".toUTF8
      if let .ok _ ← ops.fstatat none symP { symlinkNofollow := true } then
        if let .ok tgt ← ops.readlinkat none symP 4096 then
          let sug ← Env.statUidGid symP
          let (suMap, sgMap, sInGrp, su) := mappedFlags uidRanges gidRanges selfGids sug
          entries := entries ++ [{
            relDir := [dname.toUTF8], name := "sym_other".toUTF8, kind := .symlink, mode := 0o777,
            symlinkTarget := tgt,
            ownedByUid := suMap && (su == myUid), inGroup := sInGrp,
            ownerUid? := if su != 0xffffffff then some su else none,
            uidMapped := suMap, gidMapped := sgMap
          }]
  if ← (epWork / "gd").pathExists then
    let gm ← Env.statMode "gd".toUTF8
    let gug ← Env.statUidGid "gd".toUTF8
    let (guMap, ggMap, gInGrp, gu) := mappedFlags uidRanges gidRanges selfGids gug
    entries := entries ++ [{
      name := "gd".toUTF8, kind := .dir, mode := gm, modeExact := true,
      ownedByUid := guMap && (gu == myUid), inGroup := gInGrp,
      ownerUid? := if gu != 0xffffffff then some gu else none,
      uidMapped := guMap, gidMapped := ggMap
    }]
    if ← (epWork / "gd" / "sgid2640").pathExists then
      let p := "gd/sgid2640".toUTF8
      let sm ← Env.statMode p
      let sug ← Env.statUidGid p
      let (suMap, sgMap, sInGrp, su) := mappedFlags uidRanges gidRanges selfGids sug
      entries := entries ++ [{
        relDir := ["gd".toUTF8], name := "sgid2640".toUTF8, kind := .reg, mode := sm, modeExact := true,
        bytes := "sgid\n".toUTF8,
        ownedByUid := suMap && (su == myUid), inGroup := sInGrp,
        ownerUid? := if su != 0xffffffff then some su else none,
        uidMapped := suMap, gidMapped := sgMap
      }]
  return (entries, nextMid, mountEntries, mountProfiles)

private def probeOuterEntry (relDir : List ByteArray) (name : ByteArray)
    (absPath : String) (kind : FileKind) (myUid : UInt32)
    (uidRanges gidRanges : List (UInt32 × UInt32)) (selfGids : List UInt32) : IO (Option SeedEntry) := do
  let p := absPath.toUTF8
  let m ← Env.statMode p
  let dev ← Env.statDev p
  let ino ← Env.statIno p
  if m == 0 && ino == 0 then return none
  let ug ← Env.statUidGid p
  let (uMap, gMap, gInGrp, uid) := mappedFlags uidRanges gidRanges selfGids ug
  return some {
    relDir, name, kind, mode := m, modeExact := true,
    kernelDev? := if dev != 0 then some dev else none,
    kernelIno? := if ino != 0 then some ino else none,
    ownedByUid := uMap && (uid == myUid),
    inGroup := gInGrp,
    ownerUid? := if uid != 0xffffffff then some uid else none,
    uidMapped := uMap, gidMapped := gMap,
    dynamicMeta := true
  }

private def unlinkSeededCwd (s : FilesState) : FilesState :=
  let cwdSegs := (splitPathBytes s.cwdPath.bytes).2.1
  match cwdSegs.reverse, assocGet s.inodes s.cwdIno with
  | leaf :: _, some cwdVn =>
    let pIno := cwdVn.parentIno
    let inodes1 := match assocGet s.inodes pIno with
      | none => s.inodes
      | some pVn =>
        let pVn' := match pVn.data with
          | .dir dd => { pVn with
              data := .dir { dd with children := bytesAssocErase dd.children leaf }
              nlink := if pVn.nlink > 0 then pVn.nlink - 1 else 0 }
          | _ => pVn
        assocSet s.inodes pIno pVn'
    let cwdVn' := match cwdVn.data with
      | .dir dd =>
        if cwdVn.mayCopyUp then
          { cwdVn with data := .dir { dd with children := [], lifecycle := .overlayDeadLower } }
        else
          { cwdVn with data := .dir { dd with children := [], lifecycle := .unlinked }, nlink := 0 }
      | _ => cwdVn
    { s with inodes := assocSet inodes1 s.cwdIno cwdVn', cwdPath := .unbound s.cwdPath.bytes }
  | _, _ => { s with cwdPath := .unbound s.cwdPath.bytes }

private def probeOwnedByUid (ops : FilesOps) (selfUMap uMap : Bool) (uid myUid : UInt32)
    (path : ByteArray) (mode : Mode) (follow : Bool := true) (dfltUnmapped : Bool := false) : IO Bool := do
  if uMap then return (uid == myUid)
  else if selfUMap || uid != myUid then return false
  else
    let uB := (mode >>> 6) &&& 7
    let gB := (mode >>> 3) &&& 7
    let oB := mode &&& 7
    let goB := gB ||| oB
    let fl : AtFlags := { eaccess := true, symlinkNofollow := !follow }
    if (uB &&& 4) != 0 && (goB &&& 4) == 0 then
      return (← ops.faccessat none path { read := true } fl).isOk
    else if (uB &&& 1) != 0 && (goB &&& 1) == 0 then
      return (← ops.faccessat none path { exec := true } fl).isOk
    else if (uB &&& 2) != 0 && (goB &&& 2) == 0 && !(← Env.statfsIsReadOnly path) then
      return (← ops.faccessat none path { write := true } fl).isOk
    else if (uB &&& 4) == 0 && (gB &&& 4) != 0 && (oB &&& 4) != 0 then
      return !(← ops.faccessat none path { read := true } fl).isOk
    else if (uB &&& 1) == 0 && (gB &&& 1) != 0 && (oB &&& 1) != 0 then
      return !(← ops.faccessat none path { exec := true } fl).isOk
    else if (uB &&& 2) == 0 && (gB &&& 2) != 0 && (oB &&& 2) != 0 && !(← Env.statfsIsReadOnly path) then
      return !(← ops.faccessat none path { write := true } fl).isOk
    else
      return dfltUnmapped

private def materializeEpisode (ops : FilesOps) (epDir : System.FilePath)
    (crossDir? : Option System.FilePath) (supportsSeals : Bool)
    (in0 out1 err2 : FileKind × Option SpecialDevKind) (recipe : EpisodeRecipe)
    (isRoSeeded : Bool := false) (chrootUnreachable : Bool := false)
    (ambientSeccomp : Bool := false) (unlinkedCwd : Bool := false)
    (chrootOuterEntries : List SeedEntry := []) :
    IO (SeedTreeConfig × Option System.FilePath × Option String) := do
  let _ ← Env.umask 0o022
  if chrootUnreachable then
    let _ ← Env.chmod "/".toUTF8 0o755
    let _ ← Env.chmod "/etc".toUTF8 0o755
    if !(← (System.FilePath.mk "/etc/passwd").pathExists) then
      IO.FS.writeFile "/etc/passwd" "root:x:0:0:root:/:/bin/sh\n"
    let _ ← Env.chmod "/etc/passwd".toUTF8 0o644
    let _ ← Env.chmod "/sys".toUTF8 0o555
    let _ ← Env.chmod "/sys/kernel".toUTF8 0o755
    if !(← (System.FilePath.mk "/sys/kernel/cpu_byteorder").pathExists) then
      IO.FS.writeFile "/sys/kernel/cpu_byteorder" "little\n"
    let _ ← Env.chmod "/sys/kernel/cpu_byteorder".toUTF8 0o444
    let _ ← Env.chmod "/sys/kernel/debug".toUTF8 0o700
  let myUid ← Env.getUid
  let myPid ← Env.getPid
  let capEff ← Env.readCapEff
  let uidRanges ← Env.readIdMap "/proc/self/uid_map"
  let gidRanges ← Env.readIdMap "/proc/self/gid_map"
  let selfGids ← Env.readSelfGids
  let selfUMap := Env.isIdMapped uidRanges myUid
  let selfGMap := !gidRanges.isEmpty && (selfGids.isEmpty || selfGids.any (Env.isIdMapped gidRanges))
  let protReg ← Env.readSysctlU32 "/proc/sys/fs/protected_regular" 2
  let protFifo ← Env.readSysctlU32 "/proc/sys/fs/protected_fifos" 1
  let protSym ← Env.readSysctlU32 "/proc/sys/fs/protected_symlinks" 0
  let hostUg ← Env.statUidGid "/etc/passwd".toUTF8
  let (hostUidMapped, hostGidMapped, hostSyntheticInGroup, _) := mappedFlags uidRanges gidRanges selfGids hostUg
  let devNullUg ← Env.statUidGid "/dev/null".toUTF8
  let (devUidMapped, devGidMapped, devInGroup, devUid) := mappedFlags uidRanges gidRanges selfGids devNullUg
  let devOwnedByUid := devUidMapped && (devUid == myUid)
  let proc1Ug ← Env.statUidGid "/proc/1".toUTF8
  let (proc1UidMapped, proc1GidMapped, proc1InGroup, proc1Uid) := mappedFlags uidRanges gidRanges selfGids proc1Ug
  let exeUg ← Env.statFollowUidGid "/proc/self/exe".toUTF8
  let (exeUMap, _, _, exeUid) := mappedFlags uidRanges gidRanges selfGids exeUg
  let exeOwnedByUid := (exeUMap && exeUid == myUid) || !selfUMap
  let devNullDev ← Env.statDev "/dev/null".toUTF8
  let devNullIno ← Env.statIno "/dev/null".toUTF8
  let devZeroDev ← Env.statDev "/dev/zero".toUTF8
  let devZeroIno ← Env.statIno "/dev/zero".toUTF8
  let devFullDev ← Env.statDev "/dev/full".toUTF8
  let devFullIno ← Env.statIno "/dev/full".toUTF8
  let in0Mode ← Env.fdMode 0
  let in0Ug ← Env.fdUidGid 0
  let (stdinUidMapped, stdinGidMapped, stdinInGroup, in0Uid) := mappedFlags uidRanges gidRanges selfGids in0Ug
  let in0Dev ← Env.fdDev 0
  let in0Ino ← Env.fdIno 0
  let out1Mode ← Env.fdMode 1
  let out1Ug ← Env.fdUidGid 1
  let (stdoutUidMapped, stdoutGidMapped, stdoutInGroup, out1Uid) := mappedFlags uidRanges gidRanges selfGids out1Ug
  let out1Dev ← Env.fdDev 1
  let out1Ino ← Env.fdIno 1
  let err2Mode ← Env.fdMode 2
  let err2Ug ← Env.fdUidGid 2
  let (stderrUidMapped, stderrGidMapped, stderrInGroup, err2Uid) := mappedFlags uidRanges gidRanges selfGids err2Ug
  let err2Dev ← Env.fdDev 2
  let err2Ino ← Env.fdIno 2
  let stdinOwned ←
    if (← Env.fdKind 0) != 0 then probeOwnedByUid ops selfUMap stdinUidMapped in0Uid myUid "/proc/self/fd/0".toUTF8 in0Mode true false
    else pure false
  let stdoutOwned ←
    if (← Env.fdKind 1) != 0 then probeOwnedByUid ops selfUMap stdoutUidMapped out1Uid myUid "/proc/self/fd/1".toUTF8 out1Mode true false
    else pure false
  let stderrOwned ←
    if (← Env.fdKind 2) != 0 then probeOwnedByUid ops selfUMap stderrUidMapped err2Uid myUid "/proc/self/fd/2".toUTF8 err2Mode true false
    else pure false
  let lstatModeOr : ByteArray → Mode → IO Mode := fun p dflt => do
    match ← ops.fstatat none p { symlinkNofollow := true } with
    | .ok st => return st.mode
    | .error _ => return dflt
  let procFd0Mode ← lstatModeOr "/proc/self/fd/0".toUTF8 0o777
  let procFd1Mode ← lstatModeOr "/proc/self/fd/1".toUTF8 0o777
  let procFd2Mode ← lstatModeOr "/proc/self/fd/2".toUTF8 0o777

  let useSubWork := !isRoSeeded && !chrootUnreachable && !unlinkedCwd && recipe.cwdSubdir
  let mut hasPreseededLower := false
  let hasPreseededSticky := !isRoSeeded && !unlinkedCwd && (← (epDir / "s1777" / "f640").pathExists)
  let existedLowerUnlinked := unlinkedCwd && !isRoSeeded && (← epDir.pathExists)
  if !isRoSeeded then
    hasPreseededLower := (← (epDir / "lf").pathExists)
    if !hasPreseededLower && !hasPreseededSticky && !chrootUnreachable && !unlinkedCwd then
      removeDirForced epDir
    IO.FS.createDirAll epDir
  let epWork := if useSubWork && !hasPreseededLower && !hasPreseededSticky then epDir / "work" else epDir
  if useSubWork && !hasPreseededLower && !hasPreseededSticky then
    IO.FS.createDirAll epWork
  let epReal ←
    if chrootUnreachable then pure epWork
    else IO.FS.realPath epWork
  let epBytes :=
    if chrootUnreachable then s!"/{epWork.fileName.getD "ep"}".toUTF8
    else epReal.toString.toUTF8
  IO.Process.setCurrentDir epWork

  let rootMnt ← Env.statMntId "/".toUTF8
  let rootDev ← Env.statDev "/".toUTF8
  let rootIno ← Env.statIno "/".toUTF8
  let rootMode ← Env.statMode "/".toUTF8
  let rootUg ← Env.statUidGid "/".toUTF8
  let (rootUidMapped, rootGidMapped, rootInGroup, rootUid) := mappedFlags uidRanges gidRanges selfGids rootUg
  let rootOwned ← probeOwnedByUid ops selfUMap rootUidMapped rootUid myUid "/".toUTF8 rootMode true false
  let sysMnt ← Env.statMntId "/sys".toUTF8
  let rootProf ← mountProfileForPath "/".toUTF8 false
  let mut mountEntries : List MountIdEntry := [{ mntId := rootMnt, dev := rootDev, mid := 0 }]
  let mut mountProfiles : List (Nat × MountProfile) := [(0, rootProf)]
  let mut nextMid : Nat := 4

  let devNullMnt ← Env.statMntId "/dev/null".toUTF8
  let (devMountId, nm1, me1, mp1) ←
    internMountById "/dev/null".toUTF8 devNullMnt devNullDev false nextMid mountEntries mountProfiles
  nextMid := nm1; mountEntries := me1; mountProfiles := mp1

  let epMnt ← Env.statMntId ".".toUTF8
  let epDev ← Env.statDev ".".toUTF8
  let epIno ← Env.statIno ".".toUTF8
  let epMode ← Env.statMode ".".toUTF8
  let (cwdMountId, nm2, me2, mp2) ←
    internMountById ".".toUTF8 epMnt epDev supportsSeals nextMid mountEntries mountProfiles
  nextMid := nm2; mountEntries := me2; mountProfiles := mp2

  let epParentQuery := "..".toUTF8
  let epParentMnt ← Env.statMntId epParentQuery
  let epParentDev ← Env.statDev epParentQuery
  let epParentIno ← Env.statIno epParentQuery
  let epParentMode ← Env.statMode epParentQuery
  let epParentUg ← Env.statUidGid epParentQuery
  let (epParentUMap, _, _, epParentUid) := mappedFlags uidRanges gidRanges selfGids epParentUg
  let epParentOwned ← probeOwnedByUid ops selfUMap epParentUMap epParentUid myUid epParentQuery epParentMode true false
  let (cwdParentMountId, nm3, me3, mp3) ←
    internMountById epParentQuery epParentMnt epParentDev false nextMid mountEntries mountProfiles
  nextMid := nm3; mountEntries := me3; mountProfiles := mp3

  let mut chrootOutsideAncestors : List (Mode × Bool × Nat × Option UInt64 × Option UInt64) := []
  if chrootUnreachable then
    let mut ancArr : Array (Mode × Bool × Nat × Option UInt64 × Option UInt64) :=
      #[(epParentMode, epParentOwned, cwdParentMountId,
        if epParentDev != 0 then some epParentDev else none,
        if epParentIno != 0 then some epParentIno else none)]
    let mut prevDev := epParentDev
    let mut prevIno := epParentIno
    let mut curRel := "../..".toUTF8
    for _ in [:16] do
      let aMnt ← Env.statMntId curRel
      let aDev ← Env.statDev curRel
      let aIno ← Env.statIno curRel
      if aIno == 0 || (aDev == prevDev && aIno == prevIno) then
        break
      let aMode ← Env.statMode curRel
      let aUg ← Env.statUidGid curRel
      let (aUMap, _, _, aUid) := mappedFlags uidRanges gidRanges selfGids aUg
      let aOwned ← probeOwnedByUid ops selfUMap aUMap aUid myUid curRel aMode true false
      let (aMid, nmA, meA, mpA) ←
        internMountById curRel aMnt aDev false nextMid mountEntries mountProfiles
      nextMid := nmA; mountEntries := meA; mountProfiles := mpA
      ancArr := ancArr.push (aMode, aOwned, aMid, some aDev, some aIno)
      prevDev := aDev
      prevIno := aIno
      curRel := curRel ++ "/..".toUTF8
    chrootOutsideAncestors := ancArr.toList

  let internStdFdMount := fun (fdPath : ByteArray) (dev : UInt64)
      (nextMid0 : Nat) (mountProfiles0 : List (Nat × MountProfile)) => do
    let prof ← mountProfileForPath fdPath false
    match mountEntries.find? (fun e =>
        e.dev != 0 && e.dev == dev &&
        ((mountProfiles0.find? (·.1 == e.mid)).map (·.2.readOnly) == some prof.readOnly)) with
    | some e => pure (e.mid, nextMid0, mountProfiles0)
    | none =>
      let mid := nextMid0
      pure (mid, nextMid0 + 1, mountProfiles0 ++ [(mid, prof)])
  let (stdinMountId, nm4a, mp4a) ← internStdFdMount "/proc/self/fd/0".toUTF8 in0Dev nextMid mountProfiles
  let (stdoutMountId, nm4b, mp4b) ← internStdFdMount "/proc/self/fd/1".toUTF8 out1Dev nm4a mp4a
  let (stderrMountId, nm4, mp4) ← internStdFdMount "/proc/self/fd/2".toUTF8 err2Dev nm4b mp4b
  nextMid := nm4; mountProfiles := mp4
  let epProf := (mountProfiles.find? (·.1 == cwdMountId)).map (·.2) |>.getD {}

  let mut crossPathOpt : Option ByteArray := none
  let mut crossStrOpt : Option String := none
  let mut crossDirCleanup : Option System.FilePath := none
  let mut crossRealOpt : Option System.FilePath := none
  let mut crossMountId : Nat := 5
  let mut crossParentMountId : Nat := 5
  let mut crossKernelDev? : Option UInt64 := none
  let mut crossKernelIno? : Option UInt64 := none
  let mut crossMode : Mode := 0o755
  let mut crossEntries : List SeedEntry := []
  if !isRoSeeded && !chrootUnreachable && recipe.seedCross then
    if let some cd := crossDir? then
      removeDirForced cd
      IO.FS.createDirAll cd
      let cdReal ← IO.FS.realPath cd
      crossRealOpt := some cdReal
      crossDirCleanup := some cdReal
      let cdStr := cdReal.toString
      let cdBytes := cdStr.toUTF8
      crossPathOpt := some cdBytes
      crossStrOpt := some cdStr
      let cdMnt ← Env.statMntId cdBytes
      let cdDev ← Env.statDev cdBytes
      let cdIno ← Env.statIno cdBytes
      crossMode ← Env.statMode cdBytes
      crossKernelDev? := if cdDev != 0 then some cdDev else none
      crossKernelIno? := if cdIno != 0 then some cdIno else none
      let (cMid, nma, mea, mpa) ←
        internMountById cdBytes cdMnt cdDev false nextMid mountEntries mountProfiles
      nextMid := nma; mountEntries := mea; mountProfiles := mpa
      crossMountId := cMid
      let cdParentBytes := (cdReal.parent.getD "/").toString.toUTF8
      let cdParentMnt ← Env.statMntId cdParentBytes
      let cdParentDev ← Env.statDev cdParentBytes
      let (cpMid, nmb, meb, mpb) ←
        internMountById cdParentBytes cdParentMnt cdParentDev false nextMid mountEntries mountProfiles
      nextMid := nmb; mountEntries := meb; mountProfiles := mpb
      crossParentMountId := cpMid
      if let .ok cfd ← ops.openat none (cdStr ++ "/cf").toUTF8 { access := .rdwr, creat := true } 0o644 then
        let _ ← ops.write cfd "cross".toUTF8
        let _ ← ops.close cfd
        let cfMode ← Env.statMode (cdStr ++ "/cf").toUTF8
        crossEntries := [{ name := "cf".toUTF8, kind := .reg, mode := cfMode, modeExact := true, bytes := "cross".toUTF8 }]

  let mut ancestorMeta : List (ByteArray × Mode × Bool × Nat × Option UInt64 × Option UInt64) := []
  let mut ancestorOwnerUids : List (ByteArray × UInt32) := []
  let mut ancestorMapped : List (ByteArray × Bool × Bool) := []
  let mut ancestorInGroups : List (ByteArray × Bool) := []
  if !chrootUnreachable then
    let mut seenAncestors : List String := []
    let mut allAncestors := strictAncestors epReal
    if let some cdr := crossRealOpt then
      allAncestors := allAncestors ++ strictAncestors cdr
    let tmpPath := System.FilePath.mk "/tmp"
    if ← tmpPath.pathExists then
      allAncestors := allAncestors ++ [tmpPath]
    for ap in allAncestors do
      let apStr := ap.toString
      if !seenAncestors.contains apStr then
        seenAncestors := apStr :: seenAncestors
        let apBytes := apStr.toUTF8
        let apMode ← Env.statMode apBytes
        let apUg ← Env.statUidGid apBytes
        let (apUMap, apGMap, apInGrp, apUid) := mappedFlags uidRanges gidRanges selfGids apUg
        let apMnt ← Env.statMntId apBytes
        let apDev ← Env.statDev apBytes
        let apIno ← Env.statIno apBytes
        let apOwned ← probeOwnedByUid ops selfUMap apUMap apUid myUid apBytes apMode true false
        let (apMid, nmc, mec, mpc) ←
          internMountById apBytes apMnt apDev false nextMid mountEntries mountProfiles
        nextMid := nmc; mountEntries := mec; mountProfiles := mpc
        ancestorMeta := ancestorMeta ++ [
          (apBytes, apMode, apOwned, apMid,
            if apDev != 0 then some apDev else none,
            if apIno != 0 then some apIno else none)
        ]
        if apUid != 0xffffffff then
          ancestorOwnerUids := ancestorOwnerUids ++ [(apBytes, apUid)]
        ancestorMapped := ancestorMapped ++ [(apBytes, apUMap, apGMap)]
        ancestorInGroups := ancestorInGroups ++ [(apBytes, apInGrp)]

  let mut cwdEntries : List SeedEntry := []
  if isRoSeeded then
    let (roEntries, nmR, meR, mpR) ← inspectExistingEntries epWork uidRanges gidRanges selfGids nextMid mountEntries mountProfiles
    cwdEntries := roEntries
    nextMid := nmR; mountEntries := meR; mountProfiles := mpR
  else if !unlinkedCwd then
    if hasPreseededSticky then
      let (stEntries, nmS, meS, mpS) ← inspectExistingEntries epWork uidRanges gidRanges selfGids nextMid mountEntries mountProfiles
      cwdEntries := cwdEntries ++ stEntries
      nextMid := nmS; mountEntries := meS; mountProfiles := mpS
    if hasPreseededLower then
      if ← (System.FilePath.mk "lf").pathExists then
        let lfMode ← Env.statMode "lf".toUTF8
        let lfDev ← Env.statDev "lf".toUTF8
        let lfIno ← Env.statIno "lf".toUTF8
        cwdEntries := cwdEntries ++ [{
          name := "lf".toUTF8, kind := .reg, mode := lfMode, modeExact := true,
          bytes := "low-file\n".toUTF8,
          kernelDev? := if lfDev != 0 then some lfDev else none,
          kernelIno? := if lfIno != 0 then some lfIno else none,
          mayCopyUp := epProf.isOverlay
        }]
      if ← (System.FilePath.mk "hl_lo1").pathExists then
        let h1Mode ← Env.statMode "hl_lo1".toUTF8
        let h1Dev ← Env.statDev "hl_lo1".toUTF8
        let h1Ino ← Env.statIno "hl_lo1".toUTF8
        cwdEntries := cwdEntries ++ [
          { name := "hl_lo1".toUTF8, kind := .reg, mode := h1Mode, modeExact := true,
            bytes := "low-hl\n".toUTF8, hardlinkGroup? := some 2,
            kernelDev? := if h1Dev != 0 then some h1Dev else none,
            kernelIno? := if h1Ino != 0 then some h1Ino else none,
            mayCopyUp := epProf.isOverlay },
          { name := "hl_lo2".toUTF8, kind := .reg, mode := h1Mode, modeExact := true,
            bytes := "low-hl\n".toUTF8, hardlinkGroup? := some 2,
            mayCopyUp := epProf.isOverlay }
        ]
      if ← (System.FilePath.mk "ldir").pathExists then
        let ldMode ← Env.statMode "ldir".toUTF8
        let ldDev ← Env.statDev "ldir".toUTF8
        let ldIno ← Env.statIno "ldir".toUTF8
        cwdEntries := cwdEntries ++ [{
          name := "ldir".toUTF8, kind := .dir, mode := ldMode, modeExact := true,
          kernelDev? := if ldDev != 0 then some ldDev else none,
          kernelIno? := if ldIno != 0 then some ldIno else none,
          mayCopyUp := epProf.isOverlay
        }]
        if ← (System.FilePath.mk "ldir" / "x").pathExists then
          let lxMode ← Env.statMode "ldir/x".toUTF8
          let lxDev ← Env.statDev "ldir/x".toUTF8
          let lxIno ← Env.statIno "ldir/x".toUTF8
          cwdEntries := cwdEntries ++ [{
            relDir := ["ldir".toUTF8], name := "x".toUTF8, kind := .reg,
            mode := lxMode, modeExact := true, bytes := "low-x\n".toUTF8,
            kernelDev? := if lxDev != 0 then some lxDev else none,
            kernelIno? := if lxIno != 0 then some lxIno else none,
            mayCopyUp := epProf.isOverlay
          }]
      if ← (System.FilePath.mk "empty_ldir").pathExists then
        let eldMode ← Env.statMode "empty_ldir".toUTF8
        let eldDev ← Env.statDev "empty_ldir".toUTF8
        let eldIno ← Env.statIno "empty_ldir".toUTF8
        cwdEntries := cwdEntries ++ [{
          name := "empty_ldir".toUTF8, kind := .dir, mode := eldMode, modeExact := true,
          kernelDev? := if eldDev != 0 then some eldDev else none,
          kernelIno? := if eldIno != 0 then some eldIno else none,
          mayCopyUp := epProf.isOverlay
        }]
      if ← (System.FilePath.mk "sym_hla").pathExists then
        cwdEntries := cwdEntries ++ [{
          name := "sym_hla".toUTF8, kind := .symlink, mode := 0o777,
          symlinkTarget := "hl_lo1".toUTF8,
          mayCopyUp := epProf.isOverlay
        }]
      for nm in #["suid_lf", "sgid_lf", "sgid_nogrp_lf"] do
        if ← (System.FilePath.mk nm).pathExists then
          let sMode ← Env.statMode nm.toUTF8
          let sDev ← Env.statDev nm.toUTF8
          let sIno ← Env.statIno nm.toUTF8
          let sUg ← Env.statUidGid nm.toUTF8
          let (sUMap, sGMap, sInGrp, sUid) := mappedFlags uidRanges gidRanges selfGids sUg
          cwdEntries := cwdEntries ++ [{
            name := nm.toUTF8, kind := .reg, mode := sMode, modeExact := true,
            bytes := "low-suid\n".toUTF8,
            kernelDev? := if sDev != 0 then some sDev else none,
            kernelIno? := if sIno != 0 then some sIno else none,
            ownedByUid := (sUMap && sUid == myUid) || !selfUMap, inGroup := sInGrp,
            ownerUid? := if sUid != 0xffffffff then some sUid else none,
            uidMapped := sUMap, gidMapped := sGMap,
            mayCopyUp := epProf.isOverlay
          }]
    IO.FS.createDir (System.FilePath.mk "sub")
    if recipe.sgidSub then
      let _ ← Env.chmod "sub".toUTF8 0o2755
    let subMode ← Env.statMode "sub".toUTF8
    cwdEntries := cwdEntries ++ [{ name := "sub".toUTF8, kind := .dir, mode := subMode, modeExact := true }]
    if let .ok sfd ← ops.openat none "sub/a".toUTF8 { access := .rdwr, creat := true } 0o644 then
      let _ ← ops.write sfd "init-a".toUTF8
      let _ ← ops.close sfd
      let saMode ← Env.statMode "sub/a".toUTF8
      cwdEntries := cwdEntries ++ [{ relDir := ["sub".toUTF8], name := "a".toUTF8, kind := .reg, mode := saMode, modeExact := true, bytes := "init-a".toUTF8 }]

    IO.FS.createDir (System.FilePath.mk "empty_d")
    let emptyMode ← Env.statMode "empty_d".toUTF8
    cwdEntries := cwdEntries ++ [{ name := "empty_d".toUTF8, kind := .dir, mode := emptyMode, modeExact := true }]

    IO.FS.createDir (System.FilePath.mk "s1721")
    let _ ← Env.chmod "s1721".toUTF8 0o1721
    let s1721Mode ← Env.statMode "s1721".toUTF8
    let s1721Ug ← Env.statUidGid "s1721".toUTF8
    let (s1721UMap, s1721GMap, s1721InGrp, s1721Uid) := mappedFlags uidRanges gidRanges selfGids s1721Ug
    cwdEntries := cwdEntries ++ [{
      name := "s1721".toUTF8, kind := .dir, mode := s1721Mode, modeExact := true,
      ownedByUid := true, inGroup := s1721InGrp || !selfGMap,
      ownerUid? := if s1721Uid != 0xffffffff then some s1721Uid else none,
      uidMapped := s1721UMap, gidMapped := s1721GMap
    }]
    if let .ok r666 ← ops.openat none "s1721/reg666".toUTF8 { access := .rdwr, creat := true } 0o666 then
      let _ ← ops.write r666 "s".toUTF8
      let _ ← ops.close r666
      let _ ← Env.chmod "s1721/reg666".toUTF8 0o666
      let rm ← Env.statMode "s1721/reg666".toUTF8
      let rug ← Env.statUidGid "s1721/reg666".toUTF8
      let (ruMap, rgMap, rInGrp, ru) := mappedFlags uidRanges gidRanges selfGids rug
      cwdEntries := cwdEntries ++ [{
        relDir := ["s1721".toUTF8], name := "reg666".toUTF8, kind := .reg, mode := rm, modeExact := true,
        bytes := "s".toUTF8, ownedByUid := true, inGroup := rInGrp || !selfGMap,
        ownerUid? := if ru != 0xffffffff then some ru else none,
        uidMapped := ruMap, gidMapped := rgMap
      }]
    if (← Env.mkfifo "s1721/fifo666".toUTF8 0o666) == 0 then
      let _ ← Env.chmod "s1721/fifo666".toUTF8 0o666
      let fm ← Env.statMode "s1721/fifo666".toUTF8
      let fug ← Env.statUidGid "s1721/fifo666".toUTF8
      let (fuMap, fgMap, fInGrp, fu) := mappedFlags uidRanges gidRanges selfGids fug
      cwdEntries := cwdEntries ++ [{
        relDir := ["s1721".toUTF8], name := "fifo666".toUTF8, kind := .fifo, mode := fm, modeExact := true,
        ownedByUid := true, inGroup := fInGrp || !selfGMap,
        ownerUid? := if fu != 0xffffffff then some fu else none,
        uidMapped := fuMap, gidMapped := fgMap
      }]

    if recipe.seedD255 then
      IO.FS.createDir (System.FilePath.mk "d255")
      let d255Mode ← Env.statMode "d255".toUTF8
      cwdEntries := cwdEntries ++ [{ name := "d255".toUTF8, kind := .dir, mode := d255Mode, modeExact := true }]
      let pLong := "d255/".toUTF8 ++ longSName
      if let .ok lfd ← ops.openat none pLong { access := .rdwr, creat := true } 0o644 then
        let _ ← ops.close lfd
        let lsMode ← Env.statMode pLong
        cwdEntries := cwdEntries ++ [{ relDir := ["d255".toUTF8], name := longSName, kind := .reg, mode := lsMode, modeExact := true }]

    if recipe.seedHardlinks then
      if let .ok hfd ← ops.openat none "hl1".toUTF8 { access := .rdwr, creat := true } 0o644 then
        let _ ← ops.write hfd "hl-data".toUTF8
        let _ ← ops.close hfd
        let hlMode ← Env.statMode "hl1".toUTF8
        if (← Env.link "hl1".toUTF8 "hl2".toUTF8) == 0 then
          cwdEntries := cwdEntries ++ [
            { name := "hl1".toUTF8, kind := .reg, mode := hlMode, modeExact := true, bytes := "hl-data".toUTF8, hardlinkGroup? := some 1 },
            { name := "hl2".toUTF8, kind := .reg, mode := hlMode, modeExact := true, bytes := "hl-data".toUTF8, hardlinkGroup? := some 1 }
          ]
        else
          cwdEntries := cwdEntries ++ [{ name := "hl1".toUTF8, kind := .reg, mode := hlMode, modeExact := true, bytes := "hl-data".toUTF8 }]

    if recipe.seedFifo then
      if (← Env.mkfifo "p.fifo".toUTF8 0o644) == 0 then
        let _ ← Env.chmod "p.fifo".toUTF8 0o6755
        let fMode ← Env.statMode "p.fifo".toUTF8
        cwdEntries := cwdEntries ++ [{ name := "p.fifo".toUTF8, kind := .fifo, mode := fMode, modeExact := true }]
      if (← Env.mkfifo "p444.fifo".toUTF8 0o444) == 0 then
        let _ ← Env.chmod "p444.fifo".toUTF8 0o444
        let f444Mode ← Env.statMode "p444.fifo".toUTF8
        cwdEntries := cwdEntries ++ [{ name := "p444.fifo".toUTF8, kind := .fifo, mode := f444Mode, modeExact := true }]
      if (← Env.mkfifo "p000.fifo".toUTF8 0o000) == 0 then
        let _ ← Env.chmod "p000.fifo".toUTF8 0o000
        let f000Mode ← Env.statMode "p000.fifo".toUTF8
        cwdEntries := cwdEntries ++ [{ name := "p000.fifo".toUTF8, kind := .fifo, mode := f000Mode, modeExact := true }]

    if recipe.seedSock then
      if (← Env.mksock "p.sock".toUTF8) == 0 then
        let kMode ← Env.statMode "p.sock".toUTF8
        cwdEntries := cwdEntries ++ [{ name := "p.sock".toUTF8, kind := .socket, mode := kMode, modeExact := true }]

    if recipe.seedSymlinks then
      let mut syms : Array (String × String) := #[
        ("lnk_null", "/dev/null"),
        ("lnk_zero", "/dev/zero"),
        ("lnk_full", "/dev/full"),
        ("lnk_proc", "/proc/self/status"),
        ("lnk_exe", "/proc/self/exe"),
        ("lnk_etc", "/etc/passwd"),
        ("lnk_root", "/"),
        ("lnk_sub", "sub")
      ]
      if let some cs := crossStrOpt then
        syms := syms.push ("lnk_cross", cs)
      for (lname, target) in syms do
        if let .ok () ← ops.symlinkat target.toUTF8 none lname.toUTF8 then
          cwdEntries := cwdEntries ++ [{ name := lname.toUTF8, kind := .symlink, mode := 0o777, symlinkTarget := target.toUTF8 }]

  let p1SelfOwned := proc1UidMapped && (proc1Uid == myUid)
  let mut p1CwdMode : Mode := 0o755
  let mut p1CwdOwned : Bool := p1SelfOwned
  let mut p1CwdInGrp : Bool := proc1InGroup
  let mut p1CwdUMap : Bool := proc1UidMapped
  let mut p1CwdGMap : Bool := proc1GidMapped
  let mut p1CwdMountId : Nat := 0
  let mut p1CwdDev : UInt64 := 0
  let mut p1CwdIno : UInt64 := 0
  let mut p1Fd0LinkMode : Mode := 0o777
  let mut p1Fd0Kind : FileKind := .charDev
  let mut p1Fd0DevKind? : Option CharDevKind := some .nullDev
  let mut p1Fd0Mode : Mode := 0o666
  let mut p1Fd0Owned : Bool := p1SelfOwned
  let mut p1Fd0InGrp : Bool := proc1InGroup
  let mut p1Fd0UMap : Bool := proc1UidMapped
  let mut p1Fd0GMap : Bool := proc1GidMapped
  let mut p1Fd0MountId : Nat := 1
  let mut p1Fd0Dev : UInt64 := 0
  let mut p1Fd0Ino : UInt64 := 0
  if myPid != 1 && p1SelfOwned then
    let p1CwdPath := "/proc/1/cwd".toUTF8
    if let .ok st ← ops.fstatat none p1CwdPath {} then
      p1CwdMode := st.mode
      let p1CwdUg ← Env.statFollowUidGid p1CwdPath
      let (uM, gM, iG, u) := mappedFlags uidRanges gidRanges selfGids p1CwdUg
      p1CwdOwned := uM && (u == myUid); p1CwdInGrp := iG; p1CwdUMap := uM; p1CwdGMap := gM
      p1CwdDev := st.dev
      p1CwdIno := st.ino
      let (m1, nmC, mpC) ← internStdFdMount p1CwdPath p1CwdDev nextMid mountProfiles
      p1CwdMountId := m1; nextMid := nmC; mountProfiles := mpC
    let p1Fd0Path := "/proc/1/fd/0".toUTF8
    p1Fd0LinkMode ← lstatModeOr p1Fd0Path 0o777
    if let .ok st ← ops.fstatat none p1Fd0Path {} then
      p1Fd0Kind := st.kind
      p1Fd0DevKind? :=
        if st.kind == .charDev then
          if st.dev == devNullDev && st.ino == devNullIno then some .nullDev
          else if st.dev == devZeroDev && st.ino == devZeroIno then some .zeroDev
          else if st.dev == devFullDev && st.ino == devFullIno then some .fullDev
          else some .generic
        else none
      p1Fd0Mode := st.mode
      p1Fd0Dev := st.dev
      p1Fd0Ino := st.ino
      let p1Fd0Ug ← Env.statFollowUidGid p1Fd0Path
      let (uM, gM, iG, u) := mappedFlags uidRanges gidRanges selfGids p1Fd0Ug
      p1Fd0Owned := uM && (u == myUid); p1Fd0InGrp := iG; p1Fd0UMap := uM; p1Fd0GMap := gM
      let (m0, nmF, mpF) ← internStdFdMount p1Fd0Path p1Fd0Dev nextMid mountProfiles
      p1Fd0MountId := m0; nextMid := nmF; mountProfiles := mpF

  let cfg : SeedTreeConfig := {
    cwdPath := epBytes
    cwdBound := !chrootUnreachable && !unlinkedCwd
    umask := recipe.epUmask
    cwdMode := epMode
    cwdMountId := cwdMountId
    cwdParentMountId := cwdParentMountId
    cwdParentMode := epParentMode
    cwdParentOwnedByUid := epParentOwned
    cwdParentOwnerUid? := if epParentUid != 0xffffffff then some epParentUid else none
    cwdKernelIno? := if epIno != 0 then some epIno else none
    cwdKernelDev? := if epDev != 0 then some epDev else none
    cwdParentKernelIno? := if epParentIno != 0 then some epParentIno else none
    cwdParentKernelDev? := if epParentDev != 0 then some epParentDev else none
    rootKernelIno? := if rootIno != 0 then some rootIno else none
    rootKernelDev? := if rootDev != 0 then some rootDev else none
    rootMode := rootMode
    rootOwnedByUid? := some rootOwned
    rootUidMapped? := some rootUidMapped
    rootGidMapped? := some rootGidMapped
    selfUidMapped? := some selfUMap
    selfGidMapped? := some selfGMap
    rootOwnerUid? := if rootUid != 0xffffffff then some rootUid else none
    sysMountId := if sysMnt == rootMnt then 0 else 3
    hostSyntheticOwnedByUid := chrootUnreachable
    crossMountPath? := crossPathOpt
    crossMountMode := crossMode
    crossMountId := crossMountId
    crossParentMountId := crossParentMountId
    crossMountKernelIno? := crossKernelIno?
    crossMountKernelDev? := crossKernelDev?
    devMountId := devMountId
    mountProfiles := mountProfiles
    ancestorMeta := ancestorMeta
    ancestorOwnerUids := ancestorOwnerUids
    hasCapDacOverride := ((capEff &&& ((1 : UInt64) <<< 1)) != 0)
    hasCapDacReadSearch := ((capEff &&& ((1 : UInt64) <<< 2)) != 0)
    hasCapFowner := ((capEff &&& ((1 : UInt64) <<< 3)) != 0)
    hasCapFsetid := ((capEff &&& ((1 : UInt64) <<< 4)) != 0)
    inInitUserNs := (uidRanges == [(0, UInt32.ofNat 0xffffffff)])
    protectedRegular := protReg
    protectedFifos := protFifo
    protectedSymlinks := (protSym != 0)
    hostUidMapped := hostUidMapped
    hostGidMapped := hostGidMapped
    hostSyntheticInGroup := hostSyntheticInGroup
    rootInGroup? := some rootInGroup
    devOwnedByUid := devOwnedByUid
    devInGroup? := some devInGroup
    devUidMapped? := some devUidMapped
    devGidMapped? := some devGidMapped
    proc1UidMapped := proc1UidMapped
    proc1GidMapped := proc1GidMapped
    proc1InGroup := proc1InGroup
    proc1CwdMode := p1CwdMode
    proc1CwdOwnedByUid? := some p1CwdOwned
    proc1CwdInGroup? := some p1CwdInGrp
    proc1CwdUidMapped? := some p1CwdUMap
    proc1CwdGidMapped? := some p1CwdGMap
    proc1CwdMountId := p1CwdMountId
    proc1CwdKernelDev? := if p1CwdDev != 0 then some p1CwdDev else none
    proc1CwdKernelIno? := if p1CwdIno != 0 then some p1CwdIno else none
    proc1Fd0Kind := p1Fd0Kind
    proc1Fd0DevKind? := p1Fd0DevKind?
    proc1Fd0MountId := p1Fd0MountId
    proc1Fd0Mode := p1Fd0Mode
    proc1Fd0OwnedByUid? := some p1Fd0Owned
    proc1Fd0InGroup? := some p1Fd0InGrp
    proc1Fd0UidMapped? := some p1Fd0UMap
    proc1Fd0GidMapped? := some p1Fd0GMap
    proc1Fd0KernelDev? := if p1Fd0Dev != 0 then some p1Fd0Dev else none
    proc1Fd0KernelIno? := if p1Fd0Ino != 0 then some p1Fd0Ino else none
    proc1Fd0LinkMode := p1Fd0LinkMode
    stdinUidMapped := stdinUidMapped
    stdinGidMapped := stdinGidMapped
    stdinInGroup := stdinInGroup || (!selfGMap && stdinOwned)
    stdoutUidMapped := stdoutUidMapped
    stdoutGidMapped := stdoutGidMapped
    stdoutInGroup := stdoutInGroup || (!selfGMap && stdoutOwned)
    stderrUidMapped := stderrUidMapped
    stderrGidMapped := stderrGidMapped
    stderrInGroup := stderrInGroup || (!selfGMap && stderrOwned)
    ancestorMapped := ancestorMapped
    ancestorInGroups := ancestorInGroups
    ambientSeccomp := ambientSeccomp
    chrootOuterEntries := chrootOuterEntries
    cwdOverlayMerged := hasPreseededLower && epProf.isOverlay
    cwdMayCopyUp := existedLowerUnlinked && epProf.isOverlay
    chrootUnreachable := chrootUnreachable
    chrootOutsideAncestors := chrootOutsideAncestors
    proc1OwnedByUid := p1SelfOwned
    selfPidBytes := (toString myPid).toUTF8
    devNullKernelDev? := if devNullDev != 0 then some devNullDev else none
    devNullKernelIno? := if devNullIno != 0 then some devNullIno else none
    devZeroKernelDev? := if devZeroDev != 0 then some devZeroDev else none
    devZeroKernelIno? := if devZeroIno != 0 then some devZeroIno else none
    devFullKernelDev? := if devFullDev != 0 then some devFullDev else none
    devFullKernelIno? := if devFullIno != 0 then some devFullIno else none
    exeOwnedByUid := exeOwnedByUid
    stdinKind := in0.1
    stdinDevKind? := in0.2
    stdinMode := in0Mode
    stdinOwnedByUid := stdinOwned
    stdinKernelDev? := if in0Dev != 0 then some in0Dev else none
    stdinKernelIno? := if in0Ino != 0 then some in0Ino else none
    stdinMountId := stdinMountId
    stdoutMountId := stdoutMountId
    stdoutKind := out1.1
    stdoutDevKind? := out1.2
    stdoutMode := out1Mode
    stdoutOwnedByUid := stdoutOwned
    stdoutKernelDev? := if out1Dev != 0 then some out1Dev else none
    stdoutKernelIno? := if out1Ino != 0 then some out1Ino else none
    stderrMountId := stderrMountId
    stderrKind := err2.1
    stderrDevKind? := err2.2
    stderrMode := err2Mode
    stderrOwnedByUid := stderrOwned
    stderrKernelDev? := if err2Dev != 0 then some err2Dev else none
    stderrKernelIno? := if err2Ino != 0 then some err2Ino else none
    procFd0LinkMode := procFd0Mode
    procFd1LinkMode := procFd1Mode
    procFd2LinkMode := procFd2Mode
    cwdEntries := cwdEntries
    crossEntries := crossEntries
  }
  let _ ← Env.umask recipe.epUmask
  if unlinkedCwd then
    let rrc ← Env.rmdir epReal.toString.toUTF8
    if rrc != 0 then
      throw (IO.userError s!"unlinked_cwd rmdir({epReal}) failed with errno={rrc}")
  return (cfg, crossDirCleanup, crossStrOpt)

private def addMemfdToState (s : FilesState) (mode : Mode) (nlink : Nat) (kdev? kino? : Option UInt64)
    (uid? : Option UInt32) (uMap gMap : Bool) : FilesState × HandleId :=
  let memMid := s.mountProfiles.foldl (fun acc p => max acc (p.1 + 1)) 16
  let ino := s.nextIno
  let hid := s.nextHid
  let vn : VNode := {
    data := .reg { seals := .sealable 0 }
    mode := mode
    modeExact := true
    nlink := nlink
    mountId := memMid
    owner := { ownedByUid := true, inGroup := true, uid? := uid?, uidMapped := uMap, gidMapped := gMap }
    kernelId := { dev? := kdev?, ino? := kino? }
    origin := .managed false
  }
  let desc : OpenDesc := {
    ino := ino
    access := .rdwr
    append := false
    nonblock := false
    cloexec := true
    closeState := .open
  }
  let (s1, desc') := bindFreeStdioSlot s hid desc
  ({ s1 with
    inodes := assocSet s1.inodes ino vn
    fds := assocSet s1.fds hid desc'
    mountProfiles := (memMid, { supportsSeals := true }) :: s1.mountProfiles
    nextIno := ino + 1
    nextHid := hid + 1 }, hid)

private def seedEpisodeMemfd (ops : FilesOps) (s : FilesState)
    (myUid : UInt32) (uidRanges gidRanges : List (UInt32 × UInt32)) (selfGids : List UInt32) :
    IO (FilesState × Option (HandleId × RawFd)) := do
  match ← Env.openMemfd with
  | .error _ => return (s, none)
  | .ok mfd =>
    let (mode, nlink, kdev?, kino?) ← match ← ops.fstat mfd with
      | .ok st => pure (st.mode, st.nlink, if st.dev != 0 then some st.dev else none, if st.ino != 0 then some st.ino else none)
      | .error _ => pure (0o777, 0, none, none)
    let uid? := if myUid != 0xffffffff then some myUid else none
    let uMap := Env.isIdMapped uidRanges myUid
    let gMap := match selfGids with
      | [] => !gidRanges.isEmpty
      | _ => selfGids.any (Env.isIdMapped gidRanges)
    let (s', hid) := addMemfdToState s mode nlink kdev? kino? uid? uMap gMap
    return (s', some (hid, mfd))

private def filesReqMayBlock (s : FilesState) (req : FilesReq) : Bool :=
  let openBlocks (dir : Option HandleId) (path : ByteArray) (follow : Bool) (resolve : ResolveFlags)
      (flags : OpenFlags) : Bool :=
    if flags.path || flags.nonblock || (flags.creat && flags.excl) then false
    else match resolveOpenTarget s dir path follow (flags.creat && flags.excl) resolve flags.creat with
      | .ok (.externalOpaque _) => true
      | .ok (.existing ino _ _ _ _ _ _) => match assocGet s.inodes ino with
        | some vn => match vn.data with
          | .fifo p =>
            let (minR, _, minW, _) := fifoCounts s ino p
            flags.access != .rdwr &&
            (vn.isDynamic || (flags.access == .rdonly && minW == 0) || (flags.access == .wronly && minR == 0))
          | .charDev .generic => true
          | _ => vn.isDynamic && vn.kind == .other
        | none => false
      | _ => false
  match req with
  | .openat dir path flags _ => openBlocks dir path (!flags.nofollow) {} flags
  | .openat2 dir path how =>
    openBlocks dir path (!how.flags.nofollow && !how.resolve.noSymlinks) how.resolve how.flags
  | .read hid sz =>
    if sz == 0 then false
    else match assocGet s.fds hid with
      | none => false
      | some desc =>
        if desc.isExternalStdio then true
        else if desc.access == .wronly then false
        else match assocGet s.inodes desc.ino with
          | some vn => match vn.data with
            | .charDev .generic => true
            | .fifo p =>
              let (_, _, _, maxW) := fifoCounts s desc.ino p
              !desc.nonblock && p.buf.data.size == 0 && (vn.isDynamic || maxW > 0)
            | _ => false
          | none => false
  | .write hid data =>
    if data.data.size == 0 then false
    else match assocGet s.fds hid with
      | none => false
      | some desc =>
        if desc.isExternalStdio then true
        else if desc.access == .rdonly then false
        else match assocGet s.inodes desc.ino with
          | some vn => match vn.data with
            | .charDev .generic => true
            | .fifo p =>
              let (_, maxR, _, _) := fifoCounts s desc.ino p
              !desc.nonblock && (vn.isDynamic || (maxR > 0 && p.buf.data.size + data.data.size > 4096))
            | _ => false
          | none => false
  | .flock hid op =>
    match op with
    | .shared false | .exclusive false =>
      match assocGet s.fds hid with
      | none => false
      | some desc => hasConflictingFlock s hid desc.ino (op == .exclusive false)
    | _ => false
  | _ => false

private def procLinkModeOfAccess : AccessMode → Mode
  | .rdonly => 0o500
  | .wronly => 0o300
  | .rdwr => 0o700

private def reqAccessOf : SymReq → AccessMode
  | .openat _ _ f _ => if f.path then .rdonly else f.access
  | .openat2 _ _ how => if how.flags.path then .rdonly else how.flags.access
  | .reopenReadOnly _ => .rdonly
  | .dupStdio slot => match slot with | .stdin => .rdonly | _ => .rdwr
  | _ => .rdwr

private def attachOpenedProcFd (ops : FilesOps) (s : FilesState) (hid : HandleId)
    (rfd : RawFd) (dfltAccess : AccessMode) : IO (FilesState × Option Nat) := do
  let rawU ← Env.rawFdNum rfd
  if rawU == (0xffffffff : UInt32) then
    return (s, none)
  else
    let rawNum := rawU.toNat
    let fdName := (toString rawNum).toUTF8
    let p := ("/proc/self/fd/" ++ toString rawNum).toUTF8
    let mode ← match ← ops.fstatat none p { symlinkNofollow := true } with
      | .ok st => pure st.mode
      | .error _ => pure (procLinkModeOfAccess dfltAccess)
    let tgtIno := (assocGet s.fds hid).map (·.ino) |>.getD 0
    return (s.attachProcFdLink fdName tgtIno hid mode, some rawNum)

private def hexDigitChar (n : Nat) : Char :=
  if n < 10 then Char.ofNat (48 + n) else Char.ofNat (87 + n)

private def bytesToHex (bs : ByteArray) : String := Id.run do
  let mut s := ""
  for b in bs.data do
    s := s.push (hexDigitChar (b.toNat / 16))
    s := s.push (hexDigitChar (b.toNat % 16))
  return s

private def parseHexNibble (c : Char) : Option Nat :=
  if '0' <= c && c <= '9' then some (c.toNat - '0'.toNat)
  else if 'a' <= c && c <= 'f' then some (10 + c.toNat - 'a'.toNat)
  else if 'A' <= c && c <= 'F' then some (10 + c.toNat - 'A'.toNat)
  else none

private def hexToBytes (s : String) : Option ByteArray := Id.run do
  let cs := s.toList
  if cs.length % 2 != 0 then return none
  let rec loop (acc : Array UInt8) : List Char → Option ByteArray
    | [] => some (ByteArray.mk acc)
    | a :: b :: rest => do
      let hi ← parseHexNibble a
      let lo ← parseHexNibble b
      loop (acc.push (UInt8.ofNat (hi * 16 + lo))) rest
    | _ => none
  loop #[] cs

private def encOptSym : Option SymFd → String
  | none => "-"
  | some s => toString s

private def decOptSym : String → Option (Option SymFd)
  | "-" => some none
  | s => s.toNat?.map some

private def encOpenFlags (f : OpenFlags) : Nat :=
  (match f.access with | .rdonly => 0 | .wronly => 1 | .rdwr => 2) |||
  (if f.creat then 4 else 0) ||| (if f.excl then 8 else 0) |||
  (if f.trunc then 16 else 0) ||| (if f.append then 32 else 0) |||
  (if f.nofollow then 64 else 0) ||| (if f.directory then 128 else 0) |||
  (if f.nonblock then 256 else 0) ||| (if f.cloexec then 512 else 0) |||
  (if f.noctty then 1024 else 0) ||| (if f.path then 2048 else 0)

private def decOpenFlags (n : Nat) : OpenFlags :=
  { access := match n &&& 3 with | 0 => .rdonly | 1 => .wronly | _ => .rdwr
    creat := (n &&& 4) != 0, excl := (n &&& 8) != 0, trunc := (n &&& 16) != 0
    append := (n &&& 32) != 0, nofollow := (n &&& 64) != 0, directory := (n &&& 128) != 0
    nonblock := (n &&& 256) != 0, cloexec := (n &&& 512) != 0
    noctty := (n &&& 1024) != 0, path := (n &&& 2048) != 0 }

private def encResolveFlags (r : ResolveFlags) : Nat :=
  (if r.beneath then 1 else 0) ||| (if r.inRoot then 2 else 0) |||
  (if r.noMagiclinks then 4 else 0) ||| (if r.noSymlinks then 8 else 0) |||
  (if r.noXdev then 16 else 0) ||| (if r.cached then 32 else 0)

private def decResolveFlags (n : Nat) : ResolveFlags :=
  { beneath := (n &&& 1) != 0, inRoot := (n &&& 2) != 0, noMagiclinks := (n &&& 4) != 0
    noSymlinks := (n &&& 8) != 0, noXdev := (n &&& 16) != 0, cached := (n &&& 32) != 0 }

private def encAtFlags (f : AtFlags) : Nat :=
  (if f.emptyPath then 1 else 0) ||| (if f.symlinkNofollow then 2 else 0) ||| (if f.eaccess then 4 else 0)

private def decAtFlags (n : Nat) : AtFlags :=
  { emptyPath := (n &&& 1) != 0, symlinkNofollow := (n &&& 2) != 0, eaccess := (n &&& 4) != 0 }

private def encodeSymStep (st : SymStep) : String :=
  let a := encOptSym st.allocId
  match st.req with
  | .openat d p f m => s!"STEP|0|{a}|{encOptSym d}|{bytesToHex p}|{encOpenFlags f}|{m}"
  | .openat2 d p h => s!"STEP|1|{a}|{encOptSym d}|{bytesToHex p}|{encOpenFlags h.flags}|{h.mode}|{encResolveFlags h.resolve}"
  | .close fd => s!"STEP|2|{a}|{fd}"
  | .read fd n => s!"STEP|3|{a}|{fd}|{n}"
  | .write fd d => s!"STEP|4|{a}|{fd}|{bytesToHex d}"
  | .fstat fd => s!"STEP|5|{a}|{fd}"
  | .fstatat d p f => s!"STEP|6|{a}|{encOptSym d}|{bytesToHex p}|{encAtFlags f}"
  | .faccessat d p mk f =>
    let m := (if mk.read then 1 else 0) ||| (if mk.write then 2 else 0) ||| (if mk.exec then 4 else 0)
    s!"STEP|7|{a}|{encOptSym d}|{bytesToHex p}|{m}|{encAtFlags f}"
  | .mkdirat d p m => s!"STEP|8|{a}|{encOptSym d}|{bytesToHex p}|{m}"
  | .unlinkat d p r => s!"STEP|9|{a}|{encOptSym d}|{bytesToHex p}|{if r then 1 else 0}"
  | .renameat2 od op nd np rf =>
    let r := (if rf.noreplace then 1 else 0) ||| (if rf.exchange then 2 else 0) ||| (if rf.whiteout then 4 else 0)
    s!"STEP|10|{a}|{encOptSym od}|{bytesToHex op}|{encOptSym nd}|{bytesToHex np}|{r}"
  | .symlinkat t nd lp => s!"STEP|11|{a}|{bytesToHex t}|{encOptSym nd}|{bytesToHex lp}"
  | .readlinkat d p n => s!"STEP|12|{a}|{encOptSym d}|{bytesToHex p}|{n}"
  | .getdents64 fd n => s!"STEP|13|{a}|{fd}|{n}"
  | .fchmodat d p m => s!"STEP|14|{a}|{encOptSym d}|{bytesToHex p}|{m}"
  | .fchmod fd m => s!"STEP|15|{a}|{fd}|{m}"
  | .flock fd op =>
    let c := match op with | .shared false => 0 | .shared true => 1 | .exclusive false => 2 | .exclusive true => 3 | .unlock => 4
    s!"STEP|16|{a}|{fd}|{c}"
  | .fcntl fd cmd =>
    let (c, v) := match cmd with
      | .getFl => (0, 0) | .setFl nb ap => (1, (if nb then 1 else 0) ||| (if ap then 2 else 0))
      | .getFd => (2, 0) | .setFd cl => (3, if cl then 1 else 0)
      | .addSeals s => (4, s.toNat) | .getSeals => (5, 0)
    s!"STEP|17|{a}|{fd}|{c}|{v}"
  | .fsync fd => s!"STEP|18|{a}|{fd}"
  | .getcwd n => s!"STEP|19|{a}|{n}"
  | .lseek fd off w =>
    let wN := match w with | .seekSet => 0 | .seekCur => 1 | .seekEnd => 2
    s!"STEP|20|{a}|{fd}|{off.toUInt64.toNat}|{wN}"
  | .reopenReadOnly fd => s!"STEP|21|{a}|{fd}"
  | .dupStdio slot =>
    let sN := match slot with | .stdin => 0 | .stdout => 1 | .stderr => 2
    s!"STEP|22|{a}|{sN}"

private def decodeSymStep (line : String) : Option SymStep := do
  match line.splitOn "|" with
  | ["STEP", "0", aS, dS, pH, fS, mS] => do
    let allocId ← decOptSym aS; let d ← decOptSym dS; let p ← hexToBytes pH
    let f ← fS.toNat?; let m ← mS.toNat?
    pure { allocId, req := .openat d p (decOpenFlags f) (UInt32.ofNat m) }
  | ["STEP", "1", aS, dS, pH, fS, mS, rS] => do
    let allocId ← decOptSym aS; let d ← decOptSym dS; let p ← hexToBytes pH
    let f ← fS.toNat?; let m ← mS.toNat?; let r ← rS.toNat?
    pure { allocId, req := .openat2 d p { flags := decOpenFlags f, mode := UInt32.ofNat m, resolve := decResolveFlags r } }
  | ["STEP", "2", aS, fdS] => do
    let allocId ← decOptSym aS; let fd ← fdS.toNat?
    pure { allocId, req := .close fd }
  | ["STEP", "3", aS, fdS, nS] => do
    let allocId ← decOptSym aS; let fd ← fdS.toNat?; let n ← nS.toNat?
    pure { allocId, req := .read fd (UInt32.ofNat n) }
  | ["STEP", "4", aS, fdS, dH] => do
    let allocId ← decOptSym aS; let fd ← fdS.toNat?; let d ← hexToBytes dH
    pure { allocId, req := .write fd d }
  | ["STEP", "5", aS, fdS] => do
    let allocId ← decOptSym aS; let fd ← fdS.toNat?
    pure { allocId, req := .fstat fd }
  | ["STEP", "6", aS, dS, pH, atS] => do
    let allocId ← decOptSym aS; let d ← decOptSym dS; let p ← hexToBytes pH; let af ← atS.toNat?
    pure { allocId, req := .fstatat d p (decAtFlags af) }
  | ["STEP", "7", aS, dS, pH, mkS, atS] => do
    let allocId ← decOptSym aS; let d ← decOptSym dS; let p ← hexToBytes pH
    let mk ← mkS.toNat?; let af ← atS.toNat?
    pure { allocId, req := .faccessat d p { read := (mk &&& 1) != 0, write := (mk &&& 2) != 0, exec := (mk &&& 4) != 0 } (decAtFlags af) }
  | ["STEP", "8", aS, dS, pH, mS] => do
    let allocId ← decOptSym aS; let d ← decOptSym dS; let p ← hexToBytes pH; let m ← mS.toNat?
    pure { allocId, req := .mkdirat d p (UInt32.ofNat m) }
  | ["STEP", "9", aS, dS, pH, rS] => do
    let allocId ← decOptSym aS; let d ← decOptSym dS; let p ← hexToBytes pH; let r ← rS.toNat?
    pure { allocId, req := .unlinkat d p (r != 0) }
  | ["STEP", "10", aS, odS, opH, ndS, npH, rfS] => do
    let allocId ← decOptSym aS; let od ← decOptSym odS; let op ← hexToBytes opH
    let nd ← decOptSym ndS; let np ← hexToBytes npH; let rf ← rfS.toNat?
    pure { allocId, req := .renameat2 od op nd np { noreplace := (rf &&& 1) != 0, exchange := (rf &&& 2) != 0, whiteout := (rf &&& 4) != 0 } }
  | ["STEP", "11", aS, tH, ndS, lpH] => do
    let allocId ← decOptSym aS; let t ← hexToBytes tH; let nd ← decOptSym ndS; let lp ← hexToBytes lpH
    pure { allocId, req := .symlinkat t nd lp }
  | ["STEP", "12", aS, dS, pH, nS] => do
    let allocId ← decOptSym aS; let d ← decOptSym dS; let p ← hexToBytes pH; let n ← nS.toNat?
    pure { allocId, req := .readlinkat d p (UInt32.ofNat n) }
  | ["STEP", "13", aS, fdS, nS] => do
    let allocId ← decOptSym aS; let fd ← fdS.toNat?; let n ← nS.toNat?
    pure { allocId, req := .getdents64 fd (UInt32.ofNat n) }
  | ["STEP", "14", aS, dS, pH, mS] => do
    let allocId ← decOptSym aS; let d ← decOptSym dS; let p ← hexToBytes pH; let m ← mS.toNat?
    pure { allocId, req := .fchmodat d p (UInt32.ofNat m) }
  | ["STEP", "15", aS, fdS, mS] => do
    let allocId ← decOptSym aS; let fd ← fdS.toNat?; let m ← mS.toNat?
    pure { allocId, req := .fchmod fd (UInt32.ofNat m) }
  | ["STEP", "16", aS, fdS, cS] => do
    let allocId ← decOptSym aS; let fd ← fdS.toNat?; let c ← cS.toNat?
    let op := match c with | 0 => .shared false | 1 => .shared true | 2 => .exclusive false | 3 => .exclusive true | _ => .unlock
    pure { allocId, req := .flock fd op }
  | ["STEP", "17", aS, fdS, cS, vS] => do
    let allocId ← decOptSym aS; let fd ← fdS.toNat?; let c ← cS.toNat?; let v ← vS.toNat?
    let cmd := match c with
      | 0 => .getFl | 1 => .setFl ((v &&& 1) != 0) ((v &&& 2) != 0)
      | 2 => .getFd | 3 => .setFd (v != 0)
      | 4 => .addSeals (UInt32.ofNat v) | _ => .getSeals
    pure { allocId, req := .fcntl fd cmd }
  | ["STEP", "18", aS, fdS] => do
    let allocId ← decOptSym aS; let fd ← fdS.toNat?
    pure { allocId, req := .fsync fd }
  | ["STEP", "19", aS, nS] => do
    let allocId ← decOptSym aS; let n ← nS.toNat?
    pure { allocId, req := .getcwd (UInt32.ofNat n) }
  | ["STEP", "20", aS, fdS, offS, wS] => do
    let allocId ← decOptSym aS; let fd ← fdS.toNat?; let offN ← offS.toNat?; let wN ← wS.toNat?
    let w : SeekWhence := match wN with | 0 => .seekSet | 1 => .seekCur | _ => .seekEnd
    pure { allocId, req := .lseek fd (UInt64.ofNat offN).toInt64 w }
  | ["STEP", "21", aS, fdS] => do
    let allocId ← decOptSym aS; let fd ← fdS.toNat?
    pure { allocId, req := .reopenReadOnly fd }
  | ["STEP", "22", aS, sS] => do
    let allocId ← decOptSym aS; let sN ← sS.toNat?
    let slot : StdioFd := match sN with | 0 => .stdin | 1 => .stdout | _ => .stderr
    pure { allocId, req := .dupStdio slot }
  | _ => none

private def encodeSymTrace (trace : Array SymStep) : String :=
  String.intercalate "\n" (trace.toList.map encodeSymStep)

private def decodeSymTrace (txt : String) : String × Array SymStep := Id.run do
  let mut info := ""
  let mut steps : Array SymStep := #[]
  for rawLine in txt.splitOn "\n" do
    let line := rawLine.trimAscii.toString
    if line.startsWith "MISMATCH_INFO " then
      info := (line.drop 14).toString
    else if line.startsWith "STEP|" then
      if let some st := decodeSymStep line then
        steps := steps.push st
  return (info, steps)

private def applyClosedStdioToState (in0Code out1Code err2Code : UInt32) (s : FilesState) : FilesState :=
  let s0 := if in0Code == 0 then
    { (s.detachProcFdLink "0".toUTF8) with freeStdioSlots := s.freeStdioSlots ++ [.stdin] }
  else s
  let s1 := if out1Code == 0 then
    { (s0.detachProcFdLink "1".toUTF8) with freeStdioSlots := s0.freeStdioSlots ++ [.stdout] }
  else s0
  if err2Code == 0 then
    { (s1.detachProcFdLink "2".toUTF8) with freeStdioSlots := s1.freeStdioSlots ++ [.stderr] }
  else s1

private def captureStdioState (ops : FilesOps) : IO (Array (StdioFd × Bool × Bool × Option UInt64)) := do
  let mut saved : Array (StdioFd × Bool × Bool × Option UInt64) := #[]
  for slot in #[StdioFd.stdin, StdioFd.stdout, StdioFd.stderr] do
    match ← ops.dupStdio slot with
    | .ok h =>
      let fl? ← match ← ops.fcntl h .getFl with
        | .ok bits =>
          let nb := (bits &&& ((1 : UInt32) <<< 8)) != 0
          let ap := (bits &&& ((1 : UInt32) <<< 5)) != 0
          pure (some (nb, ap))
        | .error _ => pure none
      let off? ← match ← ops.lseek h 0 .seekCur with
        | .ok off => pure (some off)
        | .error _ => pure none
      if let some (nb, ap) := fl? then
        saved := saved.push (slot, nb, ap, off?)
      let _ ← ops.close h
    | .error _ => pure ()
  return saved

private def restoreStdioState (ops : FilesOps) (saved : Array (StdioFd × Bool × Bool × Option UInt64)) : IO Unit := do
  for (slot, nb, ap, off?) in saved do
    match ← ops.dupStdio slot with
    | .ok h =>
      let _ ← ops.fcntl h (.setFl nb ap)
      if let some off := off? then
        let _ ← ops.lseek h (Int64.ofNat off.toNat) .seekSet
      let _ ← ops.close h
    | .error _ => pure ()

private def statOutcomeNsecValid : FilesOutcome -> Bool
  | .statted st => st.mtimeNsec < 1000000000 && st.atimeNsec < 1000000000
  | _ => true

/-- Replay a deterministic `Array SymStep` trace inside `epDir` using `stepModel`. -/
def replayTrace (epDir : System.FilePath) (trace : Array SymStep)
    (stepModel : FilesState -> FilesReq -> FilesOutcome -> Option FilesState := allowedStep)
    (crossDir? : Option System.FilePath := none)
    (setupFn : System.FilePath -> Option System.FilePath -> IO SeedTreeConfig :=
      fun d _ => do
        removeDirForced d
        IO.FS.createDirAll d
        let dr ← IO.FS.realPath d
        IO.Process.setCurrentDir dr
        return { cwdPath := dr.toString.toUTF8, cwdBound := true })
    (postSeed : FilesState -> FilesState := id)
    (fsizeLimit? : Option UInt64 := none)
    (seedMemfd : Bool := false)
    (preLoopAction : IO Unit := pure ())
    (rlimitNofile? : Option UInt64 := none)
    (keepEpDir : Bool := false) :
    IO ReplayResult := do
  let savedCwd ← IO.Process.getCurrentDir
  let savedFsizeCur ← Env.getRlimitFsizeCur
  let savedFsizeMax ← Env.getRlimitFsizeMax
  let savedNofileCur ← Env.getRlimitNofileCur
  let savedNofileMax ← Env.getRlimitNofileMax
  let savedStdio ← captureStdioState defaultOps
  let in0Code ← Env.fdKind 0
  let out1Code ← Env.fdKind 1
  let err2Code ← Env.fdKind 2
  let ops := defaultOps
  let closedDummy? ← allocClosedDummy ops
  let cfg ← setupFn epDir crossDir?
  let mut modelState := applyClosedStdioToState in0Code out1Code err2Code (postSeed (FilesState.withSeededTree cfg))
  let mut symMap : Std.HashMap SymFd HandleId := {}
  let mut rawMap : Std.HashMap HandleId RawFd := {}
  let mut openMap : Std.HashMap HandleId RawFd := {}
  let mut procFdMap : Std.HashMap SymFd Nat := {}
  let mut hidToRawName : Std.HashMap HandleId ByteArray := {}
  try
    if seedMemfd then
      let myUid ← Env.getUid
      let uidRanges ← Env.readIdMap "/proc/self/uid_map"
      let gidRanges ← Env.readIdMap "/proc/self/gid_map"
      let selfGids ← Env.readSelfGids
      let (ms', mres?) ← seedEpisodeMemfd ops modelState myUid uidRanges gidRanges selfGids
      modelState := ms'
      if let some (hid, mfd) := mres? then
        rawMap := rawMap.insert hid mfd
        openMap := openMap.insert hid mfd
        symMap := symMap.insert 0 hid
        let (msLink, rawN?) ← attachOpenedProcFd ops modelState hid mfd .rdwr
        modelState := msLink
        if let some rn := rawN? then
          procFdMap := procFdMap.insert 0 rn
          hidToRawName := hidToRawName.insert hid (toString rn).toUTF8
    if let some flim := fsizeLimit? then
      let _ ← Env.setRlimitFsize flim savedFsizeMax true
    if let some rlim := rlimitNofile? then
      let _ ← Env.setRlimitNofile rlim 0
    preLoopAction
    for h : idx in [:trace.size] do
      let step := trace[idx]
      let effSreq := resolveSymProcFdReq procFdMap step.req
      match symReqToFilesReq symMap effSreq with
      | none =>
        return { mismatchIdx := none, mismatchReq := none, mismatchOut := none, finalState := modelState }
      | some req =>
        if filesReqMayBlock modelState req then
          return { mismatchIdx := none, mismatchReq := none, mismatchOut := none, finalState := modelState }
        let nextHid := modelState.nextHid
        let (out, opened) ← execRealReq ops rawMap nextHid req closedDummy?
        match opened with
        | some (hid, rfd) =>
          rawMap := rawMap.insert hid rfd
          openMap := openMap.insert hid rfd
          match step.allocId with
          | some sid => symMap := symMap.insert sid hid
          | none => pure ()
        | none => pure ()
        match req, out with
        | .close hid, .unit =>
          openMap := openMap.erase hid
        | _, _ => pure ()
        if !statOutcomeNsecValid out then
          return { mismatchIdx := some idx, mismatchReq := some req, mismatchOut := some out, finalState := modelState }
        match stepModel modelState req out with
        | none =>
          return { mismatchIdx := some idx, mismatchReq := some req, mismatchOut := some out, finalState := modelState }
        | some s' =>
          let mut sNext := s'
          if let (some (hid, rfd), some sid) := (opened, step.allocId) then
            let (sL, rawN?) ← attachOpenedProcFd ops sNext hid rfd (reqAccessOf effSreq)
            sNext := sL
            if let some rn := rawN? then
              procFdMap := procFdMap.insert sid rn
              hidToRawName := hidToRawName.insert hid (toString rn).toUTF8
          if let .close hid := req then
            if !(sNext.fds.any fun p => p.1 == hid) then
              if let some fn := hidToRawName.get? hid then
                sNext := sNext.detachProcFdLink fn
                hidToRawName := hidToRawName.erase hid
              if let .close sid := step.req then
                procFdMap := procFdMap.erase sid
          modelState := sNext
    return { mismatchIdx := none, mismatchReq := none, mismatchOut := none, finalState := modelState }
  finally
    if rlimitNofile?.isSome then
      let _ ← Env.setRlimitNofile savedNofileCur savedNofileMax
    restoreStdioState ops savedStdio
    let _ ← Env.setRlimitFsize savedFsizeCur savedFsizeMax false
    let rfds := openMap.toList.map (·.2) |>.toArray
    cleanupEpisodeDir ops rfds savedCwd epDir crossDir? keepEpDir

private def getCurrentPid : IO String := do
  return toString (← Env.getPid)

private def spawnCrashWatcher (pid : String) (rootDir? : Option System.FilePath) (crossRoot? : Option System.FilePath := none) : IO Unit := do
  if rootDir?.isNone && crossRoot?.isNone then
    return ()
  let crossCleanup := match crossRoot? with
    | some cr => s!"chmod -R u+rwx '{cr}' 2>/dev/null; rm -rf '{cr}'; "
    | none => ""
  let rootCleanup := match rootDir? with
    | some rd => s!"chmod -R u+rwx '{rd}' 2>/dev/null; rm -rf '{rd}'"
    | none => "true"
  let script :=
    s!"(while kill -0 {pid} 2>/dev/null; do sleep 0.2; done; {crossCleanup}{rootCleanup}) </dev/null >/dev/null 2>&1 &"
  let watcher ← IO.Process.spawn {
    cmd := "sh"
    args := #["-c", script]
    stdin := .null
    stdout := .null
    stderr := .null
  }
  let _ ← watcher.wait

/-- Summary of a complete `Files` fuzzing campaign. -/
structure FuzzReport where
  /-- Executed syscall count. -/
  totalSteps : Nat
  /-- Executed episode count. -/
  totalEpisodes : Nat
  /-- Elapsed wall-clock time in milliseconds. -/
  elapsedMs : Nat
  /-- Syscalls per second (`totalSteps * 1000 / max 1 elapsedMs`). -/
  syscallsPerSec : Nat
  /-- Hit counts by `(syscall, outcome)`. -/
  stats : HitStats
  /-- Hit counts excluding synthetic seccomp-fault workers (used for `.real` errorCoverage checks). -/
  realStats : HitStats := {}
  /-- Non-empty only when `--self-test-shrink` ran. -/
  shrinkSelfTestDetail : String := ""

private def runClosedStdinGuardRegression (rootDir : System.FilePath) : IO Unit := do
  let epCfg : SeedTreeConfig := {
    cwdPath := "/dev/shm/fuzz-root/ep-2".toUTF8
    cwdBound := true
    cwdMode := 0o755
    cwdParentMode := 0o755
    cwdParentOwnedByUid := true
    mountProfiles := [(4, { supportsSeals := true })]
    selfPidBytes := "42".toUTF8
    stdinKind := .reg
    stdinDevKind? := none
    stdinMode := 0o644
    stdinOwnedByUid := true
    exeOwnedByUid := true
    cwdEntries := [
      { name := "sub".toUTF8, kind := .dir, mode := 0o755 },
      { relDir := ["sub".toUTF8], name := "a".toUTF8, kind := .reg, mode := 0o644 }
    ]
  }
  let extSt := FilesState.withSeededTree epCfg
  let extEnv : GenEnv := {}
  if !mutTargetAllowed extSt extEnv extSt.cwdIno none true true none "/proc/self/fd/0".toUTF8 true then
    throw (IO.userError "closed_stdin regression: external safeStdin /proc/self/fd/0 was rejected")
  if mutTargetAllowed extSt extEnv extSt.cwdIno none true false none "/proc/self/fd/0".toUTF8 true then
    throw (IO.userError "closed_stdin regression: external unsafe /proc/self/fd/0 was allowed")
  let closedSt := applyClosedStdioToState 0 1 1 extSt
  if !mutTargetAllowed closedSt extEnv closedSt.cwdIno none true false none "/proc/self/fd/0".toUTF8 true then
    throw (IO.userError "closed_stdin regression: detached closed /proc/self/fd/0 should be allowed (ENOENT)")
  let parentIno := (assocGet closedSt.inodes closedSt.cwdIno).map (·.parentIno) |>.getD 0
  let parentDesc0 : OpenDesc := { ino := parentIno, access := .rdonly, isPathFd := true, cloexec := true }
  let (stPar0, parentDesc) := bindFreeStdioSlot closedSt 0 parentDesc0
  let stPar := ({ stPar0 with fds := assocSet stPar0.fds 0 parentDesc, nextHid := 1 }).attachProcFdLink "0".toUTF8 parentIno 0 0o500
  let envFd0 : GenEnv := { allFds := #[(0, 0)], openFds := #[(0, 0)], procFdMap := ({} : Std.HashMap SymFd Nat).insert 0 0 }
  if mutTargetAllowed stPar envFd0 stPar.cwdIno none true false none "/proc/self/fd/0".toUTF8 true then
    throw (IO.userError "closed_stdin regression: recycled fd 0 -> rootDir allowed with safeStdin=false")
  if mutTargetAllowed stPar envFd0 stPar.cwdIno none true true none "/proc/self/fd/0".toUTF8 true then
    throw (IO.userError "closed_stdin regression: recycled fd 0 -> rootDir allowed with safeStdin=true")
  if mutTargetAllowed stPar envFd0 stPar.cwdIno none true true none "/proc/self/fd/@0".toUTF8 true then
    throw (IO.userError "closed_stdin regression: recycled /proc/self/fd/@0 -> rootDir allowed")
  if !mutTargetAllowed stPar envFd0 stPar.cwdIno none true false none "/proc/self/fd/0".toUTF8 false then
    throw (IO.userError "closed_stdin regression: followFinal=false pseudo magic link unexpectedly rejected")
  let exeIno := match inspectPathTarget closedSt extEnv none "/proc/self/exe".toUTF8 true with
    | some (_, some ino, _) => ino
    | _ => 0
  let (stExe0, exeDesc) := bindFreeStdioSlot closedSt 0 { ino := exeIno, access := .rdonly, isPathFd := true, cloexec := true }
  let stExe := ({ stExe0 with fds := assocSet stExe0.fds 0 exeDesc, nextHid := 1 }).attachProcFdLink "0".toUTF8 exeIno 0 0o500
  if mutTargetAllowed stExe envFd0 stExe.cwdIno none true true none "/proc/self/fd/0".toUTF8 true then
    throw (IO.userError "closed_stdin regression: recycled fd 0 -> /proc/self/exe allowed")
  let pid1Closed := applyClosedStdioToState 0 1 1 (FilesState.withSeededTree { epCfg with selfPidBytes := "1".toUTF8 })
  let p1Parent := (assocGet pid1Closed.inodes pid1Closed.cwdIno).map (·.parentIno) |>.getD 0
  let (stP10, p1Desc) := bindFreeStdioSlot pid1Closed 0 { ino := p1Parent, access := .rdonly, isPathFd := true, cloexec := true }
  let stP1 := ({ stP10 with fds := assocSet stP10.fds 0 p1Desc, nextHid := 1 }).attachProcFdLink "0".toUTF8 p1Parent 0 0o500
  if mutTargetAllowed stP1 envFd0 stP1.cwdIno none true true none "/proc/1/fd/0".toUTF8 true then
    throw (IO.userError "closed_stdin regression: PID 1 recycled /proc/1/fd/0 -> rootDir allowed")
  let subAIno := match inspectPathTarget closedSt extEnv none "sub/a".toUTF8 true with
    | some (_, some ino, _) => ino
    | _ => 0
  let (stSub0, subDesc) := bindFreeStdioSlot closedSt 0 { ino := subAIno, access := .rdwr, cloexec := true }
  let stSub := ({ stSub0 with fds := assocSet stSub0.fds 0 subDesc, nextHid := 1 }).attachProcFdLink "0".toUTF8 subAIno 0 0o700
  if !mutTargetAllowed stSub envFd0 stSub.cwdIno none true false none "/proc/self/fd/0".toUTF8 true then
    throw (IO.userError "closed_stdin regression: recycled fd 0 -> sub/a rejected")
  let (stMem0, memHid) := addMemfdToState closedSt 0o777 0 none none none true true
  let memIno := (assocGet stMem0.fds memHid).map (·.ino) |>.getD 0
  let stMem := stMem0.attachProcFdLink "0".toUTF8 memIno memHid 0o700
  if !mutTargetAllowed stMem envFd0 stMem.cwdIno none true false none "/proc/self/fd/0".toUTF8 true then
    throw (IO.userError "closed_stdin regression: recycled fd 0 -> memfd rejected")
  let sentFile := rootDir / "chmod-sentinel"
  let lockDir := rootDir / "chmod-0000-ep"
  try
    removeDirForced sentFile
    removeDirForced lockDir
    IO.FS.writeFile sentFile "keep\n"
    let _ ← Env.chmod sentFile.toString.toUTF8 0o644
    IO.FS.createDirAll (lockDir / "sub")
    IO.FS.writeFile (lockDir / "sub" / "leaf") "x\n"
    let _ ← defaultOps.symlinkat sentFile.toString.toUTF8 none (lockDir / "lnk_sent").toString.toUTF8
    let _ ← Env.chmod (lockDir / "sub").toString.toUTF8 0o000
    let _ ← Env.chmod lockDir.toString.toUTF8 0o7000
    removeDirForced lockDir
    if ← lockDir.pathExists then
      throw (IO.userError "closed_stdin regression: removeDirForced left 0o7000 dir behind")
    if (← Env.statMode sentFile.toString.toUTF8) != 0o644 then
      throw (IO.userError "closed_stdin regression: removeDirForced modified symlink target mode")
    let topLink := rootDir / "chmod-sentinel-link"
    let _ ← defaultOps.symlinkat sentFile.toString.toUTF8 none topLink.toString.toUTF8
    unlinkTreeRaw topLink.toString.toUTF8
    if (← defaultOps.fstatat none topLink.toString.toUTF8 { symlinkNofollow := true }).isOk then
      throw (IO.userError "closed_stdin regression: unlinkTreeRaw left top-level symlink behind")
    if (← Env.statMode sentFile.toString.toUTF8) != 0o644 then
      throw (IO.userError "closed_stdin regression: unlinkTreeRaw modified top-level symlink target mode")
  finally
    removeDirForced (rootDir / "chmod-sentinel-link")
    removeDirForced lockDir
    removeDirForced sentFile
  let reproDir := rootDir / "closed-stdin-seed-6107754422894804096"
  try
    removeDirForced reproDir
    IO.FS.createDirAll reproDir
    let _ ← Env.chmod reproDir.toString.toUTF8 0o755
    let exe ← IO.appPath
    let out ← IO.Process.output {
      cmd := exe.toString
      args := #[
        "--worker-mode", "rw", "--close-fd0", "--dir", reproDir.toString,
        "--steps", "1666", "--seed", "6107754422894805005"
      ]
      stdin := .null
    }
    if out.exitCode != 0 then
      throw (IO.userError s!"closed_stdin seed 6107754422894804096 regression failed (exit={out.exitCode}):\n{out.stdout}\n{out.stderr}")
    let dupBadFdHit := (out.stdout.splitOn "\n").any fun raw =>
      match raw.trimAscii.toString.splitOn " " with
      | ["WORKER_STAT_KIND", "dupStdio:badFd", nStr] => nStr.toNat?.getD 0 > 0
      | _ => false
    if !dupBadFdHit then
      throw (IO.userError "closed_stdin seed 6107754422894804096 regression recorded 0 dupStdio:badFd hits")
    let reproMode ← Env.statMode reproDir.toString.toUTF8
    if reproMode != 0o755 then
      throw (IO.userError s!"closed_stdin regression: base dir mode altered to {reproMode}")
  finally
    removeDirForced reproDir

/-- Verify greedy delta-minimization and handle-ID renumbering using a generated trace and synthetic oracle fault. -/
def runShrinkSelfTest (rootDir : System.FilePath) : IO String := do
  let mut rng := Rng.seed 0x534852494e4b4d49
  let mut rawTrace : Array SymStep := #[]
  let mut nextId : SymFd := 0
  let wrFlags : OpenFlags := { access := .rdwr, creat := true }
  for i in [:12] do
    if i == 3 || i == 7 then
      let sid := nextId
      nextId := nextId + 1
      let fname := s!"f{i}".toUTF8
      rawTrace := rawTrace.push { allocId := some sid, req := .openat none fname wrFlags 0o644 }
      rawTrace := rawTrace.push { allocId := none, req := .write sid fname }
    else
      let (sz, r1) := rng.pickArray #[16, 64, 256] 64
      rng := r1
      rawTrace := rawTrace.push { allocId := none, req := .getcwd sz }
  let targetPayload := "f7".toUTF8
  let faultModel : FilesState -> FilesReq -> FilesOutcome -> Option FilesState := fun st req out =>
    match req, out with
    | .write _ data, .u32 _ =>
      if data == targetPayload then none else allowedStep st req out
    | _, _ => allowedStep st req out
  let epDir := rootDir / "shrink-self-test"
  let reproduces : Array SymStep -> IO Bool := fun cand => do
    let res ← replayTrace epDir cand faultModel
    return res.mismatchIdx.isSome
  let initOk ← reproduces rawTrace
  if !initOk then
    throw (IO.userError "shrink self-test: baseline injected failure did not trigger")
  let shrunk ← shrinkTrace rawTrace reproduces
  if shrunk.size != 2 then
    throw (IO.userError s!"shrink self-test: expected minimal size 2, got {shrunk.size} ({repr shrunk})")
  let firstId := (shrunk.getD 0 { allocId := none, req := .getcwd 1 }).allocId
  if firstId != some 0 then
    throw (IO.userError s!"shrink self-test: handle ID was not renumbered to 0 ({repr shrunk})")
  let stillFails ← reproduces shrunk
  if !stillFails then
    throw (IO.userError "shrink self-test: shrunk trace failed to reproduce mismatch")
  let bigData := ByteArray.mk (Array.replicate 256 97)
  let coupledTrace : Array SymStep := #[
    { allocId := none, req := .getcwd 64 },
    { allocId := some 1, req := .openat none "pre_pair".toUTF8 wrFlags 0o644 },
    { allocId := none, req := .write 1 bigData },
    { allocId := none, req := .fstat 0 },
    { allocId := some 2, req := .openat none "keep".toUTF8 wrFlags 0o644 },
    { allocId := none, req := .write 2 bigData }
  ]
  let coupledFault : FilesState -> FilesReq -> FilesOutcome -> Option FilesState := fun st req out =>
    match req, out with
    | .write hid d, .u32 _ =>
      if hid >= 1 && d.size >= 4 then none else allowedStep st req out
    | _, _ => allowedStep st req out
  let preDir := rootDir / "shrink-self-test-pre"
  let preRepro : Array SymStep -> IO Bool := fun cand => do
    let r ← replayTrace preDir cand coupledFault none
      (fun d _ => do
        IO.FS.createDirAll d
        let dr ← IO.FS.realPath d
        IO.Process.setCurrentDir dr
        return { cwdPath := dr.toString.toUTF8, cwdBound := true })
      id none true
    return r.mismatchIdx.isSome
  if !(← preRepro coupledTrace) then
    throw (IO.userError "shrink self-test: preSeeded=1 baseline did not trigger")
  let shrunkPre ← shrinkTrace coupledTrace preRepro 1
  if shrunkPre.size != 2 then
    throw (IO.userError s!"shrink self-test (preSeeded=1): expected 2 steps, got {shrunkPre.size} ({repr shrunkPre})")
  if (shrunkPre.getD 0 { allocId := none, req := .getcwd 1 }).allocId != some 1 then
    throw (IO.userError s!"shrink self-test (preSeeded=1): expected renumbered handle 1 ({repr shrunkPre})")
  let shrunkPayloadLen := match (shrunkPre.getD 1 { allocId := none, req := .getcwd 1 }).req with
    | .write _ d => d.size
    | _ => 999
  if shrunkPayloadLen != 4 then
    throw (IO.userError s!"shrink self-test (payload shrink): expected 4B payload, got {shrunkPayloadLen}B")
  let argTrace : Array SymStep := #[
    { allocId := some 0,
      req := .openat2 none "dir1/dir2/file".toUTF8
        { flags := { access := .rdonly, noctty := true, path := true, cloexec := false },
          mode := 0o644, resolve := { noSymlinks := true } } },
    { allocId := none,
      req := .renameat2 none "dir1/old".toUTF8 none "dir2/new".toUTF8 { exchange := true, whiteout := true } },
    { allocId := none, req := .fchmod 0 0o4755 }
  ]
  let argRepro : Array SymStep -> IO Bool := fun cand => do
    match cand[0]?, cand[1]?, cand[2]? with
    | some s0, some s1, some s2 =>
      if cand.size != 3 then return false
      match s0.req, s1.req, s2.req with
      | .openat2 none _ h, .renameat2 _ _ _ _ rf, .fchmod _ m =>
        return h.flags.path && h.flags.noctty && rf.exchange && (m &&& 0o4000) == 0o4000
      | _, _, _ => return false
    | _, _, _ => return false
  let shrunkArgs ← shrinkTrace argTrace argRepro
  match shrunkArgs[0]?, shrunkArgs[1]?, shrunkArgs[2]? with
  | some s0, some s1, some s2 =>
    if shrunkArgs.size != 3 then
      throw (IO.userError s!"shrink self-test (multi-arg): unexpected size ({repr shrunkArgs})")
    match s0.req, s1.req, s2.req with
    | .openat2 none p h, .renameat2 _ op _ np rf, .fchmod _ m =>
      if p.size != 1 || h.mode != 0 || h.resolve.noSymlinks ||
          op.size != 1 || np.size != 1 || rf.whiteout || m != 0o4000 then
        throw (IO.userError s!"shrink self-test (multi-arg): incomplete shrink ({repr shrunkArgs})")
    | _, _, _ =>
      throw (IO.userError s!"shrink self-test (multi-arg): unexpected shape ({repr shrunkArgs})")
  | _, _, _ =>
    throw (IO.userError s!"shrink self-test (multi-arg): unexpected size ({repr shrunkArgs})")
  let s1Fault : FilesState -> FilesReq -> FilesOutcome -> Option FilesState := fun st req out =>
    match req, out with
    | .fcntl _ .getFd, .u32 v =>
      if v == 1 then none else allowedStep st req out
    | _, _ => allowedStep st req out
  let s1bDir := rootDir / "shrink-self-test-s1b"
  let s1bSetup : System.FilePath -> Option System.FilePath -> IO SeedTreeConfig := fun d _ => do
    removeDirForced d
    IO.FS.createDirAll d
    let dr ← IO.FS.realPath d
    IO.Process.setCurrentDir dr
    let _ ← Env.mkfifo "p.fifo".toUTF8 0o600
    let fm ← Env.statMode "p.fifo".toUTF8
    return {
      cwdPath := dr.toString.toUTF8
      cwdBound := true
      cwdEntries := [{ name := "p.fifo".toUTF8, kind := .fifo, mode := fm, modeExact := true }]
    }
  let s1bTrace : Array SymStep := #[
    { allocId := none, req := .getcwd 64 },
    { allocId := some 0, req := .openat none "p.fifo".toUTF8 { path := true, cloexec := true } 0 },
    { allocId := none, req := .getcwd 64 },
    { allocId := some 1, req := .reopenReadOnly 0 },
    { allocId := none, req := .fcntl 1 .getFd }
  ]
  let s1bRepro : Array SymStep -> IO Bool := fun cand => do
    let r ← replayTrace s1bDir cand s1Fault none s1bSetup
    return r.mismatchIdx.isSome
  if !(← s1bRepro s1bTrace) then
    throw (IO.userError "shrink self-test (reopenReadOnly O_PATH fifo): replay did not reproduce")
  let shrunkS1b ← shrinkTrace s1bTrace s1bRepro
  if shrunkS1b.size != 3 || !(← s1bRepro shrunkS1b) then
    throw (IO.userError s!"shrink self-test (reopenReadOnly O_PATH fifo): expected 3 steps, got {shrunkS1b.size} ({repr shrunkS1b})")
  let openSlot? : Option StdioFd ← do
    if (← Env.fdKind 0) != 0 then pure (some .stdin)
    else if (← Env.fdKind 1) != 0 then pure (some .stdout)
    else if (← Env.fdKind 2) != 0 then pure (some .stderr)
    else pure none
  if let some slot := openSlot? then
    let s1aFault : FilesState -> FilesReq -> FilesOutcome -> Option FilesState := fun st req out =>
      match req with
      | .reopenReadOnly _ => none
      | _ => allowedStep st req out
    let s1aDir := rootDir / "shrink-self-test-s1a"
    let s1aTrace : Array SymStep := #[
      { allocId := none, req := .getcwd 64 },
      { allocId := some 0, req := .dupStdio slot },
      { allocId := none, req := .getcwd 64 },
      { allocId := some 1, req := .reopenReadOnly 0 },
      { allocId := none, req := .getcwd 64 }
    ]
    let s1aRepro : Array SymStep -> IO Bool := fun cand => do
      let r ← replayTrace s1aDir cand s1aFault
      return r.mismatchIdx.isSome
    if !(← s1aRepro s1aTrace) then
      throw (IO.userError "shrink self-test (reopenReadOnly external stdio): replay did not reproduce")
    let shrunkS1a ← shrinkTrace s1aTrace s1aRepro
    if shrunkS1a.size != 2 || !(← s1aRepro shrunkS1a) then
      throw (IO.userError s!"shrink self-test (reopenReadOnly external stdio): expected 2 steps, got {shrunkS1a.size} ({repr shrunkS1a})")
    let s1cFault : FilesState -> FilesReq -> FilesOutcome -> Option FilesState := fun st req out =>
      match req with
      | .openat d? p _ _ =>
        match resolveOpenTarget st d? p true false {} false with
        | .ok (.existing ino _ _ _ _ _ _) =>
          if st.fds.any (fun (_, fd) => fd.isExternalStdio && fd.ino == ino) then none
          else allowedStep st req out
        | _ => allowedStep st req out
      | _ => allowedStep st req out
    let s1cDir := rootDir / "shrink-self-test-s1c"
    let s1cBlockTrace : Array SymStep := #[
      { allocId := some 0, req := .dupStdio slot },
      { allocId := some 1, req := .openat none "/proc/self/fd/@0".toUTF8 { access := .rdonly, nonblock := false } 0 }
    ]
    let rBlock ← replayTrace s1cDir s1cBlockTrace s1cFault
    if rBlock.mismatchIdx.isSome then
      throw (IO.userError "shrink self-test (dupStdio proc-fd nonblock): blocking open was not guarded")
    let s1cTrace : Array SymStep := #[
      { allocId := none, req := .getcwd 64 },
      { allocId := some 0, req := .dupStdio slot },
      { allocId := some 1, req := .openat none "/proc/self/fd/@0".toUTF8 { access := .rdonly, nonblock := true } 0 }
    ]
    let s1cRepro : Array SymStep -> IO Bool := fun cand => do
      let r ← replayTrace s1cDir cand s1cFault
      return r.mismatchIdx.isSome
    if !(← s1cRepro s1cTrace) then
      throw (IO.userError "shrink self-test (dupStdio proc-fd nonblock): replay did not reproduce")
    let shrunkS1c ← shrinkTrace s1cTrace s1cRepro
    let keptNb := shrunkS1c.any fun st =>
      match st.req with | .openat _ _ fl _ => fl.nonblock | _ => false
    if shrunkS1c.size != 2 || !keptNb || !(← s1cRepro shrunkS1c) then
      throw (IO.userError s!"shrink self-test (dupStdio proc-fd nonblock): lost nonblock ({repr shrunkS1c})")
  let s3Dir := rootDir / "shrink-self-test-s3"
  let s3Trace : Array SymStep := #[
    { allocId := none, req := .getcwd 64 },
    { allocId := some 0, req := .openat none ".".toUTF8 { access := .rdonly } 0 },
    { allocId := some 1, req := .openat none ".".toUTF8 { access := .rdonly } 0 },
    { allocId := some 2, req := .openat none ".".toUTF8 { access := .rdonly } 0 },
    { allocId := some 3, req := .openat none ".".toUTF8 { access := .rdonly } 0 }
  ]
  let s3Fault : FilesState -> FilesReq -> FilesOutcome -> Option FilesState := fun st req out =>
    match req, out with
    | .openat _ _ _ _, .err e =>
      if e == Errno.EMFILE then none else allowedStep st req out
    | _, _ => allowedStep st req out
  let s3NoLim ← replayTrace s3Dir s3Trace s3Fault
  if s3NoLim.mismatchIdx.isSome then
    throw (IO.userError "shrink self-test (rlimitNofile=none): unexpected EMFILE without rlimit")
  let s3Repro : Array SymStep -> IO Bool := fun cand => do
    let r ← replayTrace s3Dir cand s3Fault none
      (fun d _ => do
        removeDirForced d
        IO.FS.createDirAll d
        let dr ← IO.FS.realPath d
        IO.Process.setCurrentDir dr
        return { cwdPath := dr.toString.toUTF8, cwdBound := true })
      id none false (pure ()) (some 3)
    return r.mismatchIdx.isSome
  if !(← s3Repro s3Trace) then
    throw (IO.userError "shrink self-test (rlimitNofile=3): expected EMFILE did not reproduce")
  let shrunkS3 ← shrinkTrace s3Trace s3Repro
  if shrunkS3.isEmpty || shrunkS3.size > 4 || !(← s3Repro shrunkS3) then
    throw (IO.userError s!"shrink self-test (rlimitNofile=3): unexpected shrunk trace ({repr shrunkS3})")
  let s4Dir := rootDir / "shrink-self-test-s4"
  let s4Trace : Array SymStep := #[
    { allocId := some 0, req := .openat none ".".toUTF8 { access := .rdonly, directory := true } 0 },
    { allocId := none, req := .fstatat (some 0) "missing".toUTF8 {} }
  ]
  let s4Fault : FilesState -> FilesReq -> FilesOutcome -> Option FilesState := fun st req out =>
    match req, out with
    | .fstatat _ _ _, .err e =>
      if e == Errno.ENOENT then none else allowedStep st req out
    | _, _ => allowedStep st req out
  let s4Repro : Array SymStep -> IO Bool := fun cand => do
    let r ← replayTrace s4Dir cand s4Fault
    return r.mismatchIdx.isSome
  if !(← s4Repro s4Trace) then
    throw (IO.userError "shrink self-test (dirfd decouple): baseline did not trigger")
  let shrunkS4 ← shrinkTrace s4Trace s4Repro
  if shrunkS4.size != 1 || !(← s4Repro shrunkS4) then
    throw (IO.userError s!"shrink self-test (dirfd decouple): expected 1-step AT_FDCWD trace, got {shrunkS4.size} ({repr shrunkS4})")
  let accSeekTrace : Array SymStep := #[
    { allocId := some 0, req := .openat none "sub".toUTF8 { access := .rdwr } 0o644 },
    { allocId := none, req := .lseek 0 64 .seekEnd }
  ]
  let accSeekRepro : Array SymStep -> IO Bool := fun cand => do
    match cand[0]?, cand[1]? with
    | some s0, some s1 =>
      if cand.size != 2 then return false
      match s0.req, s1.req with
      | .openat none _ fl _, .lseek _ _ _ => return fl.access != .rdonly
      | _, _ => return false
    | _, _ => return false
  let shrunkAccSeek ← shrinkTrace accSeekTrace accSeekRepro
  match shrunkAccSeek[0]?, shrunkAccSeek[1]? with
  | some s0, some s1 =>
    match s0.req, s1.req with
    | .openat none p fl mode, .lseek _ off wh =>
      if p.size != 1 || fl.access != .wronly || mode != 0 || off != 0 || wh != .seekSet then
        throw (IO.userError s!"shrink self-test (access/whence): incomplete shrink ({repr shrunkAccSeek})")
    | _, _ =>
      throw (IO.userError s!"shrink self-test (access/whence): unexpected shape ({repr shrunkAccSeek})")
  | _, _ =>
    throw (IO.userError s!"shrink self-test (access/whence): unexpected size ({repr shrunkAccSeek})")
  runClosedStdinGuardRegression rootDir
  return s!"shrinker reduced {rawTrace.size} -> {shrunk.size} steps, preSeeded=1 {coupledTrace.size} -> {shrunkPre.size} steps (payload {bigData.size}B -> {shrunkPayloadLen}B, multi-arg/reopen/rlimit/dirfd/closed-stdin ok)"

private def pickCrossParent (baseReal : System.FilePath) (uniqTag : String) : IO (Option System.FilePath) := do
  let baseBytes := baseReal.toString.toUTF8
  let baseMnt ← Env.statMntId baseBytes
  let baseDev ← Env.statDev baseBytes
  let baseFs ← Env.statfsFsType baseBytes
  let mut bestFallback : Option System.FilePath := none
  for cand in #[System.FilePath.mk "/var/tmp", System.FilePath.mk "/tmp", System.FilePath.mk "/dev/shm"] do
    if ← cand.pathExists then
      let candReal ← IO.FS.realPath cand
      let candBytes := candReal.toString.toUTF8
      let candMnt ← Env.statMntId candBytes
      let candDev ← Env.statDev candBytes
      let candFs ← Env.statfsFsType candBytes
      let diffMount :=
        if candMnt != 0 && baseMnt != 0 then candMnt != baseMnt
        else candDev != 0 && baseDev != 0 && candDev != baseDev
      if diffMount then
        let probe := candReal / s!"leanswe-fuzz-files-cross-{uniqTag}"
        try
          removeDirForced probe
          IO.FS.createDirAll probe
          let _ ← Env.chmod probe.toString.toUTF8 0o755
          if candFs != 0 && baseFs != 0 && candFs != baseFs then
            if let some fb := bestFallback then
              removeDirForced fb
            return some probe
          else if bestFallback.isNone then
            bestFallback := some probe
          else
            removeDirForced probe
        catch _ =>
          pure ()
  return bestFallback

private def seedOneOverlayLowerEp (ops : FilesOps) (d : System.FilePath) : IO Unit := do
  IO.FS.createDirAll (d / "ldir")
  IO.FS.createDirAll (d / "empty_ldir")
  IO.FS.writeFile (d / "lf") "low-file\n"
  IO.FS.writeFile (d / "ldir" / "x") "low-x\n"
  if let .ok hfd ← ops.openat none (d / "hl_lo1").toString.toUTF8 { access := .rdwr, creat := true } 0o644 then
    let _ ← ops.write hfd "low-hl\n".toUTF8
    let _ ← ops.close hfd
    let _ ← Env.link (d / "hl_lo1").toString.toUTF8 (d / "hl_lo2").toString.toUTF8
  let _ ← ops.symlinkat "hl_lo1".toUTF8 none (d / "sym_hla").toString.toUTF8
  for (nm, md) in #[("suid_lf", (0o4755 : UInt32)), ("sgid_lf", 0o2755), ("sgid_nogrp_lf", 0o2745)] do
    if let .ok sfd ← ops.openat none (d / nm).toString.toUTF8 { access := .rdwr, creat := true } 0o644 then
      let _ ← ops.write sfd "low-suid\n".toUTF8
      let _ ← ops.close sfd
      let _ ← Env.chmod (d / nm).toString.toUTF8 md

/-- Pre-seed `count` episode lower directories for an `overlayfs` worker before mounting. -/
def seedOverlayLowerDirs (lowDir : System.FilePath) (count : Nat) : IO Unit := do
  let ops := defaultOps
  for i in [:count] do
    seedOneOverlayLowerEp ops (lowDir / s!"ep-{i}")
  for i in [:512] do
    seedOneOverlayLowerEp ops (lowDir / s!"shrink-{i}")

/-- Populate one read-only source directory tree for `ro_bind` fuzzing before remounting read-only. -/
def seedReadOnlyTree (roSrc : System.FilePath) : IO Unit := do
  let saved ← IO.Process.getCurrentDir
  try
    let _ ← materializeEpisode defaultOps roSrc none false
      (.charDev, some .nullDev) (.charDev, some .nullDev) (.charDev, some .nullDev)
      { epUmask := 0o022, sgidSub := false, cwdSubdir := false, seedCross := false }
      false false
    let _ ← Env.chmod (roSrc / "sub" / "a").toString.toUTF8 0o644
    IO.FS.writeFile (roSrc / "f444") "ro444\n"
    let _ ← Env.chmod (roSrc / "f444").toString.toUTF8 0o444
    for (dname, dmode) in #[("s1777", (0o1777 : UInt32)), ("s1721", 0o1721), ("s1002", 0o1002)] do
      IO.FS.createDirAll (roSrc / dname)
      IO.FS.writeFile (roSrc / dname / "reg666") "sticky\n"
      let _ ← Env.chmod (roSrc / dname / "reg666").toString.toUTF8 0o666
      let _ ← Env.mkfifo (roSrc / dname / "fifo666").toString.toUTF8 0o666
      let _ ← Env.chmod (roSrc / dname / "fifo666").toString.toUTF8 0o666
      let _ ← Env.chmod (roSrc / dname).toString.toUTF8 dmode
  finally
    IO.Process.setCurrentDir saved

/-- Serialize `HitStats` to stdout lines for parent aggregation from worker subprocesses. -/
def formatWorkerStats (rep : FuzzReport) : String := Id.run do
  let mut lines : Array String := #[]
  lines := lines.push s!"WORKER_STAT_META {rep.totalSteps} {rep.totalEpisodes}"
  for (k, v) in rep.stats.counts.toList do
    lines := lines.push s!"WORKER_STAT_COUNT {k} {v}"
  for (k, v) in rep.stats.kindCounts.toList do
    lines := lines.push s!"WORKER_STAT_KIND {k} {v}"
  return String.intercalate "\n" lines.toList

private def parseWorkerStats (stdout : String) : HitStats := Id.run do
  let mut counts : Std.HashMap String Nat := {}
  let mut kindCounts : Std.HashMap String Nat := {}
  let mut totalSteps : Nat := 0
  let mut totalEpisodes : Nat := 0
  for rawLine in stdout.splitOn "\n" do
    let parts := rawLine.trimAscii.toString.splitOn " "
    match parts with
    | ["WORKER_STAT_META", sStr, eStr] =>
      totalSteps := totalSteps + sStr.toNat?.getD 0
      totalEpisodes := totalEpisodes + eStr.toNat?.getD 0
    | ["WORKER_STAT_COUNT", k, vStr] =>
      counts := counts.insert k (counts.getD k 0 + vStr.toNat?.getD 0)
    | ["WORKER_STAT_KIND", k, vStr] =>
      kindCounts := kindCounts.insert k (kindCounts.getD k 0 + vStr.toNat?.getD 0)
    | _ => pure ()
  return { counts, kindCounts, totalSteps, totalEpisodes }

private def runAsymSymlinkParityProbe (parityDir : System.FilePath)
    (in0 out1 err2 : FileKind × Option SpecialDevKind) : IO Unit := do
  let probeRecipe : EpisodeRecipe :=
    { epUmask := 0o022, seedFifo := false, seedSock := false,
      seedHardlinks := false, seedSymlinks := false, seedD255 := false, seedCross := false }
  let trace : Array SymStep := #[
    { allocId := none, req := .symlinkat "s_unmap/sym_other".toUTF8 none "a".toUTF8 },
    { allocId := none, req := .faccessat none "a/l".toUTF8 {} {} },
    { allocId := none, req := .faccessat none "a/l".toUTF8 { write := true } { eaccess := true } },
    { allocId := none, req := .faccessat none "a/l".toUTF8 { read := true } {} },
    { allocId := none, req := .faccessat none "a/l".toUTF8 { exec := true } {} },
    { allocId := none, req := .faccessat none "a/l".toUTF8 {} { symlinkNofollow := true } },
    { allocId := none, req := .faccessat none "a".toUTF8 {} {} },
    { allocId := none, req := .faccessat none "a".toUTF8 {} { symlinkNofollow := true } },
    { allocId := none, req := .faccessat none "a/".toUTF8 {} { symlinkNofollow := true } },
    { allocId := none, req := .symlinkat "s1777/sym_other".toUTF8 none "b".toUTF8 },
    { allocId := none, req := .faccessat none "b/l".toUTF8 {} {} },
    { allocId := none, req := .faccessat none "b".toUTF8 {} {} },
    { allocId := none, req := .symlinkat "s_unmap/sym_other/".toUTF8 none "at".toUTF8 },
    { allocId := none, req := .faccessat none "at".toUTF8 {} {} },
    { allocId := none, req := .symlinkat "s_unmap/sym_other/l".toUTF8 none "al".toUTF8 },
    { allocId := none, req := .faccessat none "al".toUTF8 {} {} },
    { allocId := none, req := .faccessat none "s_unmap/sym_other".toUTF8 {} {} },
    { allocId := none, req := .faccessat none "s_unmap/sym_other".toUTF8 {} { symlinkNofollow := true } },
    { allocId := none, req := .faccessat none "s_unmap/sym_other/".toUTF8 {} { symlinkNofollow := true } },
    { allocId := none, req := .faccessat none "s_unmap/sym_other/l".toUTF8 {} {} },
    { allocId := none, req := .faccessat none "s_unmap/sym_other/.".toUTF8 {} {} },
    { allocId := none, req := .faccessat none "s_unmap/sym_other/..".toUTF8 {} {} },
    { allocId := some 0, req := .openat none "s_unmap".toUTF8 { access := .rdonly, directory := true } 0 },
    { allocId := none, req := .faccessat (some 0) "sym_other".toUTF8 {} {} },
    { allocId := none, req := .faccessat (some 0) "sym_other/l".toUTF8 {} {} },
    { allocId := some 1, req := .openat2 (some 0) "sym_other".toUTF8 { resolve := { beneath := true } } },
    { allocId := some 2, req := .openat2 (some 0) "sym_other/l".toUTF8 { resolve := { beneath := true } } },
    { allocId := some 3, req := .openat none "a/l".toUTF8 { access := .rdonly } 0 },
    { allocId := some 4, req := .openat none "a/l".toUTF8 { access := .rdwr, creat := true } 0o644 },
    { allocId := some 5, req := .openat none "s_unmap/sym_other".toUTF8 { access := .rdonly } 0 },
    { allocId := some 6, req := .openat none "s_unmap/sym_other".toUTF8 { path := true, nofollow := true } 0 },
    { allocId := some 7, req := .openat none "s_unmap/sym_other/".toUTF8 { path := true, nofollow := true } 0 },
    { allocId := some 8, req := .openat none "s_unmap/sym_other".toUTF8 { access := .rdwr, creat := true, excl := true } 0o644 },
    { allocId := some 9, req := .openat none "s_unmap/sym_other".toUTF8 { access := .rdwr, creat := true, nofollow := true } 0o644 },
    { allocId := some 10, req := .openat none "s_unmap/sym_other/".toUTF8 { access := .rdwr, creat := true } 0o644 },
    { allocId := some 11, req := .openat2 none "s_unmap/sym_other".toUTF8 { resolve := { noSymlinks := true } } },
    { allocId := some 12, req := .openat2 none "s_unmap/sym_other/l".toUTF8 { resolve := { noSymlinks := true } } },
    { allocId := some 13, req := .openat2 none "a/l".toUTF8 { resolve := { noSymlinks := true } } },
    { allocId := none, req := .fstatat none "a/l".toUTF8 {} },
    { allocId := none, req := .fstatat none "a/l".toUTF8 { symlinkNofollow := true } },
    { allocId := none, req := .fstatat none "a".toUTF8 {} },
    { allocId := none, req := .fstatat none "s_unmap/sym_other/".toUTF8 { symlinkNofollow := true } },
    { allocId := none, req := .readlinkat none "a/l".toUTF8 64 },
    { allocId := none, req := .readlinkat none "s_unmap/sym_other".toUTF8 64 },
    { allocId := none, req := .readlinkat none "s_unmap/sym_other/".toUTF8 64 },
    { allocId := none, req := .fchmodat none "a/l".toUTF8 0o644 },
    { allocId := none, req := .fchmodat none "s_unmap/sym_other/l".toUTF8 0o644 },
    { allocId := none, req := .mkdirat none "a/l".toUTF8 0o755 },
    { allocId := none, req := .mkdirat none "s_unmap/sym_other/l".toUTF8 0o755 },
    { allocId := none, req := .unlinkat none "a/l".toUTF8 false },
    { allocId := none, req := .unlinkat none "s_unmap/sym_other/l".toUTF8 false },
    { allocId := none, req := .symlinkat "t".toUTF8 none "a/l".toUTF8 },
    { allocId := none, req := .symlinkat "t".toUTF8 none "s_unmap/sym_other/l".toUTF8 },
    { allocId := none, req := .renameat2 none "a/l".toUTF8 none "x".toUTF8 {} },
    { allocId := none, req := .renameat2 none "sub/a".toUTF8 none "a/l".toUTF8 {} }
  ]
  let r ← replayTrace parityDir trace allowedStep none
    (fun d cd? => do
      let (rcfg, _, _) ← materializeEpisode defaultOps d cd? false in0 out1 err2 probeRecipe
        false false false false []
      return rcfg)
    id none false (pure ()) none true
  if let some idx := r.mismatchIdx then
    throw (IO.userError s!"asym symlink parity probe mismatch at step {idx}: req={repr r.mismatchReq} out={repr r.mismatchOut}")

/-- Run stateful randomized episodes on a single target directory `baseDir`. -/
def runFilesFuzzOnDir (totalSteps : Nat) (seed : UInt64) (selfTestShrink : Bool)
    (baseDir : System.FilePath := "/dev/shm")
    (crossOverride? : Option System.FilePath := none)
    (isRoSeeded : Bool := false)
    (chrootDir? : Option System.FilePath := none)
    (hostProtected : Bool := false)
    (allowAutoCross : Bool := true)
    (seccompMode : Bool := false)
    (unlinkedCwdMode : Bool := false)
    (preseededEps : Bool := false)
    (rlimitNofile? : Option UInt64 := none) : IO FuzzReport := do
  Env.ignoreSigpipe
  let savedNofileCur ← Env.getRlimitNofileCur
  let savedNofileMax ← Env.getRlimitNofileMax
  let savedStdio ← captureStdioState defaultOps
  let pid ← getCurrentPid
  let chrootMode := chrootDir?.isSome
  let myUid ← Env.getUid
  let uidRanges ← Env.readIdMap "/proc/self/uid_map"
  let gidRanges ← Env.readIdMap "/proc/self/gid_map"
  let selfGids ← Env.readSelfGids
  let mut chrootOuterEntries : List SeedEntry := []
  if chrootMode then
    let probes : Array (List ByteArray × String × String × FileKind) := #[
      ([], "etc", "/etc", .dir),
      (["etc".toUTF8], "passwd", "/etc/passwd", .reg),
      ([], "sys", "/sys", .dir),
      (["sys".toUTF8], "kernel", "/sys/kernel", .dir),
      (["sys".toUTF8, "kernel".toUTF8], "cpu_byteorder", "/sys/kernel/cpu_byteorder", .reg),
      ([], "tmp", "/tmp", .dir)
    ]
    for (relD, nm, ap, kd) in probes do
      if let some ent ← probeOuterEntry relD nm.toUTF8 ap kd myUid uidRanges gidRanges selfGids then
        chrootOuterEntries := chrootOuterEntries ++ [ent]
  if let some cr := chrootDir? then
    IO.FS.createDirAll baseDir
    IO.Process.setCurrentDir baseDir
    let rc ← Env.chroot cr.toString.toUTF8
    if rc != 0 then
      throw (IO.userError s!"chroot({cr}) failed with errno={rc}")
  let baseReal ←
    if chrootMode then pure (System.FilePath.mk ".")
    else IO.FS.realPath baseDir
  let allowHostMut := (myUid != 0) || hostProtected || chrootMode
  let in0Code ← Env.fdKind 0
  let out1Code ← Env.fdKind 1
  let err2Code ← Env.fdKind 2
  let isPreseededUnlinked ←
    if unlinkedCwdMode && !isRoSeeded && !chrootMode then (baseReal / ".ovl_unlinked").pathExists
    else pure false
  let isPreseededLower ←
    if !isRoSeeded && !chrootMode && !unlinkedCwdMode then (baseReal / "ep-0" / "lf").pathExists
    else pure false
  let isPreseededRwSticky ←
    if !isRoSeeded && !chrootMode && !unlinkedCwdMode then (baseReal / "ep-0" / "s1777" / "f640").pathExists
    else pure false
  if preseededEps && !unlinkedCwdMode && !isPreseededLower && !isPreseededRwSticky then
    throw (IO.userError s!"--preseeded-eps expected preseeded lower ep-0/lf or ep-0/s1777/f640 under {baseReal}, but it was not found")
  if preseededEps && unlinkedCwdMode && !isPreseededUnlinked then
    throw (IO.userError s!"--preseeded-eps with unlinked_cwd expected {baseReal}/.ovl_unlinked, but it was not found")
  let uniqTag := s!"{pid}-{← IO.monoNanosNow}"
  let rootDir : System.FilePath :=
    if isRoSeeded then baseReal
    else if chrootMode then System.FilePath.mk "."
    else if isPreseededUnlinked || isPreseededLower || isPreseededRwSticky then baseReal
    else baseReal / s!"leanswe-fuzz-files-{uniqTag}"
  if !isRoSeeded && !chrootMode && !isPreseededUnlinked && !isPreseededLower && !isPreseededRwSticky then
    removeDirForced rootDir
    IO.FS.createDirAll rootDir
    let _ ← Env.chmod rootDir.toString.toUTF8 0o755
  let crossRoot? ←
    if isRoSeeded || chrootMode then pure crossOverride?
    else if let some co := crossOverride? then pure (some co)
    else if allowAutoCross then pickCrossParent baseReal uniqTag
    else pure none
  let watchRoot? : Option System.FilePath :=
    if !isRoSeeded && !chrootMode && !isPreseededUnlinked && !isPreseededLower && !isPreseededRwSticky then
      some rootDir
    else
      none
  let watchCross? : Option System.FilePath :=
    if crossOverride?.isNone then crossRoot? else none
  if watchRoot?.isSome || watchCross?.isSome then
    let mut stdioPins : Array RawFd := #[]
    for code in #[in0Code, out1Code, err2Code] do
      if code == 0 then
        match ← defaultOps.openat none "/dev/null".toUTF8 { access := .rdonly, cloexec := true } 0 with
        | .ok pfd => stdioPins := stdioPins.push pfd
        | .error _ => pure ()
    spawnCrashWatcher pid watchRoot? watchCross?
    for pfd in stdioPins do
      let _ ← defaultOps.close pfd
  let in0Code ← Env.fdKind 0
  let out1Code ← Env.fdKind 1
  let err2Code ← Env.fdKind 2
  let in0 := decodeProbeFdKind in0Code
  let out1 := decodeProbeFdKind out1Code
  let err2 := decodeProbeFdKind err2Code
  let safeStdin :=
    in0Code != 0 &&
    ((in0.1 == .charDev && in0.2 == some .nullDev) ||
     (in0.1 == .reg && Env.isIdMapped uidRanges myUid && (← Env.fdUid 0) == myUid))
  let savedCwd ←
    if chrootMode then pure (System.FilePath.mk ".")
    else IO.Process.getCurrentDir
  let savedUmask ← Env.umask 0o022
  let savedFsizeCur ← Env.getRlimitFsizeCur
  let savedFsizeMax ← Env.getRlimitFsizeMax
  let outsideFd? : Option RawFd ←
    if chrootMode then
      match ← defaultOps.openat none ".".toUTF8 { access := .rdonly, directory := true } 0 with
      | .ok fd => pure (some fd)
      | .error _ => pure none
    else pure none
  try
    let shrinkDetail ←
      if selfTestShrink && !isRoSeeded && !chrootMode && !seccompMode then runShrinkSelfTest rootDir else pure ""
    if isPreseededRwSticky then
      let parityDir := rootDir / "parity-sym"
      if ← (parityDir / "s_unmap" / "reg666").pathExists then
        runAsymSymlinkParityProbe parityDir in0 out1 err2
    let startNs ← IO.monoNanosNow
    let mut rng := Rng.seed seed
    let mut stats : HitStats := {}
    let mut loopSteps : Nat := 0
    let mut epIdx : Nat := 0
    let seccompErrPool : Array Errno := #[
      Errno.EPERM, Errno.EACCES, Errno.EBUSY, Errno.ENOSYS, Errno.EINVAL, Errno.EOPNOTSUPP,
      Errno.EBADF, Errno.EINTR, Errno.EIO, Errno.ENOSPC, (122 : Errno), Errno.ENOMEM,
      Errno.ESTALE, (104 : Errno), Errno.EPIPE, Errno.EAGAIN
    ]
    let closedDummy? ← allocClosedDummy defaultOps
    if seccompMode then
      let nrClose ← Env.nrForSlot 2
      let nrFcntl ← Env.nrForSlot 17
      let nrFstat ← Env.nrForSlot 5
      let nrGetcwd ← Env.nrForSlot 19
      let probePath := (rootDir / "seccomp_close_probe").toString.toUTF8
      let scProbe ← Env.forkForStatus
      if scProbe == 0 then
        match ← defaultOps.openat none probePath { access := .rdwr, creat := true } 0o644 with
        | .error _ => Env.exitImmediate 78
        | .ok pfd =>
          if (← Env.installSeccompErrno nrClose Errno.EPERM nrFcntl Errno.EBADF nrGetcwd Errno.ENOSYS) != 0 then
            Env.exitImmediate 77
          match ← defaultOps.close pfd with
          | .error e =>
            if e != Errno.EPERM then Env.exitImmediate 79
          | .ok () => Env.exitImmediate 80
          match ← defaultOps.getcwd 64 with
          | .error e =>
            if e != Errno.ENOSYS then Env.exitImmediate 82
          | .ok _ => Env.exitImmediate 83
          match ← defaultOps.fstat pfd with
          | .ok _ => Env.exitImmediate 0
          | .error _ => Env.exitImmediate 81
      if scProbe == 2077 then
        throw (IO.userError "seccomp tri-filter probe failed (PR_SET_SECCOMP unsupported)")
      if scProbe != 2000 then
        throw (IO.userError s!"seccomp tri-filter probe failed (status={scProbe}): fd_box.h closed FD on failed close+fcntl(EBADF)")
      let scProbe2 ← Env.forkForStatus
      if scProbe2 == 0 then
        match ← defaultOps.openat none probePath { access := .rdwr, creat := true } 0o644 with
        | .error _ => Env.exitImmediate 78
        | .ok pfd =>
          if (← Env.installSeccompErrno nrClose Errno.EIO nrFcntl Errno.EPERM nrFstat Errno.EPERM) != 0 then
            Env.exitImmediate 77
          match ← defaultOps.close pfd with
          | .error e =>
            if e != Errno.EIO then Env.exitImmediate 79
          | .ok () => Env.exitImmediate 80
          match ← defaultOps.fstat pfd with
          | .error e =>
            if e == Errno.EBADF then Env.exitImmediate 0 else Env.exitImmediate 81
          | .ok _ => Env.exitImmediate 82
      if scProbe2 != 2000 then
        throw (IO.userError s!"seccomp kernel-close-err probe failed (status={scProbe2}): fd_box.h failed to commit closed=1 on close(EIO)")
      removeDirForced (rootDir / "seccomp_close_probe")
    while loopSteps < totalSteps do
      let remaining := totalSteps - loopSteps
      let (epLenRaw, rLen) := rng.nextNat 101
      let (recipe, rRec) := genEpisodeRecipe rLen
      let (slot2Nat, rSl) := rRec.nextNat 21
      let (slot3Nat, rSl3) := rSl.nextNat 21
      let (useRandE1, rE0a) := rSl3.chance 1 2
      let (scErr1, rE1) :=
        if useRandE1 then
          let (raw, rTmp) := rE0a.nextNat 4095
          let code := raw + 1
          (UInt32.ofNat (if code == 14 then 13 else code), rTmp)
        else
          rE0a.pickArray seccompErrPool Errno.EPERM
      let (useRandE2, rE0b) := rE1.chance 1 2
      let (scErr2, rE2) :=
        if useRandE2 then
          let (raw, rTmp) := rE0b.nextNat 4095
          let code := raw + 1
          (UInt32.ofNat (if code == 14 then 13 else code), rTmp)
        else
          rE0b.pickArray seccompErrPool Errno.ENOSYS
      let (useRandE3, rE0c) := rE2.chance 1 2
      let (scErr3, rE3) :=
        if useRandE3 then
          let (raw, rTmp) := rE0c.nextNat 4095
          let code := raw + 1
          (UInt32.ofNat (if code == 14 then 13 else code), rTmp)
        else
          rE0c.pickArray seccompErrPool Errno.EACCES
      rng := rE3
      let slot1Nat := (epIdx + seed.toNat) % 21
      let epLen := min remaining (if seccompMode then 50 else if rlimitNofile?.isSome then 40 else 50 + epLenRaw)
      let epDir := if isRoSeeded then rootDir else rootDir / s!"ep-{epIdx}"
      let crossEpDir? := crossRoot?.map (· / s!"ep-{epIdx}")
      let ops := defaultOps
      let (cfg, crossCleanup?, crossStr?) ←
        materializeEpisode ops epDir crossEpDir? false in0 out1 err2 recipe
          isRoSeeded chrootMode seccompMode unlinkedCwdMode chrootOuterEntries
      let epFd? : Option RawFd ←
        if chrootMode then
          match ← ops.openat none ".".toUTF8 { access := .rdonly, directory := true } 0 with
          | .ok fd => pure (some fd)
          | .error _ => pure none
        else pure none
      let modelState0 := applyClosedStdioToState in0Code out1Code err2Code (FilesState.withSeededTree cfg)
      let mut modelState := if unlinkedCwdMode then unlinkSeededCwd modelState0 else modelState0
      if preseededEps && isPreseededLower && !unlinkedCwdMode && epIdx == 0 then
        let hasHlLo1 := (assocGet modelState.inodes modelState.cwdIno).map (fun cvn =>
          cvn.children.any fun (nm, _) => bytesEq nm "hl_lo1".toUTF8) |>.getD false
        if !hasHlLo1 then
          throw (IO.userError s!"preseeded overlay lower dir at {epDir} did not populate hl_lo1 in episode 0")
      let shrinkAttemptRef ← IO.mkRef (0 : Nat)
      let nextShrinkDir : IO System.FilePath := do
        if isPreseededLower || isPreseededUnlinked || isPreseededRwSticky then
          let idx ← shrinkAttemptRef.modifyGet fun n => (n, n + 1)
          let cand := rootDir / s!"shrink-{idx}"
          let existsCand ←
            if isPreseededLower then (cand / "lf").pathExists
            else if isPreseededRwSticky then (cand / "s1777" / "f640").pathExists
            else cand.pathExists
          if existsCand then return cand
        return rootDir / "shrink"
      let ownedRootIno :=
        match (splitPathBytes cfg.cwdPath).2.1.reverse with
        | leaf :: _ =>
          if !isRoSeeded && !chrootMode && bytesEq leaf ("work".toUTF8) then
            (assocGet modelState.inodes modelState.cwdIno).map (·.parentIno) |>.getD modelState.cwdIno
          else modelState.cwdIno
        | [] => modelState.cwdIno
      let crossIno? := cfg.crossMountPath?.bind fun cp =>
        match inspectPathTarget modelState {} none cp true with
        | some (_, ino?, _) => ino?
        | none => none
      let mut env : GenEnv := {}
      let mut rawMap : Std.HashMap HandleId RawFd := {}
      let mut openRfds : Std.HashMap HandleId RawFd := {}
      let mut hidToRawName : Std.HashMap HandleId ByteArray := {}
      let mut trace : Array SymStep := #[]
      let mut nextSym : SymFd := 0
      let mut hasMemfd := false
      try
        if seccompMode then
          let nr1 ← Env.nrForSlot (UInt32.ofNat slot1Nat)
          let nr2 ← Env.nrForSlot (UInt32.ofNat slot2Nat)
          let nr3 ← Env.nrForSlot (UInt32.ofNat slot3Nat)
          let nrClose ← Env.nrForSlot 2
          let nrFstat ← Env.nrForSlot 5
          let nrFstatat ← Env.nrForSlot 6
          if out1Code != 0 then
            (← IO.getStdout).flush
          if err2Code != 0 then
            (← IO.getStderr).flush
          let pipePair ← Env.pipe
          if pipePair == (0xffffffffffffffff : UInt64) then
            throw (IO.userError "seccompMode failed to allocate status pipe")
          let rPipeFd := pipePair.toUInt32
          let wPipeFd := (pipePair >>> 32).toUInt32
          let childPid ← Env.forkPid
          if childPid == (0xffffffff : UInt32) then
            let _ ← Env.closeRawFd rPipeFd
            let _ ← Env.closeRawFd wPipeFd
            throw (IO.userError "seccompMode fork failed")
          if childPid == 0 then
            let _ ← Env.closeRawFd rPipeFd
            if let some flim := recipe.fsizeLimit? then
              let _ ← Env.setRlimitFsize flim savedFsizeMax true
            let runMemfdSeed := !(in0Code == 0 || out1Code == 0 || err2Code == 0) || (epIdx % 2 == 1)
            let (msMem, memRes?) ←
              if runMemfdSeed then
                seedEpisodeMemfd ops modelState myUid uidRanges gidRanges selfGids
              else
                pure (modelState, none)
            modelState := msMem
            if let some (mHid, mFd) := memRes? then
              rawMap := rawMap.insert mHid mFd
              let (msLink, rawN?) ← attachOpenedProcFd ops modelState mHid mFd .rdwr
              modelState := msLink
              let pMap := match rawN? with | some rn => env.procFdMap.insert 0 rn | none => env.procFdMap
              if let some rn := rawN? then
                hidToRawName := hidToRawName.insert mHid (toString rn).toUTF8
              env := { allFds := env.allFds.push (0, mHid), openFds := env.openFds.push (0, mHid), procFdMap := pMap }
              nextSym := 1
              hasMemfd := true
            let scErr ← Env.installSeccompErrno nr1 scErr1 nr2 scErr2 nr3 scErr3
            if scErr != 0 then
              let _ ← Env.closeRawFd wPipeFd
              Env.exitImmediate 77
            let mut childStats : HitStats := {}
            let mut childRng := rng
            for stepIdx in [:epLen] do
              let (sreq, rNext) := genSymReq childRng env modelState ownedRootIno crossIno? crossStr? allowHostMut safeStdin
              childRng := rNext
              let isAlloc := sreq.isAlloc
              let allocId := if isAlloc then some nextSym else none
              if isAlloc then
                nextSym := nextSym + 1
              let symMap : Std.HashMap SymFd HandleId :=
                env.allFds.foldl (fun acc (s, h) => acc.insert s h) {}
              let effSreq := resolveSymProcFdReq env.procFdMap sreq
              match symReqToFilesReq symMap effSreq with
              | none =>
                let _ ← Env.writeFdSafe 2 s!"seccomp unmapped SymFd at step {stepIdx}\n".toUTF8
                let _ ← Env.closeRawFd wPipeFd
                Env.exitImmediate 41
              | some req =>
                let nextHid := modelState.nextHid
                let (out, opened) ← execRealReq ops rawMap nextHid req closedDummy?
                childStats := childStats.record (symReqName sreq) out
                trace := trace.push { allocId, req := sreq }
                match opened, allocId with
                | some (hid, rfd), some sid =>
                  rawMap := rawMap.insert hid rfd
                  env := { env with allFds := env.allFds.push (sid, hid), openFds := env.openFds.push (sid, hid) }
                | none, _ => pure ()
                | _, _ => pure ()
                match sreq, out with
                | .close sid, .err e =>
                  let closeInterceptedErr :=
                    (nr1 == nrClose && e == scErr1) ||
                    (nr2 == nrClose && e == scErr2) ||
                    (nr3 == nrClose && e == scErr3)
                  let isFstatNr := fun (n : UInt32) => n == nrFstat || n == nrFstatat
                  let fstatSeccompEbadf :=
                    (isFstatNr nr1 && scErr1 == Errno.EBADF) ||
                    (isFstatNr nr2 && scErr2 == Errno.EBADF) ||
                    (isFstatNr nr3 && scErr3 == Errno.EBADF)
                  let isKernelCloseDetachErr :=
                    e == Errno.EBADF || e == Errno.EINTR || e == Errno.EIO || e == Errno.ENOSPC ||
                    e == 122 || e == Errno.ENOMEM || e == 116 || e == 104
                  let retainsOpen := !isKernelCloseDetachErr
                  if closeInterceptedErr then
                    if let some hid := symToHid env sid then
                      if let some rfd := rawMap.get? hid then
                        if retainsOpen then
                          if !fstatSeccompEbadf then
                            match ← ops.fstat rfd with
                            | .error fe =>
                              if fe == Errno.EBADF then
                                let _ ← Env.writeFdSafe 2 s!"seccomp premature close at ep={epIdx} step={stepIdx}\n".toUTF8
                                let _ ← Env.closeRawFd wPipeFd
                                Env.exitImmediate 43
                            | .ok _ => pure ()
                        else
                          match ← ops.fstat rfd with
                          | .error fe =>
                            if fe != Errno.EBADF then
                              let _ ← Env.writeFdSafe 2 s!"seccomp non-entry close expected EBADF, got {fe} at ep={epIdx} step={stepIdx}\n".toUTF8
                              let _ ← Env.closeRawFd wPipeFd
                              Env.exitImmediate 43
                          | .ok _ =>
                            let _ ← Env.writeFdSafe 2 s!"seccomp non-entry close leaked open box at ep={epIdx} step={stepIdx}\n".toUTF8
                            let _ ← Env.closeRawFd wPipeFd
                            Env.exitImmediate 43
                | _, _ => pure ()
                let nextState? := if statOutcomeNsecValid out then allowedStep modelState req out else none
                match nextState? with
                | some s' =>
                  let mut sNext := s'
                  if let (some (hid, rfd), some sid) := (opened, allocId) then
                    let (sL, rawN?) ← attachOpenedProcFd ops sNext hid rfd (reqAccessOf effSreq)
                    sNext := sL
                    if let some rn := rawN? then
                      hidToRawName := hidToRawName.insert hid (toString rn).toUTF8
                      env := { env with procFdMap := env.procFdMap.insert sid rn }
                  match sreq with
                  | .close sid =>
                    if let some hid := symToHid env sid then
                      if !(sNext.fds.any fun p => p.1 == hid) then
                        env := { env with openFds := env.openFds.filter (fun p => p.1 != sid), procFdMap := env.procFdMap.erase sid }
                        if let some fn := hidToRawName.get? hid then
                          sNext := sNext.detachProcFdLink fn
                          hidToRawName := hidToRawName.erase hid
                  | _ => pure ()
                  modelState := sNext
                | none =>
                  let msg := s!"MISMATCH_INFO ep={epIdx} slot1={slot1Nat} err1={scErr1} slot2={slot2Nat} err2={scErr2} slot3={slot3Nat} err3={scErr3} step={stepIdx} req={repr req} out={repr out}\n" ++
                    encodeSymTrace trace ++ "\n"
                  let _ ← Env.writeFdSafe wPipeFd msg.toUTF8
                  let _ ← Env.closeRawFd wPipeFd
                  Env.exitImmediate 42
            let cRep : FuzzReport := {
              totalSteps := epLen, totalEpisodes := 1, elapsedMs := 0, syscallsPerSec := 0, stats := childStats
            }
            let _ ← Env.writeFdSafe wPipeFd (formatWorkerStats cRep ++ "\n").toUTF8
            let _ ← Env.closeRawFd wPipeFd
            Env.exitImmediate 0
          let _ ← Env.closeRawFd wPipeFd
          let pipeBytes ← Env.readFdAll rPipeFd
          let _ ← Env.closeRawFd rPipeFd
          let scStatus ← Env.waitPid childPid
          let pipeTxt := String.fromUTF8? pipeBytes |>.getD ""
          if scStatus == 2077 then
            throw (IO.userError "seccomp filter install failed (PR_SET_SECCOMP unsupported)")
          if scStatus == 2042 then
            let (diagInfo, capturedTrace) := decodeSymTrace pipeTxt
            let _ ← Env.setRlimitFsize savedFsizeCur savedFsizeMax false
            cleanupEpisodeDir ops #[] savedCwd epDir crossCleanup?
            let runMemfdSeed := !(in0Code == 0 || out1Code == 0 || err2Code == 0) || (epIdx % 2 == 1)
            let preSeeded ←
              if runMemfdSeed then
                match ← Env.openMemfd with
                | .ok fd =>
                  let _ ← defaultOps.close fd
                  pure 1
                | .error _ => pure 0
              else
                pure 0
            let reproduces : Array SymStep → IO Bool := fun cand => do
              let sDir ← nextShrinkDir
              let sCross? := crossRoot?.map (· / "shrink")
              if out1Code != 0 then
                (← IO.getStdout).flush
              if err2Code != 0 then
                (← IO.getStderr).flush
              let st ← Env.forkForStatus
              if st == 0 then
                let r ← replayTrace sDir cand allowedStep sCross?
                  (fun d cd? => do
                    let (rcfg, _, _) ← materializeEpisode ops d cd? false in0 out1 err2 recipe
                      false false true unlinkedCwdMode chrootOuterEntries
                    return rcfg)
                  (if unlinkedCwdMode then unlinkSeededCwd else id)
                  recipe.fsizeLimit?
                  runMemfdSeed
                  (do
                    if (← Env.installSeccompErrno nr1 scErr1 nr2 scErr2 nr3 scErr3) != 0 then
                      Env.exitImmediate 77)
                  rlimitNofile?
                Env.exitImmediate (if r.mismatchIdx.isSome then 42 else 0)
              return st == 2042
            let shrunk ← shrinkTrace capturedTrace reproduces preSeeded
            throw (IO.userError s!"model/kernel seccomp mismatch ({diagInfo})\nminimal trace ({shrunk.size} steps): {repr shrunk}")
          if scStatus != 2000 then
            throw (IO.userError s!"seccomp episode failed at ep={epIdx} (slot1={slot1Nat}, err1={scErr1}, slot2={slot2Nat}, err2={scErr2}, slot3={slot3Nat}, err3={scErr3}, status={scStatus})")
          let cStats := parseWorkerStats pipeTxt
          stats := HitStats.merge stats cStats
          let (_, rngAfter) := rng.nextU64
          rng := rngAfter
          loopSteps := loopSteps + epLen
        else
          if !isRoSeeded then
            let runMemfdSeed :=
              (rlimitNofile? == some 4 && epIdx % 4 != 0) ||
              !(in0Code == 0 || out1Code == 0 || err2Code == 0) ||
              (epIdx % 2 == 1)
            let (msMem, memRes?) ←
              if runMemfdSeed then
                seedEpisodeMemfd ops modelState myUid uidRanges gidRanges selfGids
              else
                pure (modelState, none)
            modelState := msMem
            if let some (mHid, mFd) := memRes? then
              rawMap := rawMap.insert mHid mFd
              openRfds := openRfds.insert mHid mFd
              let (msLink, rawN?) ← attachOpenedProcFd ops modelState mHid mFd .rdwr
              modelState := msLink
              let pMap := match rawN? with | some rn => env.procFdMap.insert 0 rn | none => env.procFdMap
              if let some rn := rawN? then
                hidToRawName := hidToRawName.insert mHid (toString rn).toUTF8
              env := { allFds := env.allFds.push (0, mHid), openFds := env.openFds.push (0, mHid), procFdMap := pMap }
              nextSym := 1
              hasMemfd := true
            if let some flim := recipe.fsizeLimit? then
              let _ ← Env.setRlimitFsize flim savedFsizeMax true
            if let some rlim := rlimitNofile? then
              let _ ← Env.setRlimitNofile rlim 0
          for stepIdx in [:epLen] do
            let (sreq, rNext) := genSymReq rng env modelState ownedRootIno crossIno? crossStr? allowHostMut safeStdin
            rng := rNext
            let isAlloc := sreq.isAlloc
            let allocId := if isAlloc then some nextSym else none
            if isAlloc then
              nextSym := nextSym + 1
            let symMap : Std.HashMap SymFd HandleId :=
              env.allFds.foldl (fun acc (s, h) => acc.insert s h) {}
            let effSreq := resolveSymProcFdReq env.procFdMap sreq
            match symReqToFilesReq symMap effSreq with
            | none =>
              throw (IO.userError s!"internal generator produced unmapped SymFd at step {stepIdx}")
            | some req =>
              let nextHid := modelState.nextHid
              let (out, opened) ← execRealReq ops rawMap nextHid req closedDummy?
              let sname := symReqName sreq
              stats := stats.record sname out
              loopSteps := loopSteps + 1
              trace := trace.push { allocId, req := sreq }
              match opened, allocId with
              | some (hid, rfd), some sid =>
                rawMap := rawMap.insert hid rfd
                openRfds := openRfds.insert hid rfd
                env := { env with allFds := env.allFds.push (sid, hid), openFds := env.openFds.push (sid, hid) }
              | none, _ => pure ()
              | _, _ => pure ()
              match sreq, out with
              | .close sid, .unit =>
                match symToHid env sid with
                | some hid => openRfds := openRfds.erase hid
                | none => pure ()
                env := { env with openFds := env.openFds.filter (fun p => p.1 != sid), procFdMap := env.procFdMap.erase sid }
              | _, _ => pure ()
              let nextState? := if statOutcomeNsecValid out then allowedStep modelState req out else none
              match nextState? with
              | some s' =>
                let mut sNext := s'
                if let (some (hid, rfd), some sid) := (opened, allocId) then
                  let (sL, rawN?) ← attachOpenedProcFd ops sNext hid rfd (reqAccessOf effSreq)
                  sNext := sL
                  if let some rn := rawN? then
                    hidToRawName := hidToRawName.insert hid (toString rn).toUTF8
                    env := { env with procFdMap := env.procFdMap.insert sid rn }
                if let .close hid := req then
                  if !(sNext.fds.any fun p => p.1 == hid) then
                    if let some fn := hidToRawName.get? hid then
                      sNext := sNext.detachProcFdLink fn
                      hidToRawName := hidToRawName.erase hid
                modelState := sNext
              | none =>
                if !chrootMode then
                  if rlimitNofile?.isSome then
                    let _ ← Env.setRlimitNofile savedNofileCur savedNofileMax
                  let _ ← Env.setRlimitFsize savedFsizeCur savedFsizeMax false
                  let cleanupRfds := openRfds.toList.map (·.2) |>.toArray
                  cleanupEpisodeDir ops cleanupRfds savedCwd epDir crossCleanup? isRoSeeded
                  let shrinkCross? := crossRoot?.map (· / "shrink")
                  let preSeeded := if hasMemfd then 1 else 0
                  let shrunk ← shrinkTrace trace (fun cand => do
                    let shrinkDir ← if isRoSeeded then pure rootDir else nextShrinkDir
                    let r ← replayTrace shrinkDir cand allowedStep shrinkCross?
                      (fun d cd? => do
                        let (rcfg, _, _) ← materializeEpisode ops d cd? false in0 out1 err2 recipe
                          isRoSeeded false seccompMode unlinkedCwdMode chrootOuterEntries
                        return rcfg)
                      (if unlinkedCwdMode then unlinkSeededCwd else id)
                      recipe.fsizeLimit?
                      hasMemfd
                      (pure ())
                      rlimitNofile?
                      isRoSeeded
                    return r.mismatchIdx.isSome) preSeeded
                  throw (IO.userError
                    s!"model/kernel mismatch at ep={epIdx} step={stepIdx} (global={stats.totalSteps}): req={repr req} out={repr out}\nminimal trace ({shrunk.size} steps): {repr shrunk}")
                else
                  let pathDetail := match req with
                    | .openat _ p _ _ => s!" path={repr p.data.toList} ({String.fromUTF8? p |>.getD "<bin>"})"
                    | .openat2 _ p _ => s!" path={repr p.data.toList} ({String.fromUTF8? p |>.getD "<bin>"})"
                    | .fstatat _ p _ => s!" path={repr p.data.toList} ({String.fromUTF8? p |>.getD "<bin>"})"
                    | .faccessat _ p _ _ => s!" path={repr p.data.toList} ({String.fromUTF8? p |>.getD "<bin>"})"
                    | .mkdirat _ p _ => s!" path={repr p.data.toList} ({String.fromUTF8? p |>.getD "<bin>"})"
                    | .unlinkat _ p _ => s!" path={repr p.data.toList} ({String.fromUTF8? p |>.getD "<bin>"})"
                    | .renameat2 _ o _ n _ => s!" old={String.fromUTF8? o |>.getD "<bin>"} new={String.fromUTF8? n |>.getD "<bin>"}"
                    | .readlinkat _ p _ => s!" path={repr p.data.toList} ({String.fromUTF8? p |>.getD "<bin>"})"
                    | _ => ""
                  throw (IO.userError
                    s!"model/kernel mismatch (ro={isRoSeeded} chroot={chrootMode}) at ep={epIdx} step={stepIdx} (global={stats.totalSteps}): req={repr req}{pathDetail} out={repr out}\ntrace ({trace.size} steps): {repr trace}")
          stats := { stats with totalEpisodes := stats.totalEpisodes + 1 }
      finally
        if rlimitNofile?.isSome then
          let _ ← Env.setRlimitNofile savedNofileCur savedNofileMax
        let _ ← Env.setRlimitFsize savedFsizeCur savedFsizeMax false
        let cleanupRfds := openRfds.toList.map (·.2) |>.toArray
        if isRoSeeded then
          for rfd in cleanupRfds do let _ ← ops.close rfd
          let _ ← Env.chmod epDir.toString.toUTF8 0o755
          IO.Process.setCurrentDir savedCwd
        else if chrootMode then
          for rfd in cleanupRfds do let _ ← ops.close rfd
          if let some efd := epFd? then
            let _ ← ops.fchmod efd 0o755
            let _ ← ops.close efd
          if let some ofd := outsideFd? then
            let _ ← ops.fchmod ofd 0o755
            let _ ← Env.fchdir ofd
          else
            let _ ← Env.chmod ".".toUTF8 0o755
            let _ ← Env.chmod "..".toUTF8 0o755
            IO.Process.setCurrentDir (System.FilePath.mk "..")
          let _ ← Env.chmod ".".toUTF8 0o755
          removeDirForced epDir
        else
          cleanupEpisodeDir ops cleanupRfds savedCwd epDir crossCleanup?
      restoreStdioState defaultOps savedStdio
      epIdx := epIdx + 1
    let endNs ← IO.monoNanosNow
    let elapsedMs := (endNs - startNs) / 1000000
    let sps := (stats.totalSteps * 1000) / max 1 elapsedMs
    return {
      totalSteps := stats.totalSteps
      totalEpisodes := stats.totalEpisodes
      elapsedMs
      syscallsPerSec := sps
      stats
      realStats := if seccompMode then {} else stats
      shrinkSelfTestDetail := shrinkDetail
    }
  finally
    if rlimitNofile?.isSome then
      let _ ← Env.setRlimitNofile savedNofileCur savedNofileMax
    restoreStdioState defaultOps savedStdio
    if let some ofd := outsideFd? then
      let _ ← defaultOps.close ofd
    let _ ← Env.setRlimitFsize savedFsizeCur savedFsizeMax false
    let _ ← Env.umask savedUmask
    if !chrootMode then
      IO.Process.setCurrentDir savedCwd
    if !isRoSeeded && !chrootMode && !isPreseededUnlinked && !isPreseededLower && !isPreseededRwSticky then
      removeDirForced rootDir
    if crossOverride?.isNone then
      if let some cr := crossRoot? then
        removeDirForced cr

private def runWorkerSubprocess (cmd : String) (args : Array String) (label : String) : IO HitStats := do
  let out ← IO.Process.output { cmd, args, stdin := .null }
  if out.exitCode != 0 then
    throw (IO.userError s!"fuzz worker '{label}' failed (exit={out.exitCode}):\n{out.stdout}\n{out.stderr}")
  return parseWorkerStats out.stdout

private def runMultiFsSuite (totalSteps : Nat) (seed : UInt64) (selfTestShrink : Bool)
    (baseDir : System.FilePath) (requireNs : Bool := false) : IO FuzzReport := do
  let startNs ← IO.monoNanosNow
  let exe ← IO.appPath
  let probeUserns ← IO.Process.output {
    cmd := "sh"
    args := #["-c", "command -v capsh >/dev/null 2>&1 && unshare -Urm true"]
  }
  let hasUserns := probeUserns.exitCode == 0
  if requireNs && !hasUserns then
    throw (IO.userError s!"--require-ns failed: capsh or unshare -Urm unavailable (exit={probeUserns.exitCode}): {probeUserns.stderr}")
  let probeAsym ← IO.Process.output {
    cmd := "sh"
    args := #["-c", "ME=$(id -un); command -v newuidmap >/dev/null 2>&1 && command -v newgidmap >/dev/null 2>&1 && grep -q \"^$ME:\" /etc/subuid 2>/dev/null && grep -q \"^$ME:\" /etc/subgid 2>/dev/null"]
  }
  let hasAsymUserns := probeAsym.exitCode == 0
  if requireNs && totalSteps >= 2000 && !hasAsymUserns then
    throw (IO.userError "--require-ns failed: newuidmap/newgidmap or /etc/subuid+/etc/subgid entry missing for current user")
  let hasVarTmp ← (System.FilePath.mk "/var/tmp").pathExists
  let unlinkedSteps := if totalSteps >= 2000 then (totalSteps * 5) / 100 else 0
  let seccompSteps := if totalSteps >= 2000 then (totalSteps * 5) / 100 else 0
  let closedStdinSteps := if totalSteps >= 2000 then max 200 (totalSteps / 30) else 0
  let rlimitNofile3Steps := if totalSteps >= 2000 then max 200 (totalSteps / 50) else 0
  let rlimitNofile4Steps := if totalSteps >= 2000 then max 250 (totalSteps / 50) else 0
  let shmSteps :=
    if totalSteps < 2000 then totalSteps
    else if hasUserns then (totalSteps * 25) / 100
    else if hasVarTmp then (totalSteps * 50) / 100
    else totalSteps - unlinkedSteps - seccompSteps - closedStdinSteps - rlimitNofile3Steps - rlimitNofile4Steps
  let shmRep ← runFilesFuzzOnDir shmSteps seed selfTestShrink baseDir
  let mut aggStats := shmRep.stats
  let mut realStats := shmRep.realStats
  let mut envSummary : Array String := #[s!"shm={shmSteps}"]

  let mut usedSteps := shmSteps
  let assertArr := fun (n : Nat) => if n >= 2000 then #["--assert-worker-hits"] else #[]
  let assertFlag := fun (n : Nat) => if n >= 2000 then " --assert-worker-hits" else ""
  if totalSteps >= 2000 && hasVarTmp then
    let varTmpSteps :=
      if hasUserns then (totalSteps * 15) / 100
      else totalSteps - usedSteps - unlinkedSteps - seccompSteps - closedStdinSteps - rlimitNofile3Steps - rlimitNofile4Steps
    if varTmpSteps > 0 then
      usedSteps := usedSteps + varTmpSteps
      let varScript :=
        "set -e; " ++
        "F=$(mktemp /var/tmp/lswf-stdin.XXXXXX); " ++
        "trap 'rm -f \"$F\"' EXIT; " ++
        "printf 'stdin-reg\\n' > \"$F\"; chmod 0444 \"$F\"; " ++
        s!"\"$1\" --worker-mode rw --dir /var/tmp --steps \"$2\" --seed \"$3\"{assertFlag varTmpSteps} < \"$F\""
      let varStats ← runWorkerSubprocess "sh"
        #["-c", varScript, "_", exe.toString, toString varTmpSteps, toString (seed + 101)]
        "var_tmp_reg_stdin"
      aggStats := HitStats.merge aggStats varStats
      realStats := HitStats.merge realStats varStats
      envSummary := envSummary.push s!"var_tmp={varTmpSteps}"

  if closedStdinSteps > 0 then
    usedSteps := usedSteps + closedStdinSteps
    let st ← runWorkerSubprocess exe.toString
      (#["--worker-mode", "rw", "--close-fd0", "--dir", baseDir.toString,
        "--steps", toString closedStdinSteps, "--seed", toString (seed + 909)] ++ assertArr closedStdinSteps)
      "closed_stdin"
    if st.kindCounts.getD "dupStdio:badFd" 0 == 0 then
      throw (IO.userError "closed_stdin worker recorded 0 dupStdio:badFd hits")
    aggStats := HitStats.merge aggStats st
    realStats := HitStats.merge realStats st
    envSummary := envSummary.push s!"closed_stdin={closedStdinSteps}"

  if rlimitNofile3Steps > 0 then
    usedSteps := usedSteps + rlimitNofile3Steps
    let st ← runWorkerSubprocess exe.toString
      #["--worker-mode", "rw", "--rlimit-nofile", "3", "--dir", baseDir.toString,
        "--steps", toString rlimitNofile3Steps, "--seed", toString (seed + 919),
        "--assert-worker-hits"]
      "rlimit_nofile3"
    aggStats := HitStats.merge aggStats st
    realStats := HitStats.merge realStats st
    envSummary := envSummary.push s!"rlimit_nofile3={rlimitNofile3Steps}"

  if rlimitNofile4Steps > 0 then
    usedSteps := usedSteps + rlimitNofile4Steps
    let st ← runWorkerSubprocess exe.toString
      #["--worker-mode", "rw", "--rlimit-nofile", "4", "--dir", baseDir.toString,
        "--steps", toString rlimitNofile4Steps, "--seed", toString (seed + 929),
        "--assert-worker-hits"]
      "rlimit_nofile4"
    aggStats := HitStats.merge aggStats st
    realStats := HitStats.merge realStats st
    envSummary := envSummary.push s!"rlimit_nofile4={rlimitNofile4Steps}"

  if unlinkedSteps > 0 then
    usedSteps := usedSteps + unlinkedSteps
    let st ← runWorkerSubprocess exe.toString
      (#["--worker-mode", "unlinked_cwd", "--dir", baseDir.toString,
        "--steps", toString unlinkedSteps, "--seed", toString (seed + 707)] ++ assertArr unlinkedSteps)
      "unlinked_cwd"
    aggStats := HitStats.merge aggStats st
    realStats := HitStats.merge realStats st
    envSummary := envSummary.push s!"unlinked_cwd={unlinkedSteps}"

  if seccompSteps > 0 then
    usedSteps := usedSteps + seccompSteps
    let st ← runWorkerSubprocess exe.toString
      (#["--worker-mode", "seccomp", "--dir", baseDir.toString,
        "--steps", toString seccompSteps, "--seed", toString (seed + 808)] ++ assertArr seccompSteps)
      "seccomp"
    aggStats := HitStats.merge aggStats st
    envSummary := envSummary.push s!"seccomp={seccompSteps}"

  if totalSteps >= 2000 && hasUserns then
    let rem := totalSteps - usedSteps
    let perWorker := rem / 12
    let ovlSteps := perWorker * 2
    let unmapSteps := perWorker
    let lastWorker := rem - perWorker * 11
    let dropCaps := "cap_dac_override,cap_dac_read_search,cap_fowner,cap_fsetid"

    let runNs := fun (label : String) (stepsN : Nat) (sOffset : UInt64) (body : String) => do
      if stepsN == 0 then return (none : Option HitStats)
      let script :=
        "set -e; " ++
        "T=$(mktemp -d /tmp/lswf-ns.XXXXXX); " ++
        "trap 'for m in \"$T/ro/s1777/u65534\" \"$T/mnt\" \"$T/ro\" \"$T/mnt_a\" \"$T/mnt_b\" \"$T/root/proc\" \"$T/root/dev\" \"$T/base\" \"$T/m\"; do umount -l \"$m\" 2>/dev/null || true; done; rm -rf \"$T\"' EXIT; " ++
        body
      let st ← runWorkerSubprocess "unshare"
        #["-Urm", "sh", "-c", script, "_", exe.toString, toString stepsN, toString (seed + sOffset)]
        label
      return some st

    if let some st ← runNs "ns_tmpfs" perWorker 202 (
      "mkdir -p \"$T/m\"; mount -t tmpfs tmpfs \"$T/m\"; " ++
      s!"capsh --drop={dropCaps} -- -c '\"$1\" --worker-mode rw --host-protected --dir \"$2\" --steps \"$3\" --seed \"$4\"{assertFlag perWorker} < /dev/null' _ \"$1\" \"$T/m\" \"$2\" \"$3\""
    ) then
      aggStats := HitStats.merge aggStats st
      realStats := HitStats.merge realStats st
      envSummary := envSummary.push s!"ns_tmpfs={perWorker}"

    if let some st ← runNs "ns_caps_rw" perWorker 252 (
      "mkdir -p \"$T/m\"; mount -t tmpfs tmpfs \"$T/m\"; " ++
      s!"\"$1\" --worker-mode rw --host-protected --dir \"$T/m\" --steps \"$2\" --seed \"$3\"{assertFlag perWorker} < /dev/null"
    ) then
      aggStats := HitStats.merge aggStats st
      realStats := HitStats.merge realStats st
      envSummary := envSummary.push s!"ns_caps_rw={perWorker}"

    if let some st ← runNs "ns_caps_ro_bind" perWorker 277 (
      "mkdir -p \"$T/ro_src\" \"$T/ro\"; " ++
      "\"$1\" --seed-ro-tree \"$T/ro_src\"; " ++
      ": > \"$T/ro_src/s1777/u65534\"; " ++
      "mount --bind \"$T/ro_src\" \"$T/ro\"; mount -o remount,ro,bind \"$T/ro\"; " ++
      "mount --bind /etc/passwd \"$T/ro/s1777/u65534\"; mount -o remount,ro,bind \"$T/ro/s1777/u65534\"; " ++
      s!"\"$1\" --worker-mode ro_bind --host-protected --dir \"$T/ro\" --steps \"$2\" --seed \"$3\"{assertFlag perWorker} < /dev/null"
    ) then
      aggStats := HitStats.merge aggStats st
      realStats := HitStats.merge realStats st
      envSummary := envSummary.push s!"ns_caps_ro_bind={perWorker}"

    let ovlLowerCount := max 8 (ovlSteps / 40 + 4)
    if let some st ← runNs "ns_overlayfs" ovlSteps 303 (
      "mkdir -p \"$T/low\" \"$T/up\" \"$T/wk\" \"$T/mnt\" \"$T/x\"; " ++
      s!"\"$1\" --seed-overlay-lower \"$T/low\" {ovlLowerCount}; " ++
      "if mount -t overlay overlay -o \"lowerdir=$T/low,upperdir=$T/up,workdir=$T/wk,userxattr\" \"$T/mnt\" 2>/dev/null; then true; " ++
      "elif command -v fuse-overlayfs >/dev/null 2>&1; then fuse-overlayfs -o \"lowerdir=$T/low,upperdir=$T/up,workdir=$T/wk\" \"$T/mnt\"; " ++
      "else echo 'ns_overlayfs: neither overlay mount nor fuse-overlayfs succeeded' >&2; exit 1; fi; " ++
      s!"capsh --drop={dropCaps} -- -c '\"$1\" --worker-mode rw --host-protected --preseeded-eps --dir \"$2\" --cross-dir \"$3\" --steps \"$4\" --seed \"$5\"{assertFlag ovlSteps} < /dev/null' _ \"$1\" \"$T/mnt\" \"$T/x\" \"$2\" \"$3\""
    ) then
      aggStats := HitStats.merge aggStats st
      realStats := HitStats.merge realStats st
      envSummary := envSummary.push s!"ns_overlayfs={ovlSteps}"

    if let some st ← runNs "ns_ro_bind" perWorker 404 (
      "mkdir -p \"$T/ro_src\" \"$T/ro\"; " ++
      "\"$1\" --seed-ro-tree \"$T/ro_src\"; " ++
      "mount --bind \"$T/ro_src\" \"$T/ro\"; mount -o remount,ro,bind \"$T/ro\"; " ++
      s!"capsh --drop={dropCaps} -- -c '\"$1\" --worker-mode ro_bind --host-protected --dir \"$2\" --steps \"$3\" --seed \"$4\"{assertFlag perWorker} < /dev/null' _ \"$1\" \"$T/ro\" \"$2\" \"$3\""
    ) then
      aggStats := HitStats.merge aggStats st
      realStats := HitStats.merge realStats st
      envSummary := envSummary.push s!"ns_ro_bind={perWorker}"

    if let some st ← runNs "ns_same_dev_bind" perWorker 505 (
      "mkdir -p \"$T/base\" \"$T/mnt_a\" \"$T/mnt_b\"; " ++
      "mount -t tmpfs tmpfs \"$T/base\"; " ++
      "mkdir -p \"$T/base/a\" \"$T/base/b\"; " ++
      "mount --bind \"$T/base/a\" \"$T/mnt_a\"; mount --bind \"$T/base/b\" \"$T/mnt_b\"; " ++
      s!"capsh --drop={dropCaps} -- -c '\"$1\" --worker-mode rw --host-protected --dir \"$2\" --cross-dir \"$3\" --steps \"$4\" --seed \"$5\"{assertFlag perWorker} < /dev/null' _ \"$1\" \"$T/mnt_a\" \"$T/mnt_b\" \"$2\" \"$3\""
    ) then
      aggStats := HitStats.merge aggStats st
      realStats := HitStats.merge realStats st
      envSummary := envSummary.push s!"ns_same_dev_bind={perWorker}"

    if let some st ← runNs "ns_chroot" perWorker 606 (
      "mkdir -p \"$T/root/dev\" \"$T/root/proc\" \"$T/root/etc\" \"$T/root/sys/kernel/debug\" \"$T/outside\"; " ++
      "mount --rbind /dev \"$T/root/dev\"; mount --rbind /proc \"$T/root/proc\"; " ++
      "cp /etc/passwd \"$T/root/etc/passwd\"; " ++
      "printf 'little\\n' > \"$T/root/sys/kernel/cpu_byteorder\"; chmod 0444 \"$T/root/sys/kernel/cpu_byteorder\"; chmod 0700 \"$T/root/sys/kernel/debug\"; " ++
      s!"capsh --drop={dropCaps} -- -c '\"$1\" --worker-mode chroot --host-protected --dir \"$2\" --chroot-dir \"$3\" --steps \"$4\" --seed \"$5\"{assertFlag perWorker} < /dev/null' _ \"$1\" \"$T/outside\" \"$T/root\" \"$2\" \"$3\""
    ) then
      aggStats := HitStats.merge aggStats st
      realStats := HitStats.merge realStats st
      envSummary := envSummary.push s!"ns_chroot={perWorker}"

    let ovlUnlinkedEpCount := perWorker / 40 + 4
    if let some st ← runNs "ns_overlay_unlinked" perWorker 656 (
      "mkdir -p \"$T/low/shrink\" \"$T/up\" \"$T/wk\" \"$T/mnt\" \"$T/x\"; " ++
      s!"i=0; while [ \"$i\" -lt {ovlUnlinkedEpCount} ]; do mkdir -p \"$T/low/ep-$i\"; i=$((i+1)); done; " ++
      "j=0; while [ \"$j\" -lt 512 ]; do mkdir -p \"$T/low/shrink-$j\"; j=$((j+1)); done; " ++
      ": > \"$T/low/.ovl_unlinked\"; " ++
      "if mount -t overlay overlay -o \"lowerdir=$T/low,upperdir=$T/up,workdir=$T/wk,userxattr\" \"$T/mnt\" 2>/dev/null; then true; " ++
      "elif command -v fuse-overlayfs >/dev/null 2>&1; then fuse-overlayfs -o \"lowerdir=$T/low,upperdir=$T/up,workdir=$T/wk\" \"$T/mnt\"; " ++
      "else echo 'ns_overlay_unlinked: neither overlay mount nor fuse-overlayfs succeeded' >&2; exit 1; fi; " ++
      s!"capsh --drop={dropCaps} -- -c '\"$1\" --worker-mode unlinked_cwd --host-protected --preseeded-eps --dir \"$2\" --cross-dir \"$3\" --steps \"$4\" --seed \"$5\"{assertFlag perWorker} < /dev/null' _ \"$1\" \"$T/mnt\" \"$T/x\" \"$2\" \"$3\""
    ) then
      aggStats := HitStats.merge aggStats st
      realStats := HitStats.merge realStats st
      envSummary := envSummary.push s!"ns_overlay_unlinked={perWorker}"

    if perWorker > 0 then
      let pidChildSteps := perWorker / 2
      let pidOneSteps := perWorker - pidChildSteps
      let pidScript :=
        "set -e; T=$(mktemp -d /tmp/lswf-pidns.XXXXXX); trap 'rm -rf \"$T\"' EXIT; " ++
        "mkdir -p \"$T/m\" \"$T/pid1_cwd\"; " ++
        "printf 'pid1-in\\n' > \"$T/f1\"; printf 'proc-in\\n' > \"$T/f2\"; chmod 0444 \"$T/f1\" \"$T/f2\"; " ++
        "if [ \"$2\" -gt 0 ]; then " ++
          "unshare -Urmpf --mount-proc sh -c " ++
            "'mount -t tmpfs tmpfs \"$3\"; cd \"$1\"; shift; \"$1\" --worker-mode rw --host-protected --dir \"$2\" --steps \"$3\" --seed \"$4\"" ++
            assertFlag pidChildSteps ++ " < \"$5\"' " ++
            "_ \"$T/pid1_cwd\" \"$1\" \"$T/m\" \"$2\" \"$3\" \"$T/f2\" < \"$T/f1\"; " ++
        "fi; " ++
        "if [ \"$4\" -gt 0 ]; then " ++
          "unshare -Urmpf --mount-proc sh -c " ++
            "'mount -t tmpfs tmpfs \"$2\"; exec \"$1\" --worker-mode rw --host-protected --dir \"$2\" --steps \"$3\" --seed \"$4\"" ++
            assertFlag pidOneSteps ++ " < \"$5\"' " ++
            "_ \"$1\" \"$T/m\" \"$4\" \"$5\" \"$T/f2\"; " ++
        "fi"
      let st ← runWorkerSubprocess "sh"
        #["-c", pidScript, "_", exe.toString, toString pidChildSteps, toString (seed + 686), toString pidOneSteps, toString (seed + 687)]
        "ns_pidns"
      aggStats := HitStats.merge aggStats st
      realStats := HitStats.merge realStats st
      envSummary := envSummary.push s!"ns_pidns={perWorker}"

    if unmapSteps > 0 then
      let umHalf := max 1 (unmapSteps / 2)
      let umRest := unmapSteps - umHalf
      let unmapScript :=
        "set -e; T=$(mktemp -d /tmp/lswf-unmap.XXXXXX); trap 'rm -rf \"$T\"' EXIT; " ++
        "mkdir -p \"$T/um\" \"$T/u\"; chmod 0755 \"$T/u\"; " ++
        "unshare --user --map-user=0 --mount sh -c " ++
          "'mount -t tmpfs tmpfs \"$2\" && \"$1\" --worker-mode ro_bind --host-protected --dir \"$2\" --steps \"$3\" --seed \"$4\" < /dev/null' " ++
          "_ \"$1\" \"$T/um\" \"$2\" \"$3\"; " ++
        "if [ \"$4\" -gt 0 ]; then " ++
          "unshare -U \"$1\" --worker-mode rw --host-protected --dir \"$T/u\" --steps \"$4\" --seed \"$5\" < /dev/null; " ++
        "fi"
      let st ← runWorkerSubprocess "sh"
        #["-c", unmapScript, "_", exe.toString, toString umHalf, toString (seed + 709), toString umRest, toString (seed + 710)]
        "ns_unmapped"
      aggStats := HitStats.merge aggStats st
      realStats := HitStats.merge realStats st
      envSummary := envSummary.push s!"ns_unmapped={unmapSteps}"

    if lastWorker > 0 then
      if hasAsymUserns then
        let asymHalf := lastWorker / 2
        let asymRwSteps := lastWorker - asymHalf
        let asymEpCount := asymRwSteps / 40 + 4
        let asymScript :=
          "set -e; " ++
          "T=$(mktemp -d /tmp/lswf-asym.XXXXXX); " ++
          "ME=$(id -un); MYU=$(id -u); MYG=$(id -g); " ++
          "SU=$(awk -F: -v u=\"$ME\" '$1==u{print $2; exit}' /etc/subuid 2>/dev/null || true); " ++
          "SG=$(awk -F: -v u=\"$ME\" '$1==u{print $2; exit}' /etc/subgid 2>/dev/null || true); " ++
          "mkfifo \"$T/sync\" \"$T/sync2\" \"$T/sync3\"; " ++
          "cleanup_asym() { " ++
            "unshare -U sh -c 'read _ < \"$1\"; chmod -R u+rwX \"$2\" \"$3\" \"$4\" 2>/dev/null || true; rm -rf \"$2\" \"$3\" \"$4\"' _ \"$T/sync3\" \"$T/asym\" \"$T/asym_rw\" \"$T/asym_stdin\" 2>/dev/null & " ++
            "CP3=$!; " ++
            "while ! newuidmap \"$CP3\" 0 \"$MYU\" 1 1 \"$SU\" 3 2>/dev/null; do kill -0 \"$CP3\" 2>/dev/null || break; done; " ++
            "if kill -0 \"$CP3\" 2>/dev/null; then newgidmap \"$CP3\" 0 \"$MYG\" 1 1 \"$SG\" 3 2>/dev/null || true; echo go > \"$T/sync3\" 2>/dev/null || true; fi; " ++
            "wait \"$CP3\" 2>/dev/null || true; rm -rf \"$T\"; " ++
          "}; trap cleanup_asym EXIT; " ++
          "mkdir -p \"$T/asym\" \"$T/ro_asym\" \"$T/asym_rw\"; \"$1\" --seed-ro-tree \"$T/asym\"; " ++
          "printf 'asym\\n' > \"$T/asym/r_nogid\"; printf 'asym\\n' > \"$T/asym/r_nouid\"; " ++
          "printf 'asym-stdin\\n' > \"$T/asym_stdin\"; " ++
          "unshare -U sh -c 'read _ < \"$1\"; python3 - \"$2\" \"$3\" \"$4\" \"$5\" << \"PY\"\n" ++
          "import os, socket, sys\n" ++
          "asym, rw, n_eps, sinp = sys.argv[1], sys.argv[2], int(sys.argv[3]), sys.argv[4]\n" ++
          "def seed_sticky(s):\n" ++
          "    os.makedirs(s, exist_ok=True)\n" ++
          "    with open(f\"{s}/reg666\", \"w\") as f: f.write(\"sticky\\n\")\n" ++
          "    os.chown(f\"{s}/reg666\", 1, 1); os.chmod(f\"{s}/reg666\", 0o666)\n" ++
          "    if not os.path.exists(f\"{s}/fifo666\"):\n" ++
          "        os.mkfifo(f\"{s}/fifo666\")\n" ++
          "    os.chown(f\"{s}/fifo666\", 1, 1); os.chmod(f\"{s}/fifo666\", 0o666)\n" ++
          "    if not os.path.lexists(f\"{s}/sym_other\"):\n" ++
          "        os.symlink(\"../sub/a\", f\"{s}/sym_other\")\n" ++
          "    os.lchown(f\"{s}/sym_other\", 1, 1)\n" ++
          "    if not os.path.exists(f\"{s}/sock666\"):\n" ++
          "        sk = socket.socket(socket.AF_UNIX, socket.SOCK_STREAM)\n" ++
          "        prev = os.getcwd(); os.chdir(s); sk.bind(\"sock666\"); os.chdir(prev); sk.close()\n" ++
          "    os.chown(f\"{s}/sock666\", 1, 1); os.chmod(f\"{s}/sock666\", 0o666)\n" ++
          "    for fn, md, gid in [(\"f640\", 0o640, 0), (\"f604\", 0o604, 0), (\"g640\", 0o640, 1), (\"g604\", 0o604, 1)]:\n" ++
          "        with open(f\"{s}/{fn}\", \"w\") as f: f.write(\"sticky\\n\")\n" ++
          "        os.chown(f\"{s}/{fn}\", 1, gid); os.chmod(f\"{s}/{fn}\", md)\n" ++
          "    os.chown(s, 2, 2); os.chmod(s, 0o1777)\n" ++
          "def seed_unmap(s):\n" ++
          "    os.makedirs(s, exist_ok=True)\n" ++
          "    with open(f\"{s}/reg666\", \"w\") as f: f.write(\"sticky\\n\")\n" ++
          "    os.chown(f\"{s}/reg666\", 3, 3); os.chmod(f\"{s}/reg666\", 0o666)\n" ++
          "    if not os.path.exists(f\"{s}/fifo666\"):\n" ++
          "        os.mkfifo(f\"{s}/fifo666\")\n" ++
          "    os.chown(f\"{s}/fifo666\", 3, 3); os.chmod(f\"{s}/fifo666\", 0o666)\n" ++
          "    if not os.path.lexists(f\"{s}/sym_other\"):\n" ++
          "        os.symlink(\"../sub/a\", f\"{s}/sym_other\")\n" ++
          "    os.lchown(f\"{s}/sym_other\", 3, 3)\n" ++
          "    if not os.path.exists(f\"{s}/sock666\"):\n" ++
          "        sk = socket.socket(socket.AF_UNIX, socket.SOCK_STREAM)\n" ++
          "        prev = os.getcwd(); os.chdir(s); sk.bind(\"sock666\"); os.chdir(prev); sk.close()\n" ++
          "    os.chown(f\"{s}/sock666\", 3, 3); os.chmod(f\"{s}/sock666\", 0o666)\n" ++
          "    os.chown(s, 2, 2); os.chmod(s, 0o1777)\n" ++
          "os.chown(sinp, 1, 1); os.chmod(sinp, 0o640)\n" ++
          "os.chown(f\"{asym}/r_nogid\", 1, 1); os.chmod(f\"{asym}/r_nogid\", 0)\n" ++
          "os.chown(f\"{asym}/r_nouid\", 2, 0); os.chmod(f\"{asym}/r_nouid\", 0)\n" ++
          "seed_sticky(f\"{asym}/s1777\"); seed_unmap(f\"{asym}/s_unmap\")\n" ++
          "os.makedirs(f\"{asym}/gd\", exist_ok=True); os.chown(f\"{asym}/gd\", 0, 1); os.chmod(f\"{asym}/gd\", 0o2755)\n" ++
          "with open(f\"{asym}/gd/sgid2640\", \"w\") as f: f.write(\"sgid\\n\")\n" ++
          "os.chown(f\"{asym}/gd/sgid2640\", 0, 1); os.chmod(f\"{asym}/gd/sgid2640\", 0o2640)\n" ++
          "dirs = [f\"{rw}/ep-{i}\" for i in range(n_eps)] + [f\"{rw}/shrink-{i}\" for i in range(512)] + [f\"{rw}/parity-sym\"]\n" ++
          "for d in dirs:\n" ++
          "    seed_sticky(f\"{d}/s1777\"); seed_unmap(f\"{d}/s_unmap\")\n" ++
          "    os.makedirs(f\"{d}/gd\", exist_ok=True); os.chown(f\"{d}/gd\", 0, 1); os.chmod(f\"{d}/gd\", 0o2755)\n" ++
          "    with open(f\"{d}/gd/sgid2640\", \"w\") as f: f.write(\"sgid\\n\")\n" ++
          "    os.chown(f\"{d}/gd/sgid2640\", 0, 1); os.chmod(f\"{d}/gd/sgid2640\", 0o2640)\n" ++
          "PY\n' _ \"$T/sync\" \"$T/asym\" \"$T/asym_rw\" " ++ toString asymEpCount ++ " \"$T/asym_stdin\" & " ++
          "CP=$!; " ++
          "while ! newuidmap \"$CP\" 0 \"$MYU\" 1 1 \"$SU\" 3 2>/dev/null; do kill -0 \"$CP\" 2>/dev/null || break; done; " ++
          "newgidmap \"$CP\" 0 \"$MYG\" 1 1 \"$SG\" 3; " ++
          "echo go > \"$T/sync\"; wait \"$CP\"; " ++
          "cat <<'CP2SH' > \"$T/cp2.sh\"\n" ++
          "set -e\n" ++
          "mount --bind \"$3\" \"$2\"\n" ++
          "mount -o remount,ro,bind \"$2\"\n" ++
          "RO_S=$(( $4 / 2 )); RW_S=$(( $4 - RO_S ))\n" ++
          s!"\"$1\" --worker-mode ro_bind --host-protected --dir \"$2\" --steps \"$RO_S\" --seed \"$5\"{assertFlag asymHalf} < /dev/null\n" ++
          s!"capsh --drop={dropCaps} -- -c '\"$1\" --worker-mode rw --host-protected --preseeded-eps --dir \"$2\" --steps \"$3\" --seed \"$4\"{assertFlag asymRwSteps}' _ \"$1\" \"$6\" \"$RW_S\" \"$7\" < \"$8\"\n" ++
          "CP2SH\n" ++
          "unshare -Um sh -c 'read _ < \"$1\"; shift; exec sh \"$@\"' " ++
            "_ \"$T/sync2\" \"$T/cp2.sh\" \"$1\" \"$T/ro_asym\" \"$T/asym\" \"$2\" \"$3\" \"$T/asym_rw\" \"$4\" \"$T/asym_stdin\" & " ++
          "CP2=$!; " ++
          "while ! newuidmap \"$CP2\" 0 \"$MYU\" 1 1 \"$SU\" 1 2>/dev/null; do kill -0 \"$CP2\" 2>/dev/null || break; done; " ++
          "newgidmap \"$CP2\" 0 \"$MYG\" 1 1 \"$SG\" 1; " ++
          "echo go > \"$T/sync2\"; wait \"$CP2\""
        let st ← runWorkerSubprocess "sh"
          #["-c", asymScript, "_", exe.toString, toString lastWorker, toString (seed + 717), toString (seed + 718)]
          "ns_asym_userns"
        aggStats := HitStats.merge aggStats st
        realStats := HitStats.merge realStats st
        envSummary := envSummary.push s!"ns_asym_userns={lastWorker}"
      else
        if let some st ← runNs "ns_userns_single" lastWorker 717 (
          "mkdir -p \"$T/m\"; mount -t tmpfs tmpfs \"$T/m\"; " ++
          "\"$1\" --worker-mode rw --host-protected --dir \"$T/m\" --steps \"$2\" --seed \"$3\" < /dev/null"
        ) then
          aggStats := HitStats.merge aggStats st
          realStats := HitStats.merge realStats st
          envSummary := envSummary.push s!"ns_userns_single={lastWorker}"

  let endNs ← IO.monoNanosNow
  let elapsedMs := (endNs - startNs) / 1000000
  let sps := (aggStats.totalSteps * 1000) / max 1 elapsedMs
  let detail :=
    let envList := String.intercalate "," envSummary.toList
    if shmRep.shrinkSelfTestDetail.isEmpty then s!"envs=[{envList}]"
    else s!"{shmRep.shrinkSelfTestDetail}; envs=[{envList}]"
  return {
    totalSteps := aggStats.totalSteps
    totalEpisodes := aggStats.totalEpisodes
    elapsedMs
    syscallsPerSec := sps
    stats := aggStats
    realStats := realStats
    shrinkSelfTestDetail := detail
  }

/-- Run stateful randomized episodes for `totalSteps` real Linux syscalls across `baseDir` (or multi-FS rotation when `explicitDir` is `false`). -/
def runFilesFuzz (totalSteps : Nat) (seed : UInt64) (selfTestShrink : Bool)
    (baseDir : System.FilePath := "/dev/shm") (explicitDir : Bool := false)
    (requireNs : Bool := false) : IO FuzzReport := do
  Fuzz.LinuxSyscall.Files.Strace.runCShimBoundaryProbes
  if explicitDir then
    runFilesFuzzOnDir totalSteps seed selfTestShrink baseDir
  else
    runMultiFsSuite totalSteps seed selfTestShrink baseDir requireNs

end Fuzz.LinuxSyscall.FilesFuzz
