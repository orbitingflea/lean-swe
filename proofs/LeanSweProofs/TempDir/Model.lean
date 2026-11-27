import LeanSwe.EnvVars.Types
import LeanSwe.Fs.Types
import LeanSwe.TempDir.Types
import LeanSwe.Time.Types
import LeanSwe.Uuid.Types
/-!
Pure domain state-transition model and single-step refinement specification for `LeanSwe.TempDir`.
Mock capability scaffolding (`mockFs*`, `mockTime*`, `mockUuid*`, `mockEnv*`, `TempDirCaps`) lives
under `LeanSwe.TempDir.Model.Internal` so cross-package internal access checks remain enforced.
-/
namespace LeanSwe.TempDir.Model
open LeanSwe.Fs (FsApiM FsError FsErrorKind EntryKind FileStat LockMode)
open LeanSwe.Time (TimeOpsM)
open LeanSwe.Uuid (UuidApiM Uuid UuidError)
open LeanSwe.EnvVars (EnvVarsApiM EnvVarsError)
/-- Insert a path string into a sorted list using lexicographical `String` order. -/
def insertSorted (x : String) : List String → List String
  | [] => [x] | y :: ys => if x ≤ y then x :: y :: ys else y :: insertSorted x ys
/-- Sort a list of path strings into ascending lexicographical order. -/
def sortStrings : List String → List String
  | [] => [] | x :: xs => insertSorted x (sortStrings xs)
/-- Entry kind stored in the `TempDirMockState` filesystem model. -/
inductive MockNode where
  /-- Directory node. -/ | dir (modifiedSec : Int) (mode : Nat)
  /-- Regular file node. -/ | file (inode : Nat) (content : String) (modifiedSec : Int) (mode : Nat)
  /-- Symlink node. -/ | symlink (target : String) (modifiedSec : Int)
  deriving Repr, DecidableEq
/-- Pure mock state backing `TempDir` stateful specifications. -/
structure TempDirMockState where
  /-- Filesystem path-to-node association list. -/ nodes : List (String × MockNode) := [("/tmp", .dir 0 0o755)]
  /-- Active `(inode, mode)` lock entries. -/ locks : List (Nat × LockMode) := []
  /-- Next fresh inode counter. -/ nextInode : Nat := 1
  /-- Optional `TMPDIR` value. -/ tmpdir : Option String := none
  /-- Current mock epoch timestamp in seconds. -/ nowSec : Int := 0
  /-- Next deterministic UUID counter. -/ nextUuid : Nat := 1
  deriving Repr, Inhabited
/-- Strip trailing `'/'` characters from a reversed character list, keeping a lone root slash. -/
def trimTrailingSlashesRev : List Char → List Char
  | [] => [] | ['/'] => ['/'] | '/' :: rest => trimTrailingSlashesRev rest | cs => cs
/-- Normalize trailing slashes on a character list. -/
def trimSlashChars (cs : List Char) : List Char := (trimTrailingSlashesRev cs.reverse).reverse
/-- Normalize trailing slashes on a mock path. -/
def normKey (p : String) : String := String.ofList (trimSlashChars p.toList)
/-- Join two mock paths. -/
def mockJoin (a b : String) : String :=
  let na := normKey a; if na.isEmpty then b else if na == "/" then "/" ++ b else na ++ "/" ++ b
/-- Split a reversed character list at the last `'/'` separator. -/
def splitLastSlashRev : List Char → Option (List Char × List Char)
  | [] => none
  | c :: cs => if c == '/' then some (cs.reverse, []) else match splitLastSlashRev cs with | none => none | some (par, base) => some (par, base ++ [c])
/-- Split a non-root normalized path into `(parent, basename)`. -/
def splitParentChild (p : String) : Option (String × String) :=
  let np := normKey p; if np == "/" || np.isEmpty then none else match splitLastSlashRev np.toList.reverse with
    | none => none | some (parCs, baseCs) => let par := if parCs.isEmpty then "/" else String.ofList parCs; let base := String.ofList baseCs
      if base.isEmpty then none else some (par, base)
/-- Convert a `MockNode` to `FileStat`. -/
def mockNodeStat : MockNode → FileStat
  | .dir t m => { kind := .dir, byteSize := 0, mode := m, modifiedSec := t, modifiedNsec := 0, accessedSec := 0, accessedNsec := 0 }
  | .file _ c t m => { kind := .file, byteSize := c.length, mode := m, modifiedSec := t, modifiedNsec := 0, accessedSec := 0, accessedNsec := 0 }
  | .symlink _ t => { kind := .symlink, byteSize := 0, mode := 0o777, modifiedSec := t, modifiedNsec := 0, accessedSec := 0, accessedNsec := 0 }
/-- Look up the first matching normalized key in `nodes`. -/
def lookupNode (nodes : List (String × MockNode)) (p : String) : Option MockNode :=
  (nodes.find? (fun e => normKey e.1 == normKey p)).map Prod.snd
/-- Pure `lstat` evaluation. -/
def mockLstatPure (s : TempDirMockState) (p : String) : Except FsError FileStat :=
  match lookupNode s.nodes p with
  | none => .error { kind := .notFound, path := some p, message := "not found" }
  | some node => .ok (mockNodeStat node)
/-- Pure `stat` evaluation. -/
def mockStatPure (s : TempDirMockState) (p : String) : Except FsError FileStat := mockLstatPure s p
/-- Write+execute bits check. -/
def hasWx (st : FileStat) : Bool := st.kind == .dir && (st.mode / 128) % 2 == 1 && (st.mode / 64) % 2 == 1
/-- Read+execute bits check. -/
def hasRx (st : FileStat) : Bool := st.kind == .dir && (st.mode / 256) % 2 == 1 && (st.mode / 64) % 2 == 1
/-- Immediate valid child name of `dir` for `full`. -/
def mockParentChild (dir full : String) : Option String :=
  let nd := normKey dir; let nf := normKey full; let pref := if nd.isEmpty then "" else if nd == "/" then "/" else nd ++ "/"
  if pref.toList.isPrefixOf nf.toList then
    let rest := String.ofList (nf.toList.drop pref.length)
    if !rest.isEmpty && rest != "." && rest != ".." && !('/' ∈ rest.toList) && !(Char.ofNat 0 ∈ rest.toList) then some rest else none
  else none
/-- Accumulator helper deduplicating strings while preserving first occurrence. -/
def eraseDupStringsAux (seen : List String) : List String → List String
  | [] => [] | x :: xs => if x ∈ seen then eraseDupStringsAux seen xs else x :: eraseDupStringsAux (x :: seen) xs
/-- Deduplicate strings preserving first occurrence. -/
def eraseDupStrings (xs : List String) : List String := eraseDupStringsAux [] xs
/-- Check lock conflict on `(ino, m)`. -/
def mockHasConflict (locks : List (Nat × LockMode)) (ino : Nat) (m : LockMode) : Bool :=
  locks.any fun (li, lm) => li == ino && (m == .exclusive || lm == .exclusive)
/-- Remove first matching `(ino, m)` lock entry. -/
def mockRemoveFirstLock (ino : Nat) (m : LockMode) : List (Nat × LockMode) → List (Nat × LockMode)
  | [] => [] | x :: xs => if x == (ino, m) then xs else x :: mockRemoveFirstLock ino m xs
/-- Allocate fresh inode above `s.nextInode` and active locks. -/
def freshInode (s : TempDirMockState) : Nat := s.locks.foldl (fun m l => Nat.max m (l.1 + 1)) s.nextInode
/-- True iff `key` equals `prefixDir` or lies beneath it. -/
def underDir (prefixDir key : String) : Bool :=
  let np := normKey prefixDir; let nk := normKey key; nk == np || (if np == "/" then "/" else np ++ "/").toList.isPrefixOf nk.toList
/-- Deterministic mock UUIDv4 from `n`. -/
def mockUuidOfNat (n : Nat) : Uuid :=
  { bytes := ByteArray.mk #[0, 0, 0, 0, 0, 0, 0x40, 0, 0x80, 0, 0, 0, 0, 0, UInt8.ofNat ((n / 256) % 256), UInt8.ofNat (n % 256)] }
/-- Render one byte as two lowercase hexadecimal characters. -/
def mockHexByte (b : UInt8) : String :=
  let d (k : Nat) : Char := if k < 10 then Char.ofNat (48 + k) else Char.ofNat (87 + k)
  String.ofList [d (b.toNat / 16), d (b.toNat % 16)]
/-- Format mock UUID as canonical lowercase hex string. -/
def mockUuidToString (u : Uuid) : String :=
  "00000000-0000-4000-8000-00000000" ++ mockHexByte (u.bytes[14]?.getD 0) ++ mockHexByte (u.bytes[15]?.getD 0)
/-- Predicate for valid temporary directory prefix strings. -/
def specValidPrefix (dirPrefix : String) : Bool :=
  !dirPrefix.isEmpty && dirPrefix.toList.head? != some '.' && !('/' ∈ dirPrefix.toList) && !(Char.ofNat 0 ∈ dirPrefix.toList)
/-- Predicate for valid root directory path strings. -/
def specValidRoot (root : String) : Bool := !root.isEmpty && !(Char.ofNat 0 ∈ root.toList)
/-- Pure mapping from `FsError` to `TempDirError`. -/
def specMapFsError (err : FsError) : TempDirError :=
  let kind := match err.kind with
    | .invalidInput => TempDirErrorKind.invalidInput | .notFound => TempDirErrorKind.notFound
    | .alreadyExists => TempDirErrorKind.alreadyExists | .permissionDenied => TempDirErrorKind.permissionDenied
    | .notADirectory => TempDirErrorKind.notADirectory | _ => TempDirErrorKind.ioError
  { kind := kind, path := err.path, message := if err.message.isEmpty then "filesystem error" else err.message }
/-- Pure `listDir` transition on `TempDirMockState`. -/
def specListDir (s : TempDirMockState) (p : String) : Except FsError (Array String) :=
  let rp := normKey p
  match lookupNode s.nodes rp with
  | none => .error { kind := .notFound, path := some p, message := "not found" }
  | some node =>
    let st := mockNodeStat node
    if st.kind != .dir then .error { kind := .notADirectory, path := some p, message := "not dir" }
    else if !hasRx st then .error { kind := .permissionDenied, path := some p, message := "no read/exec permission" }
    else .ok (sortStrings (eraseDupStrings (s.nodes.filterMap (fun e => mockParentChild rp e.1)))).toArray
/-- Pure `mkdir` transition on `TempDirMockState`. -/
def specMkdir (s : TempDirMockState) (p : String) (existOk : Bool) : Except FsError Unit × TempDirMockState :=
  match splitParentChild p with
  | none => (.error { kind := .alreadyExists, path := some p, message := "root" }, s)
  | some (par, base) => match lookupNode s.nodes par with
    | none => (.error { kind := .notFound, path := some par, message := "parent not found" }, s)
    | some parNode =>
      let stPar := mockNodeStat parNode
      if stPar.kind != .dir then (.error { kind := .notADirectory, path := some par, message := "not a dir" }, s)
      else if !hasWx stPar then (.error { kind := .permissionDenied, path := some par, message := "no write permission" }, s)
      else let rp := mockJoin par base; match lookupNode s.nodes rp with
        | some (.dir _ _) => if existOk then (.ok (), s) else (.error { kind := .alreadyExists, path := some p, message := "exists" }, s)
        | some _ => (.error { kind := .alreadyExists, path := some p, message := "exists" }, s)
        | none => (.ok (), { s with nodes := (rp, .dir s.nowSec 0o755) :: s.nodes.filter (fun e => !underDir rp e.1) })
/-- Pure `chmod` transition on `TempDirMockState`. -/
def specChmod (s : TempDirMockState) (p : String) (mode : Nat) : Except FsError Unit × TempDirMockState :=
  let rp := normKey p
  match lookupNode s.nodes rp with
  | none => (.error { kind := .notFound, path := some p, message := "not found" }, s)
  | some _ => (.ok (), { s with nodes := s.nodes.map fun (k, n) => if normKey k == rp then
      (k, match (n : MockNode) with | .dir t _ => .dir t mode | .file i c t _ => .file i c t mode | .symlink tgt t => .symlink tgt t) else (k, n) })
/-- Pure `unlink` transition on `TempDirMockState`. -/
def specUnlink (s : TempDirMockState) (p : String) (missingOk : Bool) : Except FsError Unit × TempDirMockState :=
  let rp := normKey p
  match lookupNode s.nodes rp with
  | none => if missingOk then (.ok (), s) else (.error { kind := .notFound, path := some p, message := "not found" }, s)
  | some (.dir _ _) => (.error { kind := .isADirectory, path := some p, message := "is dir" }, s)
  | some _ => (.ok (), { s with nodes := s.nodes.filter (fun e => normKey e.1 != rp) })
/-- Pure `rmdir` transition on `TempDirMockState`. -/
def specRmdir (s : TempDirMockState) (p : String) : Except FsError Unit × TempDirMockState :=
  let rp := normKey p
  match lookupNode s.nodes rp with
  | none => (.error { kind := .notFound, path := some p, message := "not found" }, s)
  | some (.dir _ _) => (.ok (), { s with nodes := s.nodes.filter (fun e => normKey e.1 != rp) })
  | some _ => (.error { kind := .notADirectory, path := some p, message := "not dir" }, s)
/-- Pure `rmtree` transition on `TempDirMockState`. -/
def specRmtree (s : TempDirMockState) (p : String) (ignoreMissing : Bool) : Except FsError Unit × TempDirMockState :=
  let rp := normKey p
  match lookupNode s.nodes rp with
  | none => if ignoreMissing then (.ok (), s) else (.error { kind := .notFound, path := some p, message := "not found" }, s)
  | some (.dir _ _) => (.ok (), { s with nodes := s.nodes.filter (fun e => !underDir rp e.1) })
  | some _ => (.error { kind := .notADirectory, path := some p, message := "not a dir" }, s)
/-- Pure bracketed `withFileLock` transition for a pure returning callback on `TempDirMockState`. -/
def specWithFileLockRet (s : TempDirMockState) (p : String) (mode : LockMode) (createIfMissing : Bool)
    (res : Except TempDirError String) : Except FsError (Except TempDirError String) × TempDirMockState :=
  let rp := normKey p
  match lookupNode s.nodes rp with
  | some (.dir _ _) => (.error { kind := .isADirectory, path := some p, message := "is dir" }, s)
  | some (.symlink _ _) => (.error { kind := .invalidInput, path := some p, message := "symlink" }, s)
  | some (.file ino _ _ _) =>
    if mockHasConflict s.locks ino mode then (.error { kind := .wouldBlock, path := some p, message := "wouldBlock" }, s) else (.ok res, s)
  | none =>
    if !createIfMissing then (.error { kind := .notFound, path := some p, message := "not found" }, s)
    else let ino := freshInode s; (.ok res, { s with nodes := (rp, .file ino "" s.nowSec 0o644) :: s.nodes, nextInode := ino + 1 })
/-- Pure domain root resolution inspecting `s.tmpdir` and `s.nodes`. -/
def specResolveRoot (s : TempDirMockState) (root? : Option String) : Except TempDirError String :=
  let root := match root? with
    | some r => r | none => match s.tmpdir with | some v => if v.isEmpty then "/tmp" else v | none => "/tmp"
  if !specValidRoot root then .error { kind := .invalidInput, path := some root, message := "invalid temporary root path" }
  else match lookupNode s.nodes root with
    | none => .error { kind := .notFound, path := some root, message := "not found" }
    | some (.dir _ _) => .ok root
    | some _ => .error { kind := .notADirectory, path := some root, message := "temporary root is not a directory" }
/-- Pure domain exclusive `0o700` temporary directory creation directly updating `s.nodes` and `s.nextUuid`. -/
def specCreateTempDir (s : TempDirMockState) (root? : Option String) (dirPrefix : String) :
    Except TempDirError String × TempDirMockState :=
  if !specValidPrefix dirPrefix then (.error { kind := .invalidInput, path := none, message := "invalid temporary directory prefix" }, s)
  else match specResolveRoot s root? with
    | .error te => (.error te, s)
    | .ok root =>
      let dir := mockJoin root (dirPrefix ++ mockUuidToString (mockUuidOfNat s.nextUuid))
      let s1 : TempDirMockState := { s with nextUuid := s.nextUuid + 1 }
      match lookupNode s.nodes root with
      | some (.dir _ mode) =>
        if !((mode / 128) % 2 == 1 && (mode / 64) % 2 == 1) then
          (.error { kind := .permissionDenied, path := some (normKey root), message := "no write permission" }, s1)
        else match lookupNode s.nodes dir with
          | some _ => (.error { kind := .alreadyExists, path := some dir, message := "exists" }, s1)
          | none => (.ok dir, { s1 with nodes := (dir, .dir s.nowSec 0o700) :: s.nodes.filter (fun e => !underDir dir e.1) })
      | _ => (.error { kind := .notFound, path := some root, message := "not found" }, s1)
/-- Finite pure action passed to `withTempDir` / `withLockedTempDir` during single-step refinement. -/
inductive StepAction where
  /-- Return the allocated temporary directory path. -/ | retDir
  /-- Fail inside the scoped callback with `err`. -/ | retErr (err : TempDirError)
  deriving Repr, BEq, DecidableEq, Inhabited
/-- Evaluate a `StepAction` given the allocated temporary directory path `dir`. -/
def evalStepAction (dir : String) : StepAction → Except TempDirError String
  | .retDir => .ok dir | .retErr err => .error err
/-- Pure domain transition for `withTempDir` over a finite returning `StepAction`. -/
def specWithTempDir (s : TempDirMockState) (root? : Option String) (dirPrefix : String) (act : StepAction) :
    Except TempDirError String × TempDirMockState :=
  match specCreateTempDir s root? dirPrefix with
  | (.error te, s1) => (.error te, s1)
  | (.ok dir, s1) => (evalStepAction dir act, { s1 with nodes := s.nodes.filter (fun e => !underDir dir e.1) })
/-- Pure domain transition for `withLockedTempDir` over a finite returning `StepAction`. -/
def specWithLockedTempDir (s : TempDirMockState) (root? : Option String) (dirPrefix : String) (act : StepAction) :
    Except TempDirError String × TempDirMockState :=
  match specCreateTempDir s root? dirPrefix with
  | (.error te, s1) => (.error te, s1)
  | (.ok dir, s1) => (evalStepAction dir act, { s1 with nodes := s.nodes.filter (fun e => !underDir dir e.1), nextInode := freshInode s + 1 })
/-- Pure domain removal of non-`.lock` children under `child` directly filtering `s.nodes`. -/
def specRemoveNonLockChildren (s : TempDirMockState) (child : String) : List String → TempDirMockState
  | [] => s
  | name :: rest =>
    if name == ".lock" then specRemoveNonLockChildren s child rest
    else
      let entry := mockJoin child name; let re := normKey entry
      match lookupNode s.nodes entry with
      | none => specRemoveNonLockChildren s child rest
      | some (.dir _ _) => specRemoveNonLockChildren { s with nodes := s.nodes.filter (fun e => !underDir re e.1) } child rest
      | some _ => specRemoveNonLockChildren { s with nodes := s.nodes.filter (fun e => normKey e.1 != re) } child rest
/-- Pure domain transition for removing a locked temporary directory (`listDir`, children, `unlink .lock`, `rmdir`). -/
def specRemoveLockedDir (s : TempDirMockState) (child lockPath : String) : Except TempDirError Unit × TempDirMockState :=
  let rc := normKey child
  match lookupNode s.nodes rc with
  | none => (.ok (), s)
  | some (.dir _ mode) =>
    if !((mode / 256) % 2 == 1 && (mode / 64) % 2 == 1) then
      (.error { kind := .permissionDenied, path := some child, message := "no read/exec permission" }, s)
    else
      let names := sortStrings (eraseDupStrings (s.nodes.filterMap (fun e => mockParentChild rc e.1)))
      let s1 := specRemoveNonLockChildren s child names; let rl := normKey lockPath
      match lookupNode s1.nodes rl with
      | some (.dir _ _) => (.error { kind := .ioError, path := some lockPath, message := "is dir" }, s1)
      | _ =>
        let s2 := match lookupNode s1.nodes rl with
          | none => s1 | some _ => { s1 with nodes := s1.nodes.filter (fun e => normKey e.1 != rl) }
        match lookupNode s2.nodes rc with
        | none => (.ok (), s2)
        | some (.dir _ _) => (.ok (), { s2 with nodes := s2.nodes.filter (fun e => normKey e.1 != rc) })
        | some _ => (.error { kind := .notADirectory, path := some child, message := "not dir" }, s2)
  | some _ => (.error { kind := .notADirectory, path := some child, message := "not dir" }, s)
/-- Pure non-blocking exclusive lock attempt executing `specRemoveLockedDir` on acquisition. -/
def specTryLockRemove (s : TempDirMockState) (child lockPath : String) :
    Except FsError (Option (Except TempDirError Unit)) × TempDirMockState :=
  match lookupNode s.nodes (normKey lockPath) with
  | none => (.error { kind := .notFound, path := some lockPath, message := "not found" }, s)
  | some (.dir _ _) => (.error { kind := .isADirectory, path := some lockPath, message := "is dir" }, s)
  | some (.symlink _ _) => (.error { kind := .invalidInput, path := some lockPath, message := "symlink" }, s)
  | some (.file ino _ _ _) =>
    if mockHasConflict s.locks ino .exclusive then (.ok none, s)
    else let (res, s') := specRemoveLockedDir s child lockPath; (.ok (some res), s')
/-- Pure single-entry sweep step directly inspecting `s.nodes` and `s.locks`. -/
def specSweepEntry (s : TempDirMockState) (root dirPrefix : String) (maxAgeSec : Nat) (nowSec : Int)
    (rep : CleanupReport) (entryName : String) : CleanupReport × TempDirMockState :=
  let child := mockJoin root entryName
  if !dirPrefix.toList.isPrefixOf entryName.toList then ({ rep with skipped := rep.skipped.push child }, s)
  else match lookupNode s.nodes child with
    | none => (rep, s)
    | some (.dir modSec _) =>
      let lockPath := mockJoin child ".lock"
      match lookupNode s.nodes lockPath with
      | some (.file ino _ _ _) =>
        if mockHasConflict s.locks ino .exclusive then ({ rep with keptLocked := rep.keptLocked.push child }, s)
        else match specRemoveLockedDir s child lockPath with
          | (.ok (), s') => ({ rep with removed := rep.removed.push child }, s')
          | (.error te, s') => ({ rep with failed := rep.failed.push te }, s')
      | some _ =>
        let err : TempDirError := { kind := .invalidInput, path := some lockPath, message := "lock entry is not a regular file" }
        ({ rep with failed := rep.failed.push err }, s)
      | none =>
        if nowSec - modSec ≤ (maxAgeSec : Int) then ({ rep with keptFresh := rep.keptFresh.push child }, s)
        else ({ rep with removed := rep.removed.push child }, { s with nodes := s.nodes.filter (fun e => !underDir (normKey child) e.1) })
    | some _ => ({ rep with skipped := rep.skipped.push child }, s)
/-- Fold `specSweepEntry` across immediate root entry names. -/
def specSweepEntries (s : TempDirMockState) (root dirPrefix : String) (maxAgeSec : Nat) (nowSec : Int)
    (rep : CleanupReport) : List String → CleanupReport × TempDirMockState
  | [] => (rep, s)
  | name :: rest =>
    let (rep', s') := specSweepEntry s root dirPrefix maxAgeSec nowSec rep name
    specSweepEntries s' root dirPrefix maxAgeSec nowSec rep' rest
/-- Pure domain transition for `cleanupStaleTempDirs` directly inspecting `s.tmpdir`, `s.nowSec`, `s.nodes`, and `s.locks`. -/
def specCleanupStaleTempDirs (s : TempDirMockState) (root? : Option String) (dirPrefix : String) (maxAgeSec : Nat) :
    Except TempDirError CleanupReport × TempDirMockState :=
  if !specValidPrefix dirPrefix then (.error { kind := .invalidInput, path := none, message := "invalid temporary directory prefix" }, s)
  else match specResolveRoot s root? with
    | .error te => (.error te, s)
    | .ok root => match specListDir s root with
      | .error fe => (.error (specMapFsError fe), s)
      | .ok names =>
        let (rep, s') := specSweepEntries s root dirPrefix maxAgeSec s.nowSec {} names.toList
        (.ok { removed := (sortStrings rep.removed.toList).toArray, keptLocked := (sortStrings rep.keptLocked.toList).toArray
               keptFresh := (sortStrings rep.keptFresh.toList).toArray, skipped := (sortStrings rep.skipped.toList).toArray, failed := rep.failed }, s')
/-- Total well-formedness guard on `TempDirMockState` for `Core.ObeysStepFromFinally`. -/
def tempDirStepWf (_ : TempDirMockState) : Bool := true
/-- Single-step lower-layer capability request sum covering every `TempDirCaps` operation invoked by `TempDir`. -/
inductive RawStepReq where
  /-- Pure path join `fs.join a b`. -/ | fsJoin (a b : String)
  /-- `fs.stat path`. -/ | fsStat (path : String)
  /-- `fs.lstat path`. -/ | fsLstat (path : String)
  /-- `fs.mkdir path parents existOk`. -/ | fsMkdir (path : String) (parents existOk : Bool)
  /-- `fs.chmod path mode`. -/ | fsChmod (path : String) (mode : Nat)
  /-- `fs.unlink path missingOk`. -/ | fsUnlink (path : String) (missingOk : Bool)
  /-- `fs.rmdir path`. -/ | fsRmdir (path : String)
  /-- `fs.rmtree path ignoreMissing`. -/ | fsRmtree (path : String) (ignoreMissing : Bool)
  /-- `fs.listDir path`. -/ | fsListDir (path : String)
  /-- `fs.withFileLock path mode createIfMissing (pure (.ok res))`. -/ | fsWithFileLockRet (path : String) (mode : LockMode) (createIfMissing : Bool) (res : Except TempDirError String)
  /-- `fs.tryWithFileLock lockPath .exclusive false (tryLockRemoveCallback fs child lockPath)`. -/ | fsTryWithFileLockRemoveLocked (child lockPath : String)
  /-- `time.nowTimestamp`. -/ | timeNowTimestamp
  /-- `uuid.getUuid`. -/ | uuidGetUuid
  /-- Pure `uuid.toString u`. -/ | uuidToString (u : Uuid)
  /-- `env.getEnv name`. -/ | envGetEnv (name : String)
/-- Single-step output sum for `RawStepReq`. -/
inductive RawStepOut where
  /-- String result (`fs.join` / `uuid.toString`). -/ | str (s : String)
  /-- File status result (`fs.stat` / `fs.lstat`). -/ | stat (res : Except FsError FileStat)
  /-- Unit filesystem result (`mkdir` / `chmod` / `unlink` / `rmdir` / `rmtree`). -/ | unitRes (res : Except FsError Unit)
  /-- Directory entry list (`listDir`). -/ | names (res : Except FsError (Array String))
  /-- Pure bracketed lock result (`withFileLock`). -/ | lockRet (res : Except FsError (Except TempDirError String))
  /-- Non-blocking exclusive removal lock result (`tryWithFileLock`). -/ | tryLockRemove (res : Except FsError (Option (Except TempDirError Unit)))
  /-- Wall-clock timestamp (`nowTimestamp`). -/ | ts (t : Std.Time.Timestamp)
  /-- UUID generation result (`getUuid`). -/ | uuid (res : Except UuidError Uuid)
  /-- Environment variable lookup (`getEnv`). -/ | env (res : Except EnvVarsError (Option String))
/-- Pure single-step evaluator for `RawStepReq` directly over `TempDirMockState`. -/
def evalRawStep (s : TempDirMockState) : RawStepReq → RawStepOut × TempDirMockState
  | .fsJoin a b => (.str (mockJoin a b), s)
  | .fsStat p => (.stat (mockStatPure s p), s)
  | .fsLstat p => (.stat (mockLstatPure s p), s)
  | .fsMkdir p _ existOk => let (r, s') := specMkdir s p existOk; (.unitRes r, s')
  | .fsChmod p mode => let (r, s') := specChmod s p mode; (.unitRes r, s')
  | .fsUnlink p missingOk => let (r, s') := specUnlink s p missingOk; (.unitRes r, s')
  | .fsRmdir p => let (r, s') := specRmdir s p; (.unitRes r, s')
  | .fsRmtree p ignoreMissing => let (r, s') := specRmtree s p ignoreMissing; (.unitRes r, s')
  | .fsListDir p => (.names (specListDir s p), s)
  | .fsWithFileLockRet p mode createIfMissing res => let (r, s') := specWithFileLockRet s p mode createIfMissing res; (.lockRet r, s')
  | .fsTryWithFileLockRemoveLocked child lockPath => let (r, s') := specTryLockRemove s child lockPath; (.tryLockRemove r, s')
  | .timeNowTimestamp => (.ts (Std.Time.Timestamp.ofSecondsSinceUnixEpoch (Std.Time.Second.Offset.ofInt s.nowSec)), s)
  | .uuidGetUuid => (.uuid (.ok (mockUuidOfNat s.nextUuid)), { s with nextUuid := s.nextUuid + 1 })
  | .uuidToString u => (.str (mockUuidToString u), s)
  | .envGetEnv name => (.env (.ok (if name == "TMPDIR" then s.tmpdir else none)), s)
/-- Allowed deterministic single-step relation for lower-layer `TempDir` capabilities over `TempDirMockState`. -/
def allowedRawStep (s : TempDirMockState) (req : RawStepReq) (out : RawStepOut) (s' : TempDirMockState) : Prop :=
  let r := evalRawStep s req; out = r.1 ∧ s' = r.2
/-- Public request sum covering all 3 `TempDirApiM` operations inside `Core.ObeysStepFromFinally`. -/
inductive PkgStepReq where
  /-- Create and clean up an exclusive temp directory, returning `evalStepAction dir act`. -/ | withTempDir (root? : Option String) (dirPrefix : String) (act : StepAction)
  /-- Like `withTempDir`, while holding a `.shared` advisory lock on `<dir>/.lock`. -/ | withLockedTempDir (root? : Option String) (dirPrefix : String) (act : StepAction)
  /-- Sweep immediate stale subdirectories of `root?` matching `dirPrefix`. -/ | cleanupStaleTempDirs (root? : Option String) (dirPrefix : String) (maxAgeSec : Nat)
  deriving Repr, BEq, DecidableEq
/-- Output sum for `PkgStepReq` transitions in `Core.ObeysStepFromFinally`. -/
inductive PkgStepOut where
  /-- Result of `withTempDir` or `withLockedTempDir`. -/ | dirRes (res : Except TempDirError String)
  /-- Result of `cleanupStaleTempDirs`. -/ | report (res : Except TempDirError CleanupReport)
  deriving Repr
/-- Execute one `PkgStepReq` against an arbitrary `TempDirApiM (StateM W)`. -/
def execPkgStep {W : Type} (api : TempDirApiM (StateM W)) : PkgStepReq → StateM W PkgStepOut
  | .withTempDir root? dirPrefix act => .dirRes <$> api.withTempDir root? dirPrefix (fun dir => pure (evalStepAction dir act))
  | .withLockedTempDir root? dirPrefix act => .dirRes <$> api.withLockedTempDir root? dirPrefix (fun dir => pure (evalStepAction dir act))
  | .cleanupStaleTempDirs root? dirPrefix maxAgeSec => .report <$> api.cleanupStaleTempDirs root? dirPrefix maxAgeSec
/-- Pure single-step evaluator for `PkgStepReq` directly over `TempDirMockState`. -/
def evalPkgStep (s : TempDirMockState) : PkgStepReq → PkgStepOut × TempDirMockState
  | .withTempDir root? dirPrefix act => let (r, s') := specWithTempDir s root? dirPrefix act; (.dirRes r, s')
  | .withLockedTempDir root? dirPrefix act => let (r, s') := specWithLockedTempDir s root? dirPrefix act; (.dirRes r, s')
  | .cleanupStaleTempDirs root? dirPrefix maxAgeSec => let (r, s') := specCleanupStaleTempDirs s root? dirPrefix maxAgeSec; (.report r, s')
/-- Allowed deterministic single-step relation for `TempDirApiM` derived directly from pure `TempDirMockState` transitions. -/
def allowedPkgStep (s : TempDirMockState) (req : PkgStepReq) (out : PkgStepOut) (s' : TempDirMockState) : Prop :=
  let r := evalPkgStep s req; out = r.1 ∧ s' = r.2
namespace Internal
/-- Alias of `LeanSwe.TempDir.Internal.TempDirCaps` retained for model/proof compatibility. -/
abbrev TempDirCaps := LeanSwe.TempDir.Internal.TempDirCaps
/-- Pure recursive directory removal in `StateM TempDirMockState`. -/
def mockRmtreePure (p : String) (ignoreMissing : Bool) : StateM TempDirMockState (Except FsError Unit) := do
  let s ← get; let rp := normKey p
  match lookupNode s.nodes rp with
  | none => if ignoreMissing then return .ok () else return .error { kind := .notFound, path := some p, message := "not found" }
  | some (.dir _ _) => set { s with nodes := s.nodes.filter (fun e => !underDir rp e.1) }; return .ok ()
  | some _ => return .error { kind := .notADirectory, path := some p, message := "not a dir" }
/-- Polymorphic lock acquisition helper. -/
def mockLockCore {m : Type → Type} {α β : Type} [Monad m] [MonadFinally m] [MonadStateOf TempDirMockState m]
    (p : String) (mode : LockMode) (createIfMissing : Bool) (onConflict : m (Except FsError β))
    (wrap : Except FsError α → Except FsError β) (action : m (Except FsError α)) : m (Except FsError β) := do
  let s ← get; let rp := normKey p
  match lookupNode s.nodes rp with
  | some (.dir _ _) => return .error { kind := .isADirectory, path := some p, message := "is dir" }
  | some (.symlink _ _) => return .error { kind := .invalidInput, path := some p, message := "symlink" }
  | some (.file ino _ _ _) =>
    if mockHasConflict s.locks ino mode then onConflict
    else set { s with locks := (ino, mode) :: s.locks }; let (r, _) ← tryFinally' action fun _ => modify fun s' => { s' with locks := mockRemoveFirstLock ino mode s'.locks }; return wrap r
  | none =>
    if !createIfMissing then return .error { kind := .notFound, path := some p, message := "not found" }
    let ino := freshInode s; set { s with nodes := (rp, .file ino "" s.nowSec 0o644) :: s.nodes, locks := (ino, mode) :: s.locks, nextInode := ino + 1 }
    let (r, _) ← tryFinally' action fun _ => modify fun s' => { s' with locks := mockRemoveFirstLock ino mode s'.locks }; return wrap r
/-- Overwrite or insert a regular file node in `TempDirMockState`. -/
def writeFileMock (p c : String) : StateM TempDirMockState (Except FsError Unit) := do
  let s ← get; let rp := normKey p; let ino := freshInode s
  set { s with nodes := (rp, .file ino c s.nowSec 0o644) :: s.nodes.filter (fun e => normKey e.1 != rp), nextInode := ino + 1 }; return .ok ()
/-- Mock `FsApiM` over `StateM TempDirMockState`. -/
def mockFs : FsApiM (StateM TempDirMockState) :=
  { join := mockJoin, joinMany := fun ps => ps.foldl mockJoin "", normPath := normKey
    parent := fun p => (splitParentChild p).map Prod.fst, name := fun p => (splitParentChild p).map Prod.snd
    stem := fun _ => none, suffix := fun _ => "", suffixes := fun _ => #[], withName := fun p _ => .ok p, withSuffix := fun p _ => .ok p
    isAbsolute := fun p => p.startsWith "/", relativeTo := fun p _ => .ok p, mapRawError := fun _ => { kind := .ioError, message := "raw" }
    readText := fun p => do match lookupNode (← get).nodes (normKey p) with
      | some (.file _ c _ _) => return .ok c | some (.dir _ _) => return .error { kind := .isADirectory, path := some p, message := "is dir" }
      | _ => return .error { kind := .notFound, path := some p, message := "not found" }
    writeText := writeFileMock, appendText := writeFileMock, readBytes := fun _ => pure (.ok ByteArray.empty), writeBytes := fun _ _ => pure (.ok ())
    atomicWriteBytes := fun _ _ => pure (.ok ()), atomicWriteText := fun _ _ => pure (.ok ()), touch := fun p _ => writeFileMock p ""
    mkdir := fun p _ existOk => do
      let s ← get; match splitParentChild p with
      | none => return .error { kind := .alreadyExists, path := some p, message := "root" }
      | some (par, base) => match lookupNode s.nodes par with
        | none => return .error { kind := .notFound, path := some par, message := "parent not found" }
        | some parNode =>
          let stPar := mockNodeStat parNode
          if stPar.kind != .dir then return .error { kind := .notADirectory, path := some par, message := "not a dir" }
          if !hasWx stPar then return .error { kind := .permissionDenied, path := some par, message := "no write permission" }
          let rp := mockJoin par base; match lookupNode s.nodes rp with
          | some (.dir _ _) => if existOk then return .ok () else return .error { kind := .alreadyExists, path := some p, message := "exists" }
          | some _ => return .error { kind := .alreadyExists, path := some p, message := "exists" }
          | none => set { s with nodes := (rp, .dir s.nowSec 0o755) :: s.nodes.filter (fun e => !underDir rp e.1) }; return .ok ()
    unlink := fun p miss => do
      let s ← get; let rp := normKey p; match lookupNode s.nodes rp with
      | none => if miss then return .ok () else return .error { kind := .notFound, path := some p, message := "not found" }
      | some (.dir _ _) => return .error { kind := .isADirectory, path := some p, message := "is dir" }
      | some _ => set { s with nodes := s.nodes.filter (fun e => normKey e.1 != rp) }; return .ok ()
    rmdir := fun p => do
      let s ← get; let rp := normKey p; match lookupNode s.nodes rp with
      | none => return .error { kind := .notFound, path := some p, message := "not found" }
      | some (.dir _ _) => set { s with nodes := s.nodes.filter (fun e => normKey e.1 != rp) }; return .ok ()
      | some _ => return .error { kind := .notADirectory, path := some p, message := "not dir" }
    rmtree := mockRmtreePure, rename := fun _ _ => pure (.ok ()), copyFile := fun _ _ => pure (.ok ()), copyTree := fun _ _ _ => pure (.ok ())
    pathExists := fun p => do return .ok ((mockStatPure (← get) p).isOk)
    isFile := fun p => do match mockStatPure (← get) p with | .ok st => return .ok (st.kind == .file) | .error _ => return .ok false
    isDir := fun p => do match mockStatPure (← get) p with | .ok st => return .ok (st.kind == .dir) | .error _ => return .ok false
    isSymlink := fun p => do match mockLstatPure (← get) p with | .ok st => return .ok (st.kind == .symlink) | .error _ => return .ok false
    stat := fun p => do return mockStatPure (← get) p, lstat := fun p => do return mockLstatPure (← get) p
    chmod := fun p mode => do
      let s ← get; let rp := normKey p; match lookupNode s.nodes rp with
      | none => return .error { kind := .notFound, path := some p, message := "not found" }
      | some _ => set { s with nodes := s.nodes.map fun (k, n) => if normKey k == rp then
          (k, match (n : MockNode) with | .dir t _ => .dir t mode | .file i c t _ => .file i c t mode | .symlink tgt t => .symlink tgt t) else (k, n) }; return .ok ()
    symlink := fun _ _ => pure (.ok ()), readLink := fun _ => pure (.error { kind := .notFound, message := "no link" }), resolve := fun p => pure (.ok (normKey p)), cwd := pure (.ok "/")
    listDir := fun p => do
      let s ← get; let rp := normKey p; match lookupNode s.nodes rp with
      | none => return .error { kind := .notFound, path := some p, message := "not found" }
      | some node =>
        let st := mockNodeStat node
        if st.kind != .dir then return .error { kind := .notADirectory, path := some p, message := "not dir" }
        if !hasRx st then return .error { kind := .permissionDenied, path := some p, message := "no read/exec permission" }
        return .ok (sortStrings (eraseDupStrings (s.nodes.filterMap (fun e => mockParentChild rp e.1)))).toArray
    walk := fun _ => pure (.ok #[]), glob := fun _ _ => pure (.ok #[]), rglob := fun _ _ => pure (.ok #[])
    withFileLock := fun p m c act => mockLockCore p m c (pure (.error { kind := .wouldBlock, path := some p, message := "wouldBlock" })) id act
    tryWithFileLock := fun p m c act => mockLockCore p m c (pure (.ok none)) (Except.map some) act }
/-- Mock `TimeOpsM` over `StateM TempDirMockState`. -/
def mockTime : TimeOpsM (StateM TempDirMockState) :=
  { nowTimestamp := do return Std.Time.Timestamp.ofSecondsSinceUnixEpoch (Std.Time.Second.Offset.ofInt (← get).nowSec), monoNanosNow := pure 0, sleep := fun _ => pure () }
/-- Mock `UuidApiM` over `StateM TempDirMockState`. -/
def mockUuid : UuidApiM (StateM TempDirMockState) :=
  { mapRawError := fun _ => { kind := .entropyFailed, message := "entropy" }, fromRandomBytes := fun _ => .ok (mockUuidOfNat 1), toString := mockUuidToString
    toHex := fun _ => "00000000000040008000000000000001", parse := fun _ => .ok (mockUuidOfNat 1), parseHex := fun _ => .ok (mockUuidOfNat 1), isValid := fun _ => true
    getUuid := do let s ← get; set { s with nextUuid := s.nextUuid + 1 }; return .ok (mockUuidOfNat s.nextUuid) }
/-- Mock `EnvVarsApiM` over `StateM TempDirMockState`. -/
def mockEnv : EnvVarsApiM (StateM TempDirMockState) :=
  { mapRawError := fun _ => { kind := .ioError, message := "env" }, getEnv := fun k => do if k == "TMPDIR" then return .ok (← get).tmpdir else return .ok none
    listEnv := pure (.ok #[]), homeDir := pure (.ok "/mock/user"), listEnvironBytes := pure #[], splitSearchPath := fun _ => #[] }
/-- Mock `FsApiM` lifted to `ExceptT String (StateM TempDirMockState)` with exception-safe locking. -/
def mockFsEx : FsApiM (ExceptT String (StateM TempDirMockState)) :=
  { join := mockFs.join, joinMany := mockFs.joinMany, normPath := mockFs.normPath, parent := mockFs.parent, name := mockFs.name, stem := mockFs.stem, suffix := mockFs.suffix, suffixes := mockFs.suffixes
    withName := mockFs.withName, withSuffix := mockFs.withSuffix, isAbsolute := mockFs.isAbsolute, relativeTo := mockFs.relativeTo, mapRawError := mockFs.mapRawError
    readText := fun p => liftM (mockFs.readText p), writeText := fun p c => liftM (mockFs.writeText p c), appendText := fun p c => liftM (mockFs.appendText p c), readBytes := fun p => liftM (mockFs.readBytes p)
    writeBytes := fun p b => liftM (mockFs.writeBytes p b), atomicWriteBytes := fun p b => liftM (mockFs.atomicWriteBytes p b), atomicWriteText := fun p c => liftM (mockFs.atomicWriteText p c)
    touch := fun p e => liftM (mockFs.touch p e), mkdir := fun p a e => liftM (mockFs.mkdir p a e), unlink := fun p m => liftM (mockFs.unlink p m), rmdir := fun p => liftM (mockFs.rmdir p), rmtree := fun p i => liftM (mockFs.rmtree p i)
    rename := fun a b => liftM (mockFs.rename a b), copyFile := fun a b => liftM (mockFs.copyFile a b), copyTree := fun a b c => liftM (mockFs.copyTree a b c), pathExists := fun p => liftM (mockFs.pathExists p)
    isFile := fun p => liftM (mockFs.isFile p), isDir := fun p => liftM (mockFs.isDir p), isSymlink := fun p => liftM (mockFs.isSymlink p), stat := fun p => liftM (mockFs.stat p), lstat := fun p => liftM (mockFs.lstat p)
    chmod := fun p m => liftM (mockFs.chmod p m), symlink := fun a b => liftM (mockFs.symlink a b), readLink := fun p => liftM (mockFs.readLink p), resolve := fun p => liftM (mockFs.resolve p), cwd := liftM mockFs.cwd
    listDir := fun p => liftM (mockFs.listDir p), walk := fun p => liftM (mockFs.walk p), glob := fun a b => liftM (mockFs.glob a b), rglob := fun a b => liftM (mockFs.rglob a b)
    withFileLock := fun p m c act => mockLockCore p m c (pure (.error { kind := .wouldBlock, path := some p, message := "wouldBlock" })) id act
    tryWithFileLock := fun p m c act => mockLockCore p m c (pure (.ok none)) (Except.map some) act }
/-- Mock `TimeOpsM` lifted to `ExceptT String (StateM TempDirMockState)`. -/
def mockTimeEx : TimeOpsM (ExceptT String (StateM TempDirMockState)) :=
  { nowTimestamp := liftM mockTime.nowTimestamp, monoNanosNow := liftM mockTime.monoNanosNow, sleep := fun ms => liftM (mockTime.sleep ms) }
/-- Mock `UuidApiM` lifted to `ExceptT String (StateM TempDirMockState)`. -/
def mockUuidEx : UuidApiM (ExceptT String (StateM TempDirMockState)) :=
  { mapRawError := mockUuid.mapRawError, fromRandomBytes := mockUuid.fromRandomBytes, toString := mockUuid.toString, toHex := mockUuid.toHex
    parse := mockUuid.parse, parseHex := mockUuid.parseHex, isValid := mockUuid.isValid, getUuid := liftM mockUuid.getUuid }
/-- Mock `EnvVarsApiM` lifted to `ExceptT String (StateM TempDirMockState)`. -/
def mockEnvEx : EnvVarsApiM (ExceptT String (StateM TempDirMockState)) :=
  { mapRawError := mockEnv.mapRawError, getEnv := fun k => liftM (mockEnv.getEnv k), listEnv := liftM mockEnv.listEnv, homeDir := liftM mockEnv.homeDir, listEnvironBytes := liftM mockEnv.listEnvironBytes, splitSearchPath := mockEnv.splitSearchPath }
/-- Pure mock capability bundle backed by `TempDirMockState`. -/
def modelCaps : TempDirCaps (StateM TempDirMockState) := { fs := mockFs, time := mockTime, uuid := mockUuid, env := mockEnv }
/-- Minimal `FsApiM` non-`.lock` child-removal loop passed inside `tryLockRemoveCallback`. -/
def tryLockRemoveChildren {W : Type} (fs : FsApiM (StateM W)) (child : String) : List String → StateM W (Except TempDirError Unit)
  | [] => return .ok ()
  | name :: rest => do
    if name == ".lock" then tryLockRemoveChildren fs child rest
    else
      let entry := fs.join child name
      match ← fs.lstat entry with
      | .error fe => if fe.kind == .notFound then tryLockRemoveChildren fs child rest else return .error (specMapFsError fe)
      | .ok st =>
        let delRes : Except TempDirError Unit ← if st.kind == .dir then
          match ← fs.rmtree entry true with
          | .ok () => pure (Except.ok ()) | .error fe => if fe.kind == .notFound then pure (Except.ok ()) else pure (Except.error (specMapFsError fe))
        else match ← fs.unlink entry true with | .ok () => pure (Except.ok ()) | .error fe => pure (Except.error (specMapFsError fe))
        match delRes with | .error te => return .error te | .ok () => tryLockRemoveChildren fs child rest
/-- Closed higher-order callback supplied to `caps.fs.tryWithFileLock` in `execRawStep`. -/
def tryLockRemoveCallback {W : Type} (fs : FsApiM (StateM W)) (child lockPath : String) : StateM W (Except FsError (Except TempDirError Unit)) := do
  match ← fs.listDir child with
  | .error fe => if fe.kind == .notFound then return .ok (.ok ()) else return .ok (.error (specMapFsError fe))
  | .ok names => match ← tryLockRemoveChildren fs child names.toList with
    | .error te => return .ok (.error te)
    | .ok () => match ← fs.unlink lockPath true with
      | .error fe => return .ok (.error (specMapFsError fe))
      | .ok () => match ← fs.rmdir child with
        | .ok () => return .ok (.ok ())
        | .error fe => if fe.kind == .notFound then return .ok (.ok ()) else return .ok (.error (specMapFsError fe))
end Internal
/-- Execute one `RawStepReq` against an arbitrary `Internal.TempDirCaps (StateM W)`. -/
def execRawStep {W : Type} (caps : Internal.TempDirCaps (StateM W)) : RawStepReq → StateM W RawStepOut
  | .fsJoin a b => pure (.str (caps.fs.join a b))
  | .fsStat p => .stat <$> caps.fs.stat p
  | .fsLstat p => .stat <$> caps.fs.lstat p
  | .fsMkdir p parents existOk => .unitRes <$> caps.fs.mkdir p parents existOk
  | .fsChmod p mode => .unitRes <$> caps.fs.chmod p mode
  | .fsUnlink p missingOk => .unitRes <$> caps.fs.unlink p missingOk
  | .fsRmdir p => .unitRes <$> caps.fs.rmdir p
  | .fsRmtree p ignoreMissing => .unitRes <$> caps.fs.rmtree p ignoreMissing
  | .fsListDir p => .names <$> caps.fs.listDir p
  | .fsWithFileLockRet p mode createIfMissing res => .lockRet <$> caps.fs.withFileLock p mode createIfMissing (pure (.ok res))
  | .fsTryWithFileLockRemoveLocked child lockPath => .tryLockRemove <$> caps.fs.tryWithFileLock lockPath .exclusive false (Internal.tryLockRemoveCallback caps.fs child lockPath)
  | .timeNowTimestamp => .ts <$> caps.time.nowTimestamp
  | .uuidGetUuid => .uuid <$> caps.uuid.getUuid
  | .uuidToString u => pure (.str (caps.uuid.toString u))
  | .envGetEnv name => .env <$> caps.env.getEnv name
end LeanSwe.TempDir.Model
