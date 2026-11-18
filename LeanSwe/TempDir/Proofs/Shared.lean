import LeanSwe.TempDir.Interface
import LeanSwe.TempDir.SpecTests

set_option Elab.async false

namespace LeanSwe.TempDir.Proofs

open Core
open Core.NondetTest
open LeanSwe.Fs (FsApiM FsError FsErrorKind EntryKind FileStat LockMode)
open LeanSwe.Time (TimeOpsM)
open LeanSwe.Uuid (UuidApiM Uuid)
open LeanSwe.EnvVars (EnvVarsApiM)

/-- Entry kind stored in the `TempDirMockState` filesystem model. -/
inductive MockNode where
  /-- Directory with modification timestamp (`modifiedSec`) and POSIX mode bits. -/
  | dir (modifiedSec : Int) (mode : Nat)
  /-- Regular file with inode id, content, modification timestamp (`modifiedSec`), and POSIX mode bits. -/
  | file (inode : Nat) (content : String) (modifiedSec : Int) (mode : Nat)
  /-- Symbolic link pointing to `target` with modification timestamp. -/
  | symlink (target : String) (modifiedSec : Int)
  deriving Repr, BEq, DecidableEq

/-- Complete deterministic mock state used to verify all `LeanSwe.TempDir` specifications. -/
structure TempDirMockState where
  /-- Association list of filesystem entries `(path, node)`. -/
  nodes : List (String × MockNode) := [("/tmp", .dir 0 0o755)]
  /-- Active advisory file locks `(inode, mode)`. -/
  locks : List (Nat × LockMode) := []
  /-- Monotonic counter used to allocate fresh file inodes. -/
  nextInode : Nat := 1
  /-- Optional `TMPDIR` environment variable value. -/
  tmpdir : Option String := none
  /-- Current mock Unix timestamp in seconds. -/
  nowSec : Int := 1000
  /-- Monotonic counter used to mint distinct mock UUIDv4 values. -/
  nextUuid : Nat := 1
  deriving Repr, BEq, DecidableEq

private def trimTrailingSlashesRev : List Char → List Char
  | [] => []
  | ['/'] => ['/']
  | '/' :: rest => trimTrailingSlashesRev rest
  | cs => cs

private def trimSlashChars (cs : List Char) : List Char :=
  (trimTrailingSlashesRev cs.reverse).reverse

/-- Shared proof helper `normKey`. -/
def normKey (p : String) : String :=
  String.ofList (trimSlashChars p.toList)

/-- Shared proof helper `mockJoin`. -/
def mockJoin (a b : String) : String :=
  let na := normKey a
  if na.isEmpty then b
  else if na == "/" then "/" ++ b
  else na ++ "/" ++ b

private def splitLastSlashRev : List Char → Option (List Char × List Char)
  | [] => none
  | c :: cs =>
    if c == '/' then some (cs.reverse, [])
    else
      match splitLastSlashRev cs with
      | none => none
      | some (par, base) => some (par, base ++ [c])

/-- Shared proof helper `splitParentChild`. -/
def splitParentChild (p : String) : Option (String × String) :=
  let np := normKey p
  if np == "/" || np.isEmpty then none
  else
    match splitLastSlashRev np.toList.reverse with
    | none => none
    | some (parCs, baseCs) =>
      let par := if parCs.isEmpty then "/" else String.ofList parCs
      let base := String.ofList baseCs
      if base.isEmpty then none else some (par, base)

/-- Shared proof helper `mockNodeStat`. -/
def mockNodeStat : MockNode → FileStat
  | .dir mtime mode =>
    { kind := .dir, byteSize := 0, mode := mode, modifiedSec := mtime, modifiedNsec := 0, accessedSec := 0, accessedNsec := 0 }
  | .file _ content mtime mode =>
    { kind := .file, byteSize := content.length, mode := mode, modifiedSec := mtime, modifiedNsec := 0, accessedSec := 0, accessedNsec := 0 }
  | .symlink _ mtime =>
    { kind := .symlink, byteSize := 0, mode := 0o777, modifiedSec := mtime, modifiedNsec := 0, accessedSec := 0, accessedNsec := 0 }

/-- Shared proof helper `lookupNode`. -/
def lookupNode (nodes : List (String × MockNode)) (p : String) : Option MockNode :=
  let np := normKey p
  (nodes.find? (fun e => normKey e.1 == np)).map Prod.snd

/-- Shared proof helper `resolveParentTarget`. -/
def resolveParentTarget (_s : TempDirMockState) (p : String) : Except FsError String :=
  .ok (normKey p)

/-- Shared proof helper `mockLstatPure`. -/
def mockLstatPure (s : TempDirMockState) (p : String) : Except FsError FileStat :=
  match lookupNode s.nodes p with
  | none => .error { kind := .notFound, path := some p, message := "not found" }
  | some node => .ok (mockNodeStat node)

/-- Shared proof helper `mockStatPure`. -/
def mockStatPure (s : TempDirMockState) (p : String) : Except FsError FileStat :=
  mockLstatPure s p

/-- Shared proof helper `hasWx`. -/
def hasWx (st : FileStat) : Bool :=
  st.kind == .dir && (st.mode / 128) % 2 == 1 && (st.mode / 64) % 2 == 1

/-- Shared proof helper `hasRx`. -/
def hasRx (st : FileStat) : Bool :=
  st.kind == .dir && (st.mode / 256) % 2 == 1 && (st.mode / 64) % 2 == 1

/-- Shared proof helper `mockParentChild`. -/
def mockParentChild (dir full : String) : Option String :=
  let nd := normKey dir
  let nf := normKey full
  let pref := if nd.isEmpty then "" else if nd == "/" then "/" else nd ++ "/"
  if pref.toList.isPrefixOf nf.toList then
    let rest := String.ofList (nf.toList.drop pref.length)
    if !rest.isEmpty && rest != "." && rest != ".." && !('/' ∈ rest.toList) && !(Char.ofNat 0 ∈ rest.toList) then
      some rest
    else none
  else none

/-- Shared proof helper `eraseDupStringsAux`. -/
def eraseDupStringsAux (seen : List String) : List String → List String
  | [] => []
  | x :: xs => if x ∈ seen then eraseDupStringsAux seen xs else x :: eraseDupStringsAux (x :: seen) xs

/-- Shared proof helper `eraseDupStrings`. -/
def eraseDupStrings (xs : List String) : List String :=
  eraseDupStringsAux [] xs

/-- Shared proof helper `mockHasConflict`. -/
def mockHasConflict (locks : List (Nat × LockMode)) (ino : Nat) (m : LockMode) : Bool :=
  locks.any fun (li, lm) => li == ino && (m == .exclusive || lm == .exclusive)

/-- Shared proof helper `mockRemoveFirstLock`. -/
def mockRemoveFirstLock (ino : Nat) (m : LockMode) : List (Nat × LockMode) → List (Nat × LockMode)
  | [] => []
  | x :: xs => if x == (ino, m) then xs else x :: mockRemoveFirstLock ino m xs

/-- Shared proof helper `freshInode`. -/
def freshInode (s : TempDirMockState) : Nat :=
  s.locks.foldl (fun m l => Nat.max m (l.1 + 1)) s.nextInode

/-- Shared proof helper `underDir`. -/
def underDir (prefixDir key : String) : Bool :=
  let np := normKey prefixDir
  let nk := normKey key
  let pref := if np == "/" then "/" else np ++ "/"
  nk == np || pref.toList.isPrefixOf nk.toList

/-- Shared proof helper `mockRmtreePure`. -/
def mockRmtreePure (p : String) (ignoreMissing : Bool) : StateM TempDirMockState (Except FsError Unit) := do
  let s ← get
  match resolveParentTarget s p with
  | .error e =>
    if ignoreMissing && e.kind == .notFound then return .ok ()
    else return .error e
  | .ok rp =>
    match lookupNode s.nodes rp with
    | none =>
      if ignoreMissing then return .ok ()
      else return .error { kind := .notFound, path := some p, message := "not found" }
    | some (.dir _ _) =>
      set { s with nodes := s.nodes.filter (fun e => !underDir rp e.1) }
      return .ok ()
    | some _ =>
      return .error { kind := .notADirectory, path := some p, message := "not a dir" }

/-- Shared proof helper `mockUuidOfNat`. -/
def mockUuidOfNat (n : Nat) : Uuid :=
  let b14 := UInt8.ofNat ((n / 256) % 256)
  let b15 := UInt8.ofNat (n % 256)
  { bytes := ByteArray.mk #[0, 0, 0, 0, 0, 0, 0x40, 0, 0x80, 0, 0, 0, 0, 0, b14, b15] }

private def mockHexByte (b : UInt8) : String :=
  let d (k : Nat) : Char :=
    if k < 10 then Char.ofNat (48 + k) else Char.ofNat (87 + k)
  String.ofList [d (b.toNat / 16), d (b.toNat % 16)]

/-- Shared proof helper `mockUuidToString`. -/
def mockUuidToString (u : Uuid) : String :=
  let b14 := u.bytes[14]?.getD 0
  let b15 := u.bytes[15]?.getD 0
  "00000000-0000-4000-8000-00000000" ++ mockHexByte b14 ++ mockHexByte b15

/-- Shared proof helper `mockFs`. -/
def mockFs : FsApiM (StateM TempDirMockState) :=
  { join := mockJoin
    joinMany := fun parts => parts.foldl mockJoin ""
    normPath := normKey
    parent := fun p => (splitParentChild p).map Prod.fst
    name := fun p => (splitParentChild p).map Prod.snd
    stem := fun _ => none
    suffix := fun _ => ""
    suffixes := fun _ => #[]
    withName := fun p _ => .ok p
    withSuffix := fun p _ => .ok p
    isAbsolute := fun p => p.startsWith "/"
    relativeTo := fun p _ => .ok p
    mapRawError := fun _ => { kind := .ioError, message := "raw" }
    readText := fun p => do
      let s ← get
      match resolveParentTarget s p with
      | .error e => return .error e
      | .ok rp =>
        match lookupNode s.nodes rp with
        | some (.file _ c _ _) => return .ok c
        | some (.dir _ _) => return .error { kind := .isADirectory, path := some p, message := "is dir" }
        | _ => return .error { kind := .notFound, path := some p, message := "not found" }
    writeText := fun p c => do
      let s ← get
      match resolveParentTarget s p with
      | .error e => return .error e
      | .ok rp =>
        let ino := freshInode s
        set { s with
          nodes := (rp, .file ino c s.nowSec 0o644) :: s.nodes.filter (fun e => normKey e.1 != rp)
          nextInode := ino + 1 }
        return .ok ()
    appendText := fun p c => do
      let s ← get
      match resolveParentTarget s p with
      | .error e => return .error e
      | .ok rp =>
        let ino := freshInode s
        set { s with
          nodes := (rp, .file ino c s.nowSec 0o644) :: s.nodes.filter (fun e => normKey e.1 != rp)
          nextInode := ino + 1 }
        return .ok ()
    readBytes := fun _ => pure (.ok ByteArray.empty)
    writeBytes := fun _ _ => pure (.ok ())
    atomicWriteBytes := fun _ _ => pure (.ok ())
    atomicWriteText := fun _ _ => pure (.ok ())
    touch := fun p _ => do
      let s ← get
      match resolveParentTarget s p with
      | .error e => return .error e
      | .ok rp =>
        let ino := freshInode s
        set { s with
          nodes := (rp, .file ino "" s.nowSec 0o644) :: s.nodes.filter (fun e => normKey e.1 != rp)
          nextInode := ino + 1 }
        return .ok ()
    mkdir := fun p _ existOk => do
      let s ← get
      match splitParentChild p with
      | none => return .error { kind := .alreadyExists, path := some p, message := "root" }
      | some (par, base) =>
        match lookupNode s.nodes par with
        | none => return .error { kind := .notFound, path := some par, message := "parent not found" }
        | some parNode =>
          let stPar := mockNodeStat parNode
          if stPar.kind != .dir then
            return .error { kind := .notADirectory, path := some par, message := "not a dir" }
          if !hasWx stPar then
            return .error { kind := .permissionDenied, path := some par, message := "no write permission" }
          let rp := mockJoin par base
          match lookupNode s.nodes rp with
          | some (.dir _ _) =>
            if existOk then return .ok ()
            else return .error { kind := .alreadyExists, path := some p, message := "exists" }
          | some _ =>
            return .error { kind := .alreadyExists, path := some p, message := "exists" }
          | none =>
            set { s with nodes := (rp, .dir s.nowSec 0o755) :: s.nodes.filter (fun e => !underDir rp e.1) }
            return .ok ()
    unlink := fun p miss => do
      let s ← get
      match resolveParentTarget s p with
      | .error e => if miss && e.kind == .notFound then return .ok () else return .error e
      | .ok rp =>
        match lookupNode s.nodes rp with
        | none => if miss then return .ok () else return .error { kind := .notFound, path := some p, message := "not found" }
        | some (.dir _ _) => return .error { kind := .isADirectory, path := some p, message := "is dir" }
        | some _ =>
          set { s with nodes := s.nodes.filter (fun e => normKey e.1 != rp) }
          return .ok ()
    rmdir := fun p => do
      let s ← get
      match resolveParentTarget s p with
      | .error e => return .error e
      | .ok rp =>
        match lookupNode s.nodes rp with
        | none => return .error { kind := .notFound, path := some p, message := "not found" }
        | some (.dir _ _) =>
          set { s with nodes := s.nodes.filter (fun e => normKey e.1 != rp) }
          return .ok ()
        | some _ => return .error { kind := .notADirectory, path := some p, message := "not dir" }
    rmtree := mockRmtreePure
    rename := fun _ _ => pure (.ok ())
    copyFile := fun _ _ => pure (.ok ())
    copyTree := fun _ _ _ => pure (.ok ())
    pathExists := fun p => do return .ok ((mockStatPure (← get) p).isOk)
    isFile := fun p => do
      match mockStatPure (← get) p with
      | .ok st => return .ok (st.kind == .file)
      | .error _ => return .ok false
    isDir := fun p => do
      match mockStatPure (← get) p with
      | .ok st => return .ok (st.kind == .dir)
      | .error _ => return .ok false
    isSymlink := fun p => do
      match mockLstatPure (← get) p with
      | .ok st => return .ok (st.kind == .symlink)
      | .error _ => return .ok false
    stat := fun p => do return mockStatPure (← get) p
    lstat := fun p => do return mockLstatPure (← get) p
    chmod := fun p mode => do
      let s ← get
      match resolveParentTarget s p with
      | .error e => return .error e
      | .ok rp =>
        match lookupNode s.nodes rp with
        | none => return .error { kind := .notFound, path := some p, message := "not found" }
        | some _ =>
          set { s with
            nodes := s.nodes.map fun (k, n) =>
              if normKey k == rp then
                let n' := match n with
                  | MockNode.dir t _ => MockNode.dir t mode
                  | MockNode.file ino c t _ => MockNode.file ino c t mode
                  | MockNode.symlink tgt t => MockNode.symlink tgt t
                (k, n')
              else (k, n) }
          return .ok ()
    symlink := fun _ _ => pure (.ok ())
    readLink := fun _ => pure (.error { kind := .notFound, message := "no link" })
    resolve := fun p => pure (.ok (normKey p))
    cwd := pure (.ok "/")
    listDir := fun p => do
      let s ← get
      let rp := normKey p
      match lookupNode s.nodes rp with
      | none => return .error { kind := .notFound, path := some p, message := "not found" }
      | some node =>
        let st := mockNodeStat node
        if st.kind != .dir then
          return .error { kind := .notADirectory, path := some p, message := "not dir" }
        if !hasRx st then
          return .error { kind := .permissionDenied, path := some p, message := "no read/exec permission" }
        let names := eraseDupStrings (s.nodes.filterMap (fun e => mockParentChild rp e.1))
        return .ok (Internal.sortStrings names).toArray
    walk := fun _ => pure (.ok #[])
    glob := fun _ _ => pure (.ok #[])
    rglob := fun _ _ => pure (.ok #[])
    withFileLock := fun p mode createIfMissing action => do
      let s ← get
      match resolveParentTarget s p with
      | .error e => return .error e
      | .ok rp =>
        match lookupNode s.nodes rp with
        | some (.dir _ _) => return .error { kind := .isADirectory, path := some p, message := "is dir" }
        | some (.symlink _ _) => return .error { kind := .invalidInput, path := some p, message := "symlink" }
        | some (.file ino _ _ _) =>
          if mockHasConflict s.locks ino mode then
            return .error { kind := .wouldBlock, path := some p, message := "wouldBlock" }
          set { s with locks := (ino, mode) :: s.locks }
          let r ← action
          modify fun s' => { s' with locks := mockRemoveFirstLock ino mode s'.locks }
          return r
        | none =>
          if !createIfMissing then
            return .error { kind := .notFound, path := some p, message := "not found" }
          let ino := freshInode s
          set { s with
            nodes := (rp, .file ino "" s.nowSec 0o644) :: s.nodes
            locks := (ino, mode) :: s.locks
            nextInode := ino + 1 }
          let r ← action
          modify fun s' => { s' with locks := mockRemoveFirstLock ino mode s'.locks }
          return r
    tryWithFileLock := fun p mode createIfMissing action => do
      let s ← get
      match resolveParentTarget s p with
      | .error e => return .error e
      | .ok rp =>
        match lookupNode s.nodes rp with
        | some (.dir _ _) => return .error { kind := .isADirectory, path := some p, message := "is dir" }
        | some (.symlink _ _) => return .error { kind := .invalidInput, path := some p, message := "symlink" }
        | some (.file ino _ _ _) =>
          if mockHasConflict s.locks ino mode then return .ok none
          set { s with locks := (ino, mode) :: s.locks }
          let r ← action
          modify fun s' => { s' with locks := mockRemoveFirstLock ino mode s'.locks }
          return r.map some
        | none =>
          if !createIfMissing then
            return .error { kind := .notFound, path := some p, message := "not found" }
          let ino := freshInode s
          set { s with
            nodes := (rp, .file ino "" s.nowSec 0o644) :: s.nodes
            locks := (ino, mode) :: s.locks
            nextInode := ino + 1 }
          let r ← action
          modify fun s' => { s' with locks := mockRemoveFirstLock ino mode s'.locks }
          return r.map some }

/-- Shared proof helper `mockTime`. -/
def mockTime : TimeOpsM (StateM TempDirMockState) :=
  { nowTimestamp := do return Std.Time.Timestamp.ofSecondsSinceUnixEpoch (Std.Time.Second.Offset.ofInt (← get).nowSec)
    monoNanosNow := pure 0
    sleep := fun _ => pure () }

/-- Shared proof helper `mockUuid`. -/
def mockUuid : UuidApiM (StateM TempDirMockState) :=
  { mapRawError := fun _ => { kind := .entropyFailed, message := "entropy" }
    fromRandomBytes := fun _ => .ok (mockUuidOfNat 1)
    toString := mockUuidToString
    toHex := fun _ => "00000000000040008000000000000001"
    parse := fun _ => .ok (mockUuidOfNat 1)
    parseHex := fun _ => .ok (mockUuidOfNat 1)
    isValid := fun _ => true
    getUuid := do
      let s ← get
      let u := mockUuidOfNat s.nextUuid
      set { s with nextUuid := s.nextUuid + 1 }
      return .ok u }

/-- Shared proof helper `mockEnv`. -/
def mockEnv : EnvVarsApiM (StateM TempDirMockState) :=
  { mapRawError := fun _ => { kind := .ioError, message := "env" }
    getEnv := fun k => do
      if k == "TMPDIR" then return .ok (← get).tmpdir
      else return .ok none
    listEnv := pure (.ok #[])
    homeDir := pure (.ok "/home/user")
    splitSearchPath := fun _ => #[] }

/-- Shared proof helper `mockFsEx`. -/
def mockFsEx : FsApiM (ExceptT String (StateM TempDirMockState)) :=
  { join := mockFs.join
    joinMany := mockFs.joinMany
    normPath := mockFs.normPath
    parent := mockFs.parent
    name := mockFs.name
    stem := mockFs.stem
    suffix := mockFs.suffix
    suffixes := mockFs.suffixes
    withName := mockFs.withName
    withSuffix := mockFs.withSuffix
    isAbsolute := mockFs.isAbsolute
    relativeTo := mockFs.relativeTo
    mapRawError := mockFs.mapRawError
    readText := fun p => liftM (mockFs.readText p)
    writeText := fun p c => liftM (mockFs.writeText p c)
    appendText := fun p c => liftM (mockFs.appendText p c)
    readBytes := fun p => liftM (mockFs.readBytes p)
    writeBytes := fun p bs => liftM (mockFs.writeBytes p bs)
    atomicWriteBytes := fun p bs => liftM (mockFs.atomicWriteBytes p bs)
    atomicWriteText := fun p c => liftM (mockFs.atomicWriteText p c)
    touch := fun p ex => liftM (mockFs.touch p ex)
    mkdir := fun p par ex => liftM (mockFs.mkdir p par ex)
    unlink := fun p m => liftM (mockFs.unlink p m)
    rmdir := fun p => liftM (mockFs.rmdir p)
    rmtree := fun p ign => liftM (mockFs.rmtree p ign)
    rename := fun a b => liftM (mockFs.rename a b)
    copyFile := fun a b => liftM (mockFs.copyFile a b)
    copyTree := fun a b c => liftM (mockFs.copyTree a b c)
    pathExists := fun p => liftM (mockFs.pathExists p)
    isFile := fun p => liftM (mockFs.isFile p)
    isDir := fun p => liftM (mockFs.isDir p)
    isSymlink := fun p => liftM (mockFs.isSymlink p)
    stat := fun p => liftM (mockFs.stat p)
    lstat := fun p => liftM (mockFs.lstat p)
    chmod := fun p m => liftM (mockFs.chmod p m)
    symlink := fun a b => liftM (mockFs.symlink a b)
    readLink := fun p => liftM (mockFs.readLink p)
    resolve := fun p => liftM (mockFs.resolve p)
    cwd := liftM mockFs.cwd
    listDir := fun p => liftM (mockFs.listDir p)
    walk := fun p => liftM (mockFs.walk p)
    glob := fun a b => liftM (mockFs.glob a b)
    rglob := fun a b => liftM (mockFs.rglob a b)
    withFileLock := fun p mode createIfMissing action => do
      let s : TempDirMockState ← get
      match resolveParentTarget s p with
      | .error e => return .error e
      | .ok rp =>
        match lookupNode s.nodes rp with
        | some (.dir _ _) => return .error { kind := .isADirectory, path := some p, message := "is dir" }
        | some (.symlink _ _) => return .error { kind := .invalidInput, path := some p, message := "symlink" }
        | some (.file ino _ _ _) =>
          if mockHasConflict s.locks ino mode then
            return .error { kind := .wouldBlock, path := some p, message := "wouldBlock" }
          liftM (set ({ s with locks := (ino, mode) :: s.locks } : TempDirMockState) : StateM TempDirMockState Unit)
          let (r, _) ← tryFinally' action (fun _ =>
            liftM (modify (fun (s' : TempDirMockState) => { s' with locks := mockRemoveFirstLock ino mode s'.locks }) : StateM TempDirMockState Unit))
          return r
        | none =>
          if !createIfMissing then
            return .error { kind := .notFound, path := some p, message := "not found" }
          let ino := freshInode s
          liftM (set ({ s with nodes := (rp, .file ino "" s.nowSec 0o644) :: s.nodes, locks := (ino, mode) :: s.locks, nextInode := ino + 1 } : TempDirMockState) : StateM TempDirMockState Unit)
          let (r, _) ← tryFinally' action (fun _ =>
            liftM (modify (fun (s' : TempDirMockState) => { s' with locks := mockRemoveFirstLock ino mode s'.locks }) : StateM TempDirMockState Unit))
          return r
    tryWithFileLock := fun p mode createIfMissing action => do
      let s : TempDirMockState ← get
      match resolveParentTarget s p with
      | .error e => return .error e
      | .ok rp =>
        match lookupNode s.nodes rp with
        | some (.dir _ _) => return .error { kind := .isADirectory, path := some p, message := "is dir" }
        | some (.symlink _ _) => return .error { kind := .invalidInput, path := some p, message := "symlink" }
        | some (.file ino _ _ _) =>
          if mockHasConflict s.locks ino mode then return .ok none
          liftM (set ({ s with locks := (ino, mode) :: s.locks } : TempDirMockState) : StateM TempDirMockState Unit)
          let (r, _) ← tryFinally' action (fun _ =>
            liftM (modify (fun (s' : TempDirMockState) => { s' with locks := mockRemoveFirstLock ino mode s'.locks }) : StateM TempDirMockState Unit))
          return r.map some
        | none =>
          if !createIfMissing then
            return .error { kind := .notFound, path := some p, message := "not found" }
          let ino := freshInode s
          liftM (set ({ s with nodes := (rp, .file ino "" s.nowSec 0o644) :: s.nodes, locks := (ino, mode) :: s.locks, nextInode := ino + 1 } : TempDirMockState) : StateM TempDirMockState Unit)
          let (r, _) ← tryFinally' action (fun _ =>
            liftM (modify (fun (s' : TempDirMockState) => { s' with locks := mockRemoveFirstLock ino mode s'.locks }) : StateM TempDirMockState Unit))
          return r.map some }

/-- Shared proof helper `mockTimeEx`. -/
def mockTimeEx : TimeOpsM (ExceptT String (StateM TempDirMockState)) :=
  { nowTimestamp := liftM mockTime.nowTimestamp
    monoNanosNow := liftM mockTime.monoNanosNow
    sleep := fun ms => liftM (mockTime.sleep ms) }

/-- Shared proof helper `mockUuidEx`. -/
def mockUuidEx : UuidApiM (ExceptT String (StateM TempDirMockState)) :=
  { mapRawError := mockUuid.mapRawError
    fromRandomBytes := mockUuid.fromRandomBytes
    toString := mockUuid.toString
    toHex := mockUuid.toHex
    parse := mockUuid.parse
    parseHex := mockUuid.parseHex
    isValid := mockUuid.isValid
    getUuid := liftM mockUuid.getUuid }

/-- Shared proof helper `mockEnvEx`. -/
def mockEnvEx : EnvVarsApiM (ExceptT String (StateM TempDirMockState)) :=
  { mapRawError := mockEnv.mapRawError
    getEnv := fun k => liftM (mockEnv.getEnv k)
    listEnv := liftM mockEnv.listEnv
    homeDir := liftM mockEnv.homeDir
    splitSearchPath := mockEnv.splitSearchPath }

/-- Shared proof helper `mem_insertSorted`. -/
theorem mem_insertSorted (x y : String) (xs : List String) :
    y ∈ Internal.insertSorted x xs ↔ y = x ∨ y ∈ xs := by
  induction xs with
  | nil => simp [Internal.insertSorted]
  | cons z zs ih =>
    simp only [Internal.insertSorted]
    split
    · simp only [List.mem_cons]
    · simp only [List.mem_cons, ih]
      exact or_left_comm

private theorem pairwise_insertSorted (x : String) (xs : List String)
    (h : List.Pairwise (· ≤ ·) xs) :
    List.Pairwise (· ≤ ·) (Internal.insertSorted x xs) := by
  induction xs with
  | nil => simp [Internal.insertSorted]
  | cons y ys ih =>
    simp only [Internal.insertSorted]
    split
    · next hxy =>
      refine List.Pairwise.cons ?_ h
      intro z hz
      simp only [List.mem_cons] at hz
      rcases hz with rfl | hz
      · exact hxy
      · exact Std.le_trans hxy (List.rel_of_pairwise_cons h hz)
    · next hxy =>
      have hyx : y ≤ x := by
        have hlt : y < x := Classical.byContradiction (fun hny => hxy hny)
        exact Std.Asymm.asymm _ _ hlt
      have hys : List.Pairwise (· ≤ ·) ys := (List.pairwise_cons.mp h).2
      refine List.Pairwise.cons ?_ (ih hys)
      intro z hz
      rw [mem_insertSorted] at hz
      rcases hz with rfl | hz
      · exact hyx
      · exact List.rel_of_pairwise_cons h hz

/-- Shared proof helper `pairwise_sortStrings`. -/
theorem pairwise_sortStrings (xs : List String) :
    List.Pairwise (· ≤ ·) (Internal.sortStrings xs) := by
  induction xs with
  | nil => simp [Internal.sortStrings]
  | cons x xs ih => exact pairwise_insertSorted x _ ih

/-- Shared proof helper `mem_sortStrings`. -/
theorem mem_sortStrings (y : String) (xs : List String) :
    y ∈ Internal.sortStrings xs ↔ y ∈ xs := by
  induction xs with
  | nil => simp [Internal.sortStrings]
  | cons x xs ih =>
    simp only [Internal.sortStrings, mem_insertSorted, List.mem_cons, ih]

private theorem mem_eraseDupStringsAux (seen xs : List String) (y : String) (hNot : y ∉ seen) :
    y ∈ eraseDupStringsAux seen xs ↔ y ∈ xs := by
  induction xs generalizing seen with
  | nil => simp [eraseDupStringsAux]
  | cons x xs ih =>
    simp only [eraseDupStringsAux]
    split
    · next hx =>
      have hne : y ≠ x := fun h => hNot (h ▸ hx)
      simp only [List.mem_cons, hne, false_or]
      exact ih seen hNot
    · next hnx =>
      simp only [List.mem_cons]
      by_cases hyx : y = x
      · subst hyx
        simp
      · simp only [hyx, false_or]
        exact ih (x :: seen) (fun h => by simp only [List.mem_cons, hyx, false_or] at h; exact hNot h)

/-- Shared proof helper `mem_eraseDupStrings`. -/
theorem mem_eraseDupStrings (xs : List String) (y : String) :
    y ∈ eraseDupStrings xs ↔ y ∈ xs :=
  mem_eraseDupStringsAux [] xs y (by simp)

private theorem trimTrailingSlashesRev_ne_nil (cs : List Char) (hne : cs ≠ []) :
    trimTrailingSlashesRev cs ≠ [] := by
  induction cs with
  | nil => exact absurd rfl hne
  | cons c rest ih =>
    cases rest with
    | nil =>
      by_cases h : c = '/' <;> simp [trimTrailingSlashesRev, h]
    | cons d ds =>
      by_cases h : c = '/'
      · subst h
        exact ih (by simp)
      · simp [trimTrailingSlashesRev, h]

/-- Shared proof helper `string_isEmpty_iff_eq_empty`. -/
theorem string_isEmpty_iff_eq_empty (s : String) : s.isEmpty = true ↔ s = "" := by
  simp only [String.isEmpty, beq_iff_eq]
  exact String.utf8ByteSize_eq_zero_iff

/-- Shared proof helper `string_length_pos_of_ne_empty`. -/
theorem string_length_pos_of_ne_empty (s : String) (h : s ≠ "") : 0 < s.length := by
  rw [← String.length_toList]
  cases hl : s.toList with
  | nil => exact absurd (String.toList_eq_nil_iff.mp hl) h
  | cons _ _ => simp

private theorem string_append_ne_empty_right (a b : String) (hb : b ≠ "") : a ++ b ≠ "" := by
  intro h
  have h1 := congrArg String.toList h
  simp only [String.toList_append, String.toList_empty, List.append_eq_nil_iff] at h1
  exact hb (String.toList_eq_nil_iff.mp h1.2)

/-- Shared proof helper `normKey_ne_empty`. -/
theorem normKey_ne_empty (a : String) (ha : a ≠ "") : normKey a ≠ "" := by
  unfold normKey trimSlashChars
  have hrev : a.toList.reverse ≠ [] := by
    intro h
    apply ha
    exact String.toList_eq_nil_iff.mp (List.reverse_eq_nil_iff.mp h)
  have htr := trimTrailingSlashesRev_ne_nil a.toList.reverse hrev
  intro he
  have h1 := congrArg String.toList he
  simp only [String.toList_ofList] at h1
  have hrev0 : trimTrailingSlashesRev a.toList.reverse = [] :=
    List.reverse_eq_nil_iff.mp (by simpa using h1)
  exact htr hrev0

private theorem trimTrailingSlashesRev_of_head_ne_slash (c : Char) (rest : List Char) (hc : c ≠ '/') :
    trimTrailingSlashesRev (c :: rest) = c :: rest := by
  cases rest with
  | nil => simp [trimTrailingSlashesRev, hc]
  | cons d ds => simp [trimTrailingSlashesRev, hc]

private theorem trimTrailingSlashesRev_idem (cs : List Char) :
    trimTrailingSlashesRev (trimTrailingSlashesRev cs) = trimTrailingSlashesRev cs := by
  induction cs with
  | nil => simp [trimTrailingSlashesRev]
  | cons c rest ih =>
    cases rest with
    | nil =>
      by_cases h : c = '/' <;> simp [trimTrailingSlashesRev, h]
    | cons d ds =>
      by_cases h : c = '/'
      · subst h
        exact ih
      · simp [trimTrailingSlashesRev, h]

/-- Shared proof helper `normKey_idem`. -/
theorem normKey_idem (p : String) : normKey (normKey p) = normKey p := by
  unfold normKey trimSlashChars
  simp [String.toList_ofList, List.reverse_reverse, trimTrailingSlashesRev_idem]

/-- Shared proof helper `mockJoin_normKey`. -/
theorem mockJoin_normKey (a b : String) : mockJoin (normKey a) b = mockJoin a b := by
  simp [mockJoin, normKey_idem]

private theorem normKey_of_last_ne_slash (s : String) (c : Char) (rest : List Char)
    (hrev : s.toList.reverse = c :: rest) (hc : c ≠ '/') :
    normKey s = s := by
  unfold normKey trimSlashChars
  rw [hrev, trimTrailingSlashesRev_of_head_ne_slash c rest hc, ← hrev, List.reverse_reverse, String.ofList_toList]

/-- Shared proof helper `normKey_mockJoin`. -/
theorem normKey_mockJoin (a b : String) (hb : b ≠ "") (hslash : '/' ∉ b.toList) :
    normKey (mockJoin a b) = mockJoin a b := by
  have hbRev : ∃ c rest, b.toList.reverse = c :: rest ∧ c ≠ '/' := by
    cases h : b.toList.reverse with
    | nil =>
      have : b.toList = [] := List.reverse_eq_nil_iff.mp h
      exact absurd (by rw [← String.ofList_toList (s := b), this]) hb
    | cons c rest =>
      refine ⟨c, rest, rfl, ?_⟩
      intro hc
      subst hc
      have hmem : '/' ∈ b.toList := List.mem_reverse.mp (by rw [h]; simp)
      exact hslash hmem
  rcases hbRev with ⟨c, rest, hrev, hc⟩
  unfold mockJoin
  dsimp only
  split
  · exact normKey_of_last_ne_slash b c rest hrev hc
  · split
    · have hstr : ("/" : String).toList = ['/'] := rfl
      exact normKey_of_last_ne_slash ("/" ++ b) c (rest ++ ['/'])
        (by rw [String.toList_append, List.reverse_append, hrev, hstr]; rfl) hc
    · have hstr : ("/" : String).toList = ['/'] := rfl
      exact normKey_of_last_ne_slash (normKey a ++ "/" ++ b) c (rest ++ ('/' :: (normKey a).toList.reverse))
        (by rw [String.toList_append, String.toList_append, List.reverse_append, List.reverse_append, hrev, hstr]; rfl) hc

private theorem splitLastSlashRev_append_no_slash (xs ys : List Char) (hno : '/' ∉ xs) :
    splitLastSlashRev (xs.reverse ++ ys) =
      match splitLastSlashRev ys with
      | none => none
      | some (par, base) => some (par, base ++ xs) := by
  have hnoRev : '/' ∉ xs.reverse := fun h => hno (List.mem_reverse.mp h)
  suffices ∀ zs : List Char, '/' ∉ zs →
      splitLastSlashRev (zs ++ ys) =
        match splitLastSlashRev ys with
        | none => none
        | some (par, base) => some (par, base ++ zs.reverse) by
    simpa [List.reverse_reverse] using this xs.reverse hnoRev
  intro zs hzs
  induction zs with
  | nil =>
    simp only [List.nil_append, List.reverse_nil]
    cases splitLastSlashRev ys <;> simp
  | cons z zs ih =>
    have hz : z ≠ '/' := fun h => hzs (h ▸ by simp)
    have hzs' : '/' ∉ zs := fun h => hzs (by simp [h])
    simp only [List.cons_append, splitLastSlashRev, beq_false_of_ne hz, ih hzs']
    cases splitLastSlashRev ys with
    | none => simp
    | some pb => simp [List.reverse_cons, List.append_assoc]

private theorem mockJoin_eq_helper (a b : String) (hna : normKey a ≠ "") :
    mockJoin a b = if normKey a == "/" then "/" ++ b else normKey a ++ "/" ++ b := by
  unfold mockJoin
  have hnaEmpty : (normKey a).isEmpty = false := by
    cases h : (normKey a).isEmpty
    · rfl
    · exact absurd ((string_isEmpty_iff_eq_empty _).mp h) hna
  rw [ite_eq_right]
  intro h; simp [hnaEmpty] at h

/-- Shared proof helper `splitParentChild_mockJoin`. -/
theorem splitParentChild_mockJoin (a b : String) (ha : a ≠ "") (hb : b ≠ "")
    (hslash : '/' ∉ b.toList) :
    splitParentChild (mockJoin a b) = some (normKey a, b) := by
  have hnorm : normKey (mockJoin a b) = mockJoin a b := normKey_mockJoin a b hb hslash
  have hna : normKey a ≠ "" := normKey_ne_empty a ha
  have hbEmpty : b.isEmpty = false := by
    cases h : b.isEmpty
    · rfl
    · exact absurd ((string_isEmpty_iff_eq_empty _).mp h) hb
  have hbListPos : 0 < b.toList.length := by
    cases hl : b.toList with
    | nil => exact absurd (String.toList_eq_nil_iff.mp hl) hb
    | cons _ _ => simp
  have hnaListPos : 0 < (normKey a).toList.length := by
    cases hl : (normKey a).toList with
    | nil => exact absurd (String.toList_eq_nil_iff.mp hl) hna
    | cons _ _ => simp
  have hmj := mockJoin_eq_helper a b hna
  unfold splitParentChild
  dsimp only
  rw [hnorm, hmj]
  by_cases hEq : normKey a = "/"
  · simp only [hEq, beq_self_eq_true, ↓reduceIte]
    have hne1 : (("/" ++ b) == "/") = false := by
      rw [beq_false_of_ne]
      intro h
      have hlen := congrArg (fun s : String => s.toList.length) h
      have h1 : ("/" : String).toList.length = 1 := rfl
      simp only [String.toList_append, List.length_append, h1] at hlen
      omega
    have hne0 : ("/" ++ b).isEmpty = false := by
      cases h : ("/" ++ b).isEmpty
      · rfl
      · exact absurd ((string_isEmpty_iff_eq_empty _).mp h) (string_append_ne_empty_right "/" b hb)
    simp only [hne1, hne0, Bool.or_self, Bool.false_eq_true, ↓reduceIte]
    simp only [String.toList_append, List.reverse_append]
    have hstr : ("/" : String).toList = ['/'] := rfl
    rw [hstr, List.reverse_cons, List.reverse_nil, List.nil_append,
      splitLastSlashRev_append_no_slash b.toList ['/'] hslash]
    simp only [splitLastSlashRev, beq_self_eq_true, ↓reduceIte, List.reverse_nil, List.nil_append,
      List.isEmpty_nil, String.ofList_toList, hbEmpty, Bool.false_eq_true]
  · have hbeq : (normKey a == "/") = false := beq_false_of_ne hEq
    simp only [hbeq, Bool.false_eq_true, ↓reduceIte]
    have hne1 : ((normKey a ++ "/" ++ b) == "/") = false := by
      rw [beq_false_of_ne]
      intro h
      have hlen := congrArg (fun s : String => s.toList.length) h
      have h1 : ("/" : String).toList.length = 1 := rfl
      simp only [String.toList_append, List.length_append, h1] at hlen
      omega
    have hne0 : (normKey a ++ "/" ++ b).isEmpty = false := by
      cases h : (normKey a ++ "/" ++ b).isEmpty
      · rfl
      · exact absurd ((string_isEmpty_iff_eq_empty _).mp h)
          (string_append_ne_empty_right (normKey a ++ "/") b hb)
    simp only [hne1, hne0, Bool.or_self, Bool.false_eq_true, ↓reduceIte]
    simp only [String.toList_append, List.reverse_append, List.append_assoc]
    have hstr : ("/" : String).toList = ['/'] := rfl
    rw [hstr, List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append, List.nil_append,
      splitLastSlashRev_append_no_slash b.toList ('/' :: (normKey a).toList.reverse) hslash]
    simp only [splitLastSlashRev, beq_self_eq_true, ↓reduceIte, List.reverse_reverse, List.nil_append]
    have hnaList : (normKey a).toList.isEmpty = false := by
      cases h : (normKey a).toList
      · exfalso; apply hna
        rw [← String.ofList_toList (s := normKey a), h]
      · rfl
    simp only [hnaList, Bool.false_eq_true, ↓reduceIte, hbEmpty, String.ofList_toList]

private theorem mockUuidToString_ne_empty (u : Uuid) : mockUuidToString u ≠ "" := by
  intro h
  have hlen := congrArg String.length h
  unfold mockUuidToString at hlen
  have h32 : ("00000000-0000-4000-8000-00000000" : String).length = 32 := rfl
  simp only [String.length_append, h32, String.length_empty] at hlen
  omega

private theorem hexDigit_ne_slash :
    ∀ k : Nat, k < 16 → (if k < 10 then Char.ofNat (48 + k) else Char.ofNat (87 + k)) ≠ '/' := by
  decide

private theorem mockHexByte_no_slash (b : UInt8) : '/' ∉ (mockHexByte b).toList := by
  unfold mockHexByte
  simp only [String.toList_ofList, List.mem_cons, List.not_mem_nil, or_false]
  intro h
  have hlt : b.toNat < 256 := UInt8.toNat_lt b
  rcases h with h1 | h1
  · exact hexDigit_ne_slash (b.toNat / 16) (by omega) h1.symm
  · exact hexDigit_ne_slash (b.toNat % 16) (by omega) h1.symm

private theorem mockUuidToString_no_slash (u : Uuid) : '/' ∉ (mockUuidToString u).toList := by
  unfold mockUuidToString
  simp only [String.toList_append, List.mem_append]
  rintro ((h | h) | h)
  · have : '/' ∈ ("00000000-0000-4000-8000-00000000" : String).toList := h
    revert this; decide
  · exact mockHexByte_no_slash _ h
  · exact mockHexByte_no_slash _ h

/-- Shared proof helper `lookupNode_cons_eq`. -/
theorem lookupNode_cons_eq (k : String) (v : MockNode) (nodes : List (String × MockNode)) (p : String)
    (heq : normKey k = normKey p) :
    lookupNode ((k, v) :: nodes) p = some v := by
  simp [lookupNode, heq]

/-- Shared proof helper `lookupNode_cons_ne`. -/
theorem lookupNode_cons_ne (k : String) (v : MockNode) (nodes : List (String × MockNode)) (p : String)
    (hne : normKey k ≠ normKey p) :
    lookupNode ((k, v) :: nodes) p = lookupNode nodes p := by
  simp [lookupNode, beq_false_of_ne hne]

/-- Shared proof helper `lookupNode_filter_underDir_eq`. -/
theorem lookupNode_filter_underDir_eq (nodes : List (String × MockNode)) (rp : String)
    (hnorm : normKey rp = rp) :
    lookupNode (nodes.filter (fun e => !underDir rp e.1)) rp = none := by
  unfold lookupNode
  rw [hnorm]
  induction nodes with
  | nil => simp
  | cons x xs ih =>
    simp only [List.filter_cons]
    split
    · next hkeep =>
      have hne : (normKey x.1 == rp) = false := by
        rw [beq_false_of_ne]
        intro hEq
        simp only [underDir, hnorm, hEq, beq_self_eq_true, Bool.true_or, Bool.not_true] at hkeep
        exact Bool.noConfusion hkeep
      simpa [List.find?_cons, hne] using ih
    · exact ih

/-- Shared proof helper `lookupNode_filter_of_preserved`. -/
theorem lookupNode_filter_of_preserved (nodes : List (String × MockNode))
    (pred : (String × MockNode) → Bool) (p : String)
    (hpres : ∀ e ∈ nodes, normKey e.1 = normKey p → pred e = true) :
    lookupNode (nodes.filter pred) p = lookupNode nodes p := by
  unfold lookupNode
  dsimp only
  induction nodes with
  | nil => simp
  | cons x xs ih =>
    have ih' := ih (fun e he h => hpres e (by simp [he]) h)
    rw [List.filter_cons]
    split
    · next hx =>
      rw [List.find?_cons, List.find?_cons]
      split
      · rfl
      · simpa using ih'
    · next hnx =>
      have hne : (normKey x.1 == normKey p) = false := by
        rw [beq_false_of_ne]
        intro hEq
        have := hpres x (by simp) hEq
        exact hnx this
      rw [List.find?_cons, hne]
      exact ih'

private theorem validPrefix_parts (p : String) (h : (!p.isEmpty && p.toList.head? != some '.' && !('/' ∈ p.toList) && !(Char.ofNat 0 ∈ p.toList)) = true) :
    p ≠ "" ∧ '/' ∉ p.toList := by
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at h
  have hpEmpty : p.isEmpty = false := h.1.1.1
  have hslash : '/' ∉ p.toList := by
    intro hm
    have hb : decide ('/' ∈ p.toList) = true := decide_eq_true hm
    have hfalse : decide ('/' ∈ p.toList) = false := h.1.2
    rw [hb] at hfalse
    exact Bool.noConfusion hfalse
  have hne : p ≠ "" := fun he => by rw [he] at hpEmpty; simp [String.isEmpty] at hpEmpty
  exact ⟨hne, hslash⟩

/-- Shared proof helper `validRoot_ne_empty`. -/
theorem validRoot_ne_empty (r : String) (h : (!r.isEmpty && !(Char.ofNat 0 ∈ r.toList)) = true) :
    r ≠ "" := by
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at h
  intro he
  rw [he] at h
  simp [String.isEmpty] at h

/-- Shared proof helper `childName_parts`. -/
theorem childName_parts (dirPrefix : String) (u : Uuid)
    (hvp : (!dirPrefix.isEmpty && dirPrefix.toList.head? != some '.' && !('/' ∈ dirPrefix.toList) && !(Char.ofNat 0 ∈ dirPrefix.toList)) = true) :
    (dirPrefix ++ mockUuidToString u) ≠ "" ∧ '/' ∉ (dirPrefix ++ mockUuidToString u).toList := by
  have ⟨hne, hno⟩ := validPrefix_parts dirPrefix hvp
  refine ⟨string_append_ne_empty_right dirPrefix (mockUuidToString u) (mockUuidToString_ne_empty u), ?_⟩
  rw [String.toList_append]
  intro h
  rcases List.mem_append.mp h with hm | hm
  · exact hno hm
  · exact mockUuidToString_no_slash u hm

/-- Shared proof helper `hasWx_of_hasRwx`. -/
theorem hasWx_of_hasRwx (st : FileStat)
    (h : st.kind = .dir ∧ (st.mode / 256) % 2 = 1 ∧ (st.mode / 128) % 2 = 1 ∧ (st.mode / 64) % 2 = 1) :
    hasWx st = true := by
  simp only [hasWx, h.1, h.2.2.1, h.2.2.2]
  decide

/-- Shared proof helper `hasRx_of_hasRwx`. -/
theorem hasRx_of_hasRwx (st : FileStat)
    (h : st.kind = .dir ∧ (st.mode / 256) % 2 = 1 ∧ (st.mode / 128) % 2 = 1 ∧ (st.mode / 64) % 2 = 1) :
    hasRx st = true := by
  simp only [hasRx, h.1, h.2.1, h.2.2.2]
  decide

/-- Shared proof helper `stateM_bind_run`. -/
theorem stateM_bind_run {S α β : Type} (x : StateM S α) (f : α → StateM S β) (s : S) :
    (x >>= f).run s = (f (x.run s).1).run (x.run s).2 := rfl

/-- Shared proof helper `stateM_get_run`. -/
theorem stateM_get_run {S : Type} (s : S) : (get : StateM S S).run s = (s, s) := rfl

/-- Shared proof helper `stateM_set_run`. -/
theorem stateM_set_run {S : Type} (s' s : S) : (set s' : StateM S Unit).run s = ((), s') := rfl

private theorem stateM_modify_run {S : Type} (f : S → S) (s : S) :
    (modify f : StateM S Unit).run s = ((), f s) := rfl

/-- Shared proof helper `stateM_pure_run`. -/
theorem stateM_pure_run {S α : Type} (a : α) (s : S) :
    (pure a : StateM S α).run s = (a, s) := rfl

/-- Shared proof helper `mockJoin_ne_root`. -/
theorem mockJoin_ne_root (root child : String) (hr : root ≠ "") (hc : child ≠ "")
    (hslash : '/' ∉ child.toList) :
    normKey (mockJoin root child) ≠ normKey root := by
  intro heq
  have hnorm : normKey (mockJoin root child) = mockJoin root child := normKey_mockJoin root child hc hslash
  rw [hnorm] at heq
  have h1 := congrArg (fun s : String => s.toList.length) heq
  have hcpos : 0 < child.toList.length := by
    rw [String.length_toList]; exact string_length_pos_of_ne_empty child hc
  have hnr : normKey root ≠ "" := normKey_ne_empty root hr
  have hnrEmpty : (normKey root).isEmpty = false := by
    cases h : (normKey root).isEmpty
    · rfl
    · exact absurd ((string_isEmpty_iff_eq_empty _).mp h) hnr
  unfold mockJoin at h1
  dsimp only at h1
  rw [hnrEmpty] at h1
  simp only [Bool.false_eq_true, ↓reduceIte] at h1
  split at h1
  · next hSlash =>
    have hEq : normKey root = "/" := beq_iff_eq.mp hSlash
    rw [hEq] at h1
    have hlen1 : ("/" : String).toList.length = 1 := rfl
    simp only [String.toList_append, List.length_append, hlen1] at h1
    omega
  · simp only [String.toList_append, List.length_append] at h1
    have hlen1 : ("/" : String).toList.length = 1 := rfl
    rw [hlen1] at h1
    omega

/-- Shared proof helper `list_map_id_of_mem`. -/
theorem list_map_id_of_mem {α : Type} (xs : List α) (f : α → α)
    (h : ∀ x ∈ xs, f x = x) : xs.map f = xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.map_cons, h x (by simp), ih (fun y hy => h y (by simp [hy]))]

/-- Shared proof helper `resolveRoot_some_mock_run`. -/
theorem resolveRoot_some_mock_run (s₀ : TempDirMockState) (root : String)
    (hvr : (!root.isEmpty && !(Char.ofNat 0 ∈ root.toList)) = true)
    (stRoot : FileStat) (hRoot : mockStatPure s₀ root = .ok stRoot)
    (hDir : stRoot.kind = .dir) :
    (Internal.resolveRoot mockFs mockEnv (some root)).run s₀ = (.ok root, s₀) := by
  have hvr' : Internal.validRoot root = true := by simpa [Internal.validRoot] using hvr
  have hStatStep : (mockFs.stat root).run s₀ = (.ok stRoot, s₀) := by
    simp [mockFs, hRoot]; rfl
  dsimp only [Internal.resolveRoot]
  rw [stateM_bind_run, stateM_pure_run]
  dsimp only
  simp only [hvr', Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  rw [stateM_bind_run, hStatStep]
  simp only [hDir, show (EntryKind.dir != EntryKind.dir) = false from rfl,
    Bool.false_eq_true, ↓reduceIte, stateM_pure_run]

/-- Shared proof helper `createTempDir_mock_steps`. -/
theorem createTempDir_mock_steps (s₀ : TempDirMockState) (root dirPrefix : String)
    (hvr : (!root.isEmpty && !(Char.ofNat 0 ∈ root.toList)) = true)
    (hvp : (!dirPrefix.isEmpty && dirPrefix.toList.head? != some '.' && !('/' ∈ dirPrefix.toList) && !(Char.ofNat 0 ∈ dirPrefix.toList)) = true)
    (stRoot : FileStat)
    (hRoot : mockStatPure s₀ root = .ok stRoot)
    (hRwx : stRoot.kind = .dir ∧ (stRoot.mode / 256) % 2 = 1 ∧ (stRoot.mode / 128) % 2 = 1 ∧ (stRoot.mode / 64) % 2 = 1)
    (hNone : (mockLstatPure { s₀ with nextUuid := s₀.nextUuid + 1 }
      (mockJoin root (dirPrefix ++ mockUuidToString (mockUuidOfNat s₀.nextUuid)))).isOk = false) :
    let u := mockUuidOfNat s₀.nextUuid
    let dir := mockJoin root (dirPrefix ++ mockUuidToString u)
    let sMk := { s₀ with
      nextUuid := s₀.nextUuid + 1
      nodes := (dir, .dir s₀.nowSec 0o700) :: s₀.nodes.filter (fun e => !underDir dir e.1) }
    (Internal.createTempDir mockFs mockUuid mockEnv (some root) dirPrefix).run s₀ = (.ok dir, sMk) := by
  intro u dir sMk
  have hrNe : root ≠ "" := validRoot_ne_empty root hvr
  have ⟨hcNe, hcNoSlash⟩ := childName_parts dirPrefix u hvp
  have hDirNorm : normKey dir = dir := normKey_mockJoin root _ hcNe hcNoSlash
  have hSp : splitParentChild dir = some (normKey root, dirPrefix ++ mockUuidToString u) :=
    splitParentChild_mockJoin root _ hrNe hcNe hcNoSlash
  have hJoinNorm : mockJoin (normKey root) (dirPrefix ++ mockUuidToString u) = dir :=
    mockJoin_normKey root (dirPrefix ++ mockUuidToString u)
  have hLookRoot : ∃ rootNode, lookupNode s₀.nodes root = some rootNode ∧ mockNodeStat rootNode = stRoot := by
    unfold mockStatPure mockLstatPure at hRoot
    cases hl : lookupNode s₀.nodes root with
    | none => simp [hl] at hRoot
    | some rn =>
      simp only [hl, Except.ok.injEq] at hRoot
      exact ⟨rn, rfl, hRoot⟩
  rcases hLookRoot with ⟨rootNode, hLookRoot, hStRoot⟩
  have hLookRootNorm : lookupNode s₀.nodes (normKey root) = some rootNode := by
    simpa [lookupNode, normKey_idem] using hLookRoot
  have hLookDirNone : lookupNode s₀.nodes dir = none := by
    unfold mockLstatPure at hNone
    cases hl : lookupNode s₀.nodes dir with
    | none => rfl
    | some dn =>
      rw [hl] at hNone
      simp [Except.toBool] at hNone
  have hvr' : Internal.validRoot root = true := by simpa [Internal.validRoot] using hvr
  have hvp' : Internal.validPrefix dirPrefix = true := by simpa [Internal.validPrefix] using hvp
  have hWx : hasWx stRoot = true := hasWx_of_hasRwx stRoot hRwx
  have hMk : (mockFs.mkdir dir false false).run { s₀ with nextUuid := s₀.nextUuid + 1 } =
      (.ok (), { s₀ with
        nextUuid := s₀.nextUuid + 1
        nodes := (dir, .dir s₀.nowSec 0o755) :: s₀.nodes.filter (fun e => !underDir dir e.1) }) := by
    dsimp only [mockFs]
    rw [stateM_bind_run, stateM_get_run]
    dsimp only
    rw [hSp]
    dsimp only
    rw [hLookRootNorm]
    dsimp only
    rw [hStRoot]
    simp only [hRwx.1, show (EntryKind.dir != EntryKind.dir) = false from rfl,
      Bool.false_eq_true, ↓reduceIte, hWx, Bool.not_true, hJoinNorm]
    rw [hLookDirNone]
    simp only [stateM_bind_run, stateM_set_run, stateM_pure_run]
  have hCh : (mockFs.chmod dir 0o700).run
      { s₀ with
        nextUuid := s₀.nextUuid + 1
        nodes := (dir, .dir s₀.nowSec 0o755) :: s₀.nodes.filter (fun e => !underDir dir e.1) } =
      (.ok (), sMk) := by
    dsimp only [mockFs, resolveParentTarget]
    rw [stateM_bind_run, stateM_get_run]
    dsimp only
    rw [hDirNorm]
    have hLook : lookupNode ((dir, MockNode.dir s₀.nowSec 0o755) :: s₀.nodes.filter (fun e => !underDir dir e.1)) dir =
        some (MockNode.dir s₀.nowSec 0o755) :=
      lookupNode_cons_eq _ _ _ _ rfl
    rw [hLook]
    simp only [stateM_bind_run, stateM_set_run, stateM_pure_run]
    have hMapId : (s₀.nodes.filter (fun e => !underDir dir e.1)).map
        (fun x => if normKey x.1 == dir then (x.1, match x.2 with
          | MockNode.dir t _ => MockNode.dir t 0o700
          | MockNode.file ino c t _ => MockNode.file ino c t 0o700
          | MockNode.symlink tgt t => MockNode.symlink tgt t) else x) =
        s₀.nodes.filter (fun e => !underDir dir e.1) := by
      apply list_map_id_of_mem
      intro x hx
      have hKeep := (List.mem_filter.mp hx).2
      have hne : (normKey x.1 == dir) = false := by
        rw [beq_false_of_ne]
        intro hEq
        simp only [underDir, hDirNorm, hEq, beq_self_eq_true, Bool.true_or, Bool.not_true] at hKeep
        exact Bool.noConfusion hKeep
      simp [hne]
    show (Except.ok (), {
      nodes := List.map (fun x => if (normKey x.1 == dir) = true then _ else x)
        ((dir, MockNode.dir s₀.nowSec 0o755) :: s₀.nodes.filter (fun e => !underDir dir e.1)),
      locks := s₀.locks, nextInode := s₀.nextInode, tmpdir := s₀.tmpdir, nowSec := s₀.nowSec,
      nextUuid := s₀.nextUuid + 1 }) = (Except.ok (), sMk)
    simp only [List.map_cons, hDirNorm, beq_self_eq_true, ↓reduceIte, hMapId]
    rfl
  have hResStep := resolveRoot_some_mock_run s₀ root hvr stRoot hRoot hRwx.1
  have hUuidStep : mockUuid.getUuid.run s₀ = (.ok u, { s₀ with nextUuid := s₀.nextUuid + 1 }) := by
    simp [mockUuid, u]; rfl
  dsimp only [Internal.createTempDir]
  simp only [hvp', Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  rw [stateM_bind_run, hResStep]
  dsimp only
  rw [stateM_bind_run, hUuidStep]
  dsimp only
  have hDirEq : mockFs.join root (dirPrefix ++ mockUuid.toString u) = dir := rfl
  simp only [hDirEq]
  rw [stateM_bind_run, hMk]
  rw [stateM_bind_run, hCh]
  rw [stateM_pure_run]

/-- Shared proof helper `cleanupDir_mock_run`. -/
theorem cleanupDir_mock_run (s : TempDirMockState) (dir : String) (hnorm : normKey dir = dir)
    (hnode : ∃ m mode, lookupNode s.nodes dir = some (.dir m mode)) :
    (Internal.cleanupDirIgnoringNotFound mockFs dir).run s =
      (.ok (), { s with nodes := s.nodes.filter (fun e => !underDir dir e.1) }) := by
  rcases hnode with ⟨m, mode, hLook⟩
  dsimp only [Internal.cleanupDirIgnoringNotFound, mockFs, mockRmtreePure, resolveParentTarget]
  rw [stateM_bind_run, stateM_bind_run, stateM_get_run]
  dsimp only
  rw [hnorm, hLook]
  simp only [stateM_bind_run, stateM_set_run, stateM_pure_run]

/-- Shared proof helper `mockFs_lstat_run`. -/
theorem mockFs_lstat_run (s : TempDirMockState) (p : String) :
    (mockFs.lstat p).run s = (mockLstatPure s p, s) := by
  simp [mockFs]; rfl

/-- Shared proof helper `mockFs_writeText_run`. -/
theorem mockFs_writeText_run (s : TempDirMockState) (p c : String) :
    (mockFs.writeText p c).run s =
      (.ok (), { s with
        nodes := (normKey p, .file (freshInode s) c s.nowSec 0o644) :: s.nodes.filter (fun e => normKey e.1 != normKey p)
        nextInode := freshInode s + 1 }) := by
  dsimp only [mockFs, resolveParentTarget]
  rw [stateM_bind_run, stateM_get_run]
  simp only [stateM_bind_run, stateM_set_run, stateM_pure_run]

/-- Shared proof helper `mkApiM_withTempDir_eq`. -/
theorem mkApiM_withTempDir_eq {m : Type → Type} {α : Type} [Monad m] [MonadFinally m]
    (fs : FsApiM m) (time : TimeOpsM m) (uuid : UuidApiM m) (env : EnvVarsApiM m)
    (root? : Option String) (dirPrefix : String) (action : String → m (Except TempDirError α)) :
    (Internal.mkApiM fs time uuid env).withTempDir root? dirPrefix action =
      Internal.withTempDirM fs uuid env root? dirPrefix action := rfl

/-- Shared proof helper `mkApiM_withLockedTempDir_eq`. -/
theorem mkApiM_withLockedTempDir_eq {m : Type → Type} {α : Type} [Monad m] [MonadFinally m]
    (fs : FsApiM m) (time : TimeOpsM m) (uuid : UuidApiM m) (env : EnvVarsApiM m)
    (root? : Option String) (dirPrefix : String) (action : String → m (Except TempDirError α)) :
    (Internal.mkApiM fs time uuid env).withLockedTempDir root? dirPrefix action =
      Internal.withLockedTempDirM fs uuid env root? dirPrefix action := rfl

/-- Shared proof helper `mkApiM_cleanupStaleTempDirs_eq`. -/
theorem mkApiM_cleanupStaleTempDirs_eq {m : Type → Type} [Monad m] [MonadFinally m]
    (fs : FsApiM m) (time : TimeOpsM m) (uuid : UuidApiM m) (env : EnvVarsApiM m)
    (root? : Option String) (dirPrefix : String) (maxAgeSec : Nat) :
    (Internal.mkApiM fs time uuid env).cleanupStaleTempDirs root? dirPrefix maxAgeSec =
      Internal.cleanupStaleTempDirsM fs time env root? dirPrefix maxAgeSec := rfl

/-- Shared proof helper `mockFs_stat_run`. -/
theorem mockFs_stat_run (s : TempDirMockState) (p : String) :
    (mockFs.stat p).run s = (mockStatPure s p, s) := by
  simp [mockFs]; rfl

/-- Shared proof helper `mockFs_lstat_isOk_false_of_lookup_none`. -/
theorem mockFs_lstat_isOk_false_of_lookup_none (s : TempDirMockState) (p : String)
    (h : lookupNode s.nodes p = none) :
    ((mockFs.lstat p).run s).1.isOk = false := by
  rw [mockFs_lstat_run]
  simp [mockLstatPure, h, Except.isOk, Except.toBool]

/-- Shared proof helper `lookupNode_of_lstat_ok`. -/
theorem lookupNode_of_lstat_ok (s : TempDirMockState) (p : String) (st : FileStat)
    (h : mockLstatPure s p = .ok st) :
    ∃ nd, lookupNode s.nodes p = some nd ∧ mockNodeStat nd = st := by
  unfold mockLstatPure at h
  cases hl : lookupNode s.nodes p with
  | none => simp [hl] at h
  | some nd =>
    simp only [hl, Except.ok.injEq] at h
    exact ⟨nd, rfl, h⟩

private theorem lookupNode_none_of_lstat_error (s : TempDirMockState) (p : String) (e : FsError)
    (h : mockLstatPure s p = .error e) :
    lookupNode s.nodes p = none ∧ e.kind = .notFound := by
  unfold mockLstatPure at h
  cases hl : lookupNode s.nodes p with
  | none =>
    simp only [hl, Except.error.injEq] at h
    exact ⟨rfl, by rw [← h]⟩
  | some nd => simp [hl] at h

/-- Shared proof helper `underDir_refl`. -/
theorem underDir_refl (d : String) (hn : normKey d = d) :
    underDir d d = true := by
  simp [underDir, hn]

private theorem takeWhile_ne_slash_append (xs ys : List Char) (hno : ¬('/' ∈ xs)) :
    (xs ++ '/' :: ys).takeWhile (· != '/') = xs := by
  induction xs with
  | nil => rfl
  | cons c cs ih =>
    have hc : (c != '/') = true := bne_iff_ne.mpr (fun h => hno (by simp [h]))
    have hcs : ¬('/' ∈ cs) := fun h => hno (by simp [h])
    simp only [List.cons_append, List.takeWhile_cons, hc, ↓reduceIte, ih hcs]

private theorem takeWhile_ne_slash_eq_self (xs : List Char) (hno : ¬('/' ∈ xs)) :
    xs.takeWhile (· != '/') = xs := by
  induction xs with
  | nil => rfl
  | cons c cs ih =>
    have hc : (c != '/') = true := bne_iff_ne.mpr (fun h => hno (by simp [h]))
    have hcs : ¬('/' ∈ cs) := fun h => hno (by simp [h])
    simp only [List.takeWhile_cons, hc, ↓reduceIte, ih hcs]

private theorem takeWhile_of_underDir_join (pfx nm rest : List Char)
    (hno : ¬('/' ∈ nm))
    (hpref : rest = pfx ++ nm ∨ ((pfx ++ nm) ++ ['/']).isPrefixOf rest = true) :
    (rest.drop pfx.length).takeWhile (· != '/') = nm := by
  rcases hpref with rfl | hp
  · rw [List.drop_left]
    exact takeWhile_ne_slash_eq_self nm hno
  · obtain ⟨t, ht⟩ := List.isPrefixOf_iff_prefix.mp hp
    rw [← ht]
    have hdrop : ((pfx ++ nm ++ ['/']) ++ t).drop pfx.length = nm ++ '/' :: t := by
      simp [List.append_assoc]
    rw [hdrop]
    exact takeWhile_ne_slash_append nm t hno

/-- Shared proof helper `mockJoin_eq_append_of_ne_empty`. -/
theorem mockJoin_eq_append_of_ne_empty (root nm : String) (hr : root ≠ "") :
    let nr := normKey root
    let pfx := if nr == "/" then ['/'] else nr.toList ++ ['/']
    (mockJoin root nm).toList = pfx ++ nm.toList := by
  have hnr : normKey root ≠ "" := normKey_ne_empty root hr
  have hnrEmpty : (normKey root).isEmpty = false := by
    cases h : (normKey root).isEmpty with
    | false => rfl
    | true => exact absurd ((string_isEmpty_iff_eq_empty _).mp h) hnr
  by_cases hslash : normKey root == "/"
  · simp [mockJoin, hnrEmpty, hslash, String.toList_append]
  · simp [mockJoin, hnrEmpty, hslash, String.toList_append]

/-- Shared proof helper `mockJoin_ne_slash`. -/
theorem mockJoin_ne_slash (root nm : String) (hr : root ≠ "") (hnm : nm ≠ "") :
    mockJoin root nm ≠ "/" := by
  have hlist := mockJoin_eq_append_of_ne_empty root nm hr
  intro heq
  have hl := congrArg String.toList heq
  rw [hlist] at hl
  have hpos : 0 < nm.toList.length := by
    rw [String.length_toList]
    exact string_length_pos_of_ne_empty nm hnm
  have hlen := congrArg List.length hl
  simp only [List.length_append, show ("/" : String).toList = ['/'] from rfl, List.length_singleton] at hlen
  have hne : (if (normKey root == "/") = true then ['/'] else (normKey root).toList ++ ['/']).length ≥ 1 := by
    split <;> simp
  omega

private theorem underDir_mockJoin_sub (root nm p : String) (hr : root ≠ "") (hnm : nm ≠ "")
    (hno : ¬('/' ∈ nm.toList)) (hu : underDir (mockJoin root nm) p = true) :
    let nr := normKey root
    let pfx := if nr == "/" then ['/'] else nr.toList ++ ['/']
    ((normKey p).toList.drop pfx.length).takeWhile (· != '/') = nm.toList := by
  have hdn : normKey (mockJoin root nm) = mockJoin root nm := normKey_mockJoin root nm hnm hno
  have hdne : mockJoin root nm ≠ "/" := mockJoin_ne_slash root nm hr hnm
  have hdb : (mockJoin root nm == "/") = false := beq_false_of_ne hdne
  simp only [underDir, hdn, hdb, Bool.or_eq_true, beq_iff_eq] at hu
  have hlist := mockJoin_eq_append_of_ne_empty root nm hr
  apply takeWhile_of_underDir_join _ _ _ hno
  rcases hu with hEq | hPref
  · left; rw [hEq, hlist]
  · right
    simp only [Bool.false_eq_true, ↓reduceIte] at hPref
    rwa [String.toList_append, hlist, show ("/" : String).toList = ['/'] from rfl] at hPref

/-- Shared proof helper `disjoint_underDir_mockJoin`. -/
theorem disjoint_underDir_mockJoin (root n1 n2 p : String)
    (hr : root ≠ "") (hn1 : n1 ≠ "") (hn2 : n2 ≠ "")
    (hno1 : ¬('/' ∈ n1.toList)) (hno2 : ¬('/' ∈ n2.toList)) (hne : n1 ≠ n2)
    (hu1 : underDir (mockJoin root n1) p = true)
    (hu2 : underDir (mockJoin root n2) p = true) : False := by
  have h1 := underDir_mockJoin_sub root n1 p hr hn1 hno1 hu1
  have h2 := underDir_mockJoin_sub root n2 p hr hn2 hno2 hu2
  have heq : n1.toList = n2.toList := h1.symm.trans h2
  exact hne (String.toList_inj.mp heq)

/-- Shared proof helper `not_underDir_mockJoin_root`. -/
theorem not_underDir_mockJoin_root (root nm p : String)
    (hr : root ≠ "") (hnm : nm ≠ "") (hno : ¬('/' ∈ nm.toList))
    (hp : normKey p = normKey root) :
    underDir (mockJoin root nm) p = false := by
  by_cases hu : underDir (mockJoin root nm) p = true
  · exfalso
    have hdn : normKey (mockJoin root nm) = mockJoin root nm := normKey_mockJoin root nm hnm hno
    have hdne : mockJoin root nm ≠ "/" := mockJoin_ne_slash root nm hr hnm
    have hdb : (mockJoin root nm == "/") = false := beq_false_of_ne hdne
    simp only [underDir, hdn, hdb, Bool.or_eq_true, beq_iff_eq, hp] at hu
    have hlist := mockJoin_eq_append_of_ne_empty root nm hr
    have hpos : 0 < nm.toList.length := by
      rw [String.length_toList]; exact string_length_pos_of_ne_empty nm hnm
    rcases hu with hEq | hPref
    · have hlen := congrArg List.length (congrArg String.toList hEq)
      rw [hlist, List.length_append] at hlen
      split at hlen <;> simp_all <;> omega
    · simp only [Bool.false_eq_true, ↓reduceIte] at hPref
      have hsub := List.IsPrefix.length_le (List.isPrefixOf_iff_prefix.mp hPref)
      rw [String.toList_append, hlist, List.length_append, List.length_append] at hsub
      have hlenSlash : ("/" : String).toList.length = 1 := rfl
      rw [hlenSlash] at hsub
      split at hsub <;> simp_all <;> omega
  · cases h : underDir (mockJoin root nm) p with
    | false => rfl
    | true => exact absurd h hu

/-- Shared proof helper `underDir_mockJoin_child`. -/
theorem underDir_mockJoin_child (dir nm p : String)
    (hd : dir ≠ "") (hdn : normKey dir = dir) (hds : dir ≠ "/")
    (hnm : nm ≠ "") (hno : ¬('/' ∈ nm.toList))
    (hu : underDir (mockJoin dir nm) p = true) :
    underDir dir p = true := by
  have hdn2 : normKey (mockJoin dir nm) = mockJoin dir nm := normKey_mockJoin dir nm hnm hno
  have hdne2 : mockJoin dir nm ≠ "/" := mockJoin_ne_slash dir nm hd hnm
  have hdb2 : (mockJoin dir nm == "/") = false := beq_false_of_ne hdne2
  have hdb : (dir == "/") = false := beq_false_of_ne hds
  have hlist : mockJoin dir nm = dir ++ "/" ++ nm := by
    have hde : dir.isEmpty = false := by
      cases h : dir.isEmpty with
      | false => rfl
      | true => exact absurd ((string_isEmpty_iff_eq_empty _).mp h) hd
    simp [mockJoin, hdn, hde, hdb, String.append_assoc]
  simp only [underDir, hdn, hdb, hdn2, hdb2, Bool.or_eq_true, beq_iff_eq] at hu ⊢
  right
  rcases hu with hEq | hPref
  · rw [hEq, hlist]
    simp [String.toList_append]
  · rw [hlist] at hPref
    have hp := List.isPrefixOf_iff_prefix.mp hPref
    apply List.isPrefixOf_iff_prefix.mpr
    have hsub : (dir ++ "/").toList <+: (dir ++ "/" ++ nm ++ "/").toList := by
      simp [String.toList_append, List.append_assoc]
    exact hsub.trans hp

/-- Shared proof helper `underDir_mockJoin_self`. -/
theorem underDir_mockJoin_self (dir nm : String)
    (hd : dir ≠ "") (hdn : normKey dir = dir) (hds : dir ≠ "/")
    (hnm : nm ≠ "") (hno : ¬('/' ∈ nm.toList)) :
    underDir dir (mockJoin dir nm) = true :=
  underDir_mockJoin_child dir nm (mockJoin dir nm) hd hdn hds hnm hno
    (underDir_refl _ (normKey_mockJoin dir nm hnm hno))

/-- Shared proof helper `underDir_eq_of_normKey_eq`. -/
theorem underDir_eq_of_normKey_eq (d a b : String) (h : normKey a = normKey b) :
    underDir d a = underDir d b := by
  simp [underDir, h]

private theorem lookupNode_of_filter_eq (nodes1 nodes2 : List (String × MockNode)) (d p : String)
    (hf : nodes1.filter (fun e => !underDir d e.1) = nodes2.filter (fun e => !underDir d e.1))
    (hu : underDir d p = false) :
    lookupNode nodes1 p = lookupNode nodes2 p := by
  have hfin : ∀ nodes : List (String × MockNode),
      nodes.find? (fun e => normKey e.1 == normKey p) =
      (nodes.filter (fun e => !underDir d e.1)).find? (fun e => normKey e.1 == normKey p) := by
    intro nodes
    induction nodes with
    | nil => rfl
    | cons x xs ih =>
      by_cases hxp : (normKey x.1 == normKey p) = true
      · have hnp : normKey x.1 = normKey p := beq_iff_eq.mp hxp
        have hux : (!underDir d x.1) = true := by
          rw [underDir_eq_of_normKey_eq d x.1 p hnp, hu]; rfl
        simp [hux, hxp]
      · have hxp' : (normKey x.1 == normKey p) = false := Bool.eq_false_iff.mpr hxp
        by_cases hux : (!underDir d x.1) = true
        · simp [hux, hxp', ih]
        · have hux' : (!underDir d x.1) = false := Bool.eq_false_iff.mpr hux
          simp [hux', hxp', ih]
  unfold lookupNode
  dsimp only
  rw [hfin nodes1, hfin nodes2, hf]

/-- Shared proof helper `mockJoin_ne_empty`. -/
theorem mockJoin_ne_empty (a b : String) (hb : b ≠ "") : mockJoin a b ≠ "" := by
  dsimp only [mockJoin]
  split
  · exact hb
  · split <;> exact string_append_ne_empty_right _ b hb

/-- Shared proof helper `validEntryName_of_mockParentChild`. -/
theorem validEntryName_of_mockParentChild (dir full rest : String)
    (h : mockParentChild dir full = some rest) :
    (!rest.isEmpty && rest != "." && rest != ".." && !('/' ∈ rest.toList) && !(Char.ofNat 0 ∈ rest.toList)) = true := by
  unfold mockParentChild at h
  dsimp only at h
  generalize (if (normKey dir).isEmpty then "" else if normKey dir == "/" then "/" else normKey dir ++ "/") = pref at h
  split at h
  · split at h
    · next hcond =>
      simp only [Option.some.injEq] at h
      rw [← h]
      exact hcond
    · contradiction
  · contradiction

private theorem underDir_of_mockParentChild (dir full rest : String)
    (h : mockParentChild dir full = some rest) (hd : dir ≠ "") :
    underDir dir full = true := by
  have hdn : normKey dir ≠ "" := normKey_ne_empty dir hd
  have hde : (normKey dir).isEmpty = false := by
    cases hb : (normKey dir).isEmpty with
    | false => rfl
    | true => exact absurd ((string_isEmpty_iff_eq_empty _).mp hb) hdn
  unfold mockParentChild at h
  simp only [underDir]
  generalize hnd : normKey dir = nd at h ⊢
  rw [hnd] at hde
  generalize normKey full = nf at h ⊢
  dsimp only at h
  simp only [hde, Bool.false_eq_true, ↓reduceIte] at h
  cases hslash : (nd == "/") <;> simp only [hslash, Bool.false_eq_true, ↓reduceIte] at h ⊢
  · split at h
    · next hpref =>
      simp only [Bool.or_eq_true, beq_iff_eq]
      right
      exact hpref
    · contradiction
  · split at h
    · next hpref =>
      simp only [Bool.or_eq_true, beq_iff_eq]
      right
      exact hpref
    · contradiction

private theorem allPass_bind {α β : Type} (a : AllPassRun α) (k : α → AllPassRun β) (post : β → Prop) :
    (a >>= k) post = a (fun x => k x post) := rfl

/-- Shared proof helper `allPass_assume`. -/
theorem allPass_assume {β : Type} (p : Prop) (k : Unit → AllPassRun β) (post : β → Prop) :
    (assume p >>= k) post = (p → k () post) := rfl

/-- Shared proof helper `allPass_assert`. -/
theorem allPass_assert {β : Type} (p : Prop) (k : Unit → AllPassRun β) (post : β → Prop) :
    (assert p >>= k) post = (p ∧ k () post) := rfl

/-- Shared proof helper `allPass_assert_end`. -/
theorem allPass_assert_end (p : Prop) :
    (assert p : AllPassRun Unit) (fun _ => True) = (p ∧ True) := rfl

private theorem canReach_bind {α β : Type} (a : CanReachRun α) (k : α → CanReachRun β) (post : β → Prop) :
    (a >>= k) post = a (fun x => k x post) := rfl

/-- Shared proof helper `canReach_nondet`. -/
theorem canReach_nondet {α β : Type} (k : α → CanReachRun β) (post : β → Prop) :
    (NondetTest.nondet α >>= k) post = ∃ x : α, k x post := rfl

/-- Shared proof helper `canReach_assume`. -/
theorem canReach_assume {β : Type} (p : Prop) (k : Unit → CanReachRun β) (post : β → Prop) :
    (assume p >>= k) post = (p ∧ k () post) := rfl

/-- Shared proof helper `canReach_assert`. -/
theorem canReach_assert {β : Type} (p : Prop) (k : Unit → CanReachRun β) (post : β → Prop) :
    (assert p >>= k) post = (p ∧ k () post) := rfl

/-- Shared proof helper `canReach_assert_end`. -/
theorem canReach_assert_end (p : Prop) :
    (assert p : CanReachRun Unit) (fun _ => True) = (p ∧ True) := rfl

private theorem canReach_assume_end (p : Prop) :
    (assume p : CanReachRun Unit) (fun _ => True) = (p ∧ True) := rfl

/-- Shared proof helper `stateM_tryFinally'_run`. -/
theorem stateM_tryFinally'_run {S α β : Type} (x : StateM S α) (f : Option α → StateM S β) (s : S) :
    (tryFinally' x f).run s =
      let (a, s1) := x.run s
      let (b, s2) := (f (some a)).run s1
      ((a, b), s2) := rfl

/-- Shared proof helper `exceptT_stateM_bind_run`. -/
theorem exceptT_stateM_bind_run {ε S α β : Type}
    (x : ExceptT ε (StateM S) α) (k : α → ExceptT ε (StateM S) β) (s : S) :
    (ExceptT.run (x >>= k)).run s =
      let (rx, s1) := (ExceptT.run x).run s
      match rx with
      | .ok a => (ExceptT.run (k a)).run s1
      | .error e => (.error e, s1) := by
  dsimp only [Bind.bind, ExceptT.bind, ExceptT.mk, ExceptT.bindCont, StateT.bind, StateT.run, ExceptT.run]
  cases hx : (ExceptT.run x).run s with
  | mk rx s1 =>
    dsimp only [StateT.run, ExceptT.run] at hx
    rw [hx]
    cases rx <;> rfl

/-- Shared proof helper `exceptT_tryFinally'_error_run`. -/
theorem exceptT_tryFinally'_error_run {ε S α β : Type}
    (x : ExceptT ε (StateM S) α) (f : Option α → ExceptT ε (StateM S) β)
    (s s1 s2 : S) (e : ε) (b : β)
    (hx : (ExceptT.run x).run s = (Except.error e, s1))
    (hf : (ExceptT.run (f none)).run s1 = (Except.ok b, s2)) :
    (ExceptT.run (tryFinally' x f)).run s = (Except.error e, s2) := by
  dsimp only [StateT.run, ExceptT.run] at hx hf
  dsimp only [tryFinally', MonadFinally.tryFinally', Bind.bind, Pure.pure, StateT.bind, StateT.pure, StateT.run, ExceptT.run, ExceptT.mk]
  rw [hx]
  dsimp only
  rw [hf]
  rfl

/-- Shared proof helper `mockFs_join_eq`. -/
theorem mockFs_join_eq : mockFs.join = mockJoin := rfl

/-- Shared proof helper `mockUuid_toString_eq`. -/
theorem mockUuid_toString_eq : mockUuid.toString = mockUuidToString := rfl

/-- Shared proof helper `mockUuid_getUuid_run`. -/
theorem mockUuid_getUuid_run (s : TempDirMockState) :
    mockUuid.getUuid.run s = (.ok (mockUuidOfNat s.nextUuid), { s with nextUuid := s.nextUuid + 1 }) := rfl

private def combineTempDirResult {α : Type} (ra : Except TempDirError α) (rc : Except TempDirError Unit) :
    Except TempDirError α :=
  match ra, rc with
  | .ok a, .ok () => .ok a
  | .ok _, .error te => .error te
  | .error e, _ => .error e

/-- Shared proof helper `withTempDir_mock_run_step`. -/
theorem withTempDir_mock_run_step {S α : Type}
    (fs : FsApiM (StateM S)) (time : TimeOpsM (StateM S))
    (uuid : UuidApiM (StateM S)) (env : EnvVarsApiM (StateM S))
    (s₀ sMk sAct sFin : S) (root? : Option String) (dirPrefix dir : String)
    (action : String → StateM S (Except TempDirError α))
    (ra : Except TempDirError α) (rc : Except TempDirError Unit)
    (hCre : (Internal.createTempDir fs uuid env root? dirPrefix).run s₀ = (.ok dir, sMk))
    (hAct : (action dir).run sMk = (ra, sAct))
    (hCln : (Internal.cleanupDirIgnoringNotFound fs dir).run sAct = (rc, sFin)) :
    ((Internal.mkApiM fs time uuid env).withTempDir root? dirPrefix action).run s₀ =
      (combineTempDirResult ra rc, sFin) := by
  rw [mkApiM_withTempDir_eq]
  dsimp only [Internal.withTempDirM]
  rw [stateM_bind_run, hCre]
  dsimp only
  rw [stateM_bind_run, stateM_tryFinally'_run, hAct]
  dsimp only
  rw [hCln]
  cases ra <;> cases rc <;> rfl

private theorem withTempDir_create_err_step {S α : Type}
    (fs : FsApiM (StateM S)) (time : TimeOpsM (StateM S))
    (uuid : UuidApiM (StateM S)) (env : EnvVarsApiM (StateM S))
    (s₀ s1 : S) (root? : Option String) (dirPrefix : String)
    (action : String → StateM S (Except TempDirError α)) (e : TempDirError)
    (hCre : (Internal.createTempDir fs uuid env root? dirPrefix).run s₀ = (.error e, s1)) :
    ((Internal.mkApiM fs time uuid env).withTempDir root? dirPrefix action).run s₀ = (.error e, s1) := by
  rw [mkApiM_withTempDir_eq]
  dsimp only [Internal.withTempDirM]
  rw [stateM_bind_run, hCre]
  rfl

/-- Shared proof helper `payload_ne_dir`. -/
theorem payload_ne_dir (root child fileName : String)
    (hrNe : root ≠ "") (hcNe : child ≠ "") (hcNoSlash : '/' ∉ child.toList)
    (hfNe : fileName ≠ "") (hfNoSlash : '/' ∉ fileName.toList) :
    normKey (mockJoin (mockJoin root child) fileName) ≠ mockJoin root child := by
  have hDirNorm : normKey (mockJoin root child) = mockJoin root child :=
    normKey_mockJoin root child hcNe hcNoSlash
  have hDirNe : mockJoin root child ≠ "" := mockJoin_ne_empty root child hcNe
  have hpn : normKey (mockJoin (mockJoin root child) fileName) = mockJoin (mockJoin root child) fileName :=
    normKey_mockJoin _ fileName hfNe hfNoSlash
  rw [hpn]
  intro hEq
  have hsp := splitParentChild_mockJoin (mockJoin root child) fileName hDirNe hfNe hfNoSlash
  rw [hEq, splitParentChild_mockJoin root child hrNe hcNe hcNoSlash] at hsp
  simp only [Option.some.injEq, Prod.mk.injEq] at hsp
  have hlen := congrArg String.length hsp.1
  rw [hDirNorm] at hlen
  have hlist := mockJoin_eq_append_of_ne_empty root child hrNe
  have hpos : 0 < child.toList.length := by
    rw [String.length_toList]; exact string_length_pos_of_ne_empty _ hcNe
  have hlenDir : (mockJoin root child).length = (mockJoin root child).toList.length := by
    rw [String.length_toList]
  have hlenRoot : (normKey root).length = (normKey root).toList.length := by
    rw [String.length_toList]
  rw [hlist, List.length_append] at hlenDir
  cases hs : (normKey root == "/")
  · simp only [hs, Bool.false_eq_true, ↓reduceIte, List.length_append] at hlenDir
    omega
  · simp only [hs, ↓reduceIte, show ['/'].length = 1 from rfl] at hlenDir
    have hsr : normKey root = "/" := beq_iff_eq.mp hs
    rw [hsr] at hlen
    have hOne : ("/" : String).length = 1 := rfl
    omega

/-- Shared proof helper `spec1_mk_step`. -/
theorem spec1_mk_step (s₀ : TempDirMockState) (root dirPrefix : String)
    (hvr : (!root.isEmpty && !(Char.ofNat 0 ∈ root.toList)) = true)
    (hvp : (!dirPrefix.isEmpty && dirPrefix.toList.head? != some '.' && !('/' ∈ dirPrefix.toList) && !(Char.ofNat 0 ∈ dirPrefix.toList)) = true)
    (stRoot : FileStat) (hRoot : mockStatPure s₀ root = .ok stRoot)
    (hRwx : stRoot.kind = .dir ∧ (stRoot.mode / 256) % 2 = 1 ∧ (stRoot.mode / 128) % 2 = 1 ∧ (stRoot.mode / 64) % 2 = 1)
    (hNone : (mockLstatPure { s₀ with nextUuid := s₀.nextUuid + 1 }
      (mockJoin root (dirPrefix ++ mockUuidToString (mockUuidOfNat s₀.nextUuid)))).isOk = false) :
    let u := mockUuidOfNat s₀.nextUuid
    let dir := mockJoin root (dirPrefix ++ mockUuidToString u)
    ∃ sMk : TempDirMockState,
      (Internal.createTempDir mockFs mockUuid mockEnv (some root) dirPrefix).run s₀ = (.ok dir, sMk) ∧
      (mockFs.lstat dir).run sMk = (.ok (mockNodeStat (.dir s₀.nowSec 0o700)), sMk) ∧
      lookupNode sMk.nodes dir = some (.dir s₀.nowSec 0o700) := by
  intro u dir
  have hCreate := createTempDir_mock_steps s₀ root dirPrefix hvr hvp stRoot hRoot hRwx hNone
  dsimp only at hCreate
  obtain ⟨sMk, hsMk⟩ : ∃ s : TempDirMockState, s =
      { s₀ with
        nextUuid := s₀.nextUuid + 1
        nodes := (dir, .dir s₀.nowSec 0o700) :: s₀.nodes.filter (fun e => !underDir dir e.1) } := ⟨_, rfl⟩
  rw [← hsMk] at hCreate
  have ⟨hcNe, hcNoSlash⟩ := childName_parts dirPrefix u hvp
  have hDirNorm : normKey dir = dir := normKey_mockJoin root _ hcNe hcNoSlash
  have hLookDirMk : lookupNode sMk.nodes dir = some (.dir s₀.nowSec 0o700) := by
    rw [hsMk]; exact lookupNode_cons_eq _ _ _ _ rfl
  have hLstatDirMk : (mockFs.lstat dir).run sMk = (.ok (mockNodeStat (.dir s₀.nowSec 0o700)), sMk) := by
    rw [mockFs_lstat_run]
    simp [mockLstatPure, hLookDirMk]
  exact ⟨sMk, hCreate, hLstatDirMk, hLookDirMk⟩

end LeanSwe.TempDir.Proofs
