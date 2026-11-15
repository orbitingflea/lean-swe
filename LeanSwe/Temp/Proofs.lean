import LeanSwe.Temp.Interface
import LeanSwe.Temp.SpecTests

namespace LeanSwe.Temp.Proofs

open Core
open Core.NondetTest
open LeanSwe.Fs (FsApiM FsError FsErrorKind EntryKind FileStat LockMode)
open LeanSwe.Time (TimeOpsM)
open LeanSwe.Uuid (UuidApiM Uuid)
open LeanSwe.EnvVars (EnvVarsApiM)

/-- Entry kind stored in the `TempMockState` filesystem model. -/
inductive MockNode where
  /-- Directory with modification timestamp (`modifiedSec`) and POSIX mode bits. -/
  | dir (modifiedSec : Int) (mode : Nat)
  /-- Regular file with inode id, content, modification timestamp (`modifiedSec`), and POSIX mode bits. -/
  | file (inode : Nat) (content : String) (modifiedSec : Int) (mode : Nat)
  /-- Symbolic link pointing to `target` with modification timestamp. -/
  | symlink (target : String) (modifiedSec : Int)
  deriving Repr, BEq, DecidableEq

/-- Complete deterministic mock state used to verify all `LeanSwe.Temp` specifications. -/
structure TempMockState where
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

private def normKey (p : String) : String :=
  String.ofList (trimSlashChars p.toList)

private def mockJoin (a b : String) : String :=
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

private def splitParentChild (p : String) : Option (String × String) :=
  let np := normKey p
  if np == "/" || np.isEmpty then none
  else
    match splitLastSlashRev np.toList.reverse with
    | none => none
    | some (parCs, baseCs) =>
      let par := if parCs.isEmpty then "/" else String.ofList parCs
      let base := String.ofList baseCs
      if base.isEmpty then none else some (par, base)

private def mockNodeStat : MockNode → FileStat
  | .dir mtime mode =>
    { kind := .dir, byteSize := 0, mode := mode, modifiedSec := mtime, modifiedNsec := 0, accessedSec := 0, accessedNsec := 0 }
  | .file _ content mtime mode =>
    { kind := .file, byteSize := content.length, mode := mode, modifiedSec := mtime, modifiedNsec := 0, accessedSec := 0, accessedNsec := 0 }
  | .symlink _ mtime =>
    { kind := .symlink, byteSize := 0, mode := 0o777, modifiedSec := mtime, modifiedNsec := 0, accessedSec := 0, accessedNsec := 0 }

private def lookupNode (nodes : List (String × MockNode)) (p : String) : Option MockNode :=
  let np := normKey p
  (nodes.find? (fun e => normKey e.1 == np)).map Prod.snd

private def resolveParentTarget (_s : TempMockState) (p : String) : Except FsError String :=
  .ok (normKey p)

private def mockLstatPure (s : TempMockState) (p : String) : Except FsError FileStat :=
  match lookupNode s.nodes p with
  | none => .error { kind := .notFound, path := some p, message := "not found" }
  | some node => .ok (mockNodeStat node)

private def mockStatPure (s : TempMockState) (p : String) : Except FsError FileStat :=
  mockLstatPure s p

private def hasWx (st : FileStat) : Bool :=
  st.kind == .dir && (st.mode / 128) % 2 == 1 && (st.mode / 64) % 2 == 1

private def hasRx (st : FileStat) : Bool :=
  st.kind == .dir && (st.mode / 256) % 2 == 1 && (st.mode / 64) % 2 == 1

private def mockParentChild (dir full : String) : Option String :=
  let nd := normKey dir
  let nf := normKey full
  let pref := if nd.isEmpty then "" else if nd == "/" then "/" else nd ++ "/"
  if pref.toList.isPrefixOf nf.toList then
    let rest := String.ofList (nf.toList.drop pref.length)
    if !rest.isEmpty && rest != "." && rest != ".." && !('/' ∈ rest.toList) && !(Char.ofNat 0 ∈ rest.toList) then
      some rest
    else none
  else none

private def eraseDupStringsAux (seen : List String) : List String → List String
  | [] => []
  | x :: xs => if x ∈ seen then eraseDupStringsAux seen xs else x :: eraseDupStringsAux (x :: seen) xs

private def eraseDupStrings (xs : List String) : List String :=
  eraseDupStringsAux [] xs

private def mockHasConflict (locks : List (Nat × LockMode)) (ino : Nat) (m : LockMode) : Bool :=
  locks.any fun (li, lm) => li == ino && (m == .exclusive || lm == .exclusive)

private def mockRemoveFirstLock (ino : Nat) (m : LockMode) : List (Nat × LockMode) → List (Nat × LockMode)
  | [] => []
  | x :: xs => if x == (ino, m) then xs else x :: mockRemoveFirstLock ino m xs

private def freshInode (s : TempMockState) : Nat :=
  s.locks.foldl (fun m l => Nat.max m (l.1 + 1)) s.nextInode

private def underDir (prefixDir key : String) : Bool :=
  let np := normKey prefixDir
  let nk := normKey key
  let pref := if np == "/" then "/" else np ++ "/"
  nk == np || pref.toList.isPrefixOf nk.toList

private def mockRmtreePure (p : String) (ignoreMissing : Bool) : StateM TempMockState (Except FsError Unit) := do
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

private def mockUuidOfNat (n : Nat) : Uuid :=
  let b14 := UInt8.ofNat ((n / 256) % 256)
  let b15 := UInt8.ofNat (n % 256)
  { bytes := ByteArray.mk #[0, 0, 0, 0, 0, 0, 0x40, 0, 0x80, 0, 0, 0, 0, 0, b14, b15] }

private def mockHexByte (b : UInt8) : String :=
  let d (k : Nat) : Char :=
    if k < 10 then Char.ofNat (48 + k) else Char.ofNat (87 + k)
  String.ofList [d (b.toNat / 16), d (b.toNat % 16)]

private def mockUuidToString (u : Uuid) : String :=
  let b14 := u.bytes[14]?.getD 0
  let b15 := u.bytes[15]?.getD 0
  "00000000-0000-4000-8000-00000000" ++ mockHexByte b14 ++ mockHexByte b15

private def mockFs : FsApiM (StateM TempMockState) :=
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

private def mockTime : TimeOpsM (StateM TempMockState) :=
  { nowTimestamp := do return Std.Time.Timestamp.ofSecondsSinceUnixEpoch (Std.Time.Second.Offset.ofInt (← get).nowSec)
    monoNanosNow := pure 0
    sleep := fun _ => pure () }

private def mockUuid : UuidApiM (StateM TempMockState) :=
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

private def mockEnv : EnvVarsApiM (StateM TempMockState) :=
  { mapRawError := fun _ => { kind := .ioError, message := "env" }
    getEnv := fun k => do
      if k == "TMPDIR" then return .ok (← get).tmpdir
      else return .ok none
    listEnv := pure (.ok #[])
    homeDir := pure (.ok "/home/user")
    splitSearchPath := fun _ => #[] }

private def mockFsEx : FsApiM (ExceptT String (StateM TempMockState)) :=
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
      let s : TempMockState ← get
      match resolveParentTarget s p with
      | .error e => return .error e
      | .ok rp =>
        match lookupNode s.nodes rp with
        | some (.dir _ _) => return .error { kind := .isADirectory, path := some p, message := "is dir" }
        | some (.symlink _ _) => return .error { kind := .invalidInput, path := some p, message := "symlink" }
        | some (.file ino _ _ _) =>
          if mockHasConflict s.locks ino mode then
            return .error { kind := .wouldBlock, path := some p, message := "wouldBlock" }
          liftM (set ({ s with locks := (ino, mode) :: s.locks } : TempMockState) : StateM TempMockState Unit)
          let (r, _) ← tryFinally' action (fun _ =>
            liftM (modify (fun (s' : TempMockState) => { s' with locks := mockRemoveFirstLock ino mode s'.locks }) : StateM TempMockState Unit))
          return r
        | none =>
          if !createIfMissing then
            return .error { kind := .notFound, path := some p, message := "not found" }
          let ino := freshInode s
          liftM (set ({ s with nodes := (rp, .file ino "" s.nowSec 0o644) :: s.nodes, locks := (ino, mode) :: s.locks, nextInode := ino + 1 } : TempMockState) : StateM TempMockState Unit)
          let (r, _) ← tryFinally' action (fun _ =>
            liftM (modify (fun (s' : TempMockState) => { s' with locks := mockRemoveFirstLock ino mode s'.locks }) : StateM TempMockState Unit))
          return r
    tryWithFileLock := fun p mode createIfMissing action => do
      let s : TempMockState ← get
      match resolveParentTarget s p with
      | .error e => return .error e
      | .ok rp =>
        match lookupNode s.nodes rp with
        | some (.dir _ _) => return .error { kind := .isADirectory, path := some p, message := "is dir" }
        | some (.symlink _ _) => return .error { kind := .invalidInput, path := some p, message := "symlink" }
        | some (.file ino _ _ _) =>
          if mockHasConflict s.locks ino mode then return .ok none
          liftM (set ({ s with locks := (ino, mode) :: s.locks } : TempMockState) : StateM TempMockState Unit)
          let (r, _) ← tryFinally' action (fun _ =>
            liftM (modify (fun (s' : TempMockState) => { s' with locks := mockRemoveFirstLock ino mode s'.locks }) : StateM TempMockState Unit))
          return r.map some
        | none =>
          if !createIfMissing then
            return .error { kind := .notFound, path := some p, message := "not found" }
          let ino := freshInode s
          liftM (set ({ s with nodes := (rp, .file ino "" s.nowSec 0o644) :: s.nodes, locks := (ino, mode) :: s.locks, nextInode := ino + 1 } : TempMockState) : StateM TempMockState Unit)
          let (r, _) ← tryFinally' action (fun _ =>
            liftM (modify (fun (s' : TempMockState) => { s' with locks := mockRemoveFirstLock ino mode s'.locks }) : StateM TempMockState Unit))
          return r.map some }

private def mockTimeEx : TimeOpsM (ExceptT String (StateM TempMockState)) :=
  { nowTimestamp := liftM mockTime.nowTimestamp
    monoNanosNow := liftM mockTime.monoNanosNow
    sleep := fun ms => liftM (mockTime.sleep ms) }

private def mockUuidEx : UuidApiM (ExceptT String (StateM TempMockState)) :=
  { mapRawError := mockUuid.mapRawError
    fromRandomBytes := mockUuid.fromRandomBytes
    toString := mockUuid.toString
    toHex := mockUuid.toHex
    parse := mockUuid.parse
    parseHex := mockUuid.parseHex
    isValid := mockUuid.isValid
    getUuid := liftM mockUuid.getUuid }

private def mockEnvEx : EnvVarsApiM (ExceptT String (StateM TempMockState)) :=
  { mapRawError := mockEnv.mapRawError
    getEnv := fun k => liftM (mockEnv.getEnv k)
    listEnv := liftM mockEnv.listEnv
    homeDir := liftM mockEnv.homeDir
    splitSearchPath := mockEnv.splitSearchPath }

private theorem mem_insertSorted (x y : String) (xs : List String) :
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

private theorem pairwise_sortStrings (xs : List String) :
    List.Pairwise (· ≤ ·) (Internal.sortStrings xs) := by
  induction xs with
  | nil => simp [Internal.sortStrings]
  | cons x xs ih => exact pairwise_insertSorted x _ ih

private theorem mem_sortStrings (y : String) (xs : List String) :
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

private theorem mem_eraseDupStrings (xs : List String) (y : String) :
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

private theorem string_isEmpty_iff_eq_empty (s : String) : s.isEmpty = true ↔ s = "" := by
  simp only [String.isEmpty, beq_iff_eq]
  exact String.utf8ByteSize_eq_zero_iff

private theorem string_length_pos_of_ne_empty (s : String) (h : s ≠ "") : 0 < s.length := by
  rw [← String.length_toList]
  cases hl : s.toList with
  | nil => exact absurd (String.toList_eq_nil_iff.mp hl) h
  | cons _ _ => simp

private theorem string_append_ne_empty_right (a b : String) (hb : b ≠ "") : a ++ b ≠ "" := by
  intro h
  have h1 := congrArg String.toList h
  simp only [String.toList_append, String.toList_empty, List.append_eq_nil_iff] at h1
  exact hb (String.toList_eq_nil_iff.mp h1.2)

private theorem normKey_ne_empty (a : String) (ha : a ≠ "") : normKey a ≠ "" := by
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

private theorem normKey_idem (p : String) : normKey (normKey p) = normKey p := by
  unfold normKey trimSlashChars
  simp [String.toList_ofList, List.reverse_reverse, trimTrailingSlashesRev_idem]

private theorem mockJoin_normKey (a b : String) : mockJoin (normKey a) b = mockJoin a b := by
  simp [mockJoin, normKey_idem]

private theorem normKey_of_last_ne_slash (s : String) (c : Char) (rest : List Char)
    (hrev : s.toList.reverse = c :: rest) (hc : c ≠ '/') :
    normKey s = s := by
  unfold normKey trimSlashChars
  rw [hrev, trimTrailingSlashesRev_of_head_ne_slash c rest hc, ← hrev, List.reverse_reverse, String.ofList_toList]

private theorem normKey_mockJoin (a b : String) (hb : b ≠ "") (hslash : '/' ∉ b.toList) :
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

private theorem splitParentChild_mockJoin (a b : String) (ha : a ≠ "") (hb : b ≠ "")
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

private theorem lookupNode_cons_eq (k : String) (v : MockNode) (nodes : List (String × MockNode)) (p : String)
    (heq : normKey k = normKey p) :
    lookupNode ((k, v) :: nodes) p = some v := by
  simp [lookupNode, heq]

private theorem lookupNode_cons_ne (k : String) (v : MockNode) (nodes : List (String × MockNode)) (p : String)
    (hne : normKey k ≠ normKey p) :
    lookupNode ((k, v) :: nodes) p = lookupNode nodes p := by
  simp [lookupNode, beq_false_of_ne hne]

private theorem lookupNode_filter_underDir_eq (nodes : List (String × MockNode)) (rp : String)
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

private theorem lookupNode_filter_of_preserved (nodes : List (String × MockNode))
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

private theorem validRoot_ne_empty (r : String) (h : (!r.isEmpty && !(Char.ofNat 0 ∈ r.toList)) = true) :
    r ≠ "" := by
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at h
  intro he
  rw [he] at h
  simp [String.isEmpty] at h

private theorem childName_parts (dirPrefix : String) (u : Uuid)
    (hvp : (!dirPrefix.isEmpty && dirPrefix.toList.head? != some '.' && !('/' ∈ dirPrefix.toList) && !(Char.ofNat 0 ∈ dirPrefix.toList)) = true) :
    (dirPrefix ++ mockUuidToString u) ≠ "" ∧ '/' ∉ (dirPrefix ++ mockUuidToString u).toList := by
  have ⟨hne, hno⟩ := validPrefix_parts dirPrefix hvp
  refine ⟨string_append_ne_empty_right dirPrefix (mockUuidToString u) (mockUuidToString_ne_empty u), ?_⟩
  rw [String.toList_append]
  intro h
  rcases List.mem_append.mp h with hm | hm
  · exact hno hm
  · exact mockUuidToString_no_slash u hm

private theorem hasWx_of_hasRwx (st : FileStat)
    (h : st.kind = .dir ∧ (st.mode / 256) % 2 = 1 ∧ (st.mode / 128) % 2 = 1 ∧ (st.mode / 64) % 2 = 1) :
    hasWx st = true := by
  simp only [hasWx, h.1, h.2.2.1, h.2.2.2]
  decide

private theorem hasRx_of_hasRwx (st : FileStat)
    (h : st.kind = .dir ∧ (st.mode / 256) % 2 = 1 ∧ (st.mode / 128) % 2 = 1 ∧ (st.mode / 64) % 2 = 1) :
    hasRx st = true := by
  simp only [hasRx, h.1, h.2.1, h.2.2.2]
  decide

private theorem stateM_bind_run {S α β : Type} (x : StateM S α) (f : α → StateM S β) (s : S) :
    (x >>= f).run s = (f (x.run s).1).run (x.run s).2 := rfl

private theorem stateM_get_run {S : Type} (s : S) : (get : StateM S S).run s = (s, s) := rfl

private theorem stateM_set_run {S : Type} (s' s : S) : (set s' : StateM S Unit).run s = ((), s') := rfl

private theorem stateM_modify_run {S : Type} (f : S → S) (s : S) :
    (modify f : StateM S Unit).run s = ((), f s) := rfl

private theorem stateM_pure_run {S α : Type} (a : α) (s : S) :
    (pure a : StateM S α).run s = (a, s) := rfl

private theorem mockJoin_ne_root (root child : String) (hr : root ≠ "") (hc : child ≠ "")
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

private theorem list_map_id_of_mem {α : Type} (xs : List α) (f : α → α)
    (h : ∀ x ∈ xs, f x = x) : xs.map f = xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.map_cons, h x (by simp), ih (fun y hy => h y (by simp [hy]))]

private theorem resolveRoot_some_mock_run (s₀ : TempMockState) (root : String)
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

private theorem createTempDir_mock_steps (s₀ : TempMockState) (root dirPrefix : String)
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

private theorem cleanupDir_mock_run (s : TempMockState) (dir : String) (hnorm : normKey dir = dir)
    (hnode : ∃ m mode, lookupNode s.nodes dir = some (.dir m mode)) :
    (Internal.cleanupDirIgnoringNotFound mockFs dir).run s =
      (.ok (), { s with nodes := s.nodes.filter (fun e => !underDir dir e.1) }) := by
  rcases hnode with ⟨m, mode, hLook⟩
  dsimp only [Internal.cleanupDirIgnoringNotFound, mockFs, mockRmtreePure, resolveParentTarget]
  rw [stateM_bind_run, stateM_bind_run, stateM_get_run]
  dsimp only
  rw [hnorm, hLook]
  simp only [stateM_bind_run, stateM_set_run, stateM_pure_run]

private theorem mockFs_lstat_run (s : TempMockState) (p : String) :
    (mockFs.lstat p).run s = (mockLstatPure s p, s) := by
  simp [mockFs]; rfl

private theorem mockFs_writeText_run (s : TempMockState) (p c : String) :
    (mockFs.writeText p c).run s =
      (.ok (), { s with
        nodes := (normKey p, .file (freshInode s) c s.nowSec 0o644) :: s.nodes.filter (fun e => normKey e.1 != normKey p)
        nextInode := freshInode s + 1 }) := by
  dsimp only [mockFs, resolveParentTarget]
  rw [stateM_bind_run, stateM_get_run]
  simp only [stateM_bind_run, stateM_set_run, stateM_pure_run]

private theorem mkApiM_withTempDir_eq {m : Type → Type} {α : Type} [Monad m] [MonadFinally m]
    (fs : FsApiM m) (time : TimeOpsM m) (uuid : UuidApiM m) (env : EnvVarsApiM m)
    (root? : Option String) (dirPrefix : String) (action : String → m (Except TempError α)) :
    (Internal.mkApiM fs time uuid env).withTempDir root? dirPrefix action =
      Internal.withTempDirM fs uuid env root? dirPrefix action := rfl

private theorem mkApiM_withLockedTempDir_eq {m : Type → Type} {α : Type} [Monad m] [MonadFinally m]
    (fs : FsApiM m) (time : TimeOpsM m) (uuid : UuidApiM m) (env : EnvVarsApiM m)
    (root? : Option String) (dirPrefix : String) (action : String → m (Except TempError α)) :
    (Internal.mkApiM fs time uuid env).withLockedTempDir root? dirPrefix action =
      Internal.withLockedTempDirM fs uuid env root? dirPrefix action := rfl

private theorem mkApiM_cleanupStaleTempDirs_eq {m : Type → Type} [Monad m] [MonadFinally m]
    (fs : FsApiM m) (time : TimeOpsM m) (uuid : UuidApiM m) (env : EnvVarsApiM m)
    (root? : Option String) (dirPrefix : String) (maxAgeSec : Nat) :
    (Internal.mkApiM fs time uuid env).cleanupStaleTempDirs root? dirPrefix maxAgeSec =
      Internal.cleanupStaleTempDirsM fs time env root? dirPrefix maxAgeSec := rfl

private theorem mockFs_stat_run (s : TempMockState) (p : String) :
    (mockFs.stat p).run s = (mockStatPure s p, s) := by
  simp [mockFs]; rfl

private theorem mockFs_lstat_isOk_false_of_lookup_none (s : TempMockState) (p : String)
    (h : lookupNode s.nodes p = none) :
    ((mockFs.lstat p).run s).1.isOk = false := by
  rw [mockFs_lstat_run]
  simp [mockLstatPure, h, Except.isOk, Except.toBool]

private theorem lookupNode_of_lstat_ok (s : TempMockState) (p : String) (st : FileStat)
    (h : mockLstatPure s p = .ok st) :
    ∃ nd, lookupNode s.nodes p = some nd ∧ mockNodeStat nd = st := by
  unfold mockLstatPure at h
  cases hl : lookupNode s.nodes p with
  | none => simp [hl] at h
  | some nd =>
    simp only [hl, Except.ok.injEq] at h
    exact ⟨nd, rfl, h⟩

private theorem lookupNode_none_of_lstat_error (s : TempMockState) (p : String) (e : FsError)
    (h : mockLstatPure s p = .error e) :
    lookupNode s.nodes p = none ∧ e.kind = .notFound := by
  unfold mockLstatPure at h
  cases hl : lookupNode s.nodes p with
  | none =>
    simp only [hl, Except.error.injEq] at h
    exact ⟨rfl, by rw [← h]⟩
  | some nd => simp [hl] at h

private theorem underDir_refl (d : String) (hn : normKey d = d) :
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

private theorem mockJoin_eq_append_of_ne_empty (root nm : String) (hr : root ≠ "") :
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

private theorem mockJoin_ne_slash (root nm : String) (hr : root ≠ "") (hnm : nm ≠ "") :
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

private theorem disjoint_underDir_mockJoin (root n1 n2 p : String)
    (hr : root ≠ "") (hn1 : n1 ≠ "") (hn2 : n2 ≠ "")
    (hno1 : ¬('/' ∈ n1.toList)) (hno2 : ¬('/' ∈ n2.toList)) (hne : n1 ≠ n2)
    (hu1 : underDir (mockJoin root n1) p = true)
    (hu2 : underDir (mockJoin root n2) p = true) : False := by
  have h1 := underDir_mockJoin_sub root n1 p hr hn1 hno1 hu1
  have h2 := underDir_mockJoin_sub root n2 p hr hn2 hno2 hu2
  have heq : n1.toList = n2.toList := h1.symm.trans h2
  exact hne (String.toList_inj.mp heq)

private theorem not_underDir_mockJoin_root (root nm p : String)
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

private theorem underDir_mockJoin_child (dir nm p : String)
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

private theorem underDir_mockJoin_self (dir nm : String)
    (hd : dir ≠ "") (hdn : normKey dir = dir) (hds : dir ≠ "/")
    (hnm : nm ≠ "") (hno : ¬('/' ∈ nm.toList)) :
    underDir dir (mockJoin dir nm) = true :=
  underDir_mockJoin_child dir nm (mockJoin dir nm) hd hdn hds hnm hno
    (underDir_refl _ (normKey_mockJoin dir nm hnm hno))

private theorem underDir_eq_of_normKey_eq (d a b : String) (h : normKey a = normKey b) :
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

private theorem mockJoin_ne_empty (a b : String) (hb : b ≠ "") : mockJoin a b ≠ "" := by
  dsimp only [mockJoin]
  split
  · exact hb
  · split <;> exact string_append_ne_empty_right _ b hb

private theorem validEntryName_of_mockParentChild (dir full rest : String)
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

private theorem allPass_assume {β : Type} (p : Prop) (k : Unit → AllPassRun β) (post : β → Prop) :
    (assume p >>= k) post = (p → k () post) := rfl

private theorem allPass_assert {β : Type} (p : Prop) (k : Unit → AllPassRun β) (post : β → Prop) :
    (assert p >>= k) post = (p ∧ k () post) := rfl

private theorem allPass_assert_end (p : Prop) :
    (assert p : AllPassRun Unit) (fun _ => True) = (p ∧ True) := rfl

private theorem canReach_bind {α β : Type} (a : CanReachRun α) (k : α → CanReachRun β) (post : β → Prop) :
    (a >>= k) post = a (fun x => k x post) := rfl

private theorem canReach_nondet {α β : Type} (k : α → CanReachRun β) (post : β → Prop) :
    (NondetTest.nondet α >>= k) post = ∃ x : α, k x post := rfl

private theorem canReach_assume {β : Type} (p : Prop) (k : Unit → CanReachRun β) (post : β → Prop) :
    (assume p >>= k) post = (p ∧ k () post) := rfl

private theorem canReach_assert {β : Type} (p : Prop) (k : Unit → CanReachRun β) (post : β → Prop) :
    (assert p >>= k) post = (p ∧ k () post) := rfl

private theorem canReach_assert_end (p : Prop) :
    (assert p : CanReachRun Unit) (fun _ => True) = (p ∧ True) := rfl

private theorem canReach_assume_end (p : Prop) :
    (assume p : CanReachRun Unit) (fun _ => True) = (p ∧ True) := rfl

private theorem stateM_tryFinally'_run {S α β : Type} (x : StateM S α) (f : Option α → StateM S β) (s : S) :
    (tryFinally' x f).run s =
      let (a, s1) := x.run s
      let (b, s2) := (f (some a)).run s1
      ((a, b), s2) := rfl

private theorem exceptT_stateM_bind_run {ε S α β : Type}
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

private theorem exceptT_tryFinally'_error_run {ε S α β : Type}
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

private theorem mockFs_join_eq : mockFs.join = mockJoin := rfl

private theorem mockUuid_toString_eq : mockUuid.toString = mockUuidToString := rfl

private theorem mockUuid_getUuid_run (s : TempMockState) :
    mockUuid.getUuid.run s = (.ok (mockUuidOfNat s.nextUuid), { s with nextUuid := s.nextUuid + 1 }) := rfl

private def combineTempResult {α : Type} (ra : Except TempError α) (rc : Except TempError Unit) :
    Except TempError α :=
  match ra, rc with
  | .ok a, .ok () => .ok a
  | .ok _, .error te => .error te
  | .error e, _ => .error e

private theorem withTempDir_mock_run_step {S α : Type}
    (fs : FsApiM (StateM S)) (time : TimeOpsM (StateM S))
    (uuid : UuidApiM (StateM S)) (env : EnvVarsApiM (StateM S))
    (s₀ sMk sAct sFin : S) (root? : Option String) (dirPrefix dir : String)
    (action : String → StateM S (Except TempError α))
    (ra : Except TempError α) (rc : Except TempError Unit)
    (hCre : (Internal.createTempDir fs uuid env root? dirPrefix).run s₀ = (.ok dir, sMk))
    (hAct : (action dir).run sMk = (ra, sAct))
    (hCln : (Internal.cleanupDirIgnoringNotFound fs dir).run sAct = (rc, sFin)) :
    ((Internal.mkApiM fs time uuid env).withTempDir root? dirPrefix action).run s₀ =
      (combineTempResult ra rc, sFin) := by
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
    (action : String → StateM S (Except TempError α)) (e : TempError)
    (hCre : (Internal.createTempDir fs uuid env root? dirPrefix).run s₀ = (.error e, s1)) :
    ((Internal.mkApiM fs time uuid env).withTempDir root? dirPrefix action).run s₀ = (.error e, s1) := by
  rw [mkApiM_withTempDir_eq]
  dsimp only [Internal.withTempDirM]
  rw [stateM_bind_run, hCre]
  rfl

private theorem payload_ne_dir (root child fileName : String)
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

private theorem spec1_mk_step (s₀ : TempMockState) (root dirPrefix : String)
    (hvr : (!root.isEmpty && !(Char.ofNat 0 ∈ root.toList)) = true)
    (hvp : (!dirPrefix.isEmpty && dirPrefix.toList.head? != some '.' && !('/' ∈ dirPrefix.toList) && !(Char.ofNat 0 ∈ dirPrefix.toList)) = true)
    (stRoot : FileStat) (hRoot : mockStatPure s₀ root = .ok stRoot)
    (hRwx : stRoot.kind = .dir ∧ (stRoot.mode / 256) % 2 = 1 ∧ (stRoot.mode / 128) % 2 = 1 ∧ (stRoot.mode / 64) % 2 = 1)
    (hNone : (mockLstatPure { s₀ with nextUuid := s₀.nextUuid + 1 }
      (mockJoin root (dirPrefix ++ mockUuidToString (mockUuidOfNat s₀.nextUuid)))).isOk = false) :
    let u := mockUuidOfNat s₀.nextUuid
    let dir := mockJoin root (dirPrefix ++ mockUuidToString u)
    ∃ sMk : TempMockState,
      (Internal.createTempDir mockFs mockUuid mockEnv (some root) dirPrefix).run s₀ = (.ok dir, sMk) ∧
      (mockFs.lstat dir).run sMk = (.ok (mockNodeStat (.dir s₀.nowSec 0o700)), sMk) ∧
      lookupNode sMk.nodes dir = some (.dir s₀.nowSec 0o700) := by
  intro u dir
  have hCreate := createTempDir_mock_steps s₀ root dirPrefix hvr hvp stRoot hRoot hRwx hNone
  dsimp only at hCreate
  obtain ⟨sMk, hsMk⟩ : ∃ s : TempMockState, s =
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

private theorem spec1_write_clean_step (s₀ sMk : TempMockState) (root dirPrefix : String)
    (hvr : (!root.isEmpty && !(Char.ofNat 0 ∈ root.toList)) = true)
    (hvp : (!dirPrefix.isEmpty && dirPrefix.toList.head? != some '.' && !('/' ∈ dirPrefix.toList) && !(Char.ofNat 0 ∈ dirPrefix.toList)) = true)
    (hLookDirMk : lookupNode sMk.nodes (mockJoin root (dirPrefix ++ mockUuidToString (mockUuidOfNat s₀.nextUuid))) = some (.dir s₀.nowSec 0o700)) :
    let u := mockUuidOfNat s₀.nextUuid
    let dir := mockJoin root (dirPrefix ++ mockUuidToString u)
    ∃ sAct sFin : TempMockState,
      (mockFs.writeText (mockJoin dir "payload.txt") "hello").run sMk = (.ok (), sAct) ∧
      (Internal.cleanupDirIgnoringNotFound mockFs dir).run sAct = (.ok (), sFin) ∧
      ((mockFs.lstat dir).run sFin).1.isOk = false := by
  intro u dir
  have hrNe : root ≠ "" := validRoot_ne_empty root hvr
  have ⟨hcNe, hcNoSlash⟩ := childName_parts dirPrefix u hvp
  have hDirNorm : normKey dir = dir := normKey_mockJoin root _ hcNe hcNoSlash
  let payload := mockJoin dir "payload.txt"
  obtain ⟨sAct, hsAct⟩ : ∃ s : TempMockState, s =
      { sMk with
        nodes := (normKey payload, .file (freshInode sMk) "hello" sMk.nowSec 0o644) ::
          sMk.nodes.filter (fun e => normKey e.1 != normKey payload)
        nextInode := freshInode sMk + 1 } := ⟨_, rfl⟩
  have hWrite : (mockFs.writeText (mockJoin dir "payload.txt") "hello").run sMk = (.ok (), sAct) := by
    rw [mockFs_writeText_run, ← hsAct]
  have hPayloadNeDir : normKey payload ≠ dir :=
    payload_ne_dir root (dirPrefix ++ mockUuidToString u) "payload.txt" hrNe hcNe hcNoSlash (by decide) (by decide)
  have hLookDirAfterWrite : lookupNode sAct.nodes dir = some (.dir s₀.nowSec 0o700) := by
    rw [hsAct]
    unfold lookupNode
    dsimp only
    have hb : (normKey (normKey payload) == normKey dir) = false := by
      rw [normKey_idem, hDirNorm, beq_false_of_ne hPayloadNeDir]
    rw [List.find?_cons, hb]
    have hfu := lookupNode_filter_of_preserved sMk.nodes (fun e => normKey e.1 != normKey payload) dir
      (by
        intro e _ he
        simp only [bne_iff_ne, ne_eq]
        rw [he, hDirNorm]
        exact ne_comm.mp hPayloadNeDir)
    exact hfu.trans hLookDirMk
  obtain ⟨sFin, hsFin⟩ : ∃ s : TempMockState, s =
      { sAct with nodes := sAct.nodes.filter (fun e => !underDir dir e.1) } := ⟨_, rfl⟩
  have hClean : (Internal.cleanupDirIgnoringNotFound mockFs dir).run sAct = (.ok (), sFin) := by
    rw [hsFin]
    exact cleanupDir_mock_run sAct dir hDirNorm ⟨_, _, hLookDirAfterWrite⟩
  have hGone : ((mockFs.lstat dir).run sFin).1.isOk = false := by
    rw [hsFin]
    apply mockFs_lstat_isOk_false_of_lookup_none
    exact lookupNode_filter_underDir_eq _ _ hDirNorm
  exact ⟨sAct, sFin, hWrite, hClean, hGone⟩

/-- Spec 1: `withTempDir` creates `<root>/<dirPrefix><uuid>` with mode `0o700`, executes `action dir`, returns `.ok val`, and removes `dir` on exit. -/
theorem proof_temp_withTempDir_okCleansUpAndSetsMode :
    AllPass (test_temp_withTempDir_okCleansUpAndSetsMode
      (S := TempMockState) Internal.mkApiM mockFs mockTime mockUuid mockEnv) := by
  dsimp only [test_temp_withTempDir_okCleansUpAndSetsMode, AllPass]
  intro s₀ root dirPrefix val ⟨hvr, hvp⟩ ⟨stRoot, hRoot, hRwx⟩
  have hRootPure : mockStatPure s₀ root = .ok stRoot := by
    rw [mockFs_stat_run] at hRoot
    exact hRoot
  rw [mockUuid_getUuid_run s₀]
  dsimp only
  rw [allPass_assume]
  intro hNone
  have hNonePure : (mockLstatPure { s₀ with nextUuid := s₀.nextUuid + 1 }
      (mockJoin root (dirPrefix ++ mockUuidToString (mockUuidOfNat s₀.nextUuid)))).isOk = false := by
    rw [mockFs_lstat_run, mockFs_join_eq, mockUuid_toString_eq] at hNone
    exact hNone
  obtain ⟨sMk, hCreate, hLstatDirMk, hLookDirMk⟩ :=
    spec1_mk_step s₀ root dirPrefix hvr hvp stRoot hRootPure hRwx hNonePure
  obtain ⟨sAct, sFin, hWrite, hClean, hGone⟩ :=
    spec1_write_clean_step s₀ sMk root dirPrefix hvr hvp hLookDirMk
  rw [mkApiM_withTempDir_eq]
  dsimp only [Internal.withTempDirM]
  rw [mockFs_join_eq, mockUuid_toString_eq]
  rw [stateM_bind_run, hCreate]
  dsimp only
  rw [stateM_bind_run, stateM_tryFinally'_run]
  rw [stateM_bind_run, hLstatDirMk]
  dsimp only [mockNodeStat]
  have hHead : (EntryKind.dir != EntryKind.dir || (448 : Nat) != 0o700) = false := by decide
  rw [hHead, Bool.false_or, bne_self_eq_false]
  simp only [Bool.false_eq_true, ↓reduceIte]
  rw [stateM_bind_run, hWrite]
  dsimp only
  rw [stateM_pure_run]
  dsimp only
  rw [hClean]
  dsimp only
  rw [stateM_pure_run]
  dsimp only
  rw [allPass_assert, allPass_assert_end]
  exact ⟨rfl, hGone, trivial⟩

/-- Non-vacuity `CanReach` witness for Spec 1 (`test_temp_withTempDir_okCleansUpAndSetsMode`). -/
theorem reach_temp_withTempDir_okCleansUpAndSetsMode :
    CanReach (test_temp_withTempDir_okCleansUpAndSetsMode
      (S := TempMockState) Internal.mkApiM mockFs mockTime mockUuid mockEnv) := by
  dsimp only [test_temp_withTempDir_okCleansUpAndSetsMode, CanReach]
  obtain ⟨s₀, hs₀⟩ : ∃ s : TempMockState, s = {} := ⟨{}, rfl⟩
  rw [canReach_nondet]; refine ⟨s₀, ?_⟩
  rw [canReach_nondet]; refine ⟨"/tmp", ?_⟩
  rw [canReach_nondet]; refine ⟨"tmp-", ?_⟩
  rw [canReach_nondet]; refine ⟨42, ?_⟩
  rw [canReach_assume]; refine ⟨⟨rfl, rfl⟩, ?_⟩
  have hRootPure : mockStatPure s₀ "/tmp" = .ok (mockNodeStat (.dir 0 0o755)) := by
    rw [hs₀]; rfl
  have hRoot : ∃ stRoot, ((mockFs.stat "/tmp").run s₀).1 = .ok stRoot ∧
      stRoot.kind = .dir ∧ (stRoot.mode / 256) % 2 = 1 ∧ (stRoot.mode / 128) % 2 = 1 ∧ (stRoot.mode / 64) % 2 = 1 :=
    ⟨mockNodeStat (.dir 0 0o755), by rw [mockFs_stat_run]; exact hRootPure, rfl, rfl, rfl, rfl⟩
  rw [canReach_assume]; refine ⟨hRoot, ?_⟩
  rw [mockUuid_getUuid_run s₀]
  dsimp only
  have hNonePure : (mockLstatPure { s₀ with nextUuid := s₀.nextUuid + 1 }
      (mockJoin "/tmp" ("tmp-" ++ mockUuidToString (mockUuidOfNat s₀.nextUuid)))).isOk = false := by
    rw [hs₀]
    unfold mockLstatPure
    dsimp only
    have ⟨hcNe, hcNoSlash⟩ := childName_parts "tmp-" (mockUuidOfNat 1) rfl
    have hNe : normKey "/tmp" ≠ normKey (mockJoin "/tmp" ("tmp-" ++ mockUuidToString (mockUuidOfNat 1))) :=
      ne_comm.mp (mockJoin_ne_root "/tmp" _ (by decide) hcNe hcNoSlash)
    rw [lookupNode_cons_ne "/tmp" (.dir 0 0o755) [] _ hNe]
    rfl
  have hNone : (mockFs.lstat (mockFs.join "/tmp" ("tmp-" ++ mockUuid.toString (mockUuidOfNat s₀.nextUuid)))).run
      { s₀ with nextUuid := s₀.nextUuid + 1 } |>.1.isOk = false := by
    rw [mockFs_lstat_run, mockFs_join_eq, mockUuid_toString_eq]
    exact hNonePure
  rw [canReach_assume]; refine ⟨hNone, ?_⟩
  obtain ⟨sMk, hCreate, hLstatDirMk, hLookDirMk⟩ :=
    spec1_mk_step s₀ "/tmp" "tmp-" rfl rfl (mockNodeStat (.dir 0 0o755)) hRootPure ⟨rfl, rfl, rfl, rfl⟩ hNonePure
  obtain ⟨sAct, sFin, hWrite, hClean, hGone⟩ :=
    spec1_write_clean_step s₀ sMk "/tmp" "tmp-" rfl rfl hLookDirMk
  rw [mkApiM_withTempDir_eq]
  dsimp only [Internal.withTempDirM]
  rw [mockFs_join_eq, mockUuid_toString_eq]
  rw [stateM_bind_run, hCreate]
  dsimp only
  rw [stateM_bind_run, stateM_tryFinally'_run]
  rw [stateM_bind_run, hLstatDirMk]
  dsimp only [mockNodeStat]
  have hHead : (EntryKind.dir != EntryKind.dir || (448 : Nat) != 0o700) = false := by decide
  rw [hHead, Bool.false_or, bne_self_eq_false]
  simp only [Bool.false_eq_true, ↓reduceIte]
  rw [stateM_bind_run, hWrite]
  dsimp only
  rw [stateM_pure_run]
  dsimp only
  rw [hClean]
  dsimp only
  rw [stateM_pure_run]
  dsimp only
  rw [canReach_assert, canReach_assert_end]
  exact ⟨rfl, hGone, trivial⟩

private theorem lookupNode_filter_none_of_none (nodes : List (String × MockNode))
    (pred : (String × MockNode) → Bool) (p : String)
    (h : lookupNode nodes p = none) :
    lookupNode (nodes.filter pred) p = none := by
  unfold lookupNode at h ⊢
  dsimp only at h ⊢
  induction nodes with
  | nil => simp
  | cons x xs ih =>
    cases hb : (normKey x.1 == normKey p) with
    | true => simp [hb] at h
    | false =>
      simp only [List.find?_cons, hb] at h
      rw [List.filter_cons]
      split
      · simp only [List.find?_cons, hb]
        exact ih h
      · exact ih h

private theorem lookupNode_none_of_lstat_isOk_false (s : TempMockState) (p : String)
    (h : ((mockFs.lstat p).run s).1.isOk = false) :
    lookupNode s.nodes p = none := by
  rw [mockFs_lstat_run] at h
  unfold mockLstatPure at h
  cases hl : lookupNode s.nodes p with
  | none => rfl
  | some nd => simp [hl, Except.isOk, Except.toBool] at h

private theorem mockJoin_tmp_ne_other (childName : String)
    (hcNe : childName ≠ "") (hcNoSlash : '/' ∉ childName.toList) :
    normKey (mockJoin "/tmp" childName) ≠ normKey "/other" := by
  rw [normKey_mockJoin "/tmp" childName hcNe hcNoSlash]
  intro hEq
  have hl := congrArg String.toList hEq
  have h1 := mockJoin_eq_append_of_ne_empty "/tmp" childName (by decide)
  have htmp : normKey "/tmp" = "/tmp" := by decide
  rw [h1, htmp] at hl
  rw [show ("/tmp" == "/") = false from by decide] at hl
  simp only [Bool.false_eq_true, ↓reduceIte] at hl
  have hdrop : (normKey "/other").toList = ['/','o','t','h','e','r'] := by decide
  have htmpList : ("/tmp" : String).toList = ['/','t','m','p'] := by decide
  rw [hdrop, htmpList] at hl
  simp at hl

private theorem createTempDir_mock_steps_custom_rm (s₀ : TempMockState) (root dirPrefix : String)
    (rm : String → Bool → StateM TempMockState (Except FsError Unit))
    (hvr : (!root.isEmpty && !(Char.ofNat 0 ∈ root.toList)) = true)
    (hvp : (!dirPrefix.isEmpty && dirPrefix.toList.head? != some '.' && !('/' ∈ dirPrefix.toList) && !(Char.ofNat 0 ∈ dirPrefix.toList)) = true)
    (stRoot : FileStat) (hRoot : mockStatPure s₀ root = .ok stRoot)
    (hRwx : stRoot.kind = .dir ∧ (stRoot.mode / 256) % 2 = 1 ∧ (stRoot.mode / 128) % 2 = 1 ∧ (stRoot.mode / 64) % 2 = 1)
    (hNone : (mockLstatPure { s₀ with nextUuid := s₀.nextUuid + 1 }
      (mockJoin root (dirPrefix ++ mockUuidToString (mockUuidOfNat s₀.nextUuid)))).isOk = false) :
    let u := mockUuidOfNat s₀.nextUuid
    let dir := mockJoin root (dirPrefix ++ mockUuidToString u)
    let sMk := { s₀ with
      nextUuid := s₀.nextUuid + 1
      nodes := (dir, .dir s₀.nowSec 0o700) :: s₀.nodes.filter (fun e => !underDir dir e.1) }
    (Internal.createTempDir { mockFs with rmtree := rm } mockUuid mockEnv (some root) dirPrefix).run s₀ = (.ok dir, sMk) := by
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
  have hMk : ({ mockFs with rmtree := rm }.mkdir dir false false).run { s₀ with nextUuid := s₀.nextUuid + 1 } =
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
  have hCh : ({ mockFs with rmtree := rm }.chmod dir 0o700).run
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
  have hResStep : (Internal.resolveRoot { mockFs with rmtree := rm } mockEnv (some root)).run s₀ = (.ok root, s₀) := by
    have h := resolveRoot_some_mock_run s₀ root hvr stRoot hRoot hRwx.1
    exact h
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

private theorem spec2_exec_parts (s₀ : TempMockState) (root dirPrefix : String)
    (hvr : (!root.isEmpty && !(Char.ofNat 0 ∈ root.toList)) = true)
    (hvp : (!dirPrefix.isEmpty && dirPrefix.toList.head? != some '.' && !('/' ∈ dirPrefix.toList) && !(Char.ofNat 0 ∈ dirPrefix.toList)) = true)
    (stRoot : FileStat) (hRoot : mockStatPure s₀ root = .ok stRoot)
    (hRwx : stRoot.kind = .dir ∧ (stRoot.mode / 256) % 2 = 1 ∧ (stRoot.mode / 128) % 2 = 1 ∧ (stRoot.mode / 64) % 2 = 1)
    (hNone : (mockLstatPure { s₀ with nextUuid := s₀.nextUuid + 1 }
      (mockJoin root (dirPrefix ++ mockUuidToString (mockUuidOfNat s₀.nextUuid)))).isOk = false) :
    let u := mockUuidOfNat s₀.nextUuid
    let dir := mockJoin root (dirPrefix ++ mockUuidToString u)
    let rmFail : String → Bool → StateM TempMockState (Except FsError Unit) :=
      fun _ _ => pure (.error { kind := .permissionDenied, message := "cleanup failed" })
    let fsFailClean : FsApiM (StateM TempMockState) := { mockFs with rmtree := rmFail }
    ∃ sMk sAct sFin : TempMockState,
      (Internal.createTempDir mockFs mockUuid mockEnv (some root) dirPrefix).run s₀ = (.ok dir, sMk) ∧
      (mockFs.writeText (mockFs.join dir "tmp.txt") "data").run sMk = (.ok (), sAct) ∧
      (Internal.cleanupDirIgnoringNotFound mockFs dir).run sAct = (.ok (), sFin) ∧
      ((mockFs.lstat dir).run sFin).1.isOk = false ∧
      (Internal.createTempDir fsFailClean mockUuid mockEnv (some root) dirPrefix).run s₀ = (.ok dir, sMk) ∧
      (Internal.cleanupDirIgnoringNotFound fsFailClean dir).run sMk =
        (.error (Internal.mapFsError { kind := .permissionDenied, message := "cleanup failed" }), sMk) := by
  intro u dir rmFail fsFailClean
  have hrNe : root ≠ "" := validRoot_ne_empty root hvr
  have ⟨hcNe, hcNoSlash⟩ := childName_parts dirPrefix u hvp
  have hDirNorm : normKey dir = dir := normKey_mockJoin root _ hcNe hcNoSlash
  have hCreate1 := createTempDir_mock_steps s₀ root dirPrefix hvr hvp stRoot hRoot hRwx hNone
  dsimp only at hCreate1
  obtain ⟨sMk, hsMk⟩ : ∃ s : TempMockState, s =
      { s₀ with
        nextUuid := s₀.nextUuid + 1
        nodes := (dir, .dir s₀.nowSec 0o700) :: s₀.nodes.filter (fun e => !underDir dir e.1) } := ⟨_, rfl⟩
  rw [← hsMk] at hCreate1
  have hLookDirMk : lookupNode sMk.nodes dir = some (.dir s₀.nowSec 0o700) := by
    rw [hsMk]; exact lookupNode_cons_eq _ _ _ _ rfl
  let tmpPath := mockJoin dir "tmp.txt"
  obtain ⟨sAct, hsAct⟩ : ∃ s : TempMockState, s =
      { sMk with
        nodes := (normKey tmpPath, .file (freshInode sMk) "data" sMk.nowSec 0o644) ::
          sMk.nodes.filter (fun e => normKey e.1 != normKey tmpPath)
        nextInode := freshInode sMk + 1 } := ⟨_, rfl⟩
  have hTmpNeDir : normKey tmpPath ≠ dir :=
    payload_ne_dir root (dirPrefix ++ mockUuidToString u) "tmp.txt" hrNe hcNe hcNoSlash (by decide) (by decide)
  have hLookDirAct : lookupNode sAct.nodes dir = some (.dir s₀.nowSec 0o700) := by
    rw [hsAct]
    unfold lookupNode
    dsimp only
    have hb : (normKey (normKey tmpPath) == normKey dir) = false := by
      rw [normKey_idem, hDirNorm, beq_false_of_ne hTmpNeDir]
    rw [List.find?_cons, hb]
    have hfu := lookupNode_filter_of_preserved sMk.nodes (fun e => normKey e.1 != normKey tmpPath) dir
      (by
        intro e _ he
        simp only [bne_iff_ne, ne_eq]
        rw [he, hDirNorm]
        exact ne_comm.mp hTmpNeDir)
    exact hfu.trans hLookDirMk
  have hWrite1 : (mockFs.writeText (mockFs.join dir "tmp.txt") "data").run sMk = (.ok (), sAct) := by
    rw [mockFs_join_eq, mockFs_writeText_run, ← hsAct]
  obtain ⟨sFin, hsFin⟩ : ∃ s : TempMockState, s =
      { sAct with nodes := sAct.nodes.filter (fun e => !underDir dir e.1) } := ⟨_, rfl⟩
  have hClean1 : (Internal.cleanupDirIgnoringNotFound mockFs dir).run sAct = (.ok (), sFin) := by
    rw [hsFin]; exact cleanupDir_mock_run sAct dir hDirNorm ⟨_, _, hLookDirAct⟩
  have hGone1 : ((mockFs.lstat dir).run sFin).1.isOk = false := by
    rw [hsFin]
    apply mockFs_lstat_isOk_false_of_lookup_none
    exact lookupNode_filter_underDir_eq _ _ hDirNorm
  have hCreate2 := createTempDir_mock_steps_custom_rm s₀ root dirPrefix rmFail hvr hvp stRoot hRoot hRwx hNone
  dsimp only at hCreate2
  rw [← hsMk] at hCreate2
  have hClean2 : (Internal.cleanupDirIgnoringNotFound fsFailClean dir).run sMk =
      (.error (Internal.mapFsError { kind := .permissionDenied, message := "cleanup failed" }), sMk) := by
    dsimp only [Internal.cleanupDirIgnoringNotFound, fsFailClean, rmFail]
    rw [stateM_bind_run, stateM_pure_run]
    dsimp only
    rw [show (FsErrorKind.permissionDenied == FsErrorKind.notFound) = false from by decide]
    simp only [Bool.false_eq_true, ↓reduceIte]
    rw [stateM_pure_run]
  exact ⟨sMk, sAct, sFin, hCreate1, hWrite1, hClean1, hGone1, hCreate2, hClean2⟩

/-- Spec 2: `withTempDir` cleans up `dir` and preserves `action`'s `.error` even when cleanup also fails. -/
theorem proof_temp_withTempDir_errorCleansUpAndPreservesError :
    AllPass (test_temp_withTempDir_errorCleansUpAndPreservesError
      (S := TempMockState) Internal.mkApiM mockFs mockTime mockUuid mockEnv) := by
  dsimp only [test_temp_withTempDir_errorCleansUpAndPreservesError, AllPass]
  intro s₀ root dirPrefix actionErr ⟨hvr, hvp⟩ ⟨stRoot, hRoot, hRwx⟩
  have hRootPure : mockStatPure s₀ root = .ok stRoot := by
    rw [mockFs_stat_run] at hRoot
    exact hRoot
  rw [mockUuid_getUuid_run s₀]
  dsimp only
  rw [allPass_assume]
  intro hNone
  have hNonePure : (mockLstatPure { s₀ with nextUuid := s₀.nextUuid + 1 }
      (mockJoin root (dirPrefix ++ mockUuidToString (mockUuidOfNat s₀.nextUuid)))).isOk = false := by
    rw [mockFs_lstat_run, mockFs_join_eq, mockUuid_toString_eq] at hNone
    exact hNone
  obtain ⟨sMk, sAct, sFin, hCreate1, hWrite1, hClean1, hGone1, hCreate2, hClean2⟩ :=
    spec2_exec_parts s₀ root dirPrefix hvr hvp stRoot hRootPure hRwx hNonePure
  rw [mkApiM_withTempDir_eq]
  dsimp only [Internal.withTempDirM]
  rw [stateM_bind_run, hCreate1]
  dsimp only
  rw [stateM_bind_run, stateM_tryFinally'_run]
  rw [stateM_bind_run, hWrite1]
  dsimp only
  rw [stateM_pure_run]
  dsimp only
  rw [hClean1]
  dsimp only
  rw [stateM_pure_run]
  dsimp only
  rw [allPass_assert, allPass_assert]
  have hGone1' : ((mockFs.lstat (mockFs.join root (dirPrefix ++ mockUuid.toString (mockUuidOfNat s₀.nextUuid)))).run
      sFin).1.isOk = false := by
    rw [mockFs_join_eq, mockUuid_toString_eq]
    exact hGone1
  refine ⟨rfl, hGone1', ?_⟩
  rw [mkApiM_withTempDir_eq]
  dsimp only [Internal.withTempDirM]
  rw [stateM_bind_run, hCreate2]
  dsimp only
  rw [stateM_bind_run, stateM_tryFinally'_run, stateM_pure_run]
  dsimp only
  rw [hClean2]
  dsimp only
  rw [stateM_pure_run]
  dsimp only
  rw [allPass_assert_end]
  exact ⟨rfl, trivial⟩

/-- Non-vacuity `CanReach` witness for Spec 2 (`test_temp_withTempDir_errorCleansUpAndPreservesError`). -/
theorem reach_temp_withTempDir_errorCleansUpAndPreservesError :
    CanReach (test_temp_withTempDir_errorCleansUpAndPreservesError
      (S := TempMockState) Internal.mkApiM mockFs mockTime mockUuid mockEnv) := by
  dsimp only [test_temp_withTempDir_errorCleansUpAndPreservesError, CanReach]
  obtain ⟨s₀, hs₀⟩ : ∃ s : TempMockState, s = {} := ⟨{}, rfl⟩
  let err : TempError := { kind := .ioError, path := none, message := "boom" }
  rw [canReach_nondet]; refine ⟨s₀, ?_⟩
  rw [canReach_nondet]; refine ⟨"/tmp", ?_⟩
  rw [canReach_nondet]; refine ⟨"tmp-", ?_⟩
  rw [canReach_nondet]; refine ⟨err, ?_⟩
  rw [canReach_assume]; refine ⟨⟨rfl, rfl⟩, ?_⟩
  have hRootPure : mockStatPure s₀ "/tmp" = .ok (mockNodeStat (.dir 0 0o755)) := by
    rw [hs₀]; rfl
  have hRoot : ∃ stRoot, ((mockFs.stat "/tmp").run s₀).1 = .ok stRoot ∧
      stRoot.kind = .dir ∧ (stRoot.mode / 256) % 2 = 1 ∧ (stRoot.mode / 128) % 2 = 1 ∧ (stRoot.mode / 64) % 2 = 1 :=
    ⟨mockNodeStat (.dir 0 0o755), by rw [mockFs_stat_run]; exact hRootPure, rfl, rfl, rfl, rfl⟩
  rw [canReach_assume]; refine ⟨hRoot, ?_⟩
  rw [mockUuid_getUuid_run s₀]
  dsimp only
  have hNonePure : (mockLstatPure { s₀ with nextUuid := s₀.nextUuid + 1 }
      (mockJoin "/tmp" ("tmp-" ++ mockUuidToString (mockUuidOfNat s₀.nextUuid)))).isOk = false := by
    rw [hs₀]
    unfold mockLstatPure
    dsimp only
    have ⟨hcNe, hcNoSlash⟩ := childName_parts "tmp-" (mockUuidOfNat 1) rfl
    have hNe : normKey "/tmp" ≠ normKey (mockJoin "/tmp" ("tmp-" ++ mockUuidToString (mockUuidOfNat 1))) :=
      ne_comm.mp (mockJoin_ne_root "/tmp" _ (by decide) hcNe hcNoSlash)
    rw [lookupNode_cons_ne "/tmp" (.dir 0 0o755) [] _ hNe]
    rfl
  have hNone : (mockFs.lstat (mockFs.join "/tmp" ("tmp-" ++ mockUuid.toString (mockUuidOfNat s₀.nextUuid)))).run
      { s₀ with nextUuid := s₀.nextUuid + 1 } |>.1.isOk = false := by
    rw [mockFs_lstat_run, mockFs_join_eq, mockUuid_toString_eq]
    exact hNonePure
  rw [canReach_assume]; refine ⟨hNone, ?_⟩
  obtain ⟨sMk, sAct, sFin, hCreate1, hWrite1, hClean1, hGone1, hCreate2, hClean2⟩ :=
    spec2_exec_parts s₀ "/tmp" "tmp-" rfl rfl (mockNodeStat (.dir 0 0o755)) hRootPure ⟨rfl, rfl, rfl, rfl⟩ hNonePure
  rw [mkApiM_withTempDir_eq]
  dsimp only [Internal.withTempDirM]
  rw [stateM_bind_run, hCreate1]
  dsimp only
  rw [stateM_bind_run, stateM_tryFinally'_run]
  rw [stateM_bind_run, hWrite1]
  dsimp only
  rw [stateM_pure_run]
  dsimp only
  rw [hClean1]
  dsimp only
  rw [stateM_pure_run]
  dsimp only
  rw [canReach_assert, canReach_assert]
  have hGone1' : ((mockFs.lstat (mockFs.join "/tmp" ("tmp-" ++ mockUuid.toString (mockUuidOfNat s₀.nextUuid)))).run
      sFin).1.isOk = false := by
    rw [mockFs_join_eq, mockUuid_toString_eq]
    exact hGone1
  refine ⟨rfl, hGone1', ?_⟩
  rw [mkApiM_withTempDir_eq]
  dsimp only [Internal.withTempDirM]
  rw [stateM_bind_run, hCreate2]
  dsimp only
  rw [stateM_bind_run, stateM_tryFinally'_run, stateM_pure_run]
  dsimp only
  rw [hClean2]
  dsimp only
  rw [stateM_pure_run]
  dsimp only
  rw [canReach_assert_end]
  exact ⟨rfl, trivial⟩

private theorem spec3_exec (s₀ : TempMockState) (root dirPrefix : String) (val : Nat)
    (hvr : (!root.isEmpty && !(Char.ofNat 0 ∈ root.toList)) = true)
    (hvp : (!dirPrefix.isEmpty && dirPrefix.toList.head? != some '.' && !('/' ∈ dirPrefix.toList) && !(Char.ofNat 0 ∈ dirPrefix.toList)) = true)
    (stRoot : FileStat) (hRoot : mockStatPure s₀ root = .ok stRoot)
    (hRwx : stRoot.kind = .dir ∧ (stRoot.mode / 256) % 2 = 1 ∧ (stRoot.mode / 128) % 2 = 1 ∧ (stRoot.mode / 64) % 2 = 1)
    (hNone : (mockLstatPure { s₀ with nextUuid := s₀.nextUuid + 1 }
      (mockJoin root (dirPrefix ++ mockUuidToString (mockUuidOfNat s₀.nextUuid)))).isOk = false) :
    let fsFailClean : FsApiM (StateM TempMockState) :=
      { mockFs with rmtree := fun p _ => pure (.error { kind := .permissionDenied, path := some p, message := "rm failed" }) }
    ∃ s₁ : TempMockState,
      ((Internal.mkApiM fsFailClean mockTime mockUuid mockEnv).withTempDir (some root) dirPrefix fun _ =>
        pure (.ok val)).run s₀ =
        (.error (Internal.mapFsError { kind := .permissionDenied, path := some (mockJoin root (dirPrefix ++ mockUuidToString (mockUuidOfNat s₀.nextUuid))), message := "rm failed" }), s₁) := by
  intro fsFailClean
  let u := mockUuidOfNat s₀.nextUuid
  let dir := mockJoin root (dirPrefix ++ mockUuidToString u)
  have hCreate := createTempDir_mock_steps_custom_rm s₀ root dirPrefix
    (fun p _ => pure (.error { kind := .permissionDenied, path := some p, message := "rm failed" }))
    hvr hvp stRoot hRoot hRwx hNone
  dsimp only at hCreate
  obtain ⟨sMk, hsMk⟩ : ∃ s : TempMockState, s =
      { s₀ with
        nextUuid := s₀.nextUuid + 1
        nodes := (dir, .dir s₀.nowSec 0o700) :: s₀.nodes.filter (fun e => !underDir dir e.1) } := ⟨_, rfl⟩
  rw [← hsMk] at hCreate
  let ce := Internal.mapFsError { kind := .permissionDenied, path := some dir, message := "rm failed" }
  have hClean : (Internal.cleanupDirIgnoringNotFound fsFailClean dir).run sMk = (.error ce, sMk) := by
    dsimp only [Internal.cleanupDirIgnoringNotFound, fsFailClean]
    rw [stateM_bind_run, stateM_pure_run]
    dsimp only
    rw [show (FsErrorKind.permissionDenied == FsErrorKind.notFound) = false from by decide]
    simp only [Bool.false_eq_true, ↓reduceIte]
    rw [stateM_pure_run]
  have hRun := withTempDir_mock_run_step fsFailClean mockTime mockUuid mockEnv s₀ sMk sMk sMk
    (some root) dirPrefix dir (fun _ => pure (.ok val)) (.ok val) (.error ce)
    hCreate (stateM_pure_run _ _) hClean
  exact ⟨sMk, hRun⟩

/-- Spec 3: `withTempDir` propagates cleanup error when `action` returns `.ok`. -/
theorem proof_temp_withTempDir_cleanupErrorReturnedOnOk :
    AllPass (test_temp_withTempDir_cleanupErrorReturnedOnOk
      (S := TempMockState) Internal.mkApiM mockFs mockTime mockUuid mockEnv) := by
  dsimp only [test_temp_withTempDir_cleanupErrorReturnedOnOk, AllPass]
  intro s₀ root dirPrefix val ⟨hvr, hvp⟩ ⟨stRoot, hRoot, hRwx⟩
  have hRootPure : mockStatPure s₀ root = .ok stRoot := by
    rw [mockFs_stat_run] at hRoot
    exact hRoot
  rw [mockUuid_getUuid_run s₀]
  dsimp only
  rw [allPass_assume]
  intro hNone
  have hNonePure : (mockLstatPure { s₀ with nextUuid := s₀.nextUuid + 1 }
      (mockJoin root (dirPrefix ++ mockUuidToString (mockUuidOfNat s₀.nextUuid)))).isOk = false := by
    rw [mockFs_lstat_run, mockFs_join_eq, mockUuid_toString_eq] at hNone
    exact hNone
  obtain ⟨s₁, hRun⟩ := spec3_exec s₀ root dirPrefix val hvr hvp stRoot hRootPure hRwx hNonePure
  rw [hRun]
  dsimp only
  rw [allPass_assert_end]
  refine ⟨⟨_, rfl, rfl, ?_⟩, trivial⟩
  dsimp only [Internal.mapFsError]
  rw [show ("rm failed" : String).isEmpty = false from rfl]
  simp

/-- Non-vacuity `CanReach` witness for Spec 3 (`test_temp_withTempDir_cleanupErrorReturnedOnOk`). -/
theorem reach_temp_withTempDir_cleanupErrorReturnedOnOk :
    CanReach (test_temp_withTempDir_cleanupErrorReturnedOnOk
      (S := TempMockState) Internal.mkApiM mockFs mockTime mockUuid mockEnv) := by
  dsimp only [test_temp_withTempDir_cleanupErrorReturnedOnOk, CanReach]
  obtain ⟨s₀, hs₀⟩ : ∃ s : TempMockState, s = {} := ⟨{}, rfl⟩
  rw [canReach_nondet]; refine ⟨s₀, ?_⟩
  rw [canReach_nondet]; refine ⟨"/tmp", ?_⟩
  rw [canReach_nondet]; refine ⟨"tmp-", ?_⟩
  rw [canReach_nondet]; refine ⟨7, ?_⟩
  rw [canReach_assume]; refine ⟨⟨rfl, rfl⟩, ?_⟩
  have hRootPure : mockStatPure s₀ "/tmp" = .ok (mockNodeStat (.dir 0 0o755)) := by
    rw [hs₀]; rfl
  have hRoot : ∃ stRoot, ((mockFs.stat "/tmp").run s₀).1 = .ok stRoot ∧
      stRoot.kind = .dir ∧ (stRoot.mode / 256) % 2 = 1 ∧ (stRoot.mode / 128) % 2 = 1 ∧ (stRoot.mode / 64) % 2 = 1 :=
    ⟨mockNodeStat (.dir 0 0o755), by rw [mockFs_stat_run]; exact hRootPure, rfl, rfl, rfl, rfl⟩
  rw [canReach_assume]; refine ⟨hRoot, ?_⟩
  rw [mockUuid_getUuid_run s₀]
  dsimp only
  have hNonePure : (mockLstatPure { s₀ with nextUuid := s₀.nextUuid + 1 }
      (mockJoin "/tmp" ("tmp-" ++ mockUuidToString (mockUuidOfNat s₀.nextUuid)))).isOk = false := by
    rw [hs₀]
    unfold mockLstatPure
    dsimp only
    have ⟨hcNe, hcNoSlash⟩ := childName_parts "tmp-" (mockUuidOfNat 1) rfl
    have hNe : normKey "/tmp" ≠ normKey (mockJoin "/tmp" ("tmp-" ++ mockUuidToString (mockUuidOfNat 1))) :=
      ne_comm.mp (mockJoin_ne_root "/tmp" _ (by decide) hcNe hcNoSlash)
    rw [lookupNode_cons_ne "/tmp" (.dir 0 0o755) [] _ hNe]
    rfl
  have hNone : (mockFs.lstat (mockFs.join "/tmp" ("tmp-" ++ mockUuid.toString (mockUuidOfNat s₀.nextUuid)))).run
      { s₀ with nextUuid := s₀.nextUuid + 1 } |>.1.isOk = false := by
    rw [mockFs_lstat_run, mockFs_join_eq, mockUuid_toString_eq]
    exact hNonePure
  rw [canReach_assume]; refine ⟨hNone, ?_⟩
  obtain ⟨s₁, hRun⟩ := spec3_exec s₀ "/tmp" "tmp-" 7 rfl rfl
    (mockNodeStat (.dir 0 0o755)) hRootPure ⟨rfl, rfl, rfl, rfl⟩ hNonePure
  rw [hRun]
  dsimp only
  rw [canReach_assert_end]
  refine ⟨⟨_, rfl, rfl, ?_⟩, trivial⟩
  dsimp only [Internal.mapFsError]
  rw [show ("rm failed" : String).isEmpty = false from rfl]
  simp

private theorem createTempDir_mock_collision (s₀ : TempMockState) (root dirPrefix : String)
    (hvr : (!root.isEmpty && !(Char.ofNat 0 ∈ root.toList)) = true)
    (hvp : (!dirPrefix.isEmpty && dirPrefix.toList.head? != some '.' && !('/' ∈ dirPrefix.toList) && !(Char.ofNat 0 ∈ dirPrefix.toList)) = true)
    (stRoot : FileStat) (hRoot : mockStatPure s₀ root = .ok stRoot)
    (hRwx : stRoot.kind = .dir ∧ (stRoot.mode / 256) % 2 = 1 ∧ (stRoot.mode / 128) % 2 = 1 ∧ (stRoot.mode / 64) % 2 = 1)
    (stExist : FileStat)
    (hExist : mockLstatPure { s₀ with nextUuid := s₀.nextUuid + 1 }
      (mockJoin root (dirPrefix ++ mockUuidToString (mockUuidOfNat s₀.nextUuid))) = .ok stExist) :
    let u := mockUuidOfNat s₀.nextUuid
    let dir := mockJoin root (dirPrefix ++ mockUuidToString u)
    let te := Internal.mapFsError { kind := .alreadyExists, path := some dir, message := "exists" }
    (Internal.createTempDir mockFs mockUuid mockEnv (some root) dirPrefix).run s₀ =
      (.error te, { s₀ with nextUuid := s₀.nextUuid + 1 }) := by
  intro u dir te
  have hrNe : root ≠ "" := validRoot_ne_empty root hvr
  have ⟨hcNe, hcNoSlash⟩ := childName_parts dirPrefix u hvp
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
  have hLookExist : ∃ existNode, lookupNode s₀.nodes dir = some existNode := by
    unfold mockLstatPure at hExist
    cases hl : lookupNode s₀.nodes dir with
    | none =>
      dsimp only [dir] at hl
      rw [hl] at hExist
      simp at hExist
    | some en => exact ⟨en, rfl⟩
  rcases hLookExist with ⟨existNode, hLookExist⟩
  have hvr' : Internal.validRoot root = true := by simpa [Internal.validRoot] using hvr
  have hvp' : Internal.validPrefix dirPrefix = true := by simpa [Internal.validPrefix] using hvp
  have hWx : hasWx stRoot = true := hasWx_of_hasRwx stRoot hRwx
  have hMkFail : (mockFs.mkdir dir false false).run { s₀ with nextUuid := s₀.nextUuid + 1 } =
      (.error { kind := .alreadyExists, path := some dir, message := "exists" },
       { s₀ with nextUuid := s₀.nextUuid + 1 }) := by
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
    rw [hLookExist]
    cases existNode <;> exact stateM_pure_run _ _
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
  rw [stateM_bind_run, hMkFail]
  dsimp only
  rw [stateM_pure_run]

/-- Spec 4: Exclusive creation rejects pre-existing directories or symlinks with `.alreadyExists`. -/
theorem proof_temp_withTempDir_collisionRejected :
    AllPass (test_temp_withTempDir_collisionRejected
      (S := TempMockState) Internal.mkApiM mockFs mockTime mockUuid mockEnv) := by
  dsimp only [test_temp_withTempDir_collisionRejected, AllPass]
  intro s₀ root dirPrefix markerPath ⟨hvr, hvp⟩ ⟨stRoot, hRoot, hRwx⟩ hMarker
  have hRootPure : mockStatPure s₀ root = .ok stRoot := by
    rw [mockFs_stat_run] at hRoot
    exact hRoot
  rw [mockUuid_getUuid_run s₀]
  dsimp only
  rw [allPass_assume]
  rintro ⟨stExist, hExist, _⟩
  have hExistPure : mockLstatPure { s₀ with nextUuid := s₀.nextUuid + 1 }
      (mockJoin root (dirPrefix ++ mockUuidToString (mockUuidOfNat s₀.nextUuid))) = .ok stExist := by
    rw [mockFs_lstat_run, mockFs_join_eq, mockUuid_toString_eq] at hExist
    exact hExist
  have hCreErr := createTempDir_mock_collision s₀ root dirPrefix hvr hvp stRoot hRootPure hRwx stExist hExistPure
  rw [mkApiM_withTempDir_eq]
  dsimp only [Internal.withTempDirM]
  rw [stateM_bind_run, hCreErr]
  dsimp only
  rw [stateM_pure_run]
  dsimp only
  rw [allPass_assert, allPass_assert, allPass_assert_end]
  have hMarkerAfter : ((mockFs.lstat markerPath).run { s₀ with nextUuid := s₀.nextUuid + 1 }).1.isOk = false := by
    rw [mockFs_lstat_run] at hMarker ⊢
    exact hMarker
  have hDirAfter : ((mockFs.lstat (mockFs.join root (dirPrefix ++ mockUuid.toString (mockUuidOfNat s₀.nextUuid)))).run
      { s₀ with nextUuid := s₀.nextUuid + 1 }).1.isOk = true := by
    rw [hExist]
    rfl
  exact ⟨⟨_, rfl, rfl⟩, hMarkerAfter, hDirAfter, trivial⟩

/-- Non-vacuity `CanReach` witness for Spec 4 (`test_temp_withTempDir_collisionRejected`). -/
theorem reach_temp_withTempDir_collisionRejected :
    CanReach (test_temp_withTempDir_collisionRejected
      (S := TempMockState) Internal.mkApiM mockFs mockTime mockUuid mockEnv) := by
  dsimp only [test_temp_withTempDir_collisionRejected, CanReach]
  let dir := mockJoin "/tmp" ("tmp-" ++ mockUuidToString (mockUuidOfNat 1))
  obtain ⟨s₀, hs₀⟩ : ∃ s : TempMockState,
      s = { nodes := [("/tmp", .dir 0 0o755), (dir, .dir 0 0o755)] } := ⟨_, rfl⟩
  rw [canReach_nondet]; refine ⟨s₀, ?_⟩
  rw [canReach_nondet]; refine ⟨"/tmp", ?_⟩
  rw [canReach_nondet]; refine ⟨"tmp-", ?_⟩
  rw [canReach_nondet]; refine ⟨"/other", ?_⟩
  rw [canReach_assume]; refine ⟨⟨rfl, rfl⟩, ?_⟩
  have hRootPure : mockStatPure s₀ "/tmp" = .ok (mockNodeStat (.dir 0 0o755)) := by
    rw [hs₀]
    unfold mockStatPure mockLstatPure
    rw [lookupNode_cons_eq "/tmp" (.dir 0 0o755) [(dir, .dir 0 0o755)] "/tmp" rfl]
  have hRoot : ∃ stRoot, ((mockFs.stat "/tmp").run s₀).1 = .ok stRoot ∧
      stRoot.kind = .dir ∧ (stRoot.mode / 256) % 2 = 1 ∧ (stRoot.mode / 128) % 2 = 1 ∧ (stRoot.mode / 64) % 2 = 1 :=
    ⟨mockNodeStat (.dir 0 0o755), by rw [mockFs_stat_run]; exact hRootPure, rfl, rfl, rfl, rfl⟩
  rw [canReach_assume]; refine ⟨hRoot, ?_⟩
  have ⟨hcNe, hcNoSlash⟩ := childName_parts "tmp-" (mockUuidOfNat 1) rfl
  have hDirNeOther : normKey dir ≠ normKey "/other" := mockJoin_tmp_ne_other _ hcNe hcNoSlash
  have hMarker : ((mockFs.lstat "/other").run s₀).1.isOk = false := by
    rw [hs₀]
    apply mockFs_lstat_isOk_false_of_lookup_none
    rw [lookupNode_cons_ne "/tmp" _ _ "/other" (by decide)]
    rw [lookupNode_cons_ne dir _ [] "/other" hDirNeOther]
    rfl
  rw [canReach_assume]; refine ⟨hMarker, ?_⟩
  rw [mockUuid_getUuid_run s₀]
  dsimp only
  have hTmpNeDir : normKey "/tmp" ≠ normKey dir :=
    ne_comm.mp (mockJoin_ne_root "/tmp" _ (by decide) hcNe hcNoSlash)
  have hNextId : s₀.nextUuid = 1 := by rw [hs₀]
  have hExistPure : mockLstatPure { s₀ with nextUuid := s₀.nextUuid + 1 }
      (mockJoin "/tmp" ("tmp-" ++ mockUuidToString (mockUuidOfNat s₀.nextUuid))) =
      .ok (mockNodeStat (.dir 0 0o755)) := by
    rw [hNextId, hs₀]
    unfold mockLstatPure
    dsimp only
    rw [lookupNode_cons_ne "/tmp" _ _ dir hTmpNeDir]
    rw [lookupNode_cons_eq dir (.dir 0 0o755) [] dir rfl]
  have hExist : ∃ stExist, ((mockFs.lstat (mockFs.join "/tmp" ("tmp-" ++ mockUuid.toString (mockUuidOfNat s₀.nextUuid)))).run
      { s₀ with nextUuid := s₀.nextUuid + 1 }).1 = .ok stExist ∧ (stExist.kind = EntryKind.dir ∨ stExist.kind = EntryKind.symlink) :=
    ⟨mockNodeStat (.dir 0 0o755), by rw [mockFs_lstat_run, mockFs_join_eq, mockUuid_toString_eq]; exact hExistPure, Or.inl rfl⟩
  rw [canReach_assume]; refine ⟨hExist, ?_⟩
  have hCreErr := createTempDir_mock_collision s₀ "/tmp" "tmp-" rfl rfl
    (mockNodeStat (.dir 0 0o755)) hRootPure ⟨rfl, rfl, rfl, rfl⟩ (mockNodeStat (.dir 0 0o755)) hExistPure
  rw [mkApiM_withTempDir_eq]
  dsimp only [Internal.withTempDirM]
  rw [stateM_bind_run, hCreErr]
  dsimp only
  rw [stateM_pure_run]
  dsimp only
  rw [canReach_assert, canReach_assert, canReach_assert_end]
  have hMarkerAfter : ((mockFs.lstat "/other").run { s₀ with nextUuid := s₀.nextUuid + 1 }).1.isOk = false := by
    rw [mockFs_lstat_run] at hMarker ⊢
    exact hMarker
  have hDirAfter : ((mockFs.lstat (mockFs.join "/tmp" ("tmp-" ++ mockUuid.toString (mockUuidOfNat s₀.nextUuid)))).run
      { s₀ with nextUuid := s₀.nextUuid + 1 }).1.isOk = true := by
    rw [mockFs_lstat_run, mockFs_join_eq, mockUuid_toString_eq, hExistPure]
    rfl
  exact ⟨⟨_, rfl, rfl⟩, hMarkerAfter, hDirAfter, trivial⟩

private theorem spec5_exec (s₀ : TempMockState) (root dirPrefix markerPath : String)
    (hvr : (!root.isEmpty && !(Char.ofNat 0 ∈ root.toList)) = true)
    (hvp : (!dirPrefix.isEmpty && dirPrefix.toList.head? != some '.' && !('/' ∈ dirPrefix.toList) && !(Char.ofNat 0 ∈ dirPrefix.toList)) = true)
    (stRoot : FileStat) (hRoot : mockStatPure s₀ root = .ok stRoot)
    (hRwx : stRoot.kind = .dir ∧ (stRoot.mode / 256) % 2 = 1 ∧ (stRoot.mode / 128) % 2 = 1 ∧ (stRoot.mode / 64) % 2 = 1)
    (hMarker : ((mockFs.lstat markerPath).run s₀).1.isOk = false)
    (hNone : (mockLstatPure { s₀ with nextUuid := s₀.nextUuid + 1 }
      (mockJoin root (dirPrefix ++ mockUuidToString (mockUuidOfNat s₀.nextUuid)))).isOk = false) :
    let u := mockUuidOfNat s₀.nextUuid
    let dir := mockJoin root (dirPrefix ++ mockUuidToString u)
    let fsBadChmod : FsApiM (StateM TempMockState) :=
      { mockFs with chmod := fun p _ => pure (.error { kind := .permissionDenied, path := some p, message := "chmod denied" }) }
    ∃ s₁ : TempMockState,
      (Internal.createTempDir fsBadChmod mockUuid mockEnv (some root) dirPrefix).run s₀ =
        (.error (Internal.mapFsError { kind := .permissionDenied, path := some dir, message := "chmod denied" }), s₁) ∧
      ((mockFs.lstat markerPath).run s₁).1.isOk = false ∧
      ((mockFs.lstat dir).run s₁).1.isOk = false := by
  intro u dir fsBadChmod
  have ⟨hcNe, hcNoSlash⟩ := childName_parts dirPrefix u hvp
  have hrNe : root ≠ "" := validRoot_ne_empty root hvr
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
  obtain ⟨sMk, hsMk⟩ : ∃ s : TempMockState, s =
      { s₀ with
        nextUuid := s₀.nextUuid + 1
        nodes := (dir, .dir s₀.nowSec 0o755) :: s₀.nodes.filter (fun e => !underDir dir e.1) } := ⟨_, rfl⟩
  have hMk : (fsBadChmod.mkdir dir false false).run { s₀ with nextUuid := s₀.nextUuid + 1 } = (.ok (), sMk) := by
    rw [hsMk]
    dsimp only [fsBadChmod, mockFs]
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
  have hLookDirMk : lookupNode sMk.nodes dir = some (.dir s₀.nowSec 0o755) := by
    rw [hsMk]; exact lookupNode_cons_eq _ _ _ _ rfl
  obtain ⟨sFin, hsFin⟩ : ∃ s : TempMockState, s =
      { sMk with nodes := sMk.nodes.filter (fun e => !underDir dir e.1) } := ⟨_, rfl⟩
  have hClean : (Internal.cleanupDirIgnoringNotFound fsBadChmod dir).run sMk = (.ok (), sFin) := by
    rw [hsFin]
    dsimp only [Internal.cleanupDirIgnoringNotFound, fsBadChmod, mockFs, mockRmtreePure, resolveParentTarget]
    rw [stateM_bind_run, stateM_bind_run, stateM_get_run]
    dsimp only
    rw [hDirNorm, hLookDirMk]
    simp only [stateM_bind_run, stateM_set_run, stateM_pure_run]
  have hResStep : (Internal.resolveRoot fsBadChmod mockEnv (some root)).run s₀ = (.ok root, s₀) :=
    resolveRoot_some_mock_run s₀ root hvr stRoot hRoot hRwx.1
  have hUuidStep : mockUuid.getUuid.run s₀ = (.ok u, { s₀ with nextUuid := s₀.nextUuid + 1 }) := by
    simp [mockUuid, u]; rfl
  have hChFail : (fsBadChmod.chmod dir 0o700).run sMk =
      (.error { kind := .permissionDenied, path := some dir, message := "chmod denied" }, sMk) := by
    dsimp only [fsBadChmod]
    exact stateM_pure_run _ _
  have hCreErr : (Internal.createTempDir fsBadChmod mockUuid mockEnv (some root) dirPrefix).run s₀ =
      (.error (Internal.mapFsError { kind := .permissionDenied, path := some dir, message := "chmod denied" }), sFin) := by
    dsimp only [Internal.createTempDir]
    simp only [hvp', Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    rw [stateM_bind_run, hResStep]
    dsimp only
    rw [stateM_bind_run, hUuidStep]
    dsimp only
    have hDirEq : fsBadChmod.join root (dirPrefix ++ mockUuid.toString u) = dir := by
      dsimp only [fsBadChmod]
      rw [mockFs_join_eq, mockUuid_toString_eq]
    simp only [hDirEq]
    rw [stateM_bind_run, hMk]
    dsimp only
    rw [stateM_bind_run, hChFail]
    dsimp only
    rw [stateM_bind_run, hClean]
    dsimp only
    rw [stateM_pure_run]
  have hMarkerNone0 : lookupNode s₀.nodes markerPath = none :=
    lookupNode_none_of_lstat_isOk_false s₀ markerPath hMarker
  have hMarkerGone : ((mockFs.lstat markerPath).run sFin).1.isOk = false := by
    rw [hsFin, hsMk]
    apply mockFs_lstat_isOk_false_of_lookup_none
    dsimp only
    rw [List.filter_cons]
    have hSelf : (!underDir dir dir) = false := by simp [underDir_refl dir hDirNorm]
    rw [hSelf]
    apply lookupNode_filter_none_of_none
    exact lookupNode_filter_none_of_none s₀.nodes _ markerPath hMarkerNone0
  have hDirGone : ((mockFs.lstat dir).run sFin).1.isOk = false := by
    rw [hsFin]
    apply mockFs_lstat_isOk_false_of_lookup_none
    exact lookupNode_filter_underDir_eq _ _ hDirNorm
  exact ⟨sFin, hCreErr, hMarkerGone, hDirGone⟩

/-- Spec 5: If `fs.chmod dir 0o700` fails right after `fs.mkdir`, `withTempDir` rolls back `dir` without running `action`. -/
theorem proof_temp_withTempDir_chmodFailureRollsBack :
    AllPass (test_temp_withTempDir_chmodFailureRollsBack
      (S := TempMockState) Internal.mkApiM mockFs mockTime mockUuid mockEnv) := by
  dsimp only [test_temp_withTempDir_chmodFailureRollsBack, AllPass]
  intro s₀ root dirPrefix markerPath ⟨hvr, hvp⟩ ⟨stRoot, hRoot, hRwx⟩ hMarker
  have hRootPure : mockStatPure s₀ root = .ok stRoot := by
    rw [mockFs_stat_run] at hRoot
    exact hRoot
  rw [mockUuid_getUuid_run s₀]
  dsimp only
  rw [allPass_assume]
  intro hNone
  have hNonePure : (mockLstatPure { s₀ with nextUuid := s₀.nextUuid + 1 }
      (mockJoin root (dirPrefix ++ mockUuidToString (mockUuidOfNat s₀.nextUuid)))).isOk = false := by
    rw [mockFs_lstat_run, mockFs_join_eq, mockUuid_toString_eq] at hNone
    exact hNone
  obtain ⟨s₁, hCreErr, hMarkerGone, hDirGone⟩ :=
    spec5_exec s₀ root dirPrefix markerPath hvr hvp stRoot hRootPure hRwx hMarker hNonePure
  rw [mkApiM_withTempDir_eq]
  dsimp only [Internal.withTempDirM]
  rw [stateM_bind_run, hCreErr]
  dsimp only
  rw [stateM_pure_run]
  dsimp only
  rw [allPass_assert, allPass_assert, allPass_assert_end]
  rw [mockFs_join_eq, mockUuid_toString_eq]
  exact ⟨⟨_, rfl, rfl⟩, hMarkerGone, hDirGone, trivial⟩

/-- Non-vacuity `CanReach` witness for Spec 5 (`test_temp_withTempDir_chmodFailureRollsBack`). -/
theorem reach_temp_withTempDir_chmodFailureRollsBack :
    CanReach (test_temp_withTempDir_chmodFailureRollsBack
      (S := TempMockState) Internal.mkApiM mockFs mockTime mockUuid mockEnv) := by
  dsimp only [test_temp_withTempDir_chmodFailureRollsBack, CanReach]
  obtain ⟨s₀, hs₀⟩ : ∃ s : TempMockState, s = {} := ⟨{}, rfl⟩
  rw [canReach_nondet]; refine ⟨s₀, ?_⟩
  rw [canReach_nondet]; refine ⟨"/tmp", ?_⟩
  rw [canReach_nondet]; refine ⟨"tmp-", ?_⟩
  rw [canReach_nondet]; refine ⟨"/other", ?_⟩
  rw [canReach_assume]; refine ⟨⟨rfl, rfl⟩, ?_⟩
  have hRootPure : mockStatPure s₀ "/tmp" = .ok (mockNodeStat (.dir 0 0o755)) := by
    rw [hs₀]; rfl
  have hRoot : ∃ stRoot, ((mockFs.stat "/tmp").run s₀).1 = .ok stRoot ∧
      stRoot.kind = .dir ∧ (stRoot.mode / 256) % 2 = 1 ∧ (stRoot.mode / 128) % 2 = 1 ∧ (stRoot.mode / 64) % 2 = 1 :=
    ⟨mockNodeStat (.dir 0 0o755), by rw [mockFs_stat_run]; exact hRootPure, rfl, rfl, rfl, rfl⟩
  rw [canReach_assume]; refine ⟨hRoot, ?_⟩
  have hMarker : ((mockFs.lstat "/other").run s₀).1.isOk = false := by
    rw [hs₀]
    apply mockFs_lstat_isOk_false_of_lookup_none
    rw [lookupNode_cons_ne "/tmp" _ [] "/other" (by decide)]
    rfl
  rw [canReach_assume]; refine ⟨hMarker, ?_⟩
  rw [mockUuid_getUuid_run s₀]
  dsimp only
  have hNonePure : (mockLstatPure { s₀ with nextUuid := s₀.nextUuid + 1 }
      (mockJoin "/tmp" ("tmp-" ++ mockUuidToString (mockUuidOfNat s₀.nextUuid)))).isOk = false := by
    rw [hs₀]
    unfold mockLstatPure
    dsimp only
    have ⟨hcNe, hcNoSlash⟩ := childName_parts "tmp-" (mockUuidOfNat 1) rfl
    have hNe : normKey "/tmp" ≠ normKey (mockJoin "/tmp" ("tmp-" ++ mockUuidToString (mockUuidOfNat 1))) :=
      ne_comm.mp (mockJoin_ne_root "/tmp" _ (by decide) hcNe hcNoSlash)
    rw [lookupNode_cons_ne "/tmp" (.dir 0 0o755) [] _ hNe]
    rfl
  have hNone : (mockFs.lstat (mockFs.join "/tmp" ("tmp-" ++ mockUuid.toString (mockUuidOfNat s₀.nextUuid)))).run
      { s₀ with nextUuid := s₀.nextUuid + 1 } |>.1.isOk = false := by
    rw [mockFs_lstat_run, mockFs_join_eq, mockUuid_toString_eq]
    exact hNonePure
  rw [canReach_assume]; refine ⟨hNone, ?_⟩
  obtain ⟨s₁, hCreErr, hMarkerGone, hDirGone⟩ :=
    spec5_exec s₀ "/tmp" "tmp-" "/other" rfl rfl (mockNodeStat (.dir 0 0o755)) hRootPure ⟨rfl, rfl, rfl, rfl⟩ hMarker hNonePure
  rw [mkApiM_withTempDir_eq]
  dsimp only [Internal.withTempDirM]
  rw [stateM_bind_run, hCreErr]
  dsimp only
  rw [stateM_pure_run]
  dsimp only
  rw [canReach_assert, canReach_assert, canReach_assert_end]
  rw [mockFs_join_eq, mockUuid_toString_eq]
  exact ⟨⟨_, rfl, rfl⟩, hMarkerGone, hDirGone, trivial⟩

private theorem resolveRoot_some_invalid_run (s₀ : TempMockState) (root : String)
    (hInv : Internal.validRoot root = false) :
    ∃ te : TempError,
      (Internal.resolveRoot mockFs mockEnv (some root)).run s₀ = (.error te, s₀) ∧
      te.kind = .invalidInput ∧ te.message ≠ "" := by
  dsimp only [Internal.resolveRoot]
  rw [stateM_bind_run, stateM_pure_run]
  dsimp only
  simp only [hInv, Bool.not_false, ↓reduceIte, stateM_pure_run]
  exact ⟨_, rfl, rfl, by simp⟩

private theorem spec6_exec (s₀ : TempMockState) (root dirPrefix : String)
    (hInv : (¬ Internal.validPrefix dirPrefix) ∨ (¬ Internal.validRoot root)) :
    (∃ e, ((Internal.mkApiM mockFs mockTime mockUuid mockEnv).withTempDir (some root) dirPrefix
      (fun _ => pure (.ok () : Except TempError Unit))).run s₀ = (.error e, s₀) ∧ e.kind = .invalidInput ∧ e.message ≠ "") ∧
    (∃ e, ((Internal.mkApiM mockFs mockTime mockUuid mockEnv).withLockedTempDir (some root) dirPrefix
      (fun _ => pure (.ok () : Except TempError Unit))).run s₀ = (.error e, s₀) ∧ e.kind = .invalidInput ∧ e.message ≠ "") ∧
    (∃ e, ((Internal.mkApiM mockFs mockTime mockUuid mockEnv).cleanupStaleTempDirs (some root) dirPrefix 86400).run s₀ =
      (.error e, s₀) ∧ e.kind = .invalidInput ∧ e.message ≠ "") := by
  by_cases hvp : Internal.validPrefix dirPrefix = true
  · have hvr : Internal.validRoot root = false := by
      rcases hInv with hnp | hnr
      · exact absurd hvp hnp
      · cases h : Internal.validRoot root with
        | false => rfl
        | true => exact absurd h hnr
    obtain ⟨te, hRes, hKind, hMsg⟩ := resolveRoot_some_invalid_run s₀ root hvr
    have hCre : (Internal.createTempDir mockFs mockUuid mockEnv (some root) dirPrefix).run s₀ = (.error te, s₀) := by
      dsimp only [Internal.createTempDir]
      simp only [hvp, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
      rw [stateM_bind_run, hRes]
      exact stateM_pure_run _ _
    have h1 : ((Internal.mkApiM mockFs mockTime mockUuid mockEnv).withTempDir (some root) dirPrefix
        (fun _ => pure (.ok () : Except TempError Unit))).run s₀ = (.error te, s₀) := by
      rw [mkApiM_withTempDir_eq]
      dsimp only [Internal.withTempDirM]
      rw [stateM_bind_run, hCre]
      exact stateM_pure_run _ _
    have h2 : ((Internal.mkApiM mockFs mockTime mockUuid mockEnv).withLockedTempDir (some root) dirPrefix
        (fun _ => pure (.ok () : Except TempError Unit))).run s₀ = (.error te, s₀) := by
      rw [mkApiM_withLockedTempDir_eq]
      dsimp only [Internal.withLockedTempDirM]
      rw [stateM_bind_run, hCre]
      exact stateM_pure_run _ _
    have h3 : ((Internal.mkApiM mockFs mockTime mockUuid mockEnv).cleanupStaleTempDirs (some root) dirPrefix 86400).run s₀ =
        (.error te, s₀) := by
      rw [mkApiM_cleanupStaleTempDirs_eq]
      dsimp only [Internal.cleanupStaleTempDirsM]
      simp only [hvp, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
      rw [stateM_bind_run, hRes]
      exact stateM_pure_run _ _
    exact ⟨⟨te, h1, hKind, hMsg⟩, ⟨te, h2, hKind, hMsg⟩, ⟨te, h3, hKind, hMsg⟩⟩
  · have hvpF : Internal.validPrefix dirPrefix = false := Bool.eq_false_iff.mpr hvp
    have hCre : (Internal.createTempDir mockFs mockUuid mockEnv (some root) dirPrefix).run s₀ =
        (.error { kind := .invalidInput, path := none, message := "invalid temporary directory prefix" }, s₀) := by
      dsimp only [Internal.createTempDir]
      simp only [hvpF, Bool.not_false, ↓reduceIte, stateM_pure_run]
    have h1 : ((Internal.mkApiM mockFs mockTime mockUuid mockEnv).withTempDir (some root) dirPrefix
        (fun _ => pure (.ok () : Except TempError Unit))).run s₀ =
        (.error { kind := .invalidInput, path := none, message := "invalid temporary directory prefix" }, s₀) := by
      rw [mkApiM_withTempDir_eq]
      dsimp only [Internal.withTempDirM]
      rw [stateM_bind_run, hCre]
      exact stateM_pure_run _ _
    have h2 : ((Internal.mkApiM mockFs mockTime mockUuid mockEnv).withLockedTempDir (some root) dirPrefix
        (fun _ => pure (.ok () : Except TempError Unit))).run s₀ =
        (.error { kind := .invalidInput, path := none, message := "invalid temporary directory prefix" }, s₀) := by
      rw [mkApiM_withLockedTempDir_eq]
      dsimp only [Internal.withLockedTempDirM]
      rw [stateM_bind_run, hCre]
      exact stateM_pure_run _ _
    have h3 : ((Internal.mkApiM mockFs mockTime mockUuid mockEnv).cleanupStaleTempDirs (some root) dirPrefix 86400).run s₀ =
        (.error { kind := .invalidInput, path := none, message := "invalid temporary directory prefix" }, s₀) := by
      rw [mkApiM_cleanupStaleTempDirs_eq]
      dsimp only [Internal.cleanupStaleTempDirsM]
      simp only [hvpF, Bool.not_false, ↓reduceIte, stateM_pure_run]
    exact ⟨⟨_, h1, rfl, by decide⟩, ⟨_, h2, rfl, by decide⟩, ⟨_, h3, rfl, by decide⟩⟩

/-- Spec 6: All three operations reject invalid `prefix` or `root` with `.invalidInput` and zero state mutations. -/
theorem proof_temp_validation_rejectsInvalidInputs :
    AllPass (test_temp_validation_rejectsInvalidInputs
      (S := TempMockState) Internal.mkApiM mockFs mockTime mockUuid mockEnv) := by
  dsimp only [test_temp_validation_rejectsInvalidInputs, AllPass]
  intro s₀ root dirPrefix hInv
  have hInv' : (¬ Internal.validPrefix dirPrefix) ∨ (¬ Internal.validRoot root) := hInv
  obtain ⟨⟨e1, h1, hk1, hm1⟩, ⟨e2, h2, hk2, hm2⟩, ⟨e3, h3, hk3, hm3⟩⟩ := spec6_exec s₀ root dirPrefix hInv'
  rw [h1, h2, h3]
  dsimp only
  rw [allPass_assert, allPass_assert, allPass_assert, allPass_assert_end]
  exact ⟨⟨e1, rfl, hk1, hm1⟩, ⟨e2, rfl, hk2, hm2⟩, ⟨e3, rfl, hk3, hm3⟩, ⟨rfl, rfl, rfl⟩, trivial⟩

/-- Non-vacuity `CanReach` witness for Spec 6 (`test_temp_validation_rejectsInvalidInputs`). -/
theorem reach_temp_validation_rejectsInvalidInputs :
    CanReach (test_temp_validation_rejectsInvalidInputs
      (S := TempMockState) Internal.mkApiM mockFs mockTime mockUuid mockEnv) := by
  dsimp only [test_temp_validation_rejectsInvalidInputs, CanReach]
  obtain ⟨s₀, hs₀⟩ : ∃ s : TempMockState, s = {} := ⟨{}, rfl⟩
  rw [canReach_nondet]; refine ⟨s₀, ?_⟩
  rw [canReach_nondet]; refine ⟨"", ?_⟩
  rw [canReach_nondet]; refine ⟨"bad/prefix", ?_⟩
  have hInv : ¬ Internal.validPrefix "bad/prefix" ∨ ¬ Internal.validRoot "" := Or.inr (by decide)
  rw [canReach_assume]; refine ⟨hInv, ?_⟩
  obtain ⟨⟨e1, h1, hk1, hm1⟩, ⟨e2, h2, hk2, hm2⟩, ⟨e3, h3, hk3, hm3⟩⟩ := spec6_exec s₀ "" "bad/prefix" hInv
  rw [h1, h2, h3]
  dsimp only
  rw [canReach_assert, canReach_assert, canReach_assert, canReach_assert_end]
  exact ⟨⟨e1, rfl, hk1, hm1⟩, ⟨e2, rfl, hk2, hm2⟩, ⟨e3, rfl, hk3, hm3⟩, ⟨rfl, rfl, rfl⟩, trivial⟩

private theorem lookupNode_filter_none_of_underDir (nodes : List (String × MockNode)) (d p : String)
    (hu : underDir d p = true) :
    lookupNode (nodes.filter (fun e => !underDir d e.1)) p = none := by
  unfold lookupNode
  dsimp only
  induction nodes with
  | nil => simp
  | cons x xs ih =>
    rw [List.filter_cons]
    cases hKeep : (!underDir d x.1) with
    | false => exact ih
    | true =>
      simp only [↓reduceIte]
      have hne : (normKey x.1 == normKey p) = false := by
        rw [beq_false_of_ne]
        intro heq
        have hu' : underDir d x.1 = true := by rw [underDir_eq_of_normKey_eq d x.1 p heq]; exact hu
        simp [hu'] at hKeep
      rw [List.find?_cons, hne]
      exact ih

private theorem resolveRoot_none_invalid_run (s₀ : TempMockState) (tmpdir : String)
    (hTmp : s₀.tmpdir = some tmpdir) (hNe : tmpdir.isEmpty = false)
    (hNul : Char.ofNat 0 ∈ tmpdir.toList) :
    ∃ te : TempError,
      (Internal.resolveRoot mockFs mockEnv none).run s₀ = (.error te, s₀) ∧
      te.kind = .invalidInput := by
  have hEnvStep : (mockEnv.getEnv "TMPDIR").run s₀ = (.ok (some tmpdir), s₀) := by
    dsimp only [mockEnv]
    rw [show ("TMPDIR" == "TMPDIR") = true from by decide]
    simp only [↓reduceIte, stateM_bind_run, stateM_get_run, stateM_pure_run, hTmp]
  have hvrF : Internal.validRoot tmpdir = false := by
    simp [Internal.validRoot, hNe, hNul]
  dsimp only [Internal.resolveRoot]
  rw [stateM_bind_run, hEnvStep]
  dsimp only
  rw [hNe]
  simp only [Bool.false_eq_true, ↓reduceIte, stateM_bind_run, stateM_pure_run]
  simp only [hvrF, Bool.not_false, ↓reduceIte, stateM_pure_run]
  exact ⟨_, rfl, rfl⟩

private theorem resolveRoot_none_stat_err_run (s₀ : TempMockState) (r : String) (fe : FsError)
    (hRaw : (match s₀.tmpdir with
      | some v => if v.isEmpty then "/tmp" else v
      | none => "/tmp") = r)
    (hvr : Internal.validRoot r = true)
    (hStat : mockStatPure s₀ r = .error fe) :
    (Internal.resolveRoot mockFs mockEnv none).run s₀ = (.error (Internal.mapFsError fe), s₀) := by
  have hEnvStep : (mockEnv.getEnv "TMPDIR").run s₀ = (.ok s₀.tmpdir, s₀) := by
    dsimp only [mockEnv]
    rw [show ("TMPDIR" == "TMPDIR") = true from by decide]
    simp only [↓reduceIte, stateM_bind_run, stateM_get_run, stateM_pure_run]
  have hStatStep : (mockFs.stat r).run s₀ = (.error fe, s₀) := by
    rw [mockFs_stat_run, hStat]
  dsimp only [Internal.resolveRoot]
  rw [stateM_bind_run, hEnvStep]
  cases ht : s₀.tmpdir with
  | none =>
    rw [ht] at hRaw; dsimp only at hRaw; subst hRaw
    rw [stateM_bind_run, stateM_pure_run]
    simp only [hvr, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    rw [stateM_bind_run, hStatStep]
    exact stateM_pure_run _ _
  | some v =>
    rw [ht] at hRaw; dsimp only at hRaw; subst hRaw
    rw [stateM_bind_run, stateM_pure_run]
    simp only [hvr, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    rw [stateM_bind_run, hStatStep]
    exact stateM_pure_run _ _

private theorem resolveRoot_none_nonDir_run (s₀ : TempMockState) (r : String) (st : FileStat)
    (hRaw : (match s₀.tmpdir with
      | some v => if v.isEmpty then "/tmp" else v
      | none => "/tmp") = r)
    (hvr : Internal.validRoot r = true)
    (hStat : mockStatPure s₀ r = .ok st)
    (hNotDir : (st.kind != .dir) = true) :
    (Internal.resolveRoot mockFs mockEnv none).run s₀ =
      (.error { kind := .notADirectory, path := some r, message := "temporary root is not a directory" }, s₀) := by
  have hEnvStep : (mockEnv.getEnv "TMPDIR").run s₀ = (.ok s₀.tmpdir, s₀) := by
    dsimp only [mockEnv]
    rw [show ("TMPDIR" == "TMPDIR") = true from by decide]
    simp only [↓reduceIte, stateM_bind_run, stateM_get_run, stateM_pure_run]
  have hStatStep : (mockFs.stat r).run s₀ = (.ok st, s₀) := by
    rw [mockFs_stat_run, hStat]
  dsimp only [Internal.resolveRoot]
  rw [stateM_bind_run, hEnvStep]
  cases ht : s₀.tmpdir with
  | none =>
    rw [ht] at hRaw; dsimp only at hRaw; subst hRaw
    rw [stateM_bind_run, stateM_pure_run]
    simp only [hvr, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    rw [stateM_bind_run, hStatStep]
    dsimp only
    simp only [hNotDir, ↓reduceIte]
    exact stateM_pure_run _ _
  | some v =>
    rw [ht] at hRaw; dsimp only at hRaw; subst hRaw
    rw [stateM_bind_run, stateM_pure_run]
    simp only [hvr, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    rw [stateM_bind_run, hStatStep]
    dsimp only
    simp only [hNotDir, ↓reduceIte]
    exact stateM_pure_run _ _

private theorem resolveRoot_none_ok_run (s₀ : TempMockState) (r : String) (st : FileStat)
    (hRaw : (match s₀.tmpdir with
      | some v => if v.isEmpty then "/tmp" else v
      | none => "/tmp") = r)
    (hvr : Internal.validRoot r = true)
    (hStat : mockStatPure s₀ r = .ok st)
    (hDir : st.kind = .dir) :
    (Internal.resolveRoot mockFs mockEnv none).run s₀ = (.ok r, s₀) := by
  have hEnvStep : (mockEnv.getEnv "TMPDIR").run s₀ = (.ok s₀.tmpdir, s₀) := by
    dsimp only [mockEnv]
    rw [show ("TMPDIR" == "TMPDIR") = true from by decide]
    simp only [↓reduceIte, stateM_bind_run, stateM_get_run, stateM_pure_run]
  have hStatStep : (mockFs.stat r).run s₀ = (.ok st, s₀) := by
    rw [mockFs_stat_run, hStat]
  dsimp only [Internal.resolveRoot]
  rw [stateM_bind_run, hEnvStep]
  cases ht : s₀.tmpdir with
  | none =>
    rw [ht] at hRaw; dsimp only at hRaw; subst hRaw
    rw [stateM_bind_run, stateM_pure_run]
    simp only [hvr, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    rw [stateM_bind_run, hStatStep]
    simp only [hDir, show (EntryKind.dir != EntryKind.dir) = false from rfl,
      Bool.false_eq_true, ↓reduceIte, stateM_pure_run]
  | some v =>
    rw [ht] at hRaw; dsimp only at hRaw; subst hRaw
    rw [stateM_bind_run, stateM_pure_run]
    simp only [hvr, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    rw [stateM_bind_run, hStatStep]
    simp only [hDir, show (EntryKind.dir != EntryKind.dir) = false from rfl,
      Bool.false_eq_true, ↓reduceIte, stateM_pure_run]

private theorem mockFs_withFileLock_create_run {α : Type}
    (s : TempMockState) (p : String) (mode : LockMode)
    (hp : normKey p = p) (hNone : lookupNode s.nodes p = none)
    (act : StateM TempMockState (Except FsError α)) :
    let ino := freshInode s
    let sLock := { s with
      nodes := (p, .file ino "" s.nowSec 0o644) :: s.nodes
      locks := (ino, mode) :: s.locks
      nextInode := ino + 1 }
    (mockFs.withFileLock p mode true act).run s =
      ((act.run sLock).1, { (act.run sLock).2 with locks := mockRemoveFirstLock ino mode (act.run sLock).2.locks }) := by
  intro ino sLock
  dsimp only [mockFs, resolveParentTarget]
  rw [stateM_bind_run, stateM_get_run]
  dsimp only
  rw [hp, hNone]
  simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, stateM_bind_run, stateM_pure_run]
  have hSet : (set ({
      nodes := (p, MockNode.file (freshInode s) "" s.nowSec 420) :: s.nodes,
      locks := (freshInode s, mode) :: s.locks,
      nextInode := freshInode s + 1, tmpdir := s.tmpdir, nowSec := s.nowSec, nextUuid := s.nextUuid } : TempMockState) :
      StateM TempMockState Unit).run s = ((), sLock) := rfl
  rw [hSet]
  dsimp only
  cases hAct : act.run sLock with
  | mk r sA =>
    dsimp only
    have hMod : ((modify fun s' : TempMockState => { s' with locks := mockRemoveFirstLock ino mode s'.locks }) :
        StateM TempMockState Unit).run sA =
        ((), { sA with locks := mockRemoveFirstLock ino mode sA.locks }) := rfl
    rw [hMod]

private theorem createTempDir_none_mock_steps (s₀ : TempMockState) (root dirPrefix : String)
    (hvr : Internal.validRoot root = true)
    (hvp : Internal.validPrefix dirPrefix = true)
    (stRoot : FileStat) (hRoot : mockStatPure s₀ root = .ok stRoot)
    (hRwx : stRoot.kind = .dir ∧ (stRoot.mode / 256) % 2 = 1 ∧ (stRoot.mode / 128) % 2 = 1 ∧ (stRoot.mode / 64) % 2 = 1)
    (hRes : (Internal.resolveRoot mockFs mockEnv none).run s₀ = (.ok root, s₀))
    (hNone : (mockLstatPure { s₀ with nextUuid := s₀.nextUuid + 1 }
      (mockJoin root (dirPrefix ++ mockUuidToString (mockUuidOfNat s₀.nextUuid)))).isOk = false) :
    let u := mockUuidOfNat s₀.nextUuid
    let dir := mockJoin root (dirPrefix ++ mockUuidToString u)
    let sMk := { s₀ with
      nextUuid := s₀.nextUuid + 1
      nodes := (dir, .dir s₀.nowSec 0o700) :: s₀.nodes.filter (fun e => !underDir dir e.1) }
    (Internal.createTempDir mockFs mockUuid mockEnv none dirPrefix).run s₀ = (.ok dir, sMk) := by
  intro u dir sMk
  have hvr' : (!root.isEmpty && !(Char.ofNat 0 ∈ root.toList)) = true := by
    simpa [Internal.validRoot] using hvr
  have hvp' : (!dirPrefix.isEmpty && dirPrefix.toList.head? != some '.' && !('/' ∈ dirPrefix.toList) && !(Char.ofNat 0 ∈ dirPrefix.toList)) = true := by
    simpa [Internal.validPrefix] using hvp
  have hrNe : root ≠ "" := validRoot_ne_empty root hvr'
  have ⟨hcNe, hcNoSlash⟩ := childName_parts dirPrefix u hvp'
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
  have hUuidStep : mockUuid.getUuid.run s₀ = (.ok u, { s₀ with nextUuid := s₀.nextUuid + 1 }) := by
    simp [mockUuid, u]; rfl
  dsimp only [Internal.createTempDir]
  simp only [hvp, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  rw [stateM_bind_run, hRes]
  dsimp only
  rw [stateM_bind_run, hUuidStep]
  dsimp only
  have hDirEq : mockFs.join root (dirPrefix ++ mockUuid.toString u) = dir := rfl
  simp only [hDirEq]
  rw [stateM_bind_run, hMk]
  rw [stateM_bind_run, hCh]
  rw [stateM_pure_run]

private theorem spec7_err_all_three (s₀ : TempMockState) (dirPrefix : String) (te : TempError)
    (hvp : Internal.validPrefix dirPrefix = true)
    (hRes : (Internal.resolveRoot mockFs mockEnv none).run s₀ = (.error te, s₀)) :
    ((Internal.mkApiM mockFs mockTime mockUuid mockEnv).withTempDir none dirPrefix
      (fun _ => pure (.ok () : Except TempError Unit))).run s₀ = (.error te, s₀) ∧
    ((Internal.mkApiM mockFs mockTime mockUuid mockEnv).withLockedTempDir none dirPrefix
      (fun _ => pure (.ok () : Except TempError Unit))).run s₀ = (.error te, s₀) ∧
    ((Internal.mkApiM mockFs mockTime mockUuid mockEnv).cleanupStaleTempDirs none dirPrefix 86400).run s₀ =
      (.error te, s₀) := by
  have hCre : (Internal.createTempDir mockFs mockUuid mockEnv none dirPrefix).run s₀ = (.error te, s₀) := by
    dsimp only [Internal.createTempDir]
    simp only [hvp, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    rw [stateM_bind_run, hRes]
    exact stateM_pure_run _ _
  have h1 : ((Internal.mkApiM mockFs mockTime mockUuid mockEnv).withTempDir none dirPrefix
      (fun _ => pure (.ok () : Except TempError Unit))).run s₀ = (.error te, s₀) := by
    rw [mkApiM_withTempDir_eq]
    dsimp only [Internal.withTempDirM]
    rw [stateM_bind_run, hCre]
    exact stateM_pure_run _ _
  have h2 : ((Internal.mkApiM mockFs mockTime mockUuid mockEnv).withLockedTempDir none dirPrefix
      (fun _ => pure (.ok () : Except TempError Unit))).run s₀ = (.error te, s₀) := by
    rw [mkApiM_withLockedTempDir_eq]
    dsimp only [Internal.withLockedTempDirM]
    rw [stateM_bind_run, hCre]
    exact stateM_pure_run _ _
  have h3 : ((Internal.mkApiM mockFs mockTime mockUuid mockEnv).cleanupStaleTempDirs none dirPrefix 86400).run s₀ =
      (.error te, s₀) := by
    rw [mkApiM_cleanupStaleTempDirs_eq]
    dsimp only [Internal.cleanupStaleTempDirsM]
    simp only [hvp, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    rw [stateM_bind_run, hRes]
    exact stateM_pure_run _ _
  exact ⟨h1, h2, h3⟩

private theorem spec7_ok_all_three (s₀ : TempMockState) (root dirPrefix : String)
    (hvr : Internal.validRoot root = true)
    (hvp : Internal.validPrefix dirPrefix = true)
    (stRoot : FileStat) (hRoot : mockStatPure s₀ root = .ok stRoot)
    (hRwx : stRoot.kind = .dir ∧ (stRoot.mode / 256) % 2 = 1 ∧ (stRoot.mode / 128) % 2 = 1 ∧ (stRoot.mode / 64) % 2 = 1)
    (hRes : (Internal.resolveRoot mockFs mockEnv none).run s₀ = (.ok root, s₀))
    (hNone : (mockLstatPure { s₀ with nextUuid := s₀.nextUuid + 1 }
      (mockJoin root (dirPrefix ++ mockUuidToString (mockUuidOfNat s₀.nextUuid)))).isOk = false) :
    let dir := mockJoin root (dirPrefix ++ mockUuidToString (mockUuidOfNat s₀.nextUuid))
    ∃ s1 s2 s3 rep3,
      ((Internal.mkApiM mockFs mockTime mockUuid mockEnv).withTempDir none dirPrefix (fun d => pure (.ok d))).run s₀ =
        (.ok dir, s1) ∧
      ((Internal.mkApiM mockFs mockTime mockUuid mockEnv).withLockedTempDir none dirPrefix (fun d => pure (.ok d))).run s₀ =
        (.ok dir, s2) ∧
      ((Internal.mkApiM mockFs mockTime mockUuid mockEnv).cleanupStaleTempDirs none dirPrefix 86400).run s₀ =
        (.ok rep3, s3) := by
  intro dir
  have hvr' : (!root.isEmpty && !(Char.ofNat 0 ∈ root.toList)) = true := by
    simpa [Internal.validRoot] using hvr
  have hvp' : (!dirPrefix.isEmpty && dirPrefix.toList.head? != some '.' && !('/' ∈ dirPrefix.toList) && !(Char.ofNat 0 ∈ dirPrefix.toList)) = true := by
    simpa [Internal.validPrefix] using hvp
  have hrNe : root ≠ "" := validRoot_ne_empty root hvr'
  let u := mockUuidOfNat s₀.nextUuid
  have ⟨hcNe, hcNoSlash⟩ := childName_parts dirPrefix u hvp'
  have hDirNorm : normKey dir = dir := normKey_mockJoin root _ hcNe hcNoSlash
  have hDirNe : dir ≠ "" := mockJoin_ne_empty root _ hcNe
  have hDirNeSlash : dir ≠ "/" := mockJoin_ne_slash root _ hrNe hcNe
  have hCreate := createTempDir_none_mock_steps s₀ root dirPrefix hvr hvp stRoot hRoot hRwx hRes hNone
  dsimp only at hCreate
  obtain ⟨sMk, hsMk⟩ : ∃ s : TempMockState, s =
      { s₀ with
        nextUuid := s₀.nextUuid + 1
        nodes := (dir, .dir s₀.nowSec 0o700) :: s₀.nodes.filter (fun e => !underDir dir e.1) } := ⟨_, rfl⟩
  rw [← hsMk] at hCreate
  have hLookDirMk : lookupNode sMk.nodes dir = some (.dir s₀.nowSec 0o700) := by
    rw [hsMk]; exact lookupNode_cons_eq _ _ _ _ rfl
  obtain ⟨sFin1, hsFin1⟩ : ∃ s : TempMockState, s =
      { sMk with nodes := sMk.nodes.filter (fun e => !underDir dir e.1) } := ⟨_, rfl⟩
  have hClean1 : (Internal.cleanupDirIgnoringNotFound mockFs dir).run sMk = (.ok (), sFin1) := by
    rw [hsFin1]; exact cleanupDir_mock_run sMk dir hDirNorm ⟨_, _, hLookDirMk⟩
  have h1 : (((Internal.mkApiM mockFs mockTime mockUuid mockEnv).withTempDir none dirPrefix (fun d => pure (.ok d))).run s₀) =
      (.ok dir, sFin1) := by
    rw [mkApiM_withTempDir_eq]
    dsimp only [Internal.withTempDirM]
    rw [stateM_bind_run, hCreate]
    dsimp only
    rw [stateM_bind_run, stateM_tryFinally'_run, stateM_pure_run]
    dsimp only
    rw [hClean1]
    dsimp only
    rw [stateM_pure_run]
  let lockPath := mockJoin dir ".lock"
  have hLockNorm : normKey lockPath = lockPath := normKey_mockJoin dir ".lock" (by decide) (by decide)
  have hLockNeDir : normKey lockPath ≠ dir :=
    payload_ne_dir root (dirPrefix ++ mockUuidToString u) ".lock" hrNe hcNe hcNoSlash (by decide) (by decide)
  have hUnderLock : underDir dir lockPath = true :=
    underDir_mockJoin_self dir ".lock" hDirNe hDirNorm hDirNeSlash (by decide) (by decide)
  have hLookLockMk : lookupNode sMk.nodes lockPath = none := by
    rw [hsMk]
    unfold lookupNode
    dsimp only
    have hb : (normKey dir == normKey lockPath) = false := by
      rw [hDirNorm, beq_false_of_ne (ne_comm.mp hLockNeDir)]
    rw [List.find?_cons, hb]
    exact lookupNode_filter_none_of_underDir s₀.nodes dir lockPath hUnderLock
  obtain ⟨sAfterLock, hsAfterLock⟩ : ∃ s : TempMockState, s =
      { nodes := (lockPath, MockNode.file (freshInode sMk) "" sMk.nowSec 0o644) :: sMk.nodes
        locks := mockRemoveFirstLock (freshInode sMk) .shared ((freshInode sMk, .shared) :: sMk.locks)
        nextInode := freshInode sMk + 1
        tmpdir := sMk.tmpdir
        nowSec := sMk.nowSec
        nextUuid := sMk.nextUuid } := ⟨_, rfl⟩
  have hLookDirAfterLock : lookupNode sAfterLock.nodes dir = some (.dir s₀.nowSec 0o700) := by
    rw [hsAfterLock]
    unfold lookupNode
    dsimp only
    have hb : (normKey lockPath == normKey dir) = false := by
      rw [hDirNorm, beq_false_of_ne hLockNeDir]
    rw [List.find?_cons, hb]
    exact hLookDirMk
  obtain ⟨sFin2, hsFin2⟩ : ∃ s : TempMockState, s =
      { sAfterLock with nodes := sAfterLock.nodes.filter (fun e => !underDir dir e.1) } := ⟨_, rfl⟩
  have hClean2 : (Internal.cleanupDirIgnoringNotFound mockFs dir).run sAfterLock = (.ok (), sFin2) := by
    rw [hsFin2]; exact cleanupDir_mock_run sAfterLock dir hDirNorm ⟨_, _, hLookDirAfterLock⟩
  have h2 : (((Internal.mkApiM mockFs mockTime mockUuid mockEnv).withLockedTempDir none dirPrefix (fun d => pure (.ok d))).run s₀) =
      (.ok dir, sFin2) := by
    rw [mkApiM_withLockedTempDir_eq]
    dsimp only [Internal.withLockedTempDirM]
    rw [stateM_bind_run, hCreate]
    dsimp only
    rw [stateM_bind_run, stateM_tryFinally'_run]
    rw [mockFs_join_eq]
    rw [mockFs_withFileLock_create_run sMk lockPath .shared hLockNorm hLookLockMk]
    rw [stateM_bind_run, stateM_pure_run, stateM_pure_run]
    dsimp only
    rw [← hsAfterLock, hClean2]
    dsimp only
    rw [stateM_pure_run]
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
  have hRx : hasRx stRoot = true := by
    simp [hasRx, hRwx.1, hRwx.2.1, hRwx.2.2.2]; decide
  have hList : (mockFs.listDir root).run s₀ =
      (.ok (Internal.sortStrings (eraseDupStrings (s₀.nodes.filterMap (fun e => mockParentChild (normKey root) e.1)))).toArray, s₀) := by
    dsimp only [mockFs]
    rw [stateM_bind_run, stateM_get_run]
    dsimp only
    rw [hLookRootNorm]
    dsimp only
    rw [hStRoot]
    simp only [hRwx.1, show (EntryKind.dir != EntryKind.dir) = false from rfl,
      Bool.false_eq_true, ↓reduceIte, hRx, Bool.not_true]
    exact stateM_pure_run _ _
  have h3 : ∃ rep3 s3,
      ((Internal.mkApiM mockFs mockTime mockUuid mockEnv).cleanupStaleTempDirs none dirPrefix 86400).run s₀ =
        (.ok rep3, s3) := by
    rw [mkApiM_cleanupStaleTempDirs_eq]
    dsimp only [Internal.cleanupStaleTempDirsM]
    simp only [hvp, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    rw [stateM_bind_run, hRes]
    dsimp only
    have hTimeStep : mockTime.nowTimestamp.run s₀ =
        (Std.Time.Timestamp.ofSecondsSinceUnixEpoch (Std.Time.Second.Offset.ofInt s₀.nowSec), s₀) := by
      simp [mockTime]; rfl
    rw [stateM_bind_run, hTimeStep]
    dsimp only
    rw [stateM_bind_run, hList]
    dsimp only
    cases hSw : (Internal.sweepEntries mockFs root dirPrefix 86400
        (Std.Time.Timestamp.ofSecondsSinceUnixEpoch (Std.Time.Second.Offset.ofInt s₀.nowSec)).toSecondsSinceUnixEpoch.val
        {} (Internal.sortStrings (eraseDupStrings (s₀.nodes.filterMap (fun e => mockParentChild (normKey root) e.1)))).toArray.toList).run s₀ with
    | mk repSw sSw =>
      let rep3 : CleanupReport :=
        { removed := (Internal.sortStrings repSw.removed.toList).toArray
          keptLocked := (Internal.sortStrings repSw.keptLocked.toList).toArray
          keptFresh := (Internal.sortStrings repSw.keptFresh.toList).toArray
          skipped := (Internal.sortStrings repSw.skipped.toList).toArray
          failed := repSw.failed }
      refine ⟨rep3, sSw, ?_⟩
      rw [stateM_bind_run, hSw]
      dsimp only
      exact stateM_pure_run _ _
  rcases h3 with ⟨rep3, s3, h3⟩
  exact ⟨sFin1, sFin2, s3, rep3, h1, h2, h3⟩

/-- Spec 7: With `root? = none`, all three operations resolve non-empty `TMPDIR`, reject NUL `TMPDIR` with `.invalidInput`, reject missing/non-dir `TMPDIR` strictly, and fall back to `"/tmp"` when `TMPDIR` is unset or empty. -/
theorem proof_temp_rootResolution_tmpdirAndFallbackAndStrictMissing :
    AllPass (test_temp_rootResolution_tmpdirAndFallbackAndStrictMissing
      (S := TempMockState) Internal.mkApiM mockFs mockTime mockUuid mockEnv) := by
  dsimp only [test_temp_rootResolution_tmpdirAndFallbackAndStrictMissing, AllPass]
  intro s₀ dirPrefix hvp
  have hvp' : Internal.validPrefix dirPrefix = true := hvp
  have hEnvStep : (mockEnv.getEnv "TMPDIR").run s₀ = (.ok s₀.tmpdir, s₀) := by
    dsimp only [mockEnv]
    rw [show ("TMPDIR" == "TMPDIR") = true from by decide]
    simp only [↓reduceIte, stateM_bind_run, stateM_get_run, stateM_pure_run]
  rw [hEnvStep]
  dsimp only
  rw [mockUuid_getUuid_run s₀]
  dsimp only
  cases hTmp : s₀.tmpdir with
  | none =>
    dsimp only
    rw [allPass_assume]
    rintro ⟨stTmp, hStatTmp, hRwxTmp⟩
    have hStatTmpPure : mockStatPure s₀ "/tmp" = .ok stTmp := by
      rw [mockFs_stat_run] at hStatTmp; exact hStatTmp
    rw [allPass_assume]
    intro hNone
    have hNonePure : (mockLstatPure { s₀ with nextUuid := s₀.nextUuid + 1 }
        (mockJoin "/tmp" (dirPrefix ++ mockUuidToString (mockUuidOfNat s₀.nextUuid)))).isOk = false := by
      rw [mockFs_lstat_run, mockFs_join_eq, mockUuid_toString_eq] at hNone
      exact hNone
    have hRes := resolveRoot_none_ok_run s₀ "/tmp" stTmp (by rw [hTmp]) rfl hStatTmpPure hRwxTmp.1
    obtain ⟨s1, s2, s3, rep3, h1, h2, h3⟩ :=
      spec7_ok_all_three s₀ "/tmp" dirPrefix rfl hvp' stTmp hStatTmpPure hRwxTmp hRes hNonePure
    rw [h1, h2, h3]
    dsimp only
    rw [allPass_assert, allPass_assert, allPass_assert_end]
    rw [mockFs_join_eq, mockUuid_toString_eq]
    exact ⟨rfl, rfl, rfl, trivial⟩
  | some tmpdir =>
    dsimp only
    by_cases hEmpty : tmpdir.isEmpty = true
    · simp only [hEmpty, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
      rw [allPass_assume]
      rintro ⟨stTmp, hStatTmp, hRwxTmp⟩
      have hStatTmpPure : mockStatPure s₀ "/tmp" = .ok stTmp := by
        rw [mockFs_stat_run] at hStatTmp; exact hStatTmp
      rw [allPass_assume]
      intro hNone
      have hNonePure : (mockLstatPure { s₀ with nextUuid := s₀.nextUuid + 1 }
          (mockJoin "/tmp" (dirPrefix ++ mockUuidToString (mockUuidOfNat s₀.nextUuid)))).isOk = false := by
        rw [mockFs_lstat_run, mockFs_join_eq, mockUuid_toString_eq] at hNone
        exact hNone
      have hRes := resolveRoot_none_ok_run s₀ "/tmp" stTmp (by simp [hTmp, hEmpty]) rfl hStatTmpPure hRwxTmp.1
      obtain ⟨s1, s2, s3, rep3, h1, h2, h3⟩ :=
        spec7_ok_all_three s₀ "/tmp" dirPrefix rfl hvp' stTmp hStatTmpPure hRwxTmp hRes hNonePure
      rw [h1, h2, h3]
      dsimp only
      rw [allPass_assert, allPass_assert, allPass_assert_end]
      rw [mockFs_join_eq, mockUuid_toString_eq]
      exact ⟨rfl, rfl, rfl, trivial⟩
    · have hNe : tmpdir.isEmpty = false := Bool.eq_false_iff.mpr hEmpty
      simp only [hNe, Bool.not_false, ↓reduceIte]
      by_cases hNul : Char.ofNat 0 ∈ tmpdir.toList
      · simp only [hNul, ↓reduceIte]
        obtain ⟨te, hRes, hKind⟩ := resolveRoot_none_invalid_run s₀ tmpdir hTmp hNe hNul
        obtain ⟨h1, h2, h3⟩ := spec7_err_all_three s₀ dirPrefix te hvp' hRes
        rw [h1, h2, h3]
        dsimp only
        rw [allPass_assert, allPass_assert, allPass_assert_end]
        exact ⟨⟨⟨te, rfl, hKind⟩, rfl⟩, ⟨⟨te, rfl, hKind⟩, rfl⟩, ⟨⟨te, rfl, hKind⟩, rfl⟩, trivial⟩
      · simp only [hNul, ↓reduceIte]
        have hvr : Internal.validRoot tmpdir = true := by
          simp [Internal.validRoot, hNe, hNul]
        have hStatSame : ((mockFs.stat tmpdir).run { s₀ with tmpdir := some tmpdir, nextUuid := s₀.nextUuid + 1 }).1 =
            ((mockFs.stat tmpdir).run s₀).1 := by
          rw [mockFs_stat_run, mockFs_stat_run]; rfl
        rw [hStatSame]
        cases hStat : (mockFs.stat tmpdir).run s₀ |>.1 with
        | error fe =>
          dsimp only
          have hStatPure : mockStatPure s₀ tmpdir = .error fe := by
            rw [mockFs_stat_run] at hStat; exact hStat
          have hRes := resolveRoot_none_stat_err_run s₀ tmpdir fe (by simp [hTmp, hNe]) hvr hStatPure
          obtain ⟨h1, h2, h3⟩ := spec7_err_all_three s₀ dirPrefix (Internal.mapFsError fe) hvp' hRes
          rw [h1, h2, h3]
          dsimp only
          rw [allPass_assert, allPass_assert, allPass_assert_end]
          have hKind : fe.kind ≠ .notFound ∨ (Internal.mapFsError fe).kind = .notFound := by
            by_cases hnf : fe.kind = .notFound
            · right; simp [Internal.mapFsError, hnf]
            · left; exact hnf
          exact ⟨⟨_, rfl, hKind⟩, ⟨_, rfl, hKind⟩, ⟨_, rfl, hKind⟩, trivial⟩
        | ok st =>
          dsimp only
          have hStatPure : mockStatPure s₀ tmpdir = .ok st := by
            rw [mockFs_stat_run] at hStat; exact hStat
          have notDirBranch (hNotDir : (st.kind != .dir) = true) :
              AllPass (do
                let (r1, _) := (Internal.mkApiM mockFs mockTime mockUuid mockEnv).withTempDir none dirPrefix (fun _ => pure (.ok ())) |>.run s₀
                let (r2, _) := (Internal.mkApiM mockFs mockTime mockUuid mockEnv).withLockedTempDir none dirPrefix (fun _ => pure (.ok ())) |>.run s₀
                let (r3, _) := (Internal.mkApiM mockFs mockTime mockUuid mockEnv).cleanupStaleTempDirs none dirPrefix 86400 |>.run s₀
                NondetTest.assert (∃ te, r1 = .error te ∧ te.kind = .notADirectory)
                NondetTest.assert (∃ te, r2 = .error te ∧ te.kind = .notADirectory)
                NondetTest.assert (∃ te, r3 = .error te ∧ te.kind = .notADirectory)) := by
            have hRes := resolveRoot_none_nonDir_run s₀ tmpdir st (by simp [hTmp, hNe]) hvr hStatPure hNotDir
            obtain ⟨h1, h2, h3⟩ := spec7_err_all_three s₀ dirPrefix
              { kind := .notADirectory, path := some tmpdir, message := "temporary root is not a directory" } hvp' hRes
            dsimp only [AllPass]
            rw [h1, h2, h3]
            dsimp only
            rw [allPass_assert, allPass_assert, allPass_assert_end]
            exact ⟨⟨_, rfl, rfl⟩, ⟨_, rfl, rfl⟩, ⟨_, rfl, rfl⟩, trivial⟩
          cases hk : st.kind with
          | dir =>
            simp only [show (EntryKind.dir != EntryKind.dir) = false from rfl,
              Bool.false_eq_true, ↓reduceIte]
            rw [allPass_assume]
            intro hRwx
            rw [allPass_assume]
            intro hNone
            have hNonePure : (mockLstatPure { s₀ with nextUuid := s₀.nextUuid + 1 }
                (mockJoin tmpdir (dirPrefix ++ mockUuidToString (mockUuidOfNat s₀.nextUuid)))).isOk = false := by
              rw [mockFs_lstat_run, mockFs_join_eq, mockUuid_toString_eq] at hNone
              exact hNone
            have hRes := resolveRoot_none_ok_run s₀ tmpdir st (by simp [hTmp, hNe]) hvr hStatPure hk
            obtain ⟨s1, s2, s3, rep3, h1, h2, h3⟩ :=
              spec7_ok_all_three s₀ tmpdir dirPrefix hvr hvp' st hStatPure hRwx hRes hNonePure
            rw [h1, h2, h3]
            dsimp only
            rw [allPass_assert, allPass_assert, allPass_assert_end]
            rw [mockFs_join_eq, mockUuid_toString_eq]
            exact ⟨rfl, rfl, rfl, trivial⟩
          | file =>
            have hNotDir : (st.kind != .dir) = true := by rw [hk]; rfl
            simp only [show (EntryKind.file != EntryKind.dir) = true from rfl, ↓reduceIte]
            exact notDirBranch hNotDir
          | symlink =>
            have hNotDir : (st.kind != .dir) = true := by rw [hk]; rfl
            simp only [show (EntryKind.symlink != EntryKind.dir) = true from rfl, ↓reduceIte]
            exact notDirBranch hNotDir
          | other =>
            have hNotDir : (st.kind != .dir) = true := by rw [hk]; rfl
            simp only [show (EntryKind.other != EntryKind.dir) = true from rfl, ↓reduceIte]
            exact notDirBranch hNotDir

/-- Non-vacuity `CanReach` witness for Spec 7 (`test_temp_rootResolution_tmpdirAndFallbackAndStrictMissing`). -/
theorem reach_temp_rootResolution_tmpdirAndFallbackAndStrictMissing :
    CanReach (test_temp_rootResolution_tmpdirAndFallbackAndStrictMissing
      (S := TempMockState) Internal.mkApiM mockFs mockTime mockUuid mockEnv) := by
  dsimp only [test_temp_rootResolution_tmpdirAndFallbackAndStrictMissing, CanReach]
  obtain ⟨s₀, hs₀⟩ : ∃ s : TempMockState, s = { tmpdir := some "/custom", nodes := [("/custom", .dir 0 0o755)] } :=
    ⟨_, rfl⟩
  rw [canReach_nondet]; refine ⟨s₀, ?_⟩
  rw [canReach_nondet]; refine ⟨"tmp-", ?_⟩
  rw [canReach_assume]; refine ⟨rfl, ?_⟩
  have hEnvStep : (mockEnv.getEnv "TMPDIR").run s₀ = (.ok (some "/custom"), s₀) := by
    rw [hs₀]; rfl
  rw [hEnvStep]
  dsimp only
  rw [mockUuid_getUuid_run s₀]
  dsimp only
  have hTmp : s₀.tmpdir = some "/custom" := by rw [hs₀]
  have hStatPure : mockStatPure s₀ "/custom" = .ok (mockNodeStat (.dir 0 0o755)) := by
    rw [hs₀]; rfl
  have hStatEq : ((mockFs.stat "/custom").run { s₀ with nextUuid := s₀.nextUuid + 1 }).1 =
      .ok (mockNodeStat (.dir 0 0o755)) := by
    rw [mockFs_stat_run]; exact hStatPure
  rw [hStatEq]
  dsimp only
  simp only [show (!"/custom".isEmpty) = true from rfl, ↓reduceIte,
    show (Char.ofNat 0 ∈ ("/custom" : String).toList) = false from by decide, Bool.false_eq_true,
    show ((mockNodeStat (.dir 0 0o755)).kind != .dir) = false from rfl]
  rw [canReach_assume]; refine ⟨⟨rfl, rfl, rfl, rfl⟩, ?_⟩
  have hNonePure : (mockLstatPure { s₀ with nextUuid := s₀.nextUuid + 1 }
      (mockJoin "/custom" ("tmp-" ++ mockUuidToString (mockUuidOfNat s₀.nextUuid)))).isOk = false := by
    rw [hs₀]
    unfold mockLstatPure
    dsimp only
    have ⟨hcNe, hcNoSlash⟩ := childName_parts "tmp-" (mockUuidOfNat 1) rfl
    have hNe : normKey "/custom" ≠ normKey (mockJoin "/custom" ("tmp-" ++ mockUuidToString (mockUuidOfNat 1))) :=
      ne_comm.mp (mockJoin_ne_root "/custom" _ (by decide) hcNe hcNoSlash)
    rw [lookupNode_cons_ne "/custom" (.dir 0 0o755) [] _ hNe]
    rfl
  have hNone : (mockFs.lstat (mockFs.join "/custom" ("tmp-" ++ mockUuid.toString (mockUuidOfNat s₀.nextUuid)))).run
      { s₀ with nextUuid := s₀.nextUuid + 1 } |>.1.isOk = false := by
    rw [mockFs_lstat_run, mockFs_join_eq, mockUuid_toString_eq]
    exact hNonePure
  rw [canReach_assume]; refine ⟨hNone, ?_⟩
  have hRes := resolveRoot_none_ok_run s₀ "/custom" (mockNodeStat (.dir 0 0o755)) (by rw [hTmp]; rfl) rfl hStatPure rfl
  obtain ⟨s1, s2, s3, rep3, h1, h2, h3⟩ := spec7_ok_all_three s₀ "/custom" "tmp-" rfl rfl
    (mockNodeStat (.dir 0 0o755)) hStatPure ⟨rfl, rfl, rfl, rfl⟩ hRes hNonePure
  rw [h1, h2, h3]
  dsimp only
  rw [canReach_assert, canReach_assert, canReach_assert_end]
  rw [mockFs_join_eq, mockUuid_toString_eq]
  exact ⟨rfl, rfl, rfl, trivial⟩

private theorem foldl_max_ge_init (xs : List (Nat × LockMode)) (init : Nat) :
    init ≤ xs.foldl (fun m l => Nat.max m (l.1 + 1)) init := by
  induction xs generalizing init with
  | nil => exact Nat.le_refl init
  | cons y ys ih =>
    simp only [List.foldl_cons]
    exact Nat.le_trans (Nat.le_max_left init (y.1 + 1)) (ih _)

private theorem foldl_max_gt_mem (xs : List (Nat × LockMode)) (init : Nat)
    (x : Nat × LockMode) (hx : x ∈ xs) :
    x.1 < xs.foldl (fun m l => Nat.max m (l.1 + 1)) init := by
  induction xs generalizing init with
  | nil => simp at hx
  | cons y ys ih =>
    simp only [List.foldl_cons]
    cases List.mem_cons.mp hx with
    | inl hxy =>
      subst hxy
      exact Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.lt_succ_self x.1) (Nat.le_max_right init (x.1 + 1)))
        (foldl_max_ge_init ys _)
    | inr hmem =>
      exact ih (Nat.max init (y.1 + 1)) hmem

private theorem freshInode_gt_mem (s : TempMockState) (x : Nat × LockMode) (hx : x ∈ s.locks) :
    x.1 < freshInode s :=
  foldl_max_gt_mem s.locks s.nextInode x hx

private theorem mockHasConflict_fresh (locks : List (Nat × LockMode)) (ino : Nat) (mode : LockMode)
    (hFresh : ∀ x ∈ locks, x.1 < ino) :
    mockHasConflict locks ino mode = false := by
  unfold mockHasConflict
  rw [List.any_eq_false]
  intro x hx hTrue
  have hlt := hFresh x hx
  have hAnd : (x.1 == ino) = true := ((Bool.and_eq_true _ _).mp hTrue).1
  have heq : x.1 = ino := beq_iff_eq.mp hAnd
  omega

private theorem mockHasConflict_cons_shared_shared (locks : List (Nat × LockMode)) (ino : Nat)
    (hFresh : ∀ x ∈ locks, x.1 < ino) :
    mockHasConflict ((ino, .shared) :: locks) ino .shared = false := by
  unfold mockHasConflict
  simp only [List.any_cons, beq_self_eq_true, show (LockMode.shared == LockMode.exclusive) = false from rfl,
    Bool.and_false, Bool.false_or]
  exact mockHasConflict_fresh locks ino .shared hFresh

private theorem mockHasConflict_cons_shared_exclusive (locks : List (Nat × LockMode)) (ino : Nat) :
    mockHasConflict ((ino, .shared) :: locks) ino .exclusive = true := by
  unfold mockHasConflict
  simp only [List.any_cons, beq_self_eq_true, show (LockMode.exclusive == LockMode.exclusive) = true from rfl,
    Bool.true_or, Bool.and_self, Bool.true_or]

private theorem mockRemoveFirstLock_head (ino : Nat) (m : LockMode) (locks : List (Nat × LockMode)) :
    mockRemoveFirstLock ino m ((ino, m) :: locks) = locks := by
  unfold mockRemoveFirstLock
  have hm : (m == m) = true := by cases m <;> rfl
  have heq : ((ino, m) == (ino, m)) = true := by
    change (ino == ino && m == m) = true
    rw [beq_self_eq_true, hm]
    rfl
  rw [heq]
  rfl

private theorem mockFs_tryWithFileLock_existing_ok_run {α : Type}
    (s : TempMockState) (p : String) (mode : LockMode) (createIfMissing : Bool)
    (ino : Nat) (c : String) (t : Int) (mode0 : Nat)
    (hp : normKey p = p)
    (hNode : lookupNode s.nodes p = some (.file ino c t mode0))
    (hNoConflict : mockHasConflict s.locks ino mode = false)
    (act : StateM TempMockState (Except FsError α)) :
    let sLock := { s with locks := (ino, mode) :: s.locks }
    (mockFs.tryWithFileLock p mode createIfMissing act).run s =
      ((act.run sLock).1.map some, { (act.run sLock).2 with locks := mockRemoveFirstLock ino mode (act.run sLock).2.locks }) := by
  intro sLock
  dsimp only [mockFs, resolveParentTarget]
  rw [stateM_bind_run, stateM_get_run]
  dsimp only
  rw [hp, hNode]
  dsimp only
  rw [hNoConflict]
  simp only [Bool.false_eq_true, ↓reduceIte, stateM_bind_run, stateM_pure_run]
  have hSet : (set ({ s with locks := (ino, mode) :: s.locks } : TempMockState) : StateM TempMockState Unit).run s =
      ((), sLock) := rfl
  rw [hSet]
  dsimp only
  cases hAct : act.run sLock with
  | mk r sA =>
    dsimp only
    have hMod : ((modify fun s' : TempMockState => { s' with locks := mockRemoveFirstLock ino mode s'.locks }) :
        StateM TempMockState Unit).run sA =
        ((), { sA with locks := mockRemoveFirstLock ino mode sA.locks }) := rfl
    rw [hMod]

private theorem mockFs_tryWithFileLock_existing_conflict_run {α : Type}
    (s : TempMockState) (p : String) (mode : LockMode) (createIfMissing : Bool)
    (ino : Nat) (c : String) (t : Int) (mode0 : Nat)
    (hp : normKey p = p)
    (hNode : lookupNode s.nodes p = some (.file ino c t mode0))
    (hConflict : mockHasConflict s.locks ino mode = true)
    (act : StateM TempMockState (Except FsError α)) :
    (mockFs.tryWithFileLock p mode createIfMissing act).run s = (.ok none, s) := by
  dsimp only [mockFs, resolveParentTarget]
  rw [stateM_bind_run, stateM_get_run]
  dsimp only
  rw [hp, hNode]
  dsimp only
  rw [hConflict]
  simp only [↓reduceIte, stateM_pure_run]

private theorem mockFs_tryWithFileLock_create_run {α : Type}
    (s : TempMockState) (p : String) (mode : LockMode)
    (hp : normKey p = p) (hNone : lookupNode s.nodes p = none)
    (act : StateM TempMockState (Except FsError α)) :
    let ino := freshInode s
    let sLock := { s with
      nodes := (p, .file ino "" s.nowSec 0o644) :: s.nodes
      locks := (ino, mode) :: s.locks
      nextInode := ino + 1 }
    (mockFs.tryWithFileLock p mode true act).run s =
      ((act.run sLock).1.map some, { (act.run sLock).2 with locks := mockRemoveFirstLock ino mode (act.run sLock).2.locks }) := by
  intro ino sLock
  dsimp only [mockFs, resolveParentTarget]
  rw [stateM_bind_run, stateM_get_run]
  dsimp only
  rw [hp, hNone]
  simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, stateM_bind_run, stateM_pure_run]
  have hSet : (set ({
      nodes := (p, MockNode.file (freshInode s) "" s.nowSec 420) :: s.nodes,
      locks := (freshInode s, mode) :: s.locks,
      nextInode := freshInode s + 1, tmpdir := s.tmpdir, nowSec := s.nowSec, nextUuid := s.nextUuid } : TempMockState) :
      StateM TempMockState Unit).run s = ((), sLock) := rfl
  rw [hSet]
  dsimp only
  cases hAct : act.run sLock with
  | mk r sA =>
    dsimp only
    have hMod : ((modify fun s' : TempMockState => { s' with locks := mockRemoveFirstLock ino mode s'.locks }) :
        StateM TempMockState Unit).run sA =
        ((), { sA with locks := mockRemoveFirstLock ino mode sA.locks }) := rfl
    rw [hMod]

private theorem underDir_mockJoin_root_false (root child : String)
    (hrNe : root ≠ "") (hcNe : child ≠ "") (hcNoSlash : '/' ∉ child.toList) :
    underDir (mockJoin root child) root = false := by
  have hNormDir : normKey (mockJoin root child) = mockJoin root child :=
    normKey_mockJoin root child hcNe hcNoSlash
  have hDirNeSlash : mockJoin root child ≠ "/" := mockJoin_ne_slash root child hrNe hcNe
  have hJoin := mockJoin_eq_append_of_ne_empty root child hrNe
  have hcPos : 0 < child.length := string_length_pos_of_ne_empty child hcNe
  have hLenLt : (normKey root).length < (mockJoin root child).length := by
    rw [← @String.length_toList (normKey root), ← @String.length_toList (mockJoin root child), hJoin]
    split
    · next hEq =>
      have hRootEq : normKey root = "/" := beq_iff_eq.mp hEq
      rw [hRootEq]
      have hSlashLen : ("/" : String).length = 1 := rfl
      simp only [List.length_append, List.length_cons, List.length_nil, String.length_toList, hSlashLen]
      omega
    · simp only [List.length_append, List.length_cons, List.length_nil, String.length_toList]
      omega
  unfold underDir
  have hNeSlashB : (mockJoin root child == "/") = false := beq_false_of_ne hDirNeSlash
  have hNe : (normKey root == mockJoin root child) = false := by
    rw [beq_false_of_ne]
    intro hEq
    have hL := congrArg String.length hEq
    omega
  have hNotPref : (mockJoin root child ++ "/").toList.isPrefixOf (normKey root).toList = false := by
    cases hp : (mockJoin root child ++ "/").toList.isPrefixOf (normKey root).toList with
    | false => rfl
    | true =>
      exfalso
      have hLe := (List.isPrefixOf_iff_prefix.mp hp).length_le
      simp only [String.length_toList, String.length_append] at hLe
      have hOne : ("/" : String).length = 1 := rfl
      omega
  simp only [hNormDir, hNeSlashB, Bool.false_eq_true, ↓reduceIte, hNe, hNotPref, Bool.or_self]

private theorem lookupNode_filter_not_underDir_eq (nodes : List (String × MockNode)) (d q : String)
    (hFalse : underDir d q = false) :
    lookupNode (nodes.filter (fun e => !underDir d e.1)) q = lookupNode nodes q := by
  induction nodes with
  | nil => rfl
  | cons x xs ih =>
    cases hb : (normKey x.1 == normKey q) with
    | true =>
      have hEq : normKey x.1 = normKey q := beq_iff_eq.mp hb
      have hux : underDir d x.1 = false := by simpa [underDir, hEq] using hFalse
      simp [lookupNode, hux, hb]
    | false =>
      simp only [lookupNode, List.find?_cons, hb]
      rw [List.filter_cons]
      split
      · simp only [List.find?_cons, hb]
        exact ih
      · exact ih

private theorem probe_exclusive_lock_after_cleanup_run
    (s : TempMockState) (root child : String)
    (hrNe : root ≠ "") (hcNe : child ≠ "") (hcNoSlash : '/' ∉ child.toList)
    (rootNode : MockNode) (stRoot : FileStat)
    (hLookRoot : lookupNode s.nodes (normKey root) = some rootNode)
    (hStRoot : mockNodeStat rootNode = stRoot)
    (hRwx : stRoot.kind = .dir ∧ (stRoot.mode / 256) % 2 = 1 ∧ (stRoot.mode / 128) % 2 = 1 ∧ (stRoot.mode / 64) % 2 = 1)
    (hLookDir : lookupNode s.nodes (mockJoin root child) = none) :
    ((do
      let _ ← mockFs.mkdir (mockJoin root child) false false
      mockFs.tryWithFileLock (mockJoin (mockJoin root child) ".lock") .exclusive true (pure (.ok ()))).run s).1 = .ok (some ()) := by
  let dir := mockJoin root child
  let lockPath := mockJoin dir ".lock"
  have hDirNorm : normKey dir = dir := normKey_mockJoin root child hcNe hcNoSlash
  have hDirNe : dir ≠ "" := mockJoin_ne_empty root child hcNe
  have hDirNeSlash : dir ≠ "/" := mockJoin_ne_slash root child hrNe hcNe
  have hLockNorm : normKey lockPath = lockPath := normKey_mockJoin dir ".lock" (by decide) (by decide)
  have hLockNeDir : normKey lockPath ≠ dir :=
    payload_ne_dir root child ".lock" hrNe hcNe hcNoSlash (by decide) (by decide)
  have hUnderLock : underDir dir lockPath = true :=
    underDir_mockJoin_self dir ".lock" hDirNe hDirNorm hDirNeSlash (by decide) (by decide)
  have hSp : splitParentChild dir = some (normKey root, child) :=
    splitParentChild_mockJoin root child hrNe hcNe hcNoSlash
  have hJoinNorm : mockJoin (normKey root) child = dir :=
    mockJoin_normKey root child
  have hWx : hasWx stRoot = true := hasWx_of_hasRwx stRoot hRwx
  obtain ⟨s1, hs1⟩ : ∃ s' : TempMockState, s' =
      { s with nodes := (dir, .dir s.nowSec 0o755) :: s.nodes.filter (fun e => !underDir dir e.1) } := ⟨_, rfl⟩
  have hMk : (mockFs.mkdir dir false false).run s = (.ok (), s1) := by
    dsimp only [mockFs]
    rw [stateM_bind_run, stateM_get_run]
    dsimp only
    rw [hSp]
    dsimp only
    rw [hLookRoot]
    dsimp only
    rw [hStRoot]
    simp only [hRwx.1, show (EntryKind.dir != EntryKind.dir) = false from rfl,
      Bool.false_eq_true, ↓reduceIte, hWx, Bool.not_true, hJoinNorm]
    rw [hLookDir, hs1]
    simp only [stateM_bind_run, stateM_set_run, stateM_pure_run]
  have hLookLock1 : lookupNode s1.nodes lockPath = none := by
    rw [hs1]
    unfold lookupNode
    dsimp only
    have hb : (normKey dir == normKey lockPath) = false := by
      rw [hDirNorm, beq_false_of_ne (ne_comm.mp hLockNeDir)]
    rw [List.find?_cons, hb]
    exact lookupNode_filter_none_of_underDir s.nodes dir lockPath hUnderLock
  rw [stateM_bind_run, hMk]
  dsimp only
  rw [mockFs_tryWithFileLock_create_run s1 lockPath .exclusive hLockNorm hLookLock1]
  rw [stateM_pure_run]
  rfl

private theorem createTempDir_mock_steps_of_ops (s₀ : TempMockState) (root dirPrefix : String)
    (fs : FsApiM (StateM TempMockState))
    (hJoin : fs.join = mockJoin) (hStat : fs.stat = mockFs.stat)
    (hMkdir : fs.mkdir = mockFs.mkdir) (hChmod : fs.chmod = mockFs.chmod)
    (hvr : (!root.isEmpty && !(Char.ofNat 0 ∈ root.toList)) = true)
    (hvp : (!dirPrefix.isEmpty && dirPrefix.toList.head? != some '.' && !('/' ∈ dirPrefix.toList) && !(Char.ofNat 0 ∈ dirPrefix.toList)) = true)
    (stRoot : FileStat) (hRoot : mockStatPure s₀ root = .ok stRoot)
    (hRwx : stRoot.kind = .dir ∧ (stRoot.mode / 256) % 2 = 1 ∧ (stRoot.mode / 128) % 2 = 1 ∧ (stRoot.mode / 64) % 2 = 1)
    (hNone : (mockLstatPure { s₀ with nextUuid := s₀.nextUuid + 1 }
      (mockJoin root (dirPrefix ++ mockUuidToString (mockUuidOfNat s₀.nextUuid)))).isOk = false) :
    let u := mockUuidOfNat s₀.nextUuid
    let dir := mockJoin root (dirPrefix ++ mockUuidToString u)
    let sMk := { s₀ with
      nextUuid := s₀.nextUuid + 1
      nodes := (dir, .dir s₀.nowSec 0o700) :: s₀.nodes.filter (fun e => !underDir dir e.1) }
    (Internal.createTempDir fs mockUuid mockEnv (some root) dirPrefix).run s₀ =
      (.ok dir, sMk) := by
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
  have hResStep : (Internal.resolveRoot fs mockEnv (some root)).run s₀ = (.ok root, s₀) := by
    dsimp only [Internal.resolveRoot]
    rw [stateM_bind_run, stateM_pure_run]
    dsimp only
    simp only [hvr', Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    rw [stateM_bind_run, hStat, mockFs_stat_run, hRoot]
    dsimp only
    simp only [hRwx.1, show (EntryKind.dir != EntryKind.dir) = false from rfl,
      Bool.false_eq_true, ↓reduceIte, stateM_pure_run]
  have hUuidStep : mockUuid.getUuid.run s₀ = (.ok u, { s₀ with nextUuid := s₀.nextUuid + 1 }) := by
    simp [mockUuid, u]; rfl
  dsimp only [Internal.createTempDir]
  simp only [hvp', Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  rw [stateM_bind_run, hResStep]
  dsimp only
  rw [stateM_bind_run, hUuidStep]
  dsimp only
  have hDirEq : fs.join root (dirPrefix ++ mockUuid.toString u) = dir := by
    rw [hJoin]; rfl
  simp only [hDirEq]
  rw [stateM_bind_run, hMkdir, hMk]
  dsimp only
  rw [stateM_bind_run, hChmod, hCh]
  dsimp only
  rw [stateM_pure_run]

private theorem withLockedTempDir_wfl_err_step {S α : Type}
    (fs : FsApiM (StateM S)) (time : TimeOpsM (StateM S))
    (uuid : UuidApiM (StateM S)) (env : EnvVarsApiM (StateM S))
    (s₀ sMk sFin : S) (root? : Option String) (dirPrefix dir : String)
    (action : String → StateM S (Except TempError α))
    (fe : FsError) (rc : Except TempError Unit)
    (hCre : (Internal.createTempDir fs uuid env root? dirPrefix).run s₀ = (.ok dir, sMk))
    (hWfl : (fs.withFileLock (fs.join dir ".lock") .shared true (do let r ← action dir; return .ok r)).run sMk = (.error fe, sMk))
    (hCln : (Internal.cleanupDirIgnoringNotFound fs dir).run sMk = (rc, sFin)) :
    ((Internal.mkApiM fs time uuid env).withLockedTempDir root? dirPrefix action).run s₀ =
      (.error (Internal.mapFsError fe), sFin) := by
  rw [mkApiM_withLockedTempDir_eq]
  dsimp only [Internal.withLockedTempDirM]
  rw [stateM_bind_run, hCre]
  dsimp only
  rw [stateM_bind_run, stateM_tryFinally'_run, hWfl]
  dsimp only
  rw [hCln]
  dsimp only
  exact stateM_pure_run _ _

private theorem cleanupDir_mock_of_rmtree (s : TempMockState) (dir : String)
    (fs : FsApiM (StateM TempMockState)) (hRm : fs.rmtree = mockFs.rmtree)
    (hnorm : normKey dir = dir) (hnode : ∃ m mode, lookupNode s.nodes dir = some (.dir m mode)) :
    (Internal.cleanupDirIgnoringNotFound fs dir).run s =
      (.ok (), { s with nodes := s.nodes.filter (fun e => !underDir dir e.1) }) := by
  dsimp only [Internal.cleanupDirIgnoringNotFound]
  rw [hRm]
  rcases hnode with ⟨m, mode, hLook⟩
  have h1 : (mockFs.rmtree dir true).run s =
      (.ok (), { s with nodes := s.nodes.filter (fun e => !underDir dir e.1) }) := by
    dsimp only [mockFs, mockRmtreePure, resolveParentTarget]
    rw [stateM_bind_run, stateM_get_run]
    dsimp only
    rw [hnorm, hLook]
    simp only [stateM_bind_run, stateM_set_run, stateM_pure_run]
  rw [stateM_bind_run, h1]
  exact stateM_pure_run _ _

private theorem cleanupDir_mock_of_rmtree_err (s : TempMockState) (dir : String)
    (fs : FsApiM (StateM TempMockState)) (err : FsError)
    (hRm : (fs.rmtree dir true).run s = (.error err, s)) (hb : (err.kind == .notFound) = false) :
    (Internal.cleanupDirIgnoringNotFound fs dir).run s =
      (.error (Internal.mapFsError err), s) := by
  dsimp only [Internal.cleanupDirIgnoringNotFound]
  rw [stateM_bind_run, hRm]
  dsimp only
  rw [hb]
  simp only [Bool.false_eq_true, ↓reduceIte]
  exact stateM_pure_run _ _

private def spec8MkState (s₀ : TempMockState) (root dirPrefix : String) : TempMockState :=
  let dir := mockJoin root (dirPrefix ++ mockUuidToString (mockUuidOfNat s₀.nextUuid))
  { s₀ with
    nextUuid := s₀.nextUuid + 1
    nodes := (dir, .dir s₀.nowSec 0o700) :: s₀.nodes.filter (fun e => !underDir dir e.1) }

private def spec8LockState (s₀ : TempMockState) (root dirPrefix : String) : TempMockState :=
  let sMk := spec8MkState s₀ root dirPrefix
  let dir := mockJoin root (dirPrefix ++ mockUuidToString (mockUuidOfNat s₀.nextUuid))
  let lockPath := mockJoin dir ".lock"
  { sMk with
    nodes := (lockPath, .file (freshInode sMk) "" sMk.nowSec 0o644) :: sMk.nodes
    locks := (freshInode sMk, .shared) :: sMk.locks
    nextInode := freshInode sMk + 1 }

private theorem spec8_lockState_probes (s₀ : TempMockState) (root dirPrefix : String)
    (hvr : (!root.isEmpty && !(Char.ofNat 0 ∈ root.toList)) = true)
    (hvp : (!dirPrefix.isEmpty && dirPrefix.toList.head? != some '.' && !('/' ∈ dirPrefix.toList) && !(Char.ofNat 0 ∈ dirPrefix.toList)) = true) :
    let u := mockUuidOfNat s₀.nextUuid
    let dir := mockJoin root (dirPrefix ++ mockUuidToString u)
    let lockPath := mockJoin dir ".lock"
    let sMk := spec8MkState s₀ root dirPrefix
    let sLock := spec8LockState s₀ root dirPrefix
    ((mockFs.lstat dir).run sLock = (.ok (mockNodeStat (.dir s₀.nowSec 0o700)), sLock)) ∧
    ((mockFs.lstat lockPath).run sLock = (.ok (mockNodeStat (.file (freshInode sMk) "" sMk.nowSec 0o644)), sLock)) ∧
    ((mockFs.tryWithFileLock lockPath .shared false (pure (.ok ()))).run sLock = (.ok (some ()), sLock)) ∧
    ((mockFs.tryWithFileLock lockPath .exclusive false (pure (.ok ()))).run sLock = (.ok none, sLock)) := by
  intro u dir lockPath sMk sLock
  have hrNe : root ≠ "" := validRoot_ne_empty root hvr
  have ⟨hcNe, hcNoSlash⟩ := childName_parts dirPrefix u hvp
  have hDirNorm : normKey dir = dir := normKey_mockJoin root _ hcNe hcNoSlash
  have hDirNe : dir ≠ "" := mockJoin_ne_empty root _ hcNe
  have hDirNeSlash : dir ≠ "/" := mockJoin_ne_slash root _ hrNe hcNe
  have hLockNorm : normKey lockPath = lockPath := normKey_mockJoin dir ".lock" (by decide) (by decide)
  have hLockNeDir : normKey lockPath ≠ dir :=
    payload_ne_dir root (dirPrefix ++ mockUuidToString u) ".lock" hrNe hcNe hcNoSlash (by decide) (by decide)
  have hUnderLock : underDir dir lockPath = true :=
    underDir_mockJoin_self dir ".lock" hDirNe hDirNorm hDirNeSlash (by decide) (by decide)
  have hLookDirMk : lookupNode sMk.nodes dir = some (.dir s₀.nowSec 0o700) :=
    lookupNode_cons_eq _ _ _ _ rfl
  have hLookDirLock : lookupNode sLock.nodes dir = some (.dir s₀.nowSec 0o700) := by
    change lookupNode ((lockPath, .file (freshInode sMk) "" sMk.nowSec 0o644) :: sMk.nodes) dir = _
    unfold lookupNode
    dsimp only
    have hb : (normKey lockPath == normKey dir) = false := by
      rw [hDirNorm, beq_false_of_ne hLockNeDir]
    rw [List.find?_cons, hb]
    exact hLookDirMk
  have hLookLockLock : lookupNode sLock.nodes lockPath = some (.file (freshInode sMk) "" sMk.nowSec 0o644) :=
    lookupNode_cons_eq _ _ _ _ rfl
  have hFreshMk : ∀ x ∈ sMk.locks, x.1 < freshInode sMk := fun x hx => freshInode_gt_mem sMk x hx
  have hNoConfShared : mockHasConflict sLock.locks (freshInode sMk) .shared = false :=
    mockHasConflict_cons_shared_shared sMk.locks (freshInode sMk) hFreshMk
  have hConfEx : mockHasConflict sLock.locks (freshInode sMk) .exclusive = true :=
    mockHasConflict_cons_shared_exclusive sMk.locks (freshInode sMk)
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [mockFs_lstat_run]; unfold mockLstatPure; rw [hLookDirLock]
  · rw [mockFs_lstat_run]; unfold mockLstatPure; rw [hLookLockLock]
  · rw [mockFs_tryWithFileLock_existing_ok_run sLock lockPath .shared false
      (freshInode sMk) "" sMk.nowSec 0o644 hLockNorm hLookLockLock hNoConfShared (pure (.ok ()))]
    simp only [stateM_pure_run, mockRemoveFirstLock_head]
    rfl
  · exact mockFs_tryWithFileLock_existing_conflict_run sLock lockPath .exclusive false
      (freshInode sMk) "" sMk.nowSec 0o644 hLockNorm hLookLockLock hConfEx (pure (.ok ()))

private theorem lookupNode_after_cleanup_root
    (nodes : List (String × MockNode)) (dir lockPath root : String)
    (ndL ndD : MockNode)
    (hNotUnder : underDir dir (normKey root) = false)
    (hb1 : (normKey lockPath == normKey (normKey root)) = false)
    (hb2 : (normKey dir == normKey (normKey root)) = false) :
    lookupNode ((lockPath, ndL) :: (dir, ndD) :: nodes.filter (fun e => !underDir dir e.1)) (normKey root) =
      lookupNode nodes (normKey root) := by
  unfold lookupNode
  dsimp only
  rw [List.find?_cons, hb1]
  dsimp only
  rw [List.find?_cons, hb2]
  exact lookupNode_filter_not_underDir_eq nodes dir (normKey root) hNotUnder

private theorem spec8_ok_exec (s₀ : TempMockState) (root dirPrefix : String) (val : Nat)
    (act : String → StateM TempMockState (Except TempError Nat))
    (hvr : (!root.isEmpty && !(Char.ofNat 0 ∈ root.toList)) = true)
    (hvp : (!dirPrefix.isEmpty && dirPrefix.toList.head? != some '.' && !('/' ∈ dirPrefix.toList) && !(Char.ofNat 0 ∈ dirPrefix.toList)) = true)
    (stRoot : FileStat) (hRoot : mockStatPure s₀ root = .ok stRoot)
    (hRwx : stRoot.kind = .dir ∧ (stRoot.mode / 256) % 2 = 1 ∧ (stRoot.mode / 128) % 2 = 1 ∧ (stRoot.mode / 64) % 2 = 1)
    (hNone : (mockLstatPure { s₀ with nextUuid := s₀.nextUuid + 1 }
      (mockJoin root (dirPrefix ++ mockUuidToString (mockUuidOfNat s₀.nextUuid)))).isOk = false)
    (hAct : (act (mockJoin root (dirPrefix ++ mockUuidToString (mockUuidOfNat s₀.nextUuid)))).run
      (spec8LockState s₀ root dirPrefix) = (.ok val, spec8LockState s₀ root dirPrefix)) :
    let u := mockUuidOfNat s₀.nextUuid
    let dir := mockJoin root (dirPrefix ++ mockUuidToString u)
    let lockPath := mockJoin dir ".lock"
    let api := Internal.mkApiM mockFs mockTime mockUuid mockEnv
    ∃ sOk : TempMockState,
      (api.withLockedTempDir (some root) dirPrefix act).run s₀ = (.ok val, sOk) ∧
      ((mockFs.lstat dir).run sOk).1.isOk = false ∧
      (∃ e, ((mockFs.lstat lockPath).run sOk).1 = .error e ∧ e.kind = .notFound) ∧
      ((do let _ ← mockFs.mkdir dir false false; mockFs.tryWithFileLock lockPath .exclusive true (pure (.ok ()))).run sOk).1 =
        .ok (some ()) := by
  intro u dir lockPath api
  have hrNe : root ≠ "" := validRoot_ne_empty root hvr
  have ⟨hcNe, hcNoSlash⟩ := childName_parts dirPrefix u hvp
  have hDirNorm : normKey dir = dir := normKey_mockJoin root _ hcNe hcNoSlash
  have hDirNe : dir ≠ "" := mockJoin_ne_empty root _ hcNe
  have hDirNeSlash : dir ≠ "/" := mockJoin_ne_slash root _ hrNe hcNe
  have hLockNorm : normKey lockPath = lockPath := normKey_mockJoin dir ".lock" (by decide) (by decide)
  have hLockNeDir : normKey lockPath ≠ dir :=
    payload_ne_dir root (dirPrefix ++ mockUuidToString u) ".lock" hrNe hcNe hcNoSlash (by decide) (by decide)
  have hUnderLock : underDir dir lockPath = true :=
    underDir_mockJoin_self dir ".lock" hDirNe hDirNorm hDirNeSlash (by decide) (by decide)
  have hRootUnderDirFalse : underDir dir (normKey root) = false := by
    simpa [underDir, normKey_idem] using
      underDir_mockJoin_root_false root (dirPrefix ++ mockUuidToString u) hrNe hcNe hcNoSlash
  have hLookRoot : ∃ rootNode, lookupNode s₀.nodes (normKey root) = some rootNode ∧ mockNodeStat rootNode = stRoot := by
    unfold mockStatPure mockLstatPure at hRoot
    cases hl : lookupNode s₀.nodes root with
    | none => simp [hl] at hRoot
    | some rn =>
      simp only [hl, Except.ok.injEq] at hRoot
      exact ⟨rn, by simpa [lookupNode, normKey_idem] using hl, hRoot⟩
  rcases hLookRoot with ⟨rootNode, hLookRootNorm, hStRoot⟩
  have hCreate := createTempDir_mock_steps s₀ root dirPrefix hvr hvp stRoot hRoot hRwx hNone
  dsimp only at hCreate
  let sMk := spec8MkState s₀ root dirPrefix
  let sLock := spec8LockState s₀ root dirPrefix
  have hsMk : sMk =
      { s₀ with
        nextUuid := s₀.nextUuid + 1
        nodes := (dir, .dir s₀.nowSec 0o700) :: s₀.nodes.filter (fun e => !underDir dir e.1) } := rfl
  rw [← hsMk] at hCreate
  have hLookDirMk : lookupNode sMk.nodes dir = some (.dir s₀.nowSec 0o700) := by
    rw [hsMk]; exact lookupNode_cons_eq _ _ _ _ rfl
  have hLookLockMk : lookupNode sMk.nodes lockPath = none := by
    rw [hsMk]
    unfold lookupNode
    dsimp only
    have hb : (normKey dir == normKey lockPath) = false := by
      rw [hDirNorm, beq_false_of_ne (ne_comm.mp hLockNeDir)]
    rw [List.find?_cons, hb]
    exact lookupNode_filter_none_of_underDir s₀.nodes dir lockPath hUnderLock
  have hsLock : sLock =
      { sMk with
        nodes := (lockPath, .file (freshInode sMk) "" sMk.nowSec 0o644) :: sMk.nodes
        locks := (freshInode sMk, .shared) :: sMk.locks
        nextInode := freshInode sMk + 1 } := rfl
  have hLookDirLock : lookupNode sLock.nodes dir = some (.dir s₀.nowSec 0o700) := by
    rw [hsLock]
    unfold lookupNode
    dsimp only
    have hb : (normKey lockPath == normKey dir) = false := by
      rw [hDirNorm, beq_false_of_ne hLockNeDir]
    rw [List.find?_cons, hb]
    exact hLookDirMk
  have hActOk :
      (do let r ← act dir; return .ok r : StateM TempMockState (Except FsError (Except TempError Nat))).run sLock =
        (.ok (.ok val), sLock) := by
    rw [stateM_bind_run, hAct]
    exact stateM_pure_run _ _
  obtain ⟨sAfterOk, hsAfterOk⟩ : ∃ s : TempMockState, s =
      { sLock with locks := mockRemoveFirstLock (freshInode sMk) .shared sLock.locks } := ⟨_, rfl⟩
  have hLookDirAfterOk : lookupNode sAfterOk.nodes dir = some (.dir s₀.nowSec 0o700) := by
    rw [hsAfterOk]; exact hLookDirLock
  obtain ⟨sOk, hsOk⟩ : ∃ s : TempMockState, s =
      { sAfterOk with nodes := sAfterOk.nodes.filter (fun e => !underDir dir e.1) } := ⟨_, rfl⟩
  have hCleanOk : (Internal.cleanupDirIgnoringNotFound mockFs dir).run sAfterOk = (.ok (), sOk) := by
    rw [hsOk]; exact cleanupDir_mock_run sAfterOk dir hDirNorm ⟨_, _, hLookDirAfterOk⟩
  have hRunOk : (api.withLockedTempDir (some root) dirPrefix act).run s₀ = (.ok val, sOk) := by
    rw [mkApiM_withLockedTempDir_eq]
    dsimp only [Internal.withLockedTempDirM]
    rw [stateM_bind_run, hCreate]
    dsimp only
    rw [stateM_bind_run, stateM_tryFinally'_run, mockFs_join_eq]
    rw [mockFs_withFileLock_create_run sMk lockPath .shared hLockNorm hLookLockMk]
    rw [← hsLock, hActOk]
    dsimp only
    rw [← hsAfterOk, hCleanOk]
    exact stateM_pure_run _ _
  have hLookDirOk : lookupNode sOk.nodes dir = none := by
    rw [hsOk]; exact lookupNode_filter_none_of_underDir sAfterOk.nodes dir dir (underDir_refl dir hDirNorm)
  have hLookLockOk : lookupNode sOk.nodes lockPath = none := by
    rw [hsOk]; exact lookupNode_filter_none_of_underDir sAfterOk.nodes dir lockPath hUnderLock
  have hLookRootOk : lookupNode sOk.nodes (normKey root) = some rootNode := by
    have hb1 : (normKey lockPath == normKey (normKey root)) = false := by
      rw [beq_false_of_ne]
      intro hEq
      have h1 : underDir dir lockPath = underDir dir (normKey root) := by unfold underDir; rw [hEq]
      rw [hUnderLock, hRootUnderDirFalse] at h1
      exact Bool.noConfusion h1
    have hb2 : (normKey dir == normKey (normKey root)) = false := by
      rw [beq_false_of_ne]
      intro hEq
      have h1 : underDir dir dir = underDir dir (normKey root) := by unfold underDir; rw [hEq]
      rw [underDir_refl dir hDirNorm, hRootUnderDirFalse] at h1
      exact Bool.noConfusion h1
    rw [hsOk, lookupNode_filter_not_underDir_eq sAfterOk.nodes dir (normKey root) hRootUnderDirFalse]
    change lookupNode (sAfterOk.nodes) (normKey root) = some rootNode
    have hSA : sAfterOk.nodes =
        (lockPath, .file (freshInode sMk) "" sMk.nowSec 0o644) ::
        (dir, .dir s₀.nowSec 0o700) ::
        s₀.nodes.filter (fun e => !underDir dir e.1) := by
      rw [hsAfterOk, hsLock, hsMk]
    rw [hSA]
    exact (lookupNode_after_cleanup_root s₀.nodes dir lockPath root _ _ hRootUnderDirFalse hb1 hb2).trans hLookRootNorm
  have hProbeOk := probe_exclusive_lock_after_cleanup_run sOk root (dirPrefix ++ mockUuidToString u)
    hrNe hcNe hcNoSlash rootNode stRoot hLookRootOk hStRoot hRwx hLookDirOk
  refine ⟨sOk, hRunOk, mockFs_lstat_isOk_false_of_lookup_none sOk dir hLookDirOk, ?_, ?_⟩
  · refine ⟨{ kind := .notFound, path := some lockPath, message := "not found" }, ?_, rfl⟩
    rw [mockFs_lstat_run]; unfold mockLstatPure; rw [hLookLockOk]
  · dsimp only [dir, lockPath]
    exact hProbeOk

private theorem spec8_err_exec (s₀ : TempMockState) (root dirPrefix : String) (err : TempError)
    (hvr : (!root.isEmpty && !(Char.ofNat 0 ∈ root.toList)) = true)
    (hvp : (!dirPrefix.isEmpty && dirPrefix.toList.head? != some '.' && !('/' ∈ dirPrefix.toList) && !(Char.ofNat 0 ∈ dirPrefix.toList)) = true)
    (stRoot : FileStat) (hRoot : mockStatPure s₀ root = .ok stRoot)
    (hRwx : stRoot.kind = .dir ∧ (stRoot.mode / 256) % 2 = 1 ∧ (stRoot.mode / 128) % 2 = 1 ∧ (stRoot.mode / 64) % 2 = 1)
    (hNone : (mockLstatPure { s₀ with nextUuid := s₀.nextUuid + 1 }
      (mockJoin root (dirPrefix ++ mockUuidToString (mockUuidOfNat s₀.nextUuid)))).isOk = false) :
    let u := mockUuidOfNat s₀.nextUuid
    let dir := mockJoin root (dirPrefix ++ mockUuidToString u)
    let lockPath := mockJoin dir ".lock"
    let api := Internal.mkApiM mockFs mockTime mockUuid mockEnv
    ∃ sErr : TempMockState,
      (api.withLockedTempDir (some root) dirPrefix fun _ =>
        pure (Except.error err : Except TempError Nat)).run s₀ = (.error err, sErr) ∧
      ((mockFs.lstat dir).run sErr).1.isOk = false ∧
      ((do let _ ← mockFs.mkdir dir false false; mockFs.tryWithFileLock lockPath .exclusive true (pure (.ok ()))).run sErr).1 =
        .ok (some ()) := by
  intro u dir lockPath api
  have hrNe : root ≠ "" := validRoot_ne_empty root hvr
  have ⟨hcNe, hcNoSlash⟩ := childName_parts dirPrefix u hvp
  have hDirNorm : normKey dir = dir := normKey_mockJoin root _ hcNe hcNoSlash
  have hDirNe : dir ≠ "" := mockJoin_ne_empty root _ hcNe
  have hDirNeSlash : dir ≠ "/" := mockJoin_ne_slash root _ hrNe hcNe
  have hLockNorm : normKey lockPath = lockPath := normKey_mockJoin dir ".lock" (by decide) (by decide)
  have hLockNeDir : normKey lockPath ≠ dir :=
    payload_ne_dir root (dirPrefix ++ mockUuidToString u) ".lock" hrNe hcNe hcNoSlash (by decide) (by decide)
  have hUnderLock : underDir dir lockPath = true :=
    underDir_mockJoin_self dir ".lock" hDirNe hDirNorm hDirNeSlash (by decide) (by decide)
  have hRootUnderDirFalse : underDir dir (normKey root) = false := by
    simpa [underDir, normKey_idem] using
      underDir_mockJoin_root_false root (dirPrefix ++ mockUuidToString u) hrNe hcNe hcNoSlash
  have hLookRoot : ∃ rootNode, lookupNode s₀.nodes (normKey root) = some rootNode ∧ mockNodeStat rootNode = stRoot := by
    unfold mockStatPure mockLstatPure at hRoot
    cases hl : lookupNode s₀.nodes root with
    | none => simp [hl] at hRoot
    | some rn =>
      simp only [hl, Except.ok.injEq] at hRoot
      exact ⟨rn, by simpa [lookupNode, normKey_idem] using hl, hRoot⟩
  rcases hLookRoot with ⟨rootNode, hLookRootNorm, hStRoot⟩
  have hCreate := createTempDir_mock_steps s₀ root dirPrefix hvr hvp stRoot hRoot hRwx hNone
  dsimp only at hCreate
  let sMk := spec8MkState s₀ root dirPrefix
  let sLock := spec8LockState s₀ root dirPrefix
  have hsMk : sMk =
      { s₀ with
        nextUuid := s₀.nextUuid + 1
        nodes := (dir, .dir s₀.nowSec 0o700) :: s₀.nodes.filter (fun e => !underDir dir e.1) } := rfl
  rw [← hsMk] at hCreate
  have hLookDirMk : lookupNode sMk.nodes dir = some (.dir s₀.nowSec 0o700) := by
    rw [hsMk]; exact lookupNode_cons_eq _ _ _ _ rfl
  have hLookLockMk : lookupNode sMk.nodes lockPath = none := by
    rw [hsMk]
    unfold lookupNode
    dsimp only
    have hb : (normKey dir == normKey lockPath) = false := by
      rw [hDirNorm, beq_false_of_ne (ne_comm.mp hLockNeDir)]
    rw [List.find?_cons, hb]
    exact lookupNode_filter_none_of_underDir s₀.nodes dir lockPath hUnderLock
  have hsLock : sLock =
      { sMk with
        nodes := (lockPath, .file (freshInode sMk) "" sMk.nowSec 0o644) :: sMk.nodes
        locks := (freshInode sMk, .shared) :: sMk.locks
        nextInode := freshInode sMk + 1 } := rfl
  have hLookDirLock : lookupNode sLock.nodes dir = some (.dir s₀.nowSec 0o700) := by
    rw [hsLock]
    unfold lookupNode
    dsimp only
    have hb : (normKey lockPath == normKey dir) = false := by
      rw [hDirNorm, beq_false_of_ne hLockNeDir]
    rw [List.find?_cons, hb]
    exact hLookDirMk
  obtain ⟨sAfterErr, hsAfterErr⟩ : ∃ s : TempMockState, s =
      { sLock with locks := mockRemoveFirstLock (freshInode sMk) .shared sLock.locks } := ⟨_, rfl⟩
  have hLookDirAfterErr : lookupNode sAfterErr.nodes dir = some (.dir s₀.nowSec 0o700) := by
    rw [hsAfterErr]; exact hLookDirLock
  obtain ⟨sErr, hsErr⟩ : ∃ s : TempMockState, s =
      { sAfterErr with nodes := sAfterErr.nodes.filter (fun e => !underDir dir e.1) } := ⟨_, rfl⟩
  have hCleanErr : (Internal.cleanupDirIgnoringNotFound mockFs dir).run sAfterErr = (.ok (), sErr) := by
    rw [hsErr]; exact cleanupDir_mock_run sAfterErr dir hDirNorm ⟨_, _, hLookDirAfterErr⟩
  have hRunErr : (api.withLockedTempDir (some root) dirPrefix fun _ =>
      pure (Except.error err : Except TempError Nat)).run s₀ = (.error err, sErr) := by
    rw [mkApiM_withLockedTempDir_eq]
    dsimp only [Internal.withLockedTempDirM]
    rw [stateM_bind_run, hCreate]
    dsimp only
    rw [stateM_bind_run, stateM_tryFinally'_run, mockFs_join_eq]
    have hLockEq : mockJoin dir ".lock" = lockPath := rfl
    rw [hLockEq, mockFs_withFileLock_create_run sMk lockPath .shared hLockNorm hLookLockMk]
    rw [← hsLock, stateM_bind_run, stateM_pure_run, stateM_pure_run]
    dsimp only
    rw [← hsAfterErr, hCleanErr]
    exact stateM_pure_run _ _
  have hLookDirErr : lookupNode sErr.nodes dir = none := by
    rw [hsErr]; exact lookupNode_filter_none_of_underDir sAfterErr.nodes dir dir (underDir_refl dir hDirNorm)
  have hLookRootErr : lookupNode sErr.nodes (normKey root) = some rootNode := by
    have hb1 : (normKey lockPath == normKey (normKey root)) = false := by
      rw [beq_false_of_ne]
      intro hEq
      have h1 : underDir dir lockPath = underDir dir (normKey root) := by unfold underDir; rw [hEq]
      rw [hUnderLock, hRootUnderDirFalse] at h1
      exact Bool.noConfusion h1
    have hb2 : (normKey dir == normKey (normKey root)) = false := by
      rw [beq_false_of_ne]
      intro hEq
      have h1 : underDir dir dir = underDir dir (normKey root) := by unfold underDir; rw [hEq]
      rw [underDir_refl dir hDirNorm, hRootUnderDirFalse] at h1
      exact Bool.noConfusion h1
    rw [hsErr, lookupNode_filter_not_underDir_eq sAfterErr.nodes dir (normKey root) hRootUnderDirFalse]
    have hSA : sAfterErr.nodes =
        (lockPath, .file (freshInode sMk) "" sMk.nowSec 0o644) ::
        (dir, .dir s₀.nowSec 0o700) ::
        s₀.nodes.filter (fun e => !underDir dir e.1) := by
      rw [hsAfterErr, hsLock, hsMk]
    rw [hSA]
    exact (lookupNode_after_cleanup_root s₀.nodes dir lockPath root _ _ hRootUnderDirFalse hb1 hb2).trans hLookRootNorm
  have hProbeErr := probe_exclusive_lock_after_cleanup_run sErr root (dirPrefix ++ mockUuidToString u)
    hrNe hcNe hcNoSlash rootNode stRoot hLookRootErr hStRoot hRwx hLookDirErr
  refine ⟨sErr, hRunErr, mockFs_lstat_isOk_false_of_lookup_none sErr dir hLookDirErr, ?_⟩
  dsimp only [dir, lockPath]
  exact hProbeErr

private theorem spec8_lockRm_exec (s₀ : TempMockState) (root dirPrefix : String) (val : Nat)
    (fs1 : FsApiM (StateM TempMockState))
    (hvr : (!root.isEmpty && !(Char.ofNat 0 ∈ root.toList)) = true)
    (hvp : (!dirPrefix.isEmpty && dirPrefix.toList.head? != some '.' && !('/' ∈ dirPrefix.toList) && !(Char.ofNat 0 ∈ dirPrefix.toList)) = true)
    (stRoot : FileStat) (hRoot : mockStatPure s₀ root = .ok stRoot)
    (hRwx : stRoot.kind = .dir ∧ (stRoot.mode / 256) % 2 = 1 ∧ (stRoot.mode / 128) % 2 = 1 ∧ (stRoot.mode / 64) % 2 = 1)
    (hNone : (mockLstatPure { s₀ with nextUuid := s₀.nextUuid + 1 }
      (mockJoin root (dirPrefix ++ mockUuidToString (mockUuidOfNat s₀.nextUuid)))).isOk = false)
    (hJoin1 : fs1.join = mockJoin) (hStat1 : fs1.stat = mockFs.stat)
    (hMkdir1 : fs1.mkdir = mockFs.mkdir) (hChmod1 : fs1.chmod = mockFs.chmod)
    (hWfl1 : ∀ {β : Type} p m c (body : StateM TempMockState (Except FsError β)),
      fs1.withFileLock p m c body = pure (.error { kind := .permissionDenied, path := some p, message := "lock denied" }))
    (hRm1 : ∀ p ign, fs1.rmtree p ign = pure (.error { kind := .ioError, path := some p, message := "rm failed" })) :
    ∃ sLockRm : TempMockState, ∃ resLockRm : Except TempError Nat,
      ((Internal.mkApiM fs1 mockTime mockUuid mockEnv).withLockedTempDir
        (some root) dirPrefix fun _ => pure (.ok val)).run s₀ = (resLockRm, sLockRm) ∧
      (∃ e, resLockRm = .error e ∧ e.kind = .permissionDenied) := by
  let u := mockUuidOfNat s₀.nextUuid
  let dir := mockJoin root (dirPrefix ++ mockUuidToString u)
  let lockPath := mockJoin dir ".lock"
  have hCreateLockRm := createTempDir_mock_steps_of_ops s₀ root dirPrefix fs1 hJoin1 hStat1 hMkdir1 hChmod1 hvr hvp stRoot hRoot hRwx hNone
  dsimp only at hCreateLockRm
  obtain ⟨sMk, hsMk⟩ : ∃ s : TempMockState, s =
      { s₀ with
        nextUuid := s₀.nextUuid + 1
        nodes := (dir, .dir s₀.nowSec 0o700) :: s₀.nodes.filter (fun e => !underDir dir e.1) } := ⟨_, rfl⟩
  rw [← hsMk] at hCreateLockRm
  have hWflLockRm :
      (fs1.withFileLock (fs1.join dir ".lock") .shared true
        (do let r ← (fun _ => (pure (.ok val) : StateM TempMockState (Except TempError Nat))) dir; return .ok r)).run sMk =
        (.error { kind := .permissionDenied, path := some lockPath, message := "lock denied" }, sMk) := by
    rw [hJoin1, hWfl1]; exact stateM_pure_run _ _
  have hCleanLockRm :
      (Internal.cleanupDirIgnoringNotFound fs1 dir).run sMk =
        (.error (Internal.mapFsError { kind := .ioError, path := some dir, message := "rm failed" }), sMk) :=
    cleanupDir_mock_of_rmtree_err sMk dir fs1 { kind := .ioError, path := some dir, message := "rm failed" }
      (by rw [hRm1]; exact stateM_pure_run _ _) rfl
  have hRunLockRm := withLockedTempDir_wfl_err_step fs1 mockTime mockUuid mockEnv s₀ sMk sMk (some root) dirPrefix dir
    (fun _ => pure (.ok val)) { kind := .permissionDenied, path := some lockPath, message := "lock denied" } _
    hCreateLockRm hWflLockRm hCleanLockRm
  exact ⟨sMk, _, hRunLockRm, _, rfl, rfl⟩

private theorem spec8_lockClean_exec (s₀ : TempMockState) (root dirPrefix : String) (val : Nat)
    (fs2 : FsApiM (StateM TempMockState))
    (hvr : (!root.isEmpty && !(Char.ofNat 0 ∈ root.toList)) = true)
    (hvp : (!dirPrefix.isEmpty && dirPrefix.toList.head? != some '.' && !('/' ∈ dirPrefix.toList) && !(Char.ofNat 0 ∈ dirPrefix.toList)) = true)
    (stRoot : FileStat) (hRoot : mockStatPure s₀ root = .ok stRoot)
    (hRwx : stRoot.kind = .dir ∧ (stRoot.mode / 256) % 2 = 1 ∧ (stRoot.mode / 128) % 2 = 1 ∧ (stRoot.mode / 64) % 2 = 1)
    (hNone : (mockLstatPure { s₀ with nextUuid := s₀.nextUuid + 1 }
      (mockJoin root (dirPrefix ++ mockUuidToString (mockUuidOfNat s₀.nextUuid)))).isOk = false)
    (hJoin2 : fs2.join = mockJoin) (hStat2 : fs2.stat = mockFs.stat)
    (hMkdir2 : fs2.mkdir = mockFs.mkdir) (hChmod2 : fs2.chmod = mockFs.chmod)
    (hWfl2 : ∀ {β : Type} p m c (body : StateM TempMockState (Except FsError β)),
      fs2.withFileLock p m c body = pure (.error { kind := .permissionDenied, path := some p, message := "lock denied" }))
    (hRm2 : fs2.rmtree = mockFs.rmtree) :
    let u := mockUuidOfNat s₀.nextUuid
    let dir := mockJoin root (dirPrefix ++ mockUuidToString u)
    ∃ sLockClean : TempMockState, ∃ resLockClean : Except TempError Nat,
      ((Internal.mkApiM fs2 mockTime mockUuid mockEnv).withLockedTempDir
        (some root) dirPrefix fun _ => pure (.ok val)).run s₀ = (resLockClean, sLockClean) ∧
      (∃ e, resLockClean = .error e ∧ e.kind = .permissionDenied) ∧
      ((mockFs.lstat dir).run sLockClean).1.isOk = false := by
  intro u dir
  let lockPath := mockJoin dir ".lock"
  have hrNe : root ≠ "" := validRoot_ne_empty root hvr
  have ⟨hcNe, hcNoSlash⟩ := childName_parts dirPrefix u hvp
  have hDirNorm : normKey dir = dir := normKey_mockJoin root _ hcNe hcNoSlash
  have hCreateLockClean := createTempDir_mock_steps_of_ops s₀ root dirPrefix fs2 hJoin2 hStat2 hMkdir2 hChmod2 hvr hvp stRoot hRoot hRwx hNone
  dsimp only at hCreateLockClean
  obtain ⟨sMk, hsMk⟩ : ∃ s : TempMockState, s =
      { s₀ with
        nextUuid := s₀.nextUuid + 1
        nodes := (dir, .dir s₀.nowSec 0o700) :: s₀.nodes.filter (fun e => !underDir dir e.1) } := ⟨_, rfl⟩
  rw [← hsMk] at hCreateLockClean
  have hLookDirMk : lookupNode sMk.nodes dir = some (.dir s₀.nowSec 0o700) := by
    rw [hsMk]; exact lookupNode_cons_eq _ _ _ _ rfl
  obtain ⟨sFinClean, hsFinClean⟩ : ∃ s : TempMockState, s =
      { sMk with nodes := sMk.nodes.filter (fun e => !underDir dir e.1) } := ⟨_, rfl⟩
  have hWflLockClean :
      (fs2.withFileLock (fs2.join dir ".lock") .shared true
        (do let r ← (fun _ => (pure (.ok val) : StateM TempMockState (Except TempError Nat))) dir; return .ok r)).run sMk =
        (.error { kind := .permissionDenied, path := some lockPath, message := "lock denied" }, sMk) := by
    rw [hJoin2, hWfl2]; exact stateM_pure_run _ _
  have hCleanLockClean : (Internal.cleanupDirIgnoringNotFound fs2 dir).run sMk = (.ok (), sFinClean) := by
    rw [hsFinClean]
    exact cleanupDir_mock_of_rmtree sMk dir fs2 hRm2 hDirNorm ⟨_, _, hLookDirMk⟩
  have hRunLockClean := withLockedTempDir_wfl_err_step fs2 mockTime mockUuid mockEnv s₀ sMk sFinClean (some root) dirPrefix dir
    (fun _ => pure (.ok val)) { kind := .permissionDenied, path := some lockPath, message := "lock denied" } (.ok ())
    hCreateLockClean hWflLockClean hCleanLockClean
  have hLookDirClean : lookupNode sFinClean.nodes dir = none := by
    rw [hsFinClean]; exact lookupNode_filter_none_of_underDir sMk.nodes dir dir (underDir_refl dir hDirNorm)
  exact ⟨sFinClean, _, hRunLockClean, ⟨_, rfl, rfl⟩,
    mockFs_lstat_isOk_false_of_lookup_none sFinClean dir hLookDirClean⟩

/-- Spec 8: `withLockedTempDir` holds a `.shared` lock on `<dir>/.lock` during `action`, releases it and deletes `dir` on `.ok`/`.error`, and cleans up even if locking fails. -/
theorem proof_temp_withLockedTempDir_holdsSharedLockDuringActionAndReleasesOnExit :
    AllPass (test_temp_withLockedTempDir_holdsSharedLockDuringActionAndReleasesOnExit
      (S := TempMockState) Internal.mkApiM mockFs mockTime mockUuid mockEnv) := by
  dsimp only [test_temp_withLockedTempDir_holdsSharedLockDuringActionAndReleasesOnExit, AllPass]
  intro s₀ root dirPrefix val err ⟨hvr, hvp⟩ ⟨stRoot, hRoot, hRwx⟩
  have hRootPure : mockStatPure s₀ root = .ok stRoot := by
    rw [mockFs_stat_run] at hRoot; exact hRoot
  rw [mockUuid_getUuid_run s₀]
  dsimp only
  rw [allPass_assume]
  intro hNone
  have hNonePure : (mockLstatPure { s₀ with nextUuid := s₀.nextUuid + 1 }
      (mockJoin root (dirPrefix ++ mockUuidToString (mockUuidOfNat s₀.nextUuid)))).isOk = false := by
    rw [mockFs_lstat_run, mockFs_join_eq, mockUuid_toString_eq] at hNone; exact hNone
  rw [mockFs_join_eq, mockUuid_toString_eq]
  have ⟨hLDir, hLLock, hShared, hEx⟩ := spec8_lockState_probes s₀ root dirPrefix hvr hvp
  let dir := mockJoin root (dirPrefix ++ mockUuidToString (mockUuidOfNat s₀.nextUuid))
  let act8 : String → StateM TempMockState (Except TempError Nat) := fun d => do
    let stDir ← mockFs.lstat d
    let lst ← mockFs.lstat (mockJoin d ".lock")
    let sharedProbe ← mockFs.tryWithFileLock (mockJoin d ".lock") .shared false (pure (.ok ()))
    let exProbe ← mockFs.tryWithFileLock (mockJoin d ".lock") .exclusive false (pure (.ok ()))
    match stDir, lst, sharedProbe, exProbe with
    | .ok info, .ok st, .ok (some ()), .ok none =>
      if info.kind == .dir && info.mode == 0o700 && d == dir && st.kind == .file then
        return .ok val
      else
        return .error { kind := .ioError, path := some d, message := "dir mode or lock invariant failed" }
    | .error _, _, _, _ =>
      return .error { kind := .notFound, path := some d, message := "lstat dir failed" }
    | _, .error _, _, _ =>
      return .error { kind := .notFound, path := some d, message := "missing lock file" }
    | _, _, _, _ =>
      return .error { kind := .ioError, path := some d, message := "lock invariant failed" }
  have hAct : (act8 dir).run (spec8LockState s₀ root dirPrefix) = (.ok val, spec8LockState s₀ root dirPrefix) := by
    dsimp only [act8, dir]
    rw [stateM_bind_run, hLDir]; dsimp only
    rw [stateM_bind_run, hLLock]; dsimp only
    rw [stateM_bind_run, hShared]; dsimp only
    rw [stateM_bind_run, hEx]; dsimp only
    have hModeDir : ((mockNodeStat (.dir s₀.nowSec 0o700)).kind == EntryKind.dir) = true := rfl
    have hModeVal : ((mockNodeStat (.dir s₀.nowSec 0o700)).mode == 0o700) = true := rfl
    have hKindFile : ((mockNodeStat (.file (freshInode (spec8MkState s₀ root dirPrefix)) "" (spec8MkState s₀ root dirPrefix).nowSec 0o644)).kind == EntryKind.file) = true := rfl
    simp only [hModeDir, hModeVal, beq_self_eq_true, hKindFile, Bool.and_self, ↓reduceIte, stateM_pure_run]
  let fs1 : FsApiM (StateM TempMockState) :=
    { mockFs with
      withFileLock := fun p _ _ _ => pure (.error { kind := .permissionDenied, path := some p, message := "lock denied" })
      rmtree := fun p _ => pure (.error { kind := .ioError, path := some p, message := "rm failed" }) }
  let fs2 : FsApiM (StateM TempMockState) :=
    { mockFs with
      withFileLock := fun p _ _ _ => pure (.error { kind := .permissionDenied, path := some p, message := "lock denied" }) }
  obtain ⟨sOk, hRunOk, h1, h2, h3⟩ :=
    spec8_ok_exec s₀ root dirPrefix val act8 hvr hvp stRoot hRootPure hRwx hNonePure hAct
  obtain ⟨sErr, hRunErr, h4, h5⟩ :=
    spec8_err_exec s₀ root dirPrefix err hvr hvp stRoot hRootPure hRwx hNonePure
  obtain ⟨sLockRm, resLockRm, hRunLockRm, h6⟩ :=
    spec8_lockRm_exec s₀ root dirPrefix val fs1 hvr hvp stRoot hRootPure hRwx hNonePure rfl rfl rfl rfl (fun _ _ _ _ => rfl) (fun _ _ => rfl)
  obtain ⟨sLockClean, resLockClean, hRunLockClean, h7, h8⟩ :=
    spec8_lockClean_exec s₀ root dirPrefix val fs2 hvr hvp stRoot hRootPure hRwx hNonePure rfl rfl rfl rfl (fun _ _ _ _ => rfl) rfl
  conv in ((Internal.mkApiM mockFs mockTime mockUuid mockEnv).withLockedTempDir (some root) dirPrefix _).run s₀ =>
    erw [hRunOk]
  dsimp only [fs1, fs2] at hRunLockRm hRunLockClean
  rw [hRunErr]
  conv in ((Internal.mkApiM _ mockTime mockUuid mockEnv).withLockedTempDir (some root) dirPrefix _).run s₀ =>
    erw [hRunLockRm]
  dsimp only
  rw [allPass_assert, allPass_assert, allPass_assert, allPass_assert, allPass_assert,
    allPass_assert, allPass_assert, allPass_assert]
  conv in ((Internal.mkApiM _ mockTime mockUuid mockEnv).withLockedTempDir (some root) dirPrefix _).run s₀ =>
    erw [hRunLockClean]
  dsimp only
  rw [allPass_assert, allPass_assert_end]
  exact ⟨rfl, h1, h2, h3, rfl, h4, h5, h6, h7, h8, trivial⟩

private theorem spec8_reach_tail (s₀ : TempMockState)
    (hRootPure : mockStatPure s₀ "/tmp" = .ok (mockNodeStat (.dir 0 0o755)))
    (hNonePure : (mockLstatPure { s₀ with nextUuid := s₀.nextUuid + 1 }
      (mockJoin "/tmp" ("tmp-" ++ mockUuidToString (mockUuidOfNat s₀.nextUuid)))).isOk = false) :
    CanReach (do
      let dir := mockJoin "/tmp" ("tmp-" ++ mockUuidToString (mockUuidOfNat s₀.nextUuid))
      let act8 : String → StateM TempMockState (Except TempError Nat) := fun d => do
        let stDir ← mockFs.lstat d
        let lst ← mockFs.lstat (mockJoin d ".lock")
        let sharedProbe ← mockFs.tryWithFileLock (mockJoin d ".lock") .shared false (pure (.ok ()))
        let exProbe ← mockFs.tryWithFileLock (mockJoin d ".lock") .exclusive false (pure (.ok ()))
        match stDir, lst, sharedProbe, exProbe with
        | .ok info, .ok st, .ok (some ()), .ok none =>
          if info.kind == .dir && info.mode == 0o700 && d == dir && st.kind == .file then
            return .ok 42
          else
            return .error { kind := .ioError, path := some d, message := "dir mode or lock invariant failed" }
        | .error _, _, _, _ =>
          return .error { kind := .notFound, path := some d, message := "lstat dir failed" }
        | _, .error _, _, _ =>
          return .error { kind := .notFound, path := some d, message := "missing lock file" }
        | _, _, _, _ =>
          return .error { kind := .ioError, path := some d, message := "lock invariant failed" }
      let (resOk, sOk) := ((Internal.mkApiM mockFs mockTime mockUuid mockEnv).withLockedTempDir (some "/tmp") "tmp-" act8).run s₀
      NondetTest.assert (resOk = .ok 42)
      NondetTest.assert (((mockFs.lstat dir).run sOk).1.isOk = false)
      NondetTest.assert (∃ e, ((mockFs.lstat (mockJoin dir ".lock")).run sOk).1 = .error e ∧ e.kind = .notFound)
      let probeOk := (do
        let _ ← mockFs.mkdir dir false false
        mockFs.tryWithFileLock (mockJoin dir ".lock") .exclusive true (pure (.ok ()))).run sOk
      NondetTest.assert (probeOk.1 = .ok (some ()))
      let (resErr, sErr) := ((Internal.mkApiM mockFs mockTime mockUuid mockEnv).withLockedTempDir (some "/tmp") "tmp-"
        fun _ => pure (Except.error { kind := .ioError, message := "err" } : Except TempError Nat)).run s₀
      NondetTest.assert (resErr = .error { kind := .ioError, message := "err" })
      NondetTest.assert (((mockFs.lstat dir).run sErr).1.isOk = false)
      let probeErr := (do
        let _ ← mockFs.mkdir dir false false
        mockFs.tryWithFileLock (mockJoin dir ".lock") .exclusive true (pure (.ok ()))).run sErr
      NondetTest.assert (probeErr.1 = .ok (some ()))
      let fsLockFailRm : FsApiM (StateM TempMockState) :=
        { mockFs with
          withFileLock := fun p _ _ _ => pure (.error { kind := .permissionDenied, path := some p, message := "lock denied" })
          rmtree := fun p _ => pure (.error { kind := .ioError, path := some p, message := "rm failed" }) }
      let (resLockRm, _) := ((Internal.mkApiM fsLockFailRm mockTime mockUuid mockEnv).withLockedTempDir (some "/tmp") "tmp-" fun _ => pure (.ok (42 : Nat))).run s₀
      NondetTest.assert (∃ e, resLockRm = .error e ∧ e.kind = .permissionDenied)
      let fsLockFailClean : FsApiM (StateM TempMockState) :=
        { mockFs with
          withFileLock := fun p _ _ _ => pure (.error { kind := .permissionDenied, path := some p, message := "lock denied" }) }
      let (resLockClean, sLockClean) := ((Internal.mkApiM fsLockFailClean mockTime mockUuid mockEnv).withLockedTempDir (some "/tmp") "tmp-" fun _ => pure (.ok (42 : Nat))).run s₀
      NondetTest.assert (∃ e, resLockClean = .error e ∧ e.kind = .permissionDenied)
      NondetTest.assert (((mockFs.lstat dir).run sLockClean).1.isOk = false)) := by
  dsimp only [CanReach]
  have ⟨hLDir, hLLock, hShared, hEx⟩ := spec8_lockState_probes s₀ "/tmp" "tmp-" rfl rfl
  let dir := mockJoin "/tmp" ("tmp-" ++ mockUuidToString (mockUuidOfNat s₀.nextUuid))
  let act8 : String → StateM TempMockState (Except TempError Nat) := fun d => do
    let stDir ← mockFs.lstat d
    let lst ← mockFs.lstat (mockJoin d ".lock")
    let sharedProbe ← mockFs.tryWithFileLock (mockJoin d ".lock") .shared false (pure (.ok ()))
    let exProbe ← mockFs.tryWithFileLock (mockJoin d ".lock") .exclusive false (pure (.ok ()))
    match stDir, lst, sharedProbe, exProbe with
    | .ok info, .ok st, .ok (some ()), .ok none =>
      if info.kind == .dir && info.mode == 0o700 && d == dir && st.kind == .file then
        return .ok 42
      else
        return .error { kind := .ioError, path := some d, message := "dir mode or lock invariant failed" }
    | .error _, _, _, _ =>
      return .error { kind := .notFound, path := some d, message := "lstat dir failed" }
    | _, .error _, _, _ =>
      return .error { kind := .notFound, path := some d, message := "missing lock file" }
    | _, _, _, _ =>
      return .error { kind := .ioError, path := some d, message := "lock invariant failed" }
  have hAct : (act8 dir).run (spec8LockState s₀ "/tmp" "tmp-") = (.ok 42, spec8LockState s₀ "/tmp" "tmp-") := by
    dsimp only [act8, dir]
    rw [stateM_bind_run, hLDir]; dsimp only
    rw [stateM_bind_run, hLLock]; dsimp only
    rw [stateM_bind_run, hShared]; dsimp only
    rw [stateM_bind_run, hEx]; dsimp only
    have hModeDir : ((mockNodeStat (.dir s₀.nowSec 0o700)).kind == EntryKind.dir) = true := rfl
    have hModeVal : ((mockNodeStat (.dir s₀.nowSec 0o700)).mode == 0o700) = true := rfl
    have hKindFile : ((mockNodeStat (.file (freshInode (spec8MkState s₀ "/tmp" "tmp-")) "" (spec8MkState s₀ "/tmp" "tmp-").nowSec 0o644)).kind == EntryKind.file) = true := rfl
    simp only [hModeDir, hModeVal, beq_self_eq_true, hKindFile, Bool.and_self, ↓reduceIte, stateM_pure_run]
  let fs1 : FsApiM (StateM TempMockState) :=
    { mockFs with
      withFileLock := fun p _ _ _ => pure (.error { kind := .permissionDenied, path := some p, message := "lock denied" })
      rmtree := fun p _ => pure (.error { kind := .ioError, path := some p, message := "rm failed" }) }
  let fs2 : FsApiM (StateM TempMockState) :=
    { mockFs with
      withFileLock := fun p _ _ _ => pure (.error { kind := .permissionDenied, path := some p, message := "lock denied" }) }
  obtain ⟨sOk, hRunOk, h1, h2, h3⟩ :=
    spec8_ok_exec s₀ "/tmp" "tmp-" 42 act8
      rfl rfl (mockNodeStat (.dir 0 0o755)) hRootPure ⟨rfl, rfl, rfl, rfl⟩ hNonePure hAct
  obtain ⟨sErr, hRunErr, h4, h5⟩ :=
    spec8_err_exec s₀ "/tmp" "tmp-" { kind := .ioError, message := "err" }
      rfl rfl (mockNodeStat (.dir 0 0o755)) hRootPure ⟨rfl, rfl, rfl, rfl⟩ hNonePure
  obtain ⟨sLockRm, resLockRm, hRunLockRm, h6⟩ :=
    spec8_lockRm_exec s₀ "/tmp" "tmp-" 42 fs1 rfl rfl (mockNodeStat (.dir 0 0o755)) hRootPure ⟨rfl, rfl, rfl, rfl⟩ hNonePure rfl rfl rfl rfl (fun _ _ _ _ => rfl) (fun _ _ => rfl)
  obtain ⟨sLockClean, resLockClean, hRunLockClean, h7, h8⟩ :=
    spec8_lockClean_exec s₀ "/tmp" "tmp-" 42 fs2 rfl rfl (mockNodeStat (.dir 0 0o755)) hRootPure ⟨rfl, rfl, rfl, rfl⟩ hNonePure rfl rfl rfl rfl (fun _ _ _ _ => rfl) rfl
  conv in ((Internal.mkApiM mockFs mockTime mockUuid mockEnv).withLockedTempDir (some "/tmp") "tmp-" _).run s₀ =>
    erw [hRunOk]
  dsimp only [fs1, fs2] at hRunLockRm hRunLockClean
  rw [hRunErr]
  conv in ((Internal.mkApiM _ mockTime mockUuid mockEnv).withLockedTempDir (some "/tmp") "tmp-" _).run s₀ =>
    erw [hRunLockRm]
  dsimp only
  rw [canReach_assert, canReach_assert, canReach_assert, canReach_assert, canReach_assert,
    canReach_assert, canReach_assert, canReach_assert]
  conv in ((Internal.mkApiM _ mockTime mockUuid mockEnv).withLockedTempDir (some "/tmp") "tmp-" _).run s₀ =>
    erw [hRunLockClean]
  dsimp only
  rw [canReach_assert, canReach_assert_end]
  exact ⟨rfl, h1, h2, h3, rfl, h4, h5, h6, h7, h8, trivial⟩

/-- Non-vacuity `CanReach` witness for Spec 8 (`test_temp_withLockedTempDir_holdsSharedLockDuringActionAndReleasesOnExit`). -/
theorem reach_temp_withLockedTempDir_holdsSharedLockDuringActionAndReleasesOnExit :
    CanReach (test_temp_withLockedTempDir_holdsSharedLockDuringActionAndReleasesOnExit
      (S := TempMockState) Internal.mkApiM mockFs mockTime mockUuid mockEnv) := by
  dsimp only [test_temp_withLockedTempDir_holdsSharedLockDuringActionAndReleasesOnExit, CanReach]
  obtain ⟨s₀, hs₀⟩ : ∃ s : TempMockState, s = {} := ⟨{}, rfl⟩
  rw [canReach_nondet]; refine ⟨s₀, ?_⟩
  rw [canReach_nondet]; refine ⟨"/tmp", ?_⟩
  rw [canReach_nondet]; refine ⟨"tmp-", ?_⟩
  rw [canReach_nondet]; refine ⟨42, ?_⟩
  rw [canReach_nondet]; refine ⟨{ kind := .ioError, message := "err" }, ?_⟩
  rw [canReach_assume]; refine ⟨⟨rfl, rfl⟩, ?_⟩
  have hRootPure : mockStatPure s₀ "/tmp" = .ok (mockNodeStat (.dir 0 0o755)) := by
    rw [hs₀]; rfl
  have hRoot : ∃ stRoot, ((mockFs.stat "/tmp").run s₀).1 = .ok stRoot ∧
      stRoot.kind = .dir ∧ (stRoot.mode / 256) % 2 = 1 ∧ (stRoot.mode / 128) % 2 = 1 ∧ (stRoot.mode / 64) % 2 = 1 :=
    ⟨mockNodeStat (.dir 0 0o755), by rw [mockFs_stat_run]; exact hRootPure, rfl, rfl, rfl, rfl⟩
  rw [canReach_assume]; refine ⟨hRoot, ?_⟩
  rw [mockUuid_getUuid_run s₀]
  dsimp only
  have hNonePure : (mockLstatPure { s₀ with nextUuid := s₀.nextUuid + 1 }
      (mockJoin "/tmp" ("tmp-" ++ mockUuidToString (mockUuidOfNat s₀.nextUuid)))).isOk = false := by
    rw [hs₀]
    unfold mockLstatPure
    dsimp only
    have ⟨hcNe, hcNoSlash⟩ := childName_parts "tmp-" (mockUuidOfNat 1) rfl
    have hNe : normKey "/tmp" ≠ normKey (mockJoin "/tmp" ("tmp-" ++ mockUuidToString (mockUuidOfNat 1))) :=
      ne_comm.mp (mockJoin_ne_root "/tmp" _ (by decide) hcNe hcNoSlash)
    rw [lookupNode_cons_ne "/tmp" (.dir 0 0o755) [] _ hNe]
    rfl
  have hNone : (mockFs.lstat (mockFs.join "/tmp" ("tmp-" ++ mockUuid.toString (mockUuidOfNat s₀.nextUuid)))).run
      { s₀ with nextUuid := s₀.nextUuid + 1 } |>.1.isOk = false := by
    rw [mockFs_lstat_run, mockFs_join_eq, mockUuid_toString_eq]; exact hNonePure
  rw [canReach_assume]; refine ⟨hNone, ?_⟩
  rw [mockFs_join_eq, mockUuid_toString_eq]
  exact spec8_reach_tail s₀ hRootPure hNonePure

private theorem spec9_exec (s₀ : TempMockState) (root dirPrefix : String) (val : Nat)
    (fsConcurrentSweep : FsApiM (StateM TempMockState))
    (hvr : (!root.isEmpty && !(Char.ofNat 0 ∈ root.toList)) = true)
    (hvp : (!dirPrefix.isEmpty && dirPrefix.toList.head? != some '.' && !('/' ∈ dirPrefix.toList) && !(Char.ofNat 0 ∈ dirPrefix.toList)) = true)
    (stRoot : FileStat) (hRoot : mockStatPure s₀ root = .ok stRoot)
    (hRwx : stRoot.kind = .dir ∧ (stRoot.mode / 256) % 2 = 1 ∧ (stRoot.mode / 128) % 2 = 1 ∧ (stRoot.mode / 64) % 2 = 1)
    (hNone : (mockLstatPure { s₀ with nextUuid := s₀.nextUuid + 1 }
      (mockJoin root (dirPrefix ++ mockUuidToString (mockUuidOfNat s₀.nextUuid)))).isOk = false)
    (hJoin : fsConcurrentSweep.join = mockJoin)
    (hStat : fsConcurrentSweep.stat = mockFs.stat)
    (hMkdir : fsConcurrentSweep.mkdir = mockFs.mkdir)
    (hChmod : fsConcurrentSweep.chmod = mockFs.chmod)
    (hWfl : ∀ {β : Type}, @fsConcurrentSweep.withFileLock β = @mockFs.withFileLock β)
    (hRm : ∀ p ign, fsConcurrentSweep.rmtree p ign = do
      let _ ← mockFs.rmtree p ign
      pure (.error { kind := .notFound, path := some p, message := "removed concurrently" })) :
    let u := mockUuidOfNat s₀.nextUuid
    let dir := mockJoin root (dirPrefix ++ mockUuidToString u)
    ∃ s₁ : TempMockState,
      ((Internal.mkApiM fsConcurrentSweep mockTime mockUuid mockEnv).withLockedTempDir
        (some root) dirPrefix fun _ => pure (.ok val)).run s₀ = (.ok val, s₁) ∧
      ((mockFs.lstat dir).run s₁).1.isOk = false := by
  intro u dir
  have hrNe : root ≠ "" := validRoot_ne_empty root hvr
  have ⟨hcNe, hcNoSlash⟩ := childName_parts dirPrefix u hvp
  have hDirNorm : normKey dir = dir := normKey_mockJoin root _ hcNe hcNoSlash
  have hDirNe : dir ≠ "" := mockJoin_ne_empty root _ hcNe
  have hDirNeSlash : dir ≠ "/" := mockJoin_ne_slash root _ hrNe hcNe
  have hLockNorm : normKey (mockJoin dir ".lock") = mockJoin dir ".lock" :=
    normKey_mockJoin dir ".lock" (by decide) (by decide)
  have hLockNeDir : normKey (mockJoin dir ".lock") ≠ dir :=
    payload_ne_dir root (dirPrefix ++ mockUuidToString u) ".lock" hrNe hcNe hcNoSlash (by decide) (by decide)
  have hUnderLock : underDir dir (mockJoin dir ".lock") = true :=
    underDir_mockJoin_self dir ".lock" hDirNe hDirNorm hDirNeSlash (by decide) (by decide)
  have hCreate := createTempDir_mock_steps_of_ops s₀ root dirPrefix fsConcurrentSweep hJoin hStat hMkdir hChmod
    hvr hvp stRoot hRoot hRwx hNone
  dsimp only at hCreate
  obtain ⟨sMk, hsMk⟩ : ∃ s : TempMockState, s =
      { s₀ with
        nextUuid := s₀.nextUuid + 1
        nodes := (dir, .dir s₀.nowSec 0o700) :: s₀.nodes.filter (fun e => !underDir dir e.1) } := ⟨_, rfl⟩
  rw [← hsMk] at hCreate
  have hLookDirMk : lookupNode sMk.nodes dir = some (.dir s₀.nowSec 0o700) := by
    rw [hsMk]; exact lookupNode_cons_eq _ _ _ _ rfl
  have hLookLockMk : lookupNode sMk.nodes (mockJoin dir ".lock") = none := by
    rw [hsMk]
    unfold lookupNode
    dsimp only
    have hb : (normKey dir == normKey (mockJoin dir ".lock")) = false := by
      rw [hDirNorm, beq_false_of_ne (ne_comm.mp hLockNeDir)]
    rw [List.find?_cons, hb]
    exact lookupNode_filter_none_of_underDir s₀.nodes dir (mockJoin dir ".lock") hUnderLock
  obtain ⟨sAfterLock, hsAfterLock⟩ : ∃ s : TempMockState, s =
      { nodes := (mockJoin dir ".lock", .file (freshInode sMk) "" sMk.nowSec 0o644) :: sMk.nodes
        locks := mockRemoveFirstLock (freshInode sMk) .shared ((freshInode sMk, .shared) :: sMk.locks)
        nextInode := freshInode sMk + 1
        tmpdir := sMk.tmpdir
        nowSec := sMk.nowSec
        nextUuid := sMk.nextUuid } := ⟨_, rfl⟩
  have hLookDirAfterLock : lookupNode sAfterLock.nodes dir = some (.dir s₀.nowSec 0o700) := by
    rw [hsAfterLock]
    unfold lookupNode
    dsimp only
    have hb : (normKey (mockJoin dir ".lock") == normKey dir) = false := by
      rw [hDirNorm, beq_false_of_ne hLockNeDir]
    rw [List.find?_cons, hb]
    exact hLookDirMk
  obtain ⟨sFin, hsFin⟩ : ∃ s : TempMockState, s =
      { sAfterLock with nodes := sAfterLock.nodes.filter (fun e => !underDir dir e.1) } := ⟨_, rfl⟩
  have hRmInner : (mockFs.rmtree dir true).run sAfterLock = (.ok (), sFin) := by
    rw [hsFin]
    dsimp only [mockFs, mockRmtreePure, resolveParentTarget]
    rw [stateM_bind_run, stateM_get_run]
    dsimp only
    rw [hDirNorm, hLookDirAfterLock]
    simp only [stateM_bind_run, stateM_set_run, stateM_pure_run]
  have hClean : (Internal.cleanupDirIgnoringNotFound fsConcurrentSweep dir).run sAfterLock = (.ok (), sFin) := by
    dsimp only [Internal.cleanupDirIgnoringNotFound]
    rw [hRm, stateM_bind_run, stateM_bind_run, hRmInner]
    dsimp only
    rw [stateM_pure_run]
    dsimp only
    rw [show (FsErrorKind.notFound == FsErrorKind.notFound) = true from rfl]
    simp only [↓reduceIte]
    exact stateM_pure_run _ _
  have hRun : ((Internal.mkApiM fsConcurrentSweep mockTime mockUuid mockEnv).withLockedTempDir
      (some root) dirPrefix fun _ => pure (.ok val)).run s₀ = (.ok val, sFin) := by
    rw [mkApiM_withLockedTempDir_eq]
    dsimp only [Internal.withLockedTempDirM]
    rw [stateM_bind_run, hCreate]
    dsimp only
    rw [stateM_bind_run, stateM_tryFinally'_run, hJoin, hWfl]
    rw [mockFs_withFileLock_create_run sMk (mockJoin dir ".lock") .shared hLockNorm hLookLockMk]
    rw [stateM_bind_run, stateM_pure_run, stateM_pure_run]
    dsimp only
    rw [← hsAfterLock, hClean]
    dsimp only
    exact stateM_pure_run _ _
  have hLookDirFin : lookupNode sFin.nodes dir = none := by
    rw [hsFin]; exact lookupNode_filter_none_of_underDir sAfterLock.nodes dir dir (underDir_refl dir hDirNorm)
  exact ⟨sFin, hRun, mockFs_lstat_isOk_false_of_lookup_none sFin dir hLookDirFin⟩

/-- Spec 9: `withLockedTempDir` ignores `.notFound` from `fs.rmtree` in its finalizer on concurrent cleanup. -/
theorem proof_temp_withLockedTempDir_ignoresNotFoundOnConcurrentCleanup :
    AllPass (test_temp_withLockedTempDir_ignoresNotFoundOnConcurrentCleanup
      (S := TempMockState) Internal.mkApiM mockFs mockTime mockUuid mockEnv) := by
  dsimp only [test_temp_withLockedTempDir_ignoresNotFoundOnConcurrentCleanup, AllPass]
  intro s₀ root dirPrefix val ⟨hvr, hvp⟩ ⟨stRoot, hRoot, hRwx⟩
  have hRootPure : mockStatPure s₀ root = .ok stRoot := by
    rw [mockFs_stat_run] at hRoot; exact hRoot
  rw [mockUuid_getUuid_run s₀]
  dsimp only
  rw [allPass_assume]
  intro hNone
  have hNonePure : (mockLstatPure { s₀ with nextUuid := s₀.nextUuid + 1 }
      (mockJoin root (dirPrefix ++ mockUuidToString (mockUuidOfNat s₀.nextUuid)))).isOk = false := by
    rw [mockFs_lstat_run, mockFs_join_eq, mockUuid_toString_eq] at hNone; exact hNone
  let fsConcurrentSweep : FsApiM (StateM TempMockState) :=
    { mockFs with
      rmtree := fun p ign => do
        let _ ← mockFs.rmtree p ign
        pure (.error { kind := .notFound, path := some p, message := "removed concurrently" }) }
  obtain ⟨s₁, hRun, hDead⟩ := spec9_exec s₀ root dirPrefix val fsConcurrentSweep hvr hvp stRoot hRootPure hRwx hNonePure
    rfl rfl rfl rfl rfl (fun _ _ => rfl)
  rw [hRun]
  dsimp only
  rw [allPass_assert, allPass_assert_end]
  exact ⟨rfl, hDead, trivial⟩

/-- Non-vacuity `CanReach` witness for Spec 9 (`test_temp_withLockedTempDir_ignoresNotFoundOnConcurrentCleanup`). -/
theorem reach_temp_withLockedTempDir_ignoresNotFoundOnConcurrentCleanup :
    CanReach (test_temp_withLockedTempDir_ignoresNotFoundOnConcurrentCleanup
      (S := TempMockState) Internal.mkApiM mockFs mockTime mockUuid mockEnv) := by
  dsimp only [test_temp_withLockedTempDir_ignoresNotFoundOnConcurrentCleanup, CanReach]
  obtain ⟨s₀, hs₀⟩ : ∃ s : TempMockState, s = {} := ⟨{}, rfl⟩
  rw [canReach_nondet]; refine ⟨s₀, ?_⟩
  rw [canReach_nondet]; refine ⟨"/tmp", ?_⟩
  rw [canReach_nondet]; refine ⟨"tmp-", ?_⟩
  rw [canReach_nondet]; refine ⟨7, ?_⟩
  rw [canReach_assume]; refine ⟨⟨rfl, rfl⟩, ?_⟩
  have hRootPure : mockStatPure s₀ "/tmp" = .ok (mockNodeStat (.dir 0 0o755)) := by
    rw [hs₀]; rfl
  have hRoot : ∃ stRoot, ((mockFs.stat "/tmp").run s₀).1 = .ok stRoot ∧
      stRoot.kind = .dir ∧ (stRoot.mode / 256) % 2 = 1 ∧ (stRoot.mode / 128) % 2 = 1 ∧ (stRoot.mode / 64) % 2 = 1 :=
    ⟨mockNodeStat (.dir 0 0o755), by rw [mockFs_stat_run]; exact hRootPure, rfl, rfl, rfl, rfl⟩
  rw [canReach_assume]; refine ⟨hRoot, ?_⟩
  rw [mockUuid_getUuid_run s₀]
  dsimp only
  have hNonePure : (mockLstatPure { s₀ with nextUuid := s₀.nextUuid + 1 }
      (mockJoin "/tmp" ("tmp-" ++ mockUuidToString (mockUuidOfNat s₀.nextUuid)))).isOk = false := by
    rw [hs₀]
    unfold mockLstatPure
    dsimp only
    have ⟨hcNe, hcNoSlash⟩ := childName_parts "tmp-" (mockUuidOfNat 1) rfl
    have hNe : normKey "/tmp" ≠ normKey (mockJoin "/tmp" ("tmp-" ++ mockUuidToString (mockUuidOfNat 1))) :=
      ne_comm.mp (mockJoin_ne_root "/tmp" _ (by decide) hcNe hcNoSlash)
    rw [lookupNode_cons_ne "/tmp" (.dir 0 0o755) [] _ hNe]
    rfl
  have hNone : (mockFs.lstat (mockFs.join "/tmp" ("tmp-" ++ mockUuid.toString (mockUuidOfNat s₀.nextUuid)))).run
      { s₀ with nextUuid := s₀.nextUuid + 1 } |>.1.isOk = false := by
    rw [mockFs_lstat_run, mockFs_join_eq, mockUuid_toString_eq]; exact hNonePure
  rw [canReach_assume]; refine ⟨hNone, ?_⟩
  let fsConcurrentSweep : FsApiM (StateM TempMockState) :=
    { mockFs with
      rmtree := fun p ign => do
        let _ ← mockFs.rmtree p ign
        pure (.error { kind := .notFound, path := some p, message := "removed concurrently" }) }
  obtain ⟨s₁, hRun, hDead⟩ := spec9_exec s₀ "/tmp" "tmp-" 7 fsConcurrentSweep rfl rfl (mockNodeStat (.dir 0 0o755)) hRootPure ⟨rfl, rfl, rfl, rfl⟩ hNonePure
    rfl rfl rfl rfl rfl (fun _ _ => rfl)
  rw [hRun]
  dsimp only
  rw [canReach_assert, canReach_assert_end]
  exact ⟨rfl, hDead, trivial⟩

private theorem exceptT_liftM_stateM_run {ε S α : Type} (x : StateM S α) (s : S) :
    (ExceptT.run (liftM x : ExceptT ε (StateM S) α)).run s = (.ok (x.run s).1, (x.run s).2) := by
  dsimp only [liftM, monadLift, MonadLift.monadLift, ExceptT.lift, ExceptT.mk, StateT.run, ExceptT.run]
  cases hx : x.run s with
  | mk a s' => rfl

private theorem exceptT_stateM_pure_run {ε S α : Type} (a : α) (s : S) :
    (ExceptT.run (pure a : ExceptT ε (StateM S) α)).run s = (.ok a, s) := rfl

private theorem exceptT_stateM_throw_run {ε S α : Type} (e : ε) (s : S) :
    (ExceptT.run (throw e : ExceptT ε (StateM S) α)).run s = (.error e, s) := rfl

private theorem createTempDir_ex_mock_steps (s₀ : TempMockState) (root dirPrefix : String)
    (hvr : (!root.isEmpty && !(Char.ofNat 0 ∈ root.toList)) = true)
    (hvp : (!dirPrefix.isEmpty && dirPrefix.toList.head? != some '.' && !('/' ∈ dirPrefix.toList) && !(Char.ofNat 0 ∈ dirPrefix.toList)) = true)
    (stRoot : FileStat) (hRoot : mockStatPure s₀ root = .ok stRoot)
    (hRwx : stRoot.kind = .dir ∧ (stRoot.mode / 256) % 2 = 1 ∧ (stRoot.mode / 128) % 2 = 1 ∧ (stRoot.mode / 64) % 2 = 1)
    (hNone : (mockLstatPure { s₀ with nextUuid := s₀.nextUuid + 1 }
      (mockJoin root (dirPrefix ++ mockUuidToString (mockUuidOfNat s₀.nextUuid)))).isOk = false) :
    let u := mockUuidOfNat s₀.nextUuid
    let dir := mockJoin root (dirPrefix ++ mockUuidToString u)
    let sMk := { s₀ with
      nextUuid := s₀.nextUuid + 1
      nodes := (dir, .dir s₀.nowSec 0o700) :: s₀.nodes.filter (fun e => !underDir dir e.1) }
    (ExceptT.run (Internal.createTempDir mockFsEx mockUuidEx mockEnvEx (some root) dirPrefix)).run s₀ =
      (.ok (.ok dir), sMk) := by
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
  have hResEx : (ExceptT.run (Internal.resolveRoot mockFsEx mockEnvEx (some root))).run s₀ = (.ok (.ok root), s₀) := by
    dsimp only [Internal.resolveRoot]
    rw [exceptT_stateM_bind_run, exceptT_stateM_pure_run]
    dsimp only
    simp only [hvr', Bool.not_true, Bool.false_eq_true, ↓reduceIte, exceptT_stateM_bind_run]
    have hStEx : (ExceptT.run (mockFsEx.stat root)).run s₀ = (.ok (.ok stRoot), s₀) := by
      dsimp only [mockFsEx]
      rw [exceptT_liftM_stateM_run, mockFs_stat_run, hRoot]
    rw [hStEx]
    dsimp only
    simp only [hRwx.1, show (EntryKind.dir != EntryKind.dir) = false from rfl,
      Bool.false_eq_true, ↓reduceIte, exceptT_stateM_pure_run]
  have hUuidStep : mockUuid.getUuid.run s₀ = (.ok u, { s₀ with nextUuid := s₀.nextUuid + 1 }) := by
    simp [mockUuid, u]; rfl
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
  dsimp only [Internal.createTempDir]
  simp only [hvp', Bool.not_true, Bool.false_eq_true, ↓reduceIte, exceptT_stateM_bind_run, hResEx]
  have hUuidEx : (ExceptT.run mockUuidEx.getUuid).run s₀ = (.ok (.ok u), { s₀ with nextUuid := s₀.nextUuid + 1 }) := by
    dsimp only [mockUuidEx]
    rw [exceptT_liftM_stateM_run, hUuidStep]
  rw [hUuidEx]
  dsimp only
  have hDirEq : mockFsEx.join root (dirPrefix ++ mockUuidEx.toString u) = dir := rfl
  simp only [hDirEq]
  have hMkEx : (ExceptT.run (mockFsEx.mkdir dir false false)).run { s₀ with nextUuid := s₀.nextUuid + 1 } =
      (.ok (.ok ()), { s₀ with
        nextUuid := s₀.nextUuid + 1
        nodes := (dir, .dir s₀.nowSec 0o755) :: s₀.nodes.filter (fun e => !underDir dir e.1) }) := by
    dsimp only [mockFsEx]
    rw [exceptT_liftM_stateM_run, hMk]
  rw [exceptT_stateM_bind_run, hMkEx]
  dsimp only
  have hChEx : (ExceptT.run (mockFsEx.chmod dir 0o700)).run
      { s₀ with
        nextUuid := s₀.nextUuid + 1
        nodes := (dir, .dir s₀.nowSec 0o755) :: s₀.nodes.filter (fun e => !underDir dir e.1) } =
      (.ok (.ok ()), sMk) := by
    dsimp only [mockFsEx]
    rw [exceptT_liftM_stateM_run, hCh]
  rw [exceptT_stateM_bind_run, hChEx]
  exact exceptT_stateM_pure_run _ _

private theorem cleanupDir_ex_mock_run (s : TempMockState) (dir : String) (hnorm : normKey dir = dir)
    (hnode : ∃ m mode, lookupNode s.nodes dir = some (.dir m mode)) :
    (ExceptT.run (Internal.cleanupDirIgnoringNotFound mockFsEx dir)).run s =
      (.ok (.ok ()), { s with nodes := s.nodes.filter (fun e => !underDir dir e.1) }) := by
  dsimp only [Internal.cleanupDirIgnoringNotFound]
  rw [exceptT_stateM_bind_run]
  have hRmEx : (ExceptT.run (mockFsEx.rmtree dir true)).run s =
      (.ok (.ok ()), { s with nodes := s.nodes.filter (fun e => !underDir dir e.1) }) := by
    dsimp only [mockFsEx]
    rw [exceptT_liftM_stateM_run]
    rcases hnode with ⟨m, mode, hLook⟩
    have hRm : (mockFs.rmtree dir true).run s =
        (.ok (), { s with nodes := s.nodes.filter (fun e => !underDir dir e.1) }) := by
      dsimp only [mockFs, mockRmtreePure, resolveParentTarget]
      rw [stateM_bind_run, stateM_get_run]
      dsimp only
      rw [hnorm, hLook]
      simp only [stateM_bind_run, stateM_set_run, stateM_pure_run]
    rw [hRm]
  rw [hRmEx]
  exact exceptT_stateM_pure_run _ _

private theorem mockFsEx_withFileLock_create_throw_run
    (s : TempMockState) (p : String) (mode : LockMode)
    (hp : normKey p = p) (hNone : lookupNode s.nodes p = none)
    (act : ExceptT String (StateM TempMockState) (Except FsError (Except TempError Unit))) (errStr : String)
    (hActThrow : (ExceptT.run act).run
      { s with
        nodes := (p, .file (freshInode s) "" s.nowSec 0o644) :: s.nodes
        locks := (freshInode s, mode) :: s.locks
        nextInode := freshInode s + 1 } =
      (.error errStr, { s with
        nodes := (p, .file (freshInode s) "" s.nowSec 0o644) :: s.nodes
        locks := (freshInode s, mode) :: s.locks
        nextInode := freshInode s + 1 })) :
    let ino := freshInode s
    let sAfter := { s with
      nodes := (p, .file ino "" s.nowSec 0o644) :: s.nodes
      locks := mockRemoveFirstLock ino mode ((ino, mode) :: s.locks)
      nextInode := ino + 1 }
    (ExceptT.run (mockFsEx.withFileLock p mode true act)).run s = (.error errStr, sAfter) := by
  intro ino sAfter
  dsimp only [mockFsEx, resolveParentTarget]
  rw [exceptT_stateM_bind_run]
  have hGet : (ExceptT.run (get : ExceptT String (StateM TempMockState) TempMockState)).run s = (.ok s, s) := rfl
  rw [hGet]
  dsimp only
  rw [hp, hNone]
  simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, exceptT_stateM_bind_run, exceptT_stateM_pure_run]
  let sLock : TempMockState := { s with
    nodes := (p, .file ino "" s.nowSec 0o644) :: s.nodes
    locks := (ino, mode) :: s.locks
    nextInode := ino + 1 }
  have hSetEx : (ExceptT.run (liftM (set ({
      nodes := (p, MockNode.file (freshInode s) "" s.nowSec 420) :: s.nodes,
      locks := (freshInode s, mode) :: s.locks,
      nextInode := freshInode s + 1, tmpdir := s.tmpdir, nowSec := s.nowSec, nextUuid := s.nextUuid } : TempMockState) :
      StateM TempMockState Unit) : ExceptT String (StateM TempMockState) Unit)).run s = (.ok (), sLock) := by
    rw [exceptT_liftM_stateM_run]; rfl
  rw [hSetEx]
  dsimp only
  let fin : Option (Except FsError (Except TempError Unit)) → ExceptT String (StateM TempMockState) Unit :=
    fun _ => liftM (modify (fun s' : TempMockState => { s' with locks := mockRemoveFirstLock ino mode s'.locks }) :
      StateM TempMockState Unit)
  have hModEx : (ExceptT.run (fin none)).run sLock = (.ok (), sAfter) := by
    dsimp only [fin]; rw [exceptT_liftM_stateM_run]; rfl
  rw [exceptT_tryFinally'_error_run act fin sLock sLock sAfter errStr () hActThrow hModEx]

private theorem spec10_part1_exec (s₀ : TempMockState) (root dirPrefix : String)
    (hvr : (!root.isEmpty && !(Char.ofNat 0 ∈ root.toList)) = true)
    (hvp : (!dirPrefix.isEmpty && dirPrefix.toList.head? != some '.' && !('/' ∈ dirPrefix.toList) && !(Char.ofNat 0 ∈ dirPrefix.toList)) = true)
    (stRoot : FileStat) (hRoot : mockStatPure s₀ root = .ok stRoot)
    (hRwx : stRoot.kind = .dir ∧ (stRoot.mode / 256) % 2 = 1 ∧ (stRoot.mode / 128) % 2 = 1 ∧ (stRoot.mode / 64) % 2 = 1)
    (hNone : (mockLstatPure { s₀ with nextUuid := s₀.nextUuid + 1 }
      (mockJoin root (dirPrefix ++ mockUuidToString (mockUuidOfNat s₀.nextUuid)))).isOk = false) :
    let u := mockUuidOfNat s₀.nextUuid
    let dir := mockJoin root (dirPrefix ++ mockUuidToString u)
    let apiEx := Internal.mkApiM mockFsEx mockTimeEx mockUuidEx mockEnvEx
    ∃ s1 : TempMockState,
      (ExceptT.run (apiEx.withTempDir (some root) dirPrefix fun _ =>
        (throw "boom" : ExceptT String (StateM TempMockState) (Except TempError Unit)))).run s₀ =
        (.error "boom", s1) ∧
      ((mockFs.lstat dir).run s1).1.isOk = false := by
  intro u dir apiEx
  have hrNe : root ≠ "" := validRoot_ne_empty root hvr
  have ⟨hcNe, hcNoSlash⟩ := childName_parts dirPrefix u hvp
  have hDirNorm : normKey dir = dir := normKey_mockJoin root _ hcNe hcNoSlash
  have hCreate := createTempDir_ex_mock_steps s₀ root dirPrefix hvr hvp stRoot hRoot hRwx hNone
  dsimp only at hCreate
  obtain ⟨sMk, hsMk⟩ : ∃ s : TempMockState, s =
      { s₀ with
        nextUuid := s₀.nextUuid + 1
        nodes := (dir, .dir s₀.nowSec 0o700) :: s₀.nodes.filter (fun e => !underDir dir e.1) } := ⟨_, rfl⟩
  rw [← hsMk] at hCreate
  have hLookDirMk : lookupNode sMk.nodes dir = some (.dir s₀.nowSec 0o700) := by
    rw [hsMk]; exact lookupNode_cons_eq _ _ _ _ rfl
  obtain ⟨s1Fin, hs1Fin⟩ : ∃ s : TempMockState, s =
      { sMk with nodes := sMk.nodes.filter (fun e => !underDir dir e.1) } := ⟨_, rfl⟩
  have hClean1 : (ExceptT.run (Internal.cleanupDirIgnoringNotFound mockFsEx dir)).run sMk = (.ok (.ok ()), s1Fin) := by
    rw [hs1Fin]; exact cleanupDir_ex_mock_run sMk dir hDirNorm ⟨_, _, hLookDirMk⟩
  have hRun1 : (ExceptT.run (apiEx.withTempDir (some root) dirPrefix fun _ =>
      (throw "boom" : ExceptT String (StateM TempMockState) (Except TempError Unit)))).run s₀ =
      (.error "boom", s1Fin) := by
    rw [mkApiM_withTempDir_eq]
    dsimp only [Internal.withTempDirM]
    rw [exceptT_stateM_bind_run, hCreate]
    dsimp only
    rw [exceptT_stateM_bind_run]
    rw [exceptT_tryFinally'_error_run (throw "boom" : ExceptT String (StateM TempMockState) (Except TempError Unit))
      (fun _ => Internal.cleanupDirIgnoringNotFound mockFsEx dir) sMk sMk s1Fin "boom" (.ok ())
      (exceptT_stateM_throw_run "boom" sMk) hClean1]
  have hLookDir1 : lookupNode s1Fin.nodes dir = none := by
    rw [hs1Fin]; exact lookupNode_filter_none_of_underDir _ dir dir (underDir_refl dir hDirNorm)
  exact ⟨s1Fin, hRun1, mockFs_lstat_isOk_false_of_lookup_none s1Fin dir hLookDir1⟩

private theorem withLockedTempDir_ex_throw_step {E S α : Type}
    (fs : FsApiM (ExceptT E (StateM S))) (time : TimeOpsM (ExceptT E (StateM S)))
    (uuid : UuidApiM (ExceptT E (StateM S))) (env : EnvVarsApiM (ExceptT E (StateM S)))
    (s₀ sMk sAfterLock sFin : S) (root? : Option String) (dirPrefix dir : String)
    (action : String → ExceptT E (StateM S) (Except TempError α))
    (err : E) (rc : Except TempError Unit)
    (hCre : (ExceptT.run (Internal.createTempDir fs uuid env root? dirPrefix)).run s₀ = (.ok (.ok dir), sMk))
    (hWfl : (ExceptT.run (fs.withFileLock (fs.join dir ".lock") .shared true
        (do let r ← action dir; return .ok r))).run sMk = (.error err, sAfterLock))
    (hCln : (ExceptT.run (Internal.cleanupDirIgnoringNotFound fs dir)).run sAfterLock = (.ok rc, sFin)) :
    (ExceptT.run ((Internal.mkApiM fs time uuid env).withLockedTempDir root? dirPrefix action)).run s₀ =
      (.error err, sFin) := by
  rw [mkApiM_withLockedTempDir_eq]
  dsimp only [Internal.withLockedTempDirM]
  rw [exceptT_stateM_bind_run, hCre]
  dsimp only
  rw [exceptT_stateM_bind_run]
  rw [exceptT_tryFinally'_error_run
    (fs.withFileLock (fs.join dir ".lock") .shared true (do let r ← action dir; return .ok r))
    (fun _ => Internal.cleanupDirIgnoringNotFound fs dir)
    sMk sAfterLock sFin err rc hWfl hCln]

private theorem spec10_part2_run (s₀ : TempMockState) (root dirPrefix : String)
    (sMk sAfterLock s2Fin : TempMockState)
    (hvr : (!root.isEmpty && !(Char.ofNat 0 ∈ root.toList)) = true)
    (hvp : (!dirPrefix.isEmpty && dirPrefix.toList.head? != some '.' && !('/' ∈ dirPrefix.toList) && !(Char.ofNat 0 ∈ dirPrefix.toList)) = true)
    (stRoot : FileStat) (hRoot : mockStatPure s₀ root = .ok stRoot)
    (hRwx : stRoot.kind = .dir ∧ (stRoot.mode / 256) % 2 = 1 ∧ (stRoot.mode / 128) % 2 = 1 ∧ (stRoot.mode / 64) % 2 = 1)
    (hNone : (mockLstatPure { s₀ with nextUuid := s₀.nextUuid + 1 }
      (mockJoin root (dirPrefix ++ mockUuidToString (mockUuidOfNat s₀.nextUuid)))).isOk = false)
    (hsMk : sMk =
      { s₀ with
        nextUuid := s₀.nextUuid + 1
        nodes := (mockJoin root (dirPrefix ++ mockUuidToString (mockUuidOfNat s₀.nextUuid)), .dir s₀.nowSec 0o700) ::
          s₀.nodes.filter (fun e => !underDir (mockJoin root (dirPrefix ++ mockUuidToString (mockUuidOfNat s₀.nextUuid))) e.1) })
    (hsAfterLock : sAfterLock =
      { sMk with
        nodes := (mockJoin (mockJoin root (dirPrefix ++ mockUuidToString (mockUuidOfNat s₀.nextUuid))) ".lock",
          .file (freshInode sMk) "" sMk.nowSec 0o644) :: sMk.nodes
        locks := sMk.locks
        nextInode := freshInode sMk + 1 })
    (hs2Fin : s2Fin =
      { sAfterLock with nodes := sAfterLock.nodes.filter (fun e =>
        !underDir (mockJoin root (dirPrefix ++ mockUuidToString (mockUuidOfNat s₀.nextUuid))) e.1) }) :
    let apiEx := Internal.mkApiM mockFsEx mockTimeEx mockUuidEx mockEnvEx
    (ExceptT.run (apiEx.withLockedTempDir (some root) dirPrefix fun _ =>
      (throw "boom" : ExceptT String (StateM TempMockState) (Except TempError Unit)))).run s₀ =
      (.error "boom", s2Fin) := by
  intro _
  let u := mockUuidOfNat s₀.nextUuid
  let dir := mockJoin root (dirPrefix ++ mockUuidToString u)
  let lockPath := mockJoin dir ".lock"
  have hrNe : root ≠ "" := validRoot_ne_empty root hvr
  have ⟨hcNe, hcNoSlash⟩ := childName_parts dirPrefix u hvp
  have hDirNorm : normKey dir = dir := normKey_mockJoin root _ hcNe hcNoSlash
  have hDirNe : dir ≠ "" := mockJoin_ne_empty root _ hcNe
  have hDirNeSlash : dir ≠ "/" := mockJoin_ne_slash root _ hrNe hcNe
  have hLockNorm : normKey lockPath = lockPath := normKey_mockJoin dir ".lock" (by decide) (by decide)
  have hLockNeDir : normKey lockPath ≠ dir :=
    payload_ne_dir root (dirPrefix ++ mockUuidToString u) ".lock" hrNe hcNe hcNoSlash (by decide) (by decide)
  have hUnderLock : underDir dir lockPath = true :=
    underDir_mockJoin_self dir ".lock" hDirNe hDirNorm hDirNeSlash (by decide) (by decide)
  have hCreate := createTempDir_ex_mock_steps s₀ root dirPrefix hvr hvp stRoot hRoot hRwx hNone
  dsimp only at hCreate
  rw [← hsMk] at hCreate
  have hLookDirMk : lookupNode sMk.nodes dir = some (.dir s₀.nowSec 0o700) := by
    rw [hsMk]; exact lookupNode_cons_eq _ _ _ _ rfl
  have hLookLockMk : lookupNode sMk.nodes lockPath = none := by
    rw [hsMk]
    unfold lookupNode
    dsimp only
    have hb : (normKey dir == normKey lockPath) = false := by
      rw [hDirNorm, beq_false_of_ne (ne_comm.mp hLockNeDir)]
    rw [List.find?_cons, hb]
    exact lookupNode_filter_none_of_underDir s₀.nodes dir lockPath hUnderLock
  have hLookDirAfterLock : lookupNode sAfterLock.nodes dir = some (.dir s₀.nowSec 0o700) := by
    rw [hsAfterLock]
    unfold lookupNode
    dsimp only
    have hb : (normKey lockPath == normKey dir) = false := by
      rw [hDirNorm, beq_false_of_ne hLockNeDir]
    rw [List.find?_cons, hb]
    exact hLookDirMk
  have hClean2 : (ExceptT.run (Internal.cleanupDirIgnoringNotFound mockFsEx dir)).run sAfterLock =
      (.ok (.ok ()), s2Fin) := by
    rw [hs2Fin]; exact cleanupDir_ex_mock_run sAfterLock dir hDirNorm ⟨_, _, hLookDirAfterLock⟩
  have hInnerThrow : (ExceptT.run (do
      let r ← (throw "boom" : ExceptT String (StateM TempMockState) (Except TempError Unit))
      return .ok r : ExceptT String (StateM TempMockState) (Except FsError (Except TempError Unit)))).run
      { sMk with
        nodes := (lockPath, .file (freshInode sMk) "" sMk.nowSec 0o644) :: sMk.nodes
        locks := (freshInode sMk, .shared) :: sMk.locks
        nextInode := freshInode sMk + 1 } =
      (.error "boom", { sMk with
        nodes := (lockPath, .file (freshInode sMk) "" sMk.nowSec 0o644) :: sMk.nodes
        locks := (freshInode sMk, .shared) :: sMk.locks
        nextInode := freshInode sMk + 1 }) := by
    rw [exceptT_stateM_bind_run, exceptT_stateM_throw_run]
  have hWflThrow := mockFsEx_withFileLock_create_throw_run sMk lockPath .shared hLockNorm hLookLockMk _ "boom" hInnerThrow
  dsimp only at hWflThrow
  rw [mockRemoveFirstLock_head, ← hsAfterLock] at hWflThrow
  have hJoinEx : mockFsEx.join = mockJoin := rfl
  have hWflLock : (ExceptT.run (mockFsEx.withFileLock (mockFsEx.join dir ".lock") .shared true
      (do let r ← (fun _ => (throw "boom" : ExceptT String (StateM TempMockState) (Except TempError Unit))) dir; return .ok r))).run sMk =
      (.error "boom", sAfterLock) := by
    rw [hJoinEx]
    exact hWflThrow
  exact withLockedTempDir_ex_throw_step mockFsEx mockTimeEx mockUuidEx mockEnvEx
    s₀ sMk sAfterLock s2Fin (some root) dirPrefix dir
    (fun _ => (throw "boom" : ExceptT String (StateM TempMockState) (Except TempError Unit)))
    "boom" (.ok ()) hCreate hWflLock hClean2

private theorem spec10_part2_probe_exec (s₀ sMk sAfterLock s2Fin : TempMockState) (root dirPrefix : String)
    (hvr : (!root.isEmpty && !(Char.ofNat 0 ∈ root.toList)) = true)
    (hvp : (!dirPrefix.isEmpty && dirPrefix.toList.head? != some '.' && !('/' ∈ dirPrefix.toList) && !(Char.ofNat 0 ∈ dirPrefix.toList)) = true)
    (stRoot : FileStat) (hRoot : mockStatPure s₀ root = .ok stRoot)
    (hRwx : stRoot.kind = .dir ∧ (stRoot.mode / 256) % 2 = 1 ∧ (stRoot.mode / 128) % 2 = 1 ∧ (stRoot.mode / 64) % 2 = 1)
    (hsMk : sMk =
      { s₀ with
        nextUuid := s₀.nextUuid + 1
        nodes := (mockJoin root (dirPrefix ++ mockUuidToString (mockUuidOfNat s₀.nextUuid)), .dir s₀.nowSec 0o700) ::
          s₀.nodes.filter (fun e => !underDir (mockJoin root (dirPrefix ++ mockUuidToString (mockUuidOfNat s₀.nextUuid))) e.1) })
    (hsAfterLock : sAfterLock =
      { sMk with
        nodes := (mockJoin (mockJoin root (dirPrefix ++ mockUuidToString (mockUuidOfNat s₀.nextUuid))) ".lock",
          .file (freshInode sMk) "" sMk.nowSec 0o644) :: sMk.nodes
        locks := sMk.locks
        nextInode := freshInode sMk + 1 })
    (hs2Fin : s2Fin =
      { sAfterLock with nodes := sAfterLock.nodes.filter (fun e =>
        !underDir (mockJoin root (dirPrefix ++ mockUuidToString (mockUuidOfNat s₀.nextUuid))) e.1) }) :
    let u := mockUuidOfNat s₀.nextUuid
    let dir := mockJoin root (dirPrefix ++ mockUuidToString u)
    ((mockFs.lstat dir).run s2Fin).1.isOk = false ∧
    ((do let _ ← mockFs.mkdir dir false false; mockFs.tryWithFileLock (mockJoin dir ".lock") .exclusive true (pure (.ok ()))).run s2Fin).1 =
      .ok (some ()) := by
  intro u dir
  have hrNe : root ≠ "" := validRoot_ne_empty root hvr
  have ⟨hcNe, hcNoSlash⟩ := childName_parts dirPrefix u hvp
  have hDirNorm : normKey dir = dir := normKey_mockJoin root _ hcNe hcNoSlash
  have hDirNe : dir ≠ "" := mockJoin_ne_empty root _ hcNe
  have hDirNeSlash : dir ≠ "/" := mockJoin_ne_slash root _ hrNe hcNe
  let lockPath := mockJoin dir ".lock"
  have hLockNeDir : normKey lockPath ≠ dir :=
    payload_ne_dir root (dirPrefix ++ mockUuidToString u) ".lock" hrNe hcNe hcNoSlash (by decide) (by decide)
  have hUnderLock : underDir dir lockPath = true :=
    underDir_mockJoin_self dir ".lock" hDirNe hDirNorm hDirNeSlash (by decide) (by decide)
  have hRootUnderDirFalse : underDir dir (normKey root) = false := by
    simpa [underDir, normKey_idem] using
      underDir_mockJoin_root_false root (dirPrefix ++ mockUuidToString u) hrNe hcNe hcNoSlash
  have hLookRoot : ∃ rootNode, lookupNode s₀.nodes (normKey root) = some rootNode ∧ mockNodeStat rootNode = stRoot := by
    unfold mockStatPure mockLstatPure at hRoot
    cases hl : lookupNode s₀.nodes root with
    | none => simp [hl] at hRoot
    | some rn =>
      simp only [hl, Except.ok.injEq] at hRoot
      exact ⟨rn, by simpa [lookupNode, normKey_idem] using hl, hRoot⟩
  rcases hLookRoot with ⟨rootNode, hLookRootNorm, hStRoot⟩
  have hLookDir2 : lookupNode s2Fin.nodes dir = none := by
    rw [hs2Fin]; exact lookupNode_filter_none_of_underDir sAfterLock.nodes dir dir (underDir_refl dir hDirNorm)
  have hLookRoot2 : lookupNode s2Fin.nodes (normKey root) = some rootNode := by
    have hb1 : (normKey lockPath == normKey (normKey root)) = false := by
      rw [beq_false_of_ne]
      intro hEq
      have h1 : underDir dir lockPath = underDir dir (normKey root) := by unfold underDir; rw [hEq]
      rw [hUnderLock, hRootUnderDirFalse] at h1
      exact Bool.noConfusion h1
    have hb2 : (normKey dir == normKey (normKey root)) = false := by
      rw [beq_false_of_ne]
      intro hEq
      have h1 : underDir dir dir = underDir dir (normKey root) := by unfold underDir; rw [hEq]
      rw [underDir_refl dir hDirNorm, hRootUnderDirFalse] at h1
      exact Bool.noConfusion h1
    rw [hs2Fin, lookupNode_filter_not_underDir_eq sAfterLock.nodes dir (normKey root) hRootUnderDirFalse]
    have hAL : sAfterLock.nodes =
        (lockPath, .file (freshInode sMk) "" sMk.nowSec 0o644) ::
        (dir, .dir s₀.nowSec 0o700) ::
        s₀.nodes.filter (fun e => !underDir dir e.1) := by
      rw [hsAfterLock, hsMk]
    rw [hAL]
    exact (lookupNode_after_cleanup_root s₀.nodes dir lockPath root _ _ hRootUnderDirFalse hb1 hb2).trans hLookRootNorm
  have hProbeS2 := probe_exclusive_lock_after_cleanup_run s2Fin root (dirPrefix ++ mockUuidToString u)
    hrNe hcNe hcNoSlash rootNode stRoot hLookRoot2 hStRoot hRwx hLookDir2
  refine ⟨mockFs_lstat_isOk_false_of_lookup_none s2Fin dir hLookDir2, ?_⟩
  dsimp only [dir]
  exact hProbeS2

private theorem spec10_part2_exec (s₀ : TempMockState) (root dirPrefix : String)
    (hvr : (!root.isEmpty && !(Char.ofNat 0 ∈ root.toList)) = true)
    (hvp : (!dirPrefix.isEmpty && dirPrefix.toList.head? != some '.' && !('/' ∈ dirPrefix.toList) && !(Char.ofNat 0 ∈ dirPrefix.toList)) = true)
    (stRoot : FileStat) (hRoot : mockStatPure s₀ root = .ok stRoot)
    (hRwx : stRoot.kind = .dir ∧ (stRoot.mode / 256) % 2 = 1 ∧ (stRoot.mode / 128) % 2 = 1 ∧ (stRoot.mode / 64) % 2 = 1)
    (hNone : (mockLstatPure { s₀ with nextUuid := s₀.nextUuid + 1 }
      (mockJoin root (dirPrefix ++ mockUuidToString (mockUuidOfNat s₀.nextUuid)))).isOk = false) :
    let u := mockUuidOfNat s₀.nextUuid
    let dir := mockJoin root (dirPrefix ++ mockUuidToString u)
    let apiEx := Internal.mkApiM mockFsEx mockTimeEx mockUuidEx mockEnvEx
    ∃ s2 : TempMockState,
      (ExceptT.run (apiEx.withLockedTempDir (some root) dirPrefix fun _ =>
        (throw "boom" : ExceptT String (StateM TempMockState) (Except TempError Unit)))).run s₀ =
        (.error "boom", s2) ∧
      ((mockFs.lstat dir).run s2).1.isOk = false ∧
      ((do let _ ← mockFs.mkdir dir false false; mockFs.tryWithFileLock (mockJoin dir ".lock") .exclusive true (pure (.ok ()))).run s2).1 =
        .ok (some ()) := by
  intro u dir _
  obtain ⟨sMk, hsMk⟩ : ∃ s : TempMockState, s =
      { s₀ with
        nextUuid := s₀.nextUuid + 1
        nodes := (dir, .dir s₀.nowSec 0o700) :: s₀.nodes.filter (fun e => !underDir dir e.1) } := ⟨_, rfl⟩
  obtain ⟨sAfterLock, hsAfterLock⟩ : ∃ s : TempMockState, s =
      { sMk with
        nodes := (mockJoin dir ".lock", .file (freshInode sMk) "" sMk.nowSec 0o644) :: sMk.nodes
        locks := sMk.locks
        nextInode := freshInode sMk + 1 } := ⟨_, rfl⟩
  obtain ⟨s2Fin, hs2Fin⟩ : ∃ s : TempMockState, s =
      { sAfterLock with nodes := sAfterLock.nodes.filter (fun e => !underDir dir e.1) } := ⟨_, rfl⟩
  have hRun2 := spec10_part2_run s₀ root dirPrefix sMk sAfterLock s2Fin hvr hvp stRoot hRoot hRwx hNone
    hsMk hsAfterLock hs2Fin
  have ⟨hLstat2, hProbe2⟩ := spec10_part2_probe_exec s₀ sMk sAfterLock s2Fin root dirPrefix hvr hvp stRoot hRoot hRwx
    hsMk hsAfterLock hs2Fin
  dsimp only [u, dir] at hLstat2 hProbe2 ⊢
  dsimp only [Internal.mkApiM] at hRun2 ⊢
  exact ⟨s2Fin, hRun2, hLstat2, hProbe2⟩

/-- Spec 10: Over `ExceptT String (StateM TempMockState)`, throwing inside `withTempDir` or `withLockedTempDir` cleans up and releases the lock while propagating the exception. -/
theorem proof_temp_tryFinally_exceptionCleansUpAndReleasesLock :
    AllPass (test_temp_tryFinally_exceptionCleansUpAndReleasesLock
      (S := TempMockState) Internal.mkApiM mockFsEx mockTimeEx mockUuidEx mockEnvEx mockFs mockUuid) := by
  dsimp only [test_temp_tryFinally_exceptionCleansUpAndReleasesLock, AllPass]
  intro s₀ root dirPrefix ⟨hvr, hvp⟩ ⟨stRoot, hRoot, hRwx⟩
  have hRootPure : mockStatPure s₀ root = .ok stRoot := by
    rw [mockFs_stat_run] at hRoot; exact hRoot
  rw [mockUuid_getUuid_run s₀]
  dsimp only
  rw [allPass_assume]
  intro hNone
  have hNonePure : (mockLstatPure { s₀ with nextUuid := s₀.nextUuid + 1 }
      (mockJoin root (dirPrefix ++ mockUuidToString (mockUuidOfNat s₀.nextUuid)))).isOk = false := by
    rw [mockFs_lstat_run, mockFs_join_eq, mockUuid_toString_eq] at hNone; exact hNone
  obtain ⟨s1, hRun1, h1⟩ := spec10_part1_exec s₀ root dirPrefix hvr hvp stRoot hRootPure hRwx hNonePure
  obtain ⟨s2, hRun2, h2, h3⟩ := spec10_part2_exec s₀ root dirPrefix hvr hvp stRoot hRootPure hRwx hNonePure
  rw [mockFs_join_eq, mockUuid_toString_eq]
  rw [hRun1, hRun2]
  dsimp only
  rw [allPass_assert, allPass_assert, allPass_assert, allPass_assert, allPass_assert_end]
  exact ⟨rfl, h1, rfl, h2, h3, trivial⟩

/-- Non-vacuity `CanReach` witness for Spec 10 (`test_temp_tryFinally_exceptionCleansUpAndReleasesLock`). -/
theorem reach_temp_tryFinally_exceptionCleansUpAndReleasesLock :
    CanReach (test_temp_tryFinally_exceptionCleansUpAndReleasesLock
      (S := TempMockState) Internal.mkApiM mockFsEx mockTimeEx mockUuidEx mockEnvEx mockFs mockUuid) := by
  dsimp only [test_temp_tryFinally_exceptionCleansUpAndReleasesLock, CanReach]
  obtain ⟨s₀, hs₀⟩ : ∃ s : TempMockState, s = {} := ⟨{}, rfl⟩
  rw [canReach_nondet]; refine ⟨s₀, ?_⟩
  rw [canReach_nondet]; refine ⟨"/tmp", ?_⟩
  rw [canReach_nondet]; refine ⟨"tmp-", ?_⟩
  rw [canReach_assume]; refine ⟨⟨rfl, rfl⟩, ?_⟩
  have hRootPure : mockStatPure s₀ "/tmp" = .ok (mockNodeStat (.dir 0 0o755)) := by
    rw [hs₀]; rfl
  have hRoot : ∃ stRoot, ((mockFs.stat "/tmp").run s₀).1 = .ok stRoot ∧
      stRoot.kind = .dir ∧ (stRoot.mode / 256) % 2 = 1 ∧ (stRoot.mode / 128) % 2 = 1 ∧ (stRoot.mode / 64) % 2 = 1 :=
    ⟨mockNodeStat (.dir 0 0o755), by rw [mockFs_stat_run]; exact hRootPure, rfl, rfl, rfl, rfl⟩
  rw [canReach_assume]; refine ⟨hRoot, ?_⟩
  rw [mockUuid_getUuid_run s₀]
  dsimp only
  have hNonePure : (mockLstatPure { s₀ with nextUuid := s₀.nextUuid + 1 }
      (mockJoin "/tmp" ("tmp-" ++ mockUuidToString (mockUuidOfNat s₀.nextUuid)))).isOk = false := by
    rw [hs₀]
    unfold mockLstatPure
    dsimp only
    have ⟨hcNe, hcNoSlash⟩ := childName_parts "tmp-" (mockUuidOfNat 1) rfl
    have hNe : normKey "/tmp" ≠ normKey (mockJoin "/tmp" ("tmp-" ++ mockUuidToString (mockUuidOfNat 1))) :=
      ne_comm.mp (mockJoin_ne_root "/tmp" _ (by decide) hcNe hcNoSlash)
    rw [lookupNode_cons_ne "/tmp" (.dir 0 0o755) [] _ hNe]
    rfl
  have hNone : (mockFs.lstat (mockFs.join "/tmp" ("tmp-" ++ mockUuid.toString (mockUuidOfNat s₀.nextUuid)))).run
      { s₀ with nextUuid := s₀.nextUuid + 1 } |>.1.isOk = false := by
    rw [mockFs_lstat_run, mockFs_join_eq, mockUuid_toString_eq]; exact hNonePure
  rw [canReach_assume]; refine ⟨hNone, ?_⟩
  obtain ⟨s1, hRun1, h1⟩ :=
    spec10_part1_exec s₀ "/tmp" "tmp-" rfl rfl (mockNodeStat (.dir 0 0o755)) hRootPure ⟨rfl, rfl, rfl, rfl⟩ hNonePure
  obtain ⟨s2, hRun2, h2, h3⟩ :=
    spec10_part2_exec s₀ "/tmp" "tmp-" rfl rfl (mockNodeStat (.dir 0 0o755)) hRootPure ⟨rfl, rfl, rfl, rfl⟩ hNonePure
  rw [mockFs_join_eq, mockUuid_toString_eq]
  rw [hRun1, hRun2]
  dsimp only
  rw [canReach_assert, canReach_assert, canReach_assert, canReach_assert, canReach_assert_end]
  exact ⟨rfl, h1, rfl, h2, h3, trivial⟩

private def pValidPrefix (p : String) : Bool :=
  !p.isEmpty && p.toList.head? != some '.' && !('/' ∈ p.toList) && !(Char.ofNat 0 ∈ p.toList)

private def pValidRoot (r : String) : Bool :=
  !r.isEmpty && !(Char.ofNat 0 ∈ r.toList)

private def pValidEntryName (n : String) : Bool :=
  !n.isEmpty && n != "." && n != ".." && !('/' ∈ n.toList) && !(Char.ofNat 0 ∈ n.toList)

private def pHasRwx (st : FileStat) : Prop :=
  st.kind = .dir ∧ (st.mode / 256) % 2 = 1 ∧ (st.mode / 128) % 2 = 1 ∧ (st.mode / 64) % 2 = 1

private def pHasPath (xs : Array String) (p : String) : Bool :=
  xs.toList.contains p

private def pIsSorted (xs : Array String) : Bool :=
  xs.toList.Pairwise (· ≤ ·)

private theorem validEntryName_parts (n : String) (h : pValidEntryName n = true) :
    n ≠ "" ∧ n ≠ "." ∧ n ≠ ".." ∧ ¬('/' ∈ n.toList) := by
  have h1 := h
  unfold pValidEntryName at h1
  simp only [Bool.and_eq_true, Bool.not_eq_true', bne_iff_ne, ne_eq] at h1
  rcases h1 with ⟨⟨⟨⟨hnEmpty, hDot⟩, hDotDot⟩, hSlash⟩, _⟩
  exact ⟨fun he => by rw [he] at hnEmpty; simp [String.isEmpty] at hnEmpty, hDot, hDotDot, by simpa using hSlash⟩

private theorem nodup_eraseDupStringsAux (seen xs : List String) (hs : seen.Nodup) :
    (∀ y ∈ seen, y ∉ eraseDupStringsAux seen xs) ∧ (eraseDupStringsAux seen xs).Nodup := by
  induction xs generalizing seen with
  | nil => exact ⟨fun _ _ h => (nomatch h), List.nodup_nil⟩
  | cons x xs ih =>
    simp only [eraseDupStringsAux]
    split
    · exact ih seen hs
    · next hnx =>
      have hs' : (x :: seen).Nodup := List.nodup_cons.mpr ⟨hnx, hs⟩
      have ⟨hMem, hNd⟩ := ih (x :: seen) hs'
      refine ⟨?_, List.nodup_cons.mpr ⟨hMem x List.mem_cons_self, hNd⟩⟩
      intro y hy hyOut
      simp only [List.mem_cons] at hyOut
      rcases hyOut with rfl | hyTail
      · exact hnx hy
      · exact hMem y (List.mem_cons_of_mem x hy) hyTail

private theorem nodup_eraseDupStrings (xs : List String) : (eraseDupStrings xs).Nodup :=
  (nodup_eraseDupStringsAux [] xs List.nodup_nil).2

private theorem nodup_insertSorted (x : String) (xs : List String)
    (hNd : xs.Nodup) (hx : x ∉ xs) : (Internal.insertSorted x xs).Nodup := by
  induction xs with
  | nil => exact List.nodup_cons.mpr ⟨by simp, List.nodup_nil⟩
  | cons y ys ih =>
    simp only [Internal.insertSorted]
    split
    · exact List.nodup_cons.mpr ⟨hx, hNd⟩
    · have ⟨hyYs, hYsNd⟩ := List.nodup_cons.mp hNd
      have hxYs : x ∉ ys := fun h => hx (List.mem_cons_of_mem y h)
      have hxy : y ≠ x := fun h => hx (h ▸ List.mem_cons_self)
      refine List.nodup_cons.mpr ⟨?_, ih hYsNd hxYs⟩
      intro hyIn
      rw [mem_insertSorted] at hyIn
      rcases hyIn with rfl | hyInYs
      · exact hxy rfl
      · exact hyYs hyInYs

private theorem nodup_sortStrings (xs : List String) (hNd : xs.Nodup) :
    (Internal.sortStrings xs).Nodup := by
  induction xs with
  | nil => exact List.nodup_nil
  | cons x xs ih =>
    have ⟨hx, hXs⟩ := List.nodup_cons.mp hNd
    exact nodup_insertSorted x (Internal.sortStrings xs) (ih hXs) (by rwa [mem_sortStrings])

private theorem list_nodup_split {α : Type} (xs : List α) (x : α) (hNd : xs.Nodup) (hx : x ∈ xs) :
    ∃ a b, xs = a ++ x :: b ∧ x ∉ a ∧ x ∉ b := by
  induction xs with
  | nil => cases hx
  | cons y ys ih =>
    have ⟨hy, hYs⟩ := List.nodup_cons.mp hNd
    simp only [List.mem_cons] at hx
    rcases hx with rfl | hxYs
    · exact ⟨[], ys, rfl, fun h => (nomatch h), hy⟩
    · obtain ⟨a, b, hEq, hna, hnb⟩ := ih hYs hxYs
      have hxy : x ≠ y := fun h => hy (h ▸ hxYs)
      exact ⟨y :: a, b, by simp [hEq], fun h => by
        simp only [List.mem_cons] at h
        rcases h with rfl | ha
        · exact hxy rfl
        · exact hna ha, hnb⟩

private theorem list_filter_filterMap_eq {α β : Type} (xs : List α) (keep : α → Bool) (f : α → Option β)
    (h : ∀ x, (f x).isSome = true → keep x = true) :
    (xs.filter keep).filterMap f = xs.filterMap f := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    cases hx : f x with
    | none =>
      by_cases hk : keep x = true <;> simp [hk, hx, ih]
    | some v =>
      have hk : keep x = true := h x (by simp [hx])
      simp [hk, hx, ih]

private theorem hasPath_toArray_mem (xs : List String) (p : String) :
    pHasPath xs.toArray p = true ↔ p ∈ xs := by
  simp [pHasPath]

private theorem isSorted_sortStrings (xs : List String) :
    pIsSorted (Internal.sortStrings xs).toArray = true := by
  simpa [pIsSorted] using pairwise_sortStrings xs

private theorem mockFs_withFileLock_existing_conflict_run (s : TempMockState) (p : String)
    (mode : LockMode) (createIfMissing : Bool)
    (ino : Nat) (c : String) (t : Int) (m : Nat)
    (hnorm : normKey p = p)
    (hnode : lookupNode s.nodes p = some (.file ino c t m))
    (hconf : mockHasConflict s.locks ino mode = true)
    {β : Type} (act : StateM TempMockState (Except FsError β)) :
    (mockFs.withFileLock p mode createIfMissing act).run s =
      (.error { kind := .wouldBlock, path := some p, message := "wouldBlock" }, s) := by
  dsimp only [mockFs, resolveParentTarget]
  rw [stateM_bind_run, stateM_get_run]
  dsimp only
  rw [hnorm, hnode]
  dsimp only
  rw [hconf]
  simp only [↓reduceIte, stateM_pure_run]

private theorem mockFs_withFileLock_existing_ok_run (s : TempMockState) (p : String)
    (mode : LockMode) (createIfMissing : Bool)
    (ino : Nat) (c : String) (t : Int) (m : Nat)
    (hnorm : normKey p = p)
    (hnode : lookupNode s.nodes p = some (.file ino c t m))
    (hconf : mockHasConflict s.locks ino mode = false)
    {β : Type} (act : StateM TempMockState (Except FsError β)) :
    (mockFs.withFileLock p mode createIfMissing act).run s =
      let (r, s1) := act.run { s with locks := (ino, mode) :: s.locks }
      (r, { s1 with locks := mockRemoveFirstLock ino mode s1.locks }) := by
  dsimp only [mockFs, resolveParentTarget]
  rw [stateM_bind_run, stateM_get_run]
  dsimp only
  rw [hnorm, hnode]
  dsimp only
  rw [hconf]
  simp only [Bool.false_eq_true, ↓reduceIte, stateM_bind_run, stateM_set_run]
  generalize act.run { s with locks := (ino, mode) :: s.locks } = res
  rcases res with ⟨r, s1⟩
  rfl

private theorem mockFs_unlink_existing_run (s : TempMockState) (p : String) (miss : Bool)
    (ino : Nat) (c : String) (t : Int) (m : Nat)
    (hnorm : normKey p = p)
    (hnode : lookupNode s.nodes p = some (.file ino c t m)) :
    (mockFs.unlink p miss).run s =
      (.ok (), { s with nodes := s.nodes.filter (fun e => normKey e.1 != p) }) := by
  dsimp only [mockFs, resolveParentTarget]
  rw [stateM_bind_run, stateM_get_run]
  dsimp only
  rw [hnorm, hnode]
  simp only [stateM_bind_run, stateM_set_run, stateM_pure_run]

private theorem mockFs_rmdir_dir_run (s : TempMockState) (p : String) (t : Int) (m : Nat)
    (hnorm : normKey p = p)
    (hnode : lookupNode s.nodes p = some (.dir t m)) :
    (mockFs.rmdir p).run s =
      (.ok (), { s with nodes := s.nodes.filter (fun e => normKey e.1 != p) }) := by
  dsimp only [mockFs, resolveParentTarget]
  rw [stateM_bind_run, stateM_get_run]
  dsimp only
  rw [hnorm, hnode]
  simp only [stateM_bind_run, stateM_set_run, stateM_pure_run]

private theorem mockParentChild_self_join (root name : String) (hr : root ≠ "") (hn : pValidEntryName name = true) :
    mockParentChild (normKey root) (mockJoin root name) = some name := by
  have ⟨hne, hDot, hDotDot, hNoSlash⟩ := validEntryName_parts name hn
  have hjNorm := normKey_mockJoin root name hne hNoSlash
  have hList := mockJoin_eq_append_of_ne_empty root name hr
  unfold mockParentChild
  rw [normKey_idem, hjNorm]
  have hrNormNe : normKey root ≠ "" := normKey_ne_empty root hr
  have hrNormEmpty : (normKey root).isEmpty = false := by
    cases hb : (normKey root).isEmpty with
    | false => rfl
    | true => exact absurd ((string_isEmpty_iff_eq_empty _).mp hb) hrNormNe
  dsimp only
  simp only [hrNormEmpty, Bool.false_eq_true, ↓reduceIte]
  have hPref : (if (normKey root == "/") = true then "/" else normKey root ++ "/").toList =
      if (normKey root == "/") = true then ['/'] else (normKey root).toList ++ ['/'] := by
    by_cases h : (normKey root == "/") = true
    · simp only [h, ↓reduceIte]; rfl
    · simp only [h, Bool.false_eq_true, ↓reduceIte, String.toList_append]; rfl
  have hIsPref : (if (normKey root == "/") = true then "/" else normKey root ++ "/").toList.isPrefixOf
      (mockJoin root name).toList = true := by
    rw [List.isPrefixOf_iff_prefix, hPref, hList]
    exact ⟨name.toList, rfl⟩
  rw [hIsPref]
  have hLen : (if (normKey root == "/") = true then "/" else normKey root ++ "/").length =
      (if (normKey root == "/") = true then ['/'] else (normKey root).toList ++ ['/']).length := by
    rw [← String.length_toList, hPref]
  have hDrop : String.ofList ((mockJoin root name).toList.drop
      (if (normKey root == "/") = true then "/" else normKey root ++ "/").length) = name := by
    rw [hList, hLen, List.drop_left, String.ofList_toList]
  rw [hDrop]
  have hValidEq : pValidEntryName name = (!name.isEmpty && name != "." && name != ".." && !('/' ∈ name.toList) && !(Char.ofNat 0 ∈ name.toList)) := rfl
  rw [← hValidEq, hn]
  rfl

private theorem mockParentChild_eq_of_normKey (dir a b : String) (h : normKey a = normKey b) :
    mockParentChild dir a = mockParentChild dir b := by
  unfold mockParentChild
  rw [h]

private theorem mockFs_listDir_run_of_rwx (s : TempMockState) (dir : String)
    (st : FileStat) (hStat : mockStatPure s dir = .ok st) (hRwx : pHasRwx st) :
    let rp := normKey dir
    let names := Internal.sortStrings (eraseDupStrings (s.nodes.filterMap (fun e => mockParentChild rp e.1)))
    (mockFs.listDir dir).run s = (.ok names.toArray, s) ∧
    names.Nodup ∧
    (∀ nm ∈ names, pValidEntryName nm = true) := by
  intro rp names
  obtain ⟨nd, hLook, hSt⟩ := lookupNode_of_lstat_ok s dir st hStat
  have hLookRp : lookupNode s.nodes rp = some nd := by simpa [lookupNode, rp, normKey_idem] using hLook
  have hRx : hasRx st = true := hasRx_of_hasRwx st hRwx
  have hNotDir : (st.kind != .dir) = false := by
    have hDir : st.kind = .dir := hRwx.1
    rw [hDir]; rfl
  have hRun : (mockFs.listDir dir).run s = (.ok names.toArray, s) := by
    dsimp only [mockFs]
    rw [stateM_bind_run, stateM_get_run]
    dsimp only
    rw [hLookRp]
    dsimp only
    rw [hSt, hNotDir, hRx]
    simp only [Bool.false_eq_true, ↓reduceIte, Bool.not_true]
    rfl
  have hNd : names.Nodup := nodup_sortStrings _ (nodup_eraseDupStrings _)
  have hValid : ∀ nm ∈ names, pValidEntryName nm = true := by
    intro nm hnm
    rw [mem_sortStrings, mem_eraseDupStrings, List.mem_filterMap] at hnm
    rcases hnm with ⟨e, _, he⟩
    exact validEntryName_of_mockParentChild rp e.1 nm he
  exact ⟨hRun, hNd, hValid⟩

private theorem mockFs_listDir_mem_of_lookupNode (s : TempMockState) (dir childName : String)
    (hd : dir ≠ "") (hn : pValidEntryName childName = true)
    (ndChild : MockNode) (hLookChild : lookupNode s.nodes (mockJoin dir childName) = some ndChild) :
    let rp := normKey dir
    let names := Internal.sortStrings (eraseDupStrings (s.nodes.filterMap (fun e => mockParentChild rp e.1)))
    childName ∈ names := by
  intro rp names
  have ⟨hcNe, _, _, hcNoSlash⟩ := validEntryName_parts childName hn
  have hJoinNorm : normKey (mockJoin dir childName) = mockJoin dir childName := normKey_mockJoin dir childName hcNe hcNoSlash
  unfold lookupNode at hLookChild
  dsimp only at hLookChild
  cases hf : s.nodes.find? (fun e => normKey e.1 == normKey (mockJoin dir childName)) with
  | none => simp [hf] at hLookChild
  | some p =>
    have hpMem : p ∈ s.nodes := List.mem_of_find?_eq_some hf
    have hpEq : normKey p.1 = mockJoin dir childName := by
      have hb := List.find?_some hf
      rw [hJoinNorm, beq_iff_eq] at hb
      exact hb
    have hPc : mockParentChild rp p.1 = some childName := by
      rw [mockParentChild_eq_of_normKey rp p.1 (mockJoin dir childName) (by rw [hpEq, hJoinNorm])]
      exact mockParentChild_self_join dir childName hd hn
    rw [mem_sortStrings, mem_eraseDupStrings, List.mem_filterMap]
    exact ⟨p, hpMem, hPc⟩

private def NodesFilteredPres (P : String → Prop) (s s' : TempMockState) : Prop :=
  (∃ keep : String → Bool,
    (∀ k, P k → keep k = true) ∧
    s'.nodes = s.nodes.filter (fun e => keep e.1)) ∧
  s'.locks = s.locks ∧ s'.nextInode = s.nextInode ∧
  s'.tmpdir = s.tmpdir ∧ s'.nowSec = s.nowSec ∧ s'.nextUuid = s.nextUuid

private theorem nodesFilteredPres_refl (P : String → Prop) (s : TempMockState) :
    NodesFilteredPres P s s := by
  refine ⟨⟨fun _ => true, fun _ _ => rfl, ?_⟩, rfl, rfl, rfl, rfl, rfl⟩
  induction s.nodes with
  | nil => rfl
  | cons x xs ih => exact congrArg (List.cons x) ih

private theorem nodesFilteredPres_trans {P : String → Prop} {s s1 s2 : TempMockState}
    (h1 : NodesFilteredPres P s s1) (h2 : NodesFilteredPres P s1 s2) :
    NodesFilteredPres P s s2 := by
  rcases h1 with ⟨⟨k1, hk1, hn1⟩, hl1, hi1, ht1, hs1, hu1⟩
  rcases h2 with ⟨⟨k2, hk2, hn2⟩, hl2, hi2, ht2, hs2, hu2⟩
  refine ⟨⟨fun p => k1 p && k2 p, fun p hp => by simp [hk1 p hp, hk2 p hp], ?_⟩,
    hl2.trans hl1, hi2.trans hi1, ht2.trans ht1, hs2.trans hs1, hu2.trans hu1⟩
  rw [hn2, hn1, List.filter_filter]
  congr 1
  funext e
  exact Bool.and_comm (k2 e.1) (k1 e.1)

private theorem nodesFilteredPres_mono {P Q : String → Prop} {s s' : TempMockState}
    (hPQ : ∀ k, Q k → P k) (h : NodesFilteredPres P s s') :
    NodesFilteredPres Q s s' := by
  rcases h with ⟨⟨keep, hk, hn⟩, hl, hi, ht, hs, hu⟩
  exact ⟨⟨keep, fun k hq => hk k (hPQ k hq), hn⟩, hl, hi, ht, hs, hu⟩

private theorem nodesFilteredPres_lookupNode {P : String → Prop} {s s' : TempMockState}
    (hPres : NodesFilteredPres P s s') (p : String)
    (hp : ∀ k, normKey k = normKey p → P k) :
    lookupNode s'.nodes p = lookupNode s.nodes p := by
  rcases hPres with ⟨⟨keep, hk, hn⟩, _⟩
  unfold lookupNode
  dsimp only
  rw [hn]
  congr 1
  induction s.nodes with
  | nil => rfl
  | cons x xs ih =>
    by_cases hxp : (normKey x.1 == normKey p) = true
    · have hkx : keep x.1 = true := hk x.1 (hp x.1 (beq_iff_eq.mp hxp))
      rw [List.filter_cons]; simp only [hkx, ↓reduceIte, List.find?_cons, hxp]
    · have hxpF : (normKey x.1 == normKey p) = false := Bool.eq_false_iff.mpr hxp
      by_cases hkx : keep x.1 = true
      · rw [List.filter_cons]; simp only [hkx, ↓reduceIte, List.find?_cons, hxpF]
        exact ih
      · have hkxF : keep x.1 = false := Bool.eq_false_iff.mpr hkx
        rw [List.filter_cons]; simp only [hkxF, Bool.false_eq_true, ↓reduceIte, List.find?_cons, hxpF]
        exact ih

private theorem nodesFilteredPres_listDir {P : String → Prop} {s s' : TempMockState}
    (hPres : NodesFilteredPres P s s') (dir : String) (hd : dir ≠ "")
    (hDirP : ∀ k, normKey k = normKey dir → P k)
    (hUnderP : ∀ k, underDir dir k = true → P k) :
    ((mockFs.listDir dir).run s').1 = ((mockFs.listDir dir).run s).1 ∧
    ((mockFs.listDir dir).run s').2 = s' := by
  have hLook : lookupNode s'.nodes (normKey dir) = lookupNode s.nodes (normKey dir) :=
    nodesFilteredPres_lookupNode hPres (normKey dir) (fun k hk => hDirP k (by simpa [normKey_idem] using hk))
  have hUnderOfPc : ∀ k nm, mockParentChild (normKey dir) k = some nm → underDir dir k = true := by
    intro k nm hpc
    unfold mockParentChild at hpc
    rw [normKey_idem] at hpc
    have hdNorm : normKey dir ≠ "" := normKey_ne_empty dir hd
    have hdEmpty : (normKey dir).isEmpty = false := by
      cases hb : (normKey dir).isEmpty with
      | false => rfl
      | true => exact absurd ((string_isEmpty_iff_eq_empty _).mp hb) hdNorm
    simp only [hdEmpty, Bool.false_eq_true, ↓reduceIte] at hpc
    split at hpc
    · rename_i hSlash
      split at hpc
      · rename_i hPref
        unfold underDir
        simp only [hSlash, ↓reduceIte, hPref, Bool.or_true]
      · simp at hpc
    · rename_i hNotSlash
      split at hpc
      · rename_i hPref
        unfold underDir
        have hNotSlashF : (normKey dir == "/") = false := Bool.eq_false_iff.mpr hNotSlash
        simp only [hNotSlashF, Bool.false_eq_true, ↓reduceIte, hPref, Bool.or_true]
      · simp at hpc
  rcases hPres with ⟨⟨keep, hk, hn⟩, _⟩
  have hFm : s'.nodes.filterMap (fun e => mockParentChild (normKey dir) e.1) =
      s.nodes.filterMap (fun e => mockParentChild (normKey dir) e.1) := by
    rw [hn]
    apply list_filter_filterMap_eq
    intro e he
    cases hpc : mockParentChild (normKey dir) e.1 with
    | none => simp [hpc] at he
    | some nm => exact hk e.1 (hUnderP e.1 (hUnderOfPc e.1 nm hpc))
  dsimp only [mockFs]
  rw [stateM_bind_run, stateM_get_run, stateM_bind_run, stateM_get_run]
  dsimp only
  rw [hLook]
  cases hl : lookupNode s.nodes (normKey dir) with
  | none => exact ⟨rfl, rfl⟩
  | some nd =>
    dsimp only
    by_cases h1 : ((mockNodeStat nd).kind != EntryKind.dir) = true
    · simp only [h1, ↓reduceIte]; constructor <;> rfl
    · have h1f : ((mockNodeStat nd).kind != EntryKind.dir) = false := Bool.eq_false_iff.mpr h1
      by_cases h2 : (!hasRx (mockNodeStat nd)) = true
      · simp only [h1f, h2, Bool.false_eq_true, ↓reduceIte]; constructor <;> rfl
      · have h2f : (!hasRx (mockNodeStat nd)) = false := Bool.eq_false_iff.mpr h2
        simp only [h1f, h2f, Bool.false_eq_true, ↓reduceIte, hFm]; constructor <;> rfl

private structure SweepFsOps (fs : FsApiM (StateM TempMockState)) : Prop where
  hJoin : fs.join = mockJoin
  hStat : fs.stat = mockFs.stat
  hLstat : fs.lstat = mockFs.lstat
  hListDir : fs.listDir = mockFs.listDir
  hTryWfl : ∀ {α : Type}, @fs.tryWithFileLock α = @mockFs.tryWithFileLock α
  hRm : fs.rmtree = mockFs.rmtree
  hRmdir : fs.rmdir = mockFs.rmdir
  hUnlink : ∀ p miss s,
    (fs.unlink p miss).run s = (mockFs.unlink p miss).run s ∨
    ∃ fe, (fs.unlink p miss).run s = (.error fe, s)

private theorem sweepFsOps_mockFs : SweepFsOps mockFs :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, fun _ _ _ => Or.inl rfl⟩

private theorem cleanupDirIgnoringNotFound_filteredPres
    (fs : FsApiM (StateM TempMockState)) (hRm : fs.rmtree = mockFs.rmtree)
    (target : String) (s : TempMockState) :
    let (_, s') := (Internal.cleanupDirIgnoringNotFound fs target).run s
    NodesFilteredPres (fun k => underDir target k = false) s s' := by
  dsimp only [Internal.cleanupDirIgnoringNotFound]
  rw [hRm]
  dsimp only [mockFs, mockRmtreePure, resolveParentTarget]
  rw [stateM_bind_run, stateM_bind_run, stateM_get_run]
  dsimp only
  cases hl : lookupNode s.nodes (normKey target) with
  | none => exact nodesFilteredPres_refl _ s
  | some nd =>
    cases nd with
    | dir t m =>
      simp only [stateM_bind_run, stateM_set_run, stateM_pure_run]
      refine ⟨⟨fun k => !underDir (normKey target) k, fun k hk => ?_, rfl⟩, rfl, rfl, rfl, rfl, rfl⟩
      have hu : underDir (normKey target) k = underDir target k := by unfold underDir; rw [normKey_idem]
      simp [hu, hk]
    | file _ _ _ _ => exact nodesFilteredPres_refl _ s
    | symlink _ _ => exact nodesFilteredPres_refl _ s

private theorem unlink_filteredPres
    (fs : FsApiM (StateM TempMockState))
    (hUnlink : ∀ p miss s, (fs.unlink p miss).run s = (mockFs.unlink p miss).run s ∨ ∃ fe, (fs.unlink p miss).run s = (.error fe, s))
    (p : String) (miss : Bool) (s : TempMockState) :
    NodesFilteredPres (fun k => normKey k ≠ normKey p) s ((fs.unlink p miss).run s).2 := by
  rcases hUnlink p miss s with hEq | ⟨fe, hErr⟩
  · rw [hEq]
    dsimp only [mockFs, resolveParentTarget]
    rw [stateM_bind_run, stateM_get_run]
    dsimp only
    cases hl : lookupNode s.nodes (normKey p) with
    | none =>
      cases miss <;> exact nodesFilteredPres_refl _ s
    | some nd =>
      cases nd with
      | dir _ _ => exact nodesFilteredPres_refl _ s
      | file _ _ _ _ =>
        simp only [stateM_bind_run, stateM_set_run, stateM_pure_run]
        refine ⟨⟨fun k => normKey k != normKey p, fun k hk => bne_iff_ne.mpr hk, rfl⟩, rfl, rfl, rfl, rfl, rfl⟩
      | symlink _ _ =>
        simp only [stateM_bind_run, stateM_set_run, stateM_pure_run]
        refine ⟨⟨fun k => normKey k != normKey p, fun k hk => bne_iff_ne.mpr hk, rfl⟩, rfl, rfl, rfl, rfl, rfl⟩
  · rw [hErr]
    exact nodesFilteredPres_refl _ s

private theorem rmdir_filteredPres
    (fs : FsApiM (StateM TempMockState)) (hRmdir : fs.rmdir = mockFs.rmdir)
    (p : String) (s : TempMockState) :
    NodesFilteredPres (fun k => normKey k ≠ normKey p) s ((fs.rmdir p).run s).2 := by
  rw [hRmdir]
  dsimp only [mockFs, resolveParentTarget]
  rw [stateM_bind_run, stateM_get_run]
  dsimp only
  cases hl : lookupNode s.nodes (normKey p) with
  | none => exact nodesFilteredPres_refl _ s
  | some nd =>
    cases nd with
    | dir _ _ =>
      simp only [stateM_bind_run, stateM_set_run, stateM_pure_run]
      refine ⟨⟨fun k => normKey k != normKey p, fun k hk => bne_iff_ne.mpr hk, rfl⟩, rfl, rfl, rfl, rfl, rfl⟩
    | file _ _ _ _ => exact nodesFilteredPres_refl _ s
    | symlink _ _ => exact nodesFilteredPres_refl _ s

private theorem removeNonLockChildren_filteredPres
    (fs : FsApiM (StateM TempMockState)) (hOps : SweepFsOps fs)
    (other : String) (hoNe : other ≠ "") (hoNorm : normKey other = other) (hoSlash : other ≠ "/")
    (names : List String) (hValid : ∀ nm ∈ names, pValidEntryName nm = true) (s : TempMockState) :
    NodesFilteredPres (fun k => underDir other k = false) s
      ((Internal.removeNonLockChildren fs other names).run s).2 := by
  induction names generalizing s with
  | nil =>
    dsimp only [Internal.removeNonLockChildren]
    rw [stateM_pure_run]
    exact nodesFilteredPres_refl _ s
  | cons nm rest ih =>
    have hnmV : pValidEntryName nm = true := hValid nm (List.mem_cons_self)
    have hrestV : ∀ x ∈ rest, pValidEntryName x = true := fun x hx => hValid x (List.mem_cons_of_mem nm hx)
    dsimp only [Internal.removeNonLockChildren]
    by_cases hLock : (nm == ".lock") = true
    · simp only [hLock, ↓reduceIte]
      exact ih hrestV s
    · have hLockF : (nm == ".lock") = false := Bool.eq_false_iff.mpr hLock
      simp only [hLockF, Bool.false_eq_true, ↓reduceIte]
      rw [stateM_bind_run, hOps.hLstat, mockFs_lstat_run, hOps.hJoin]
      have ⟨hnmNe, _, _, hnmSlash⟩ := validEntryName_parts nm hnmV
      have hUnderEntry : ∀ k, underDir (mockJoin other nm) k = true → underDir other k = true :=
        fun k hk => underDir_mockJoin_child other nm k hoNe hoNorm hoSlash hnmNe hnmSlash hk
      have hNotUnderOtherEntry : ∀ k, underDir other k = false → underDir (mockJoin other nm) k = false := by
        intro k hk
        cases hb : underDir (mockJoin other nm) k with
        | false => rfl
        | true => exact absurd (hUnderEntry k hb) (by rw [hk]; decide)
      have hNotNormEq : ∀ k, underDir other k = false → normKey k ≠ normKey (mockJoin other nm) := by
        intro k hk hEq
        have hu1 : underDir (mockJoin other nm) k = true := by
          unfold underDir
          rw [hEq]
          exact underDir_refl (mockJoin other nm) (normKey_mockJoin other nm hnmNe hnmSlash)
        exact absurd (hUnderEntry k hu1) (by rw [hk]; decide)
      cases hl : mockLstatPure s (mockJoin other nm) with
      | error fe =>
        dsimp only
        by_cases hnf : (fe.kind == .notFound) = true
        · simp only [hnf, ↓reduceIte]; exact ih hrestV s
        · simp only [Bool.eq_false_iff.mpr hnf, Bool.false_eq_true, ↓reduceIte, stateM_pure_run]
          exact nodesFilteredPres_refl _ s
      | ok st =>
        dsimp only
        by_cases hDir : (st.kind == .dir) = true
        · simp only [hDir, ↓reduceIte]
          rw [stateM_bind_run]
          have hStep := cleanupDirIgnoringNotFound_filteredPres fs hOps.hRm (mockJoin other nm) s
          cases hc : (Internal.cleanupDirIgnoringNotFound fs (mockJoin other nm)).run s with
          | mk rc sc =>
            dsimp only at hStep ⊢
            rw [hc] at hStep
            dsimp only at hStep
            have hStep' : NodesFilteredPres (fun k => underDir other k = false) s sc :=
              nodesFilteredPres_mono hNotUnderOtherEntry hStep
            cases rc with
            | error _ => rw [stateM_pure_run]; exact hStep'
            | ok _ => exact nodesFilteredPres_trans hStep' (ih hrestV sc)
        · have hDirF : (st.kind == .dir) = false := Bool.eq_false_iff.mpr hDir
          simp only [hDirF, Bool.false_eq_true, ↓reduceIte]
          rw [stateM_bind_run]
          have h1 := unlink_filteredPres fs hOps.hUnlink (mockJoin other nm) true s
          cases hu : (fs.unlink (mockJoin other nm) true).run s with
          | mk ru su =>
            dsimp only at h1 ⊢
            rw [hu] at h1
            dsimp only at h1
            have h1' : NodesFilteredPres (fun k => underDir other k = false) s su :=
              nodesFilteredPres_mono hNotNormEq h1
            cases ru with
            | error _ =>
              dsimp only
              rw [stateM_bind_run, stateM_pure_run]
              dsimp only
              rw [stateM_pure_run]
              exact h1'
            | ok _ => exact nodesFilteredPres_trans h1' (ih hrestV su)

private theorem removeLockedTempDir_filteredPres
    (fs : FsApiM (StateM TempMockState)) (hOps : SweepFsOps fs)
    (other : String) (hoNe : other ≠ "") (hoNorm : normKey other = other) (hoSlash : other ≠ "/")
    (s : TempMockState) :
    NodesFilteredPres (fun k => underDir other k = false) s
      ((Internal.removeLockedTempDir fs other (mockJoin other ".lock")).run s).2 := by
  dsimp only [Internal.removeLockedTempDir]
  rw [stateM_bind_run, hOps.hListDir]
  cases hList : (mockFs.listDir other).run s with
  | mk resList sList =>
    have hsListEq : sList = s := by
      dsimp only [mockFs] at hList
      rw [stateM_bind_run, stateM_get_run] at hList
      dsimp only at hList
      cases hl : lookupNode s.nodes (normKey other) with
      | none =>
        rw [hl] at hList
        dsimp only [pure, StateT.pure] at hList
        exact (Prod.mk.inj hList).2.symm
      | some nd =>
        rw [hl] at hList
        dsimp only at hList
        by_cases h1 : (mockNodeStat nd).kind != EntryKind.dir <;> by_cases h2 : !hasRx (mockNodeStat nd) <;>
          simp [h1, h2] at hList
        · exact (Prod.mk.inj hList).2.symm
        · exact (Prod.mk.inj hList).2.symm
        · exact (Prod.mk.inj hList).2.symm
        · exact (Prod.mk.inj hList).2.symm
    have hList' : (mockFs.listDir other).run s = (resList, s) := by rw [hList, hsListEq]
    subst sList
    dsimp only
    cases resList with
    | error fe =>
      by_cases hnf : (fe.kind == .notFound) = true
      · simp only [hnf, ↓reduceIte, stateM_pure_run]; exact nodesFilteredPres_refl _ s
      · simp only [Bool.eq_false_iff.mpr hnf, Bool.false_eq_true, ↓reduceIte, stateM_pure_run]
        exact nodesFilteredPres_refl _ s
    | ok arr =>
      have hValidArr : ∀ nm ∈ arr.toList, pValidEntryName nm = true := by
        intro nm hnm
        dsimp only [mockFs] at hList'
        rw [stateM_bind_run, stateM_get_run] at hList'
        dsimp only [Pure.pure] at hList'
        cases hl : lookupNode s.nodes (normKey other) with
        | none =>
          simp only [hl] at hList'
          dsimp only [StateT.pure, StateT.run] at hList'
          cases (Prod.mk.inj hList').1
        | some nd =>
          rw [hl] at hList'
          dsimp only at hList'
          by_cases h1 : ((mockNodeStat nd).kind != EntryKind.dir) = true
          · simp only [h1, ↓reduceIte] at hList'
            dsimp only [StateT.pure, StateT.run] at hList'
            cases (Prod.mk.inj hList').1
          · have h1f : ((mockNodeStat nd).kind != EntryKind.dir) = false := Bool.eq_false_iff.mpr h1
            by_cases h2 : (!hasRx (mockNodeStat nd)) = true
            · simp only [h1f, h2, Bool.false_eq_true, ↓reduceIte] at hList'
              try dsimp only [Bind.bind, StateT.bind, StateT.pure, Pure.pure] at hList'
              cases (Prod.mk.inj hList').1
            · have h2f : (!hasRx (mockNodeStat nd)) = false := Bool.eq_false_iff.mpr h2
              simp only [h1f, h2f, Bool.false_eq_true, ↓reduceIte] at hList'
              try dsimp only [Bind.bind, StateT.bind, StateT.pure, Pure.pure] at hList'
              have hArr : arr = (Internal.sortStrings (eraseDupStrings (s.nodes.filterMap (fun e => mockParentChild (normKey other) e.1)))).toArray :=
                (Except.ok.inj (Prod.mk.inj hList').1).symm
              have hnm' : nm ∈ Internal.sortStrings (eraseDupStrings (s.nodes.filterMap (fun e => mockParentChild (normKey other) e.1))) := by
                rw [hArr] at hnm; exact hnm
              rw [mem_sortStrings, mem_eraseDupStrings, List.mem_filterMap] at hnm'
              rcases hnm' with ⟨e, _, he⟩
              exact validEntryName_of_mockParentChild (normKey other) e.1 nm he
      have hRem := removeNonLockChildren_filteredPres fs hOps other hoNe hoNorm hoSlash arr.toList hValidArr s
      rw [stateM_bind_run]
      cases hr : (Internal.removeNonLockChildren fs other arr.toList).run s with
      | mk rRem s1 =>
        rw [hr] at hRem
        dsimp only at hRem
        cases rRem with
        | error te =>
          rw [stateM_pure_run]
          exact hRem
        | ok _ =>
          rw [stateM_bind_run]
          have hUnlinkLock := unlink_filteredPres fs hOps.hUnlink (mockJoin other ".lock") true s1
          have hNotLock : ∀ k, underDir other k = false → normKey k ≠ normKey (mockJoin other ".lock") := by
            intro k hk hEq
            have hu : underDir other (mockJoin other ".lock") = true :=
              underDir_mockJoin_self other ".lock" hoNe hoNorm hoSlash (by decide) (by decide)
            have hu2 : underDir other k = true := by
              rwa [underDir_eq_of_normKey_eq other k (mockJoin other ".lock") hEq]
            rw [hu2] at hk
            exact Bool.noConfusion hk
          have hUnlinkPres : NodesFilteredPres (fun k => underDir other k = false) s1
              ((fs.unlink (mockJoin other ".lock") true).run s1).2 :=
            nodesFilteredPres_mono hNotLock hUnlinkLock
          cases hu : (fs.unlink (mockJoin other ".lock") true).run s1 with
          | mk ru s2 =>
            dsimp only at hUnlinkPres ⊢
            rw [hu] at hUnlinkPres
            dsimp only at hUnlinkPres
            cases ru with
            | error fe =>
              rw [stateM_pure_run]
              exact nodesFilteredPres_trans hRem hUnlinkPres
            | ok _ =>
              rw [stateM_bind_run]
              have hRmDir := rmdir_filteredPres fs hOps.hRmdir other s2
              have hNotSelf : ∀ k, underDir other k = false → normKey k ≠ normKey other := by
                intro k hk hEq
                have hu : underDir other k = true := by
                  rw [underDir_eq_of_normKey_eq other k other hEq, underDir_refl other hoNorm]
                rw [hu] at hk
                exact Bool.noConfusion hk
              have hRmPres : NodesFilteredPres (fun k => underDir other k = false) s2
                  ((fs.rmdir other).run s2).2 :=
                nodesFilteredPres_mono hNotSelf hRmDir
              cases hd : (fs.rmdir other).run s2 with
              | mk rd s3 =>
                dsimp only at hRmPres ⊢
                rw [hd] at hRmPres
                dsimp only at hRmPres
                have hAll := nodesFilteredPres_trans hRem (nodesFilteredPres_trans hUnlinkPres hRmPres)
                cases rd with
                | ok _ =>
                  rw [stateM_pure_run]; exact hAll
                | error fe =>
                  by_cases hnf : (fe.kind == .notFound) = true
                  · simp only [hnf, ↓reduceIte, stateM_pure_run]; exact hAll
                  · simp only [Bool.eq_false_iff.mpr hnf, Bool.false_eq_true, ↓reduceIte, stateM_pure_run]; exact hAll

private theorem sweepEntry_other_preserves
    (fs : FsApiM (StateM TempMockState)) (hOps : SweepFsOps fs)
    (root dirPrefix childName otherName : String) (maxAgeSec : Nat) (nowSec : Int)
    (hr : root ≠ "") (hcV : pValidEntryName childName = true) (hoV : pValidEntryName otherName = true)
    (hNe : otherName ≠ childName) (rep : CleanupReport) (s : TempMockState) :
    let child := mockJoin root childName
    let P : String → Prop := fun k => underDir child k = true ∨ normKey k = normKey root
    let (rep', s') := (Internal.sweepEntry fs root dirPrefix maxAgeSec nowSec rep otherName).run s
    NodesFilteredPres P s s' ∧
    (child ∈ rep'.removed.toList ↔ child ∈ rep.removed.toList) ∧
    (child ∈ rep'.keptLocked.toList ↔ child ∈ rep.keptLocked.toList) ∧
    (child ∈ rep'.keptFresh.toList ↔ child ∈ rep.keptFresh.toList) ∧
    (child ∈ rep'.skipped.toList ↔ child ∈ rep.skipped.toList) ∧
    (rep.failed.isEmpty = false → rep'.failed.isEmpty = false) ∧
    (∀ e ∈ rep.failed.toList, e ∈ rep'.failed.toList) := by
  intro child P
  have ⟨hcNe, _, _, hcSlash⟩ := validEntryName_parts childName hcV
  have ⟨hoNe, _, _, hoSlash⟩ := validEntryName_parts otherName hoV
  let other := mockJoin root otherName
  have hoFullNe : other ≠ "" := mockJoin_ne_empty root otherName hoNe
  have hoFullNorm : normKey other = other := normKey_mockJoin root otherName hoNe hoSlash
  have hoFullSlash : other ≠ "/" := mockJoin_ne_slash root otherName hr hoNe
  have hOtherNeChild : other ≠ child := by
    intro hEq
    have hu1 : underDir child other = true := by
      rw [hEq]; exact underDir_refl child (normKey_mockJoin root childName hcNe hcSlash)
    have hu2 : underDir other other = true := underDir_refl other hoFullNorm
    exact disjoint_underDir_mockJoin root otherName childName other hr hoNe hcNe hoSlash hcSlash hNe hu2 hu1
  have hDisjointP : ∀ k, P k → underDir other k = false := by
    intro k hk
    rcases hk with hChild | hRoot
    · cases hb : underDir other k with
      | false => rfl
      | true => exact absurd (disjoint_underDir_mockJoin root otherName childName k hr hoNe hcNe hoSlash hcSlash hNe hb hChild) False.elim
    · exact not_underDir_mockJoin_root root otherName k hr hoNe hoSlash hRoot
  have hSameState :
      NodesFilteredPres P s s ∧
      (child ∈ rep.removed.toList ↔ child ∈ rep.removed.toList) ∧
      (child ∈ rep.keptLocked.toList ↔ child ∈ rep.keptLocked.toList) ∧
      (child ∈ rep.keptFresh.toList ↔ child ∈ rep.keptFresh.toList) ∧
      (child ∈ rep.skipped.toList ↔ child ∈ rep.skipped.toList) ∧
      (rep.failed.isEmpty = false → rep.failed.isEmpty = false) ∧
      (∀ e ∈ rep.failed.toList, e ∈ rep.failed.toList) :=
    ⟨nodesFilteredPres_refl P s, Iff.rfl, Iff.rfl, Iff.rfl, Iff.rfl, id, fun _ h => h⟩
  have hPushFailed : ∀ err : TempError,
      NodesFilteredPres P s s ∧
      (child ∈ rep.removed.toList ↔ child ∈ rep.removed.toList) ∧
      (child ∈ rep.keptLocked.toList ↔ child ∈ rep.keptLocked.toList) ∧
      (child ∈ rep.keptFresh.toList ↔ child ∈ rep.keptFresh.toList) ∧
      (child ∈ rep.skipped.toList ↔ child ∈ rep.skipped.toList) ∧
      (rep.failed.isEmpty = false → (rep.failed.push err).isEmpty = false) ∧
      (∀ e ∈ rep.failed.toList, e ∈ (rep.failed.push err).toList) := by
    intro err
    refine ⟨nodesFilteredPres_refl P s, Iff.rfl, Iff.rfl, Iff.rfl, Iff.rfl, ?_, ?_⟩
    · intro _; simp
    · intro e he; simp [Array.toList_push, he]
  dsimp only [Internal.sweepEntry]
  rw [hOps.hJoin]
  by_cases hPref : (!dirPrefix.toList.isPrefixOf otherName.toList) = true
  · simp only [hPref, ↓reduceIte, stateM_pure_run]
    refine ⟨nodesFilteredPres_refl P s, trivial, trivial, trivial, ?_, id, fun _ h => h⟩
    dsimp only [other] at hOtherNeChild
    simp [Array.toList_push, hOtherNeChild.symm]
  · have hPrefF : (!dirPrefix.toList.isPrefixOf otherName.toList) = false := Bool.eq_false_iff.mpr hPref
    simp only [hPrefF, Bool.false_eq_true, ↓reduceIte]
    rw [stateM_bind_run, hOps.hLstat, mockFs_lstat_run]
    cases hlChild : mockLstatPure s other with
    | error fe =>
      dsimp only
      by_cases hnf : (fe.kind == .notFound) = true
      · simp only [hnf, ↓reduceIte, stateM_pure_run]
        exact ⟨nodesFilteredPres_refl P s, trivial, trivial, trivial, trivial, id, fun _ h => h⟩
      · simp only [Bool.eq_false_iff.mpr hnf, Bool.false_eq_true, ↓reduceIte, stateM_pure_run]
        refine ⟨nodesFilteredPres_refl P s, trivial, trivial, trivial, trivial, fun _ => by simp, fun e he => by simp [Array.toList_push, he]⟩
    | ok stChild =>
      dsimp only
      by_cases hNotDir : (stChild.kind != .dir) = true
      · simp only [hNotDir, ↓reduceIte, stateM_pure_run]
        refine ⟨nodesFilteredPres_refl P s, trivial, trivial, trivial, ?_, id, fun _ h => h⟩
        dsimp only [other] at hOtherNeChild
        simp [Array.toList_push, hOtherNeChild.symm]
      · simp only [Bool.eq_false_iff.mpr hNotDir, Bool.false_eq_true, ↓reduceIte]
        rw [stateM_bind_run, mockFs_lstat_run]
        cases hlLock : mockLstatPure s (mockJoin other ".lock") with
        | error fe =>
          dsimp only
          by_cases hnf : (fe.kind != .notFound) = true
          · simp only [hnf, ↓reduceIte, stateM_pure_run]
            refine ⟨nodesFilteredPres_refl P s, trivial, trivial, trivial, trivial, fun _ => by simp, fun e he => by simp [Array.toList_push, he]⟩
          · simp only [Bool.eq_false_iff.mpr hnf, Bool.false_eq_true, ↓reduceIte]
            by_cases hFresh : (nowSec - stChild.modifiedSec ≤ (maxAgeSec : Int))
            · simp only [hFresh, ↓reduceIte, stateM_pure_run]
              refine ⟨nodesFilteredPres_refl P s, trivial, trivial, ?_, trivial, id, fun _ h => h⟩
              dsimp only [other] at hOtherNeChild
              simp [Array.toList_push, hOtherNeChild.symm]
            · simp only [hFresh, ↓reduceIte]
              rw [stateM_bind_run]
              have hClean := cleanupDirIgnoringNotFound_filteredPres fs hOps.hRm other s
              cases hc : (Internal.cleanupDirIgnoringNotFound fs other).run s with
              | mk rc sc =>
                dsimp only at hClean ⊢
                rw [hc] at hClean
                dsimp only at hClean
                have hPres : NodesFilteredPres P s sc := nodesFilteredPres_mono hDisjointP hClean
                cases rc with
                | ok _ =>
                  rw [stateM_pure_run]
                  refine ⟨hPres, ?_, Iff.rfl, Iff.rfl, Iff.rfl, id, fun _ h => h⟩
                  dsimp only [other] at hOtherNeChild
                  simp [Array.toList_push, hOtherNeChild.symm]
                | error te =>
                  rw [stateM_pure_run]
                  refine ⟨hPres, Iff.rfl, Iff.rfl, Iff.rfl, Iff.rfl, ?_, ?_⟩
                  · intro _; simp
                  · intro e he; simp [Array.toList_push, he]
        | ok stLock =>
          dsimp only
          by_cases hNotFile : (stLock.kind != .file) = true
          · simp only [hNotFile, ↓reduceIte, stateM_pure_run]
            refine ⟨nodesFilteredPres_refl P s, trivial, trivial, trivial, trivial, fun _ => by simp, fun e he => by simp [Array.toList_push, he]⟩
          · simp only [Bool.eq_false_iff.mpr hNotFile, Bool.false_eq_true, ↓reduceIte]
            rw [stateM_bind_run, hOps.hTryWfl]
            obtain ⟨ndLock, hLookLock, hStLock⟩ := lookupNode_of_lstat_ok s (mockJoin other ".lock") stLock hlLock
            have hNotFileEq : stLock.kind = .file := by revert hNotFile; cases stLock.kind <;> decide
            have hLockNorm : normKey (mockJoin other ".lock") = mockJoin other ".lock" :=
              normKey_mockJoin other ".lock" (by decide) (by decide)
            cases ndLock with
            | dir _ _ => dsimp only [mockNodeStat] at hStLock; rw [← hStLock] at hNotFileEq; exact EntryKind.noConfusion hNotFileEq
            | symlink _ _ => dsimp only [mockNodeStat] at hStLock; rw [← hStLock] at hNotFileEq; exact EntryKind.noConfusion hNotFileEq
            | file ino c t m =>
              by_cases hConf : mockHasConflict s.locks ino .exclusive = true
              · rw [mockFs_tryWithFileLock_existing_conflict_run s (mockJoin other ".lock") .exclusive false ino c t m hLockNorm hLookLock hConf]
                dsimp only
                rw [stateM_pure_run]
                refine ⟨nodesFilteredPres_refl P s, Iff.rfl, ?_, Iff.rfl, Iff.rfl, id, fun _ h => h⟩
                dsimp only [other] at hOtherNeChild
                simp [Array.toList_push, hOtherNeChild.symm]
              · have hConfF : mockHasConflict s.locks ino .exclusive = false := Bool.eq_false_iff.mpr hConf
                rw [mockFs_tryWithFileLock_existing_ok_run s (mockJoin other ".lock") .exclusive false ino c t m hLockNorm hLookLock hConfF]
                dsimp only
                have hRemLock := removeLockedTempDir_filteredPres fs hOps other hoFullNe hoFullNorm hoFullSlash { s with locks := (ino, .exclusive) :: s.locks }
                cases hrl : (Internal.removeLockedTempDir fs other (mockJoin other ".lock")).run { s with locks := (ino, .exclusive) :: s.locks } with
                | mk rrl srl =>
                  dsimp only at hRemLock ⊢
                  rw [hrl] at hRemLock
                  dsimp only at hRemLock
                  have hLocksEq : srl.locks = (ino, .exclusive) :: s.locks := hRemLock.2.1
                  have hUnlocks : mockRemoveFirstLock ino .exclusive srl.locks = s.locks := by
                    rw [hLocksEq, mockRemoveFirstLock_head]
                  have hPres : NodesFilteredPres P s { srl with locks := mockRemoveFirstLock ino .exclusive srl.locks } := by
                    rcases hRemLock with ⟨⟨keep, hk, hn⟩, _, hi, ht, hs, hu⟩
                    refine ⟨⟨keep, fun k hkP => hk k (hDisjointP k hkP), hn⟩, hUnlocks, hi, ht, hs, hu⟩
                  cases rrl with
                  | error fe =>
                    dsimp only [Except.map]
                    by_cases hnf : (fe.kind == .notFound) = true
                    · simp only [hnf, ↓reduceIte, stateM_pure_run]
                      exact ⟨hPres, trivial, trivial, trivial, trivial, id, fun _ h => h⟩
                    · simp only [Bool.eq_false_iff.mpr hnf, Bool.false_eq_true, ↓reduceIte, stateM_pure_run]
                      refine ⟨hPres, trivial, trivial, trivial, trivial, ?_, ?_⟩
                      · intro _; simp
                      · intro e he; simp [Array.toList_push, he]
                  | ok rInner =>
                    dsimp only [Except.map]
                    cases rInner with
                    | ok _ =>
                      rw [stateM_pure_run]
                      refine ⟨hPres, ?_, Iff.rfl, Iff.rfl, Iff.rfl, id, fun _ h => h⟩
                      dsimp only [other] at hOtherNeChild
                      simp [Array.toList_push, hOtherNeChild.symm]
                    | error te =>
                      rw [stateM_pure_run]
                      refine ⟨hPres, Iff.rfl, Iff.rfl, Iff.rfl, Iff.rfl, ?_, ?_⟩
                      · intro _; simp
                      · intro e he; simp [Array.toList_push, he]

private theorem sweepEntries_append (fs : FsApiM (StateM TempMockState))
    (root dirPrefix : String) (maxAgeSec : Nat) (nowSec : Int)
    (rep : CleanupReport) (xs ys : List String) (s : TempMockState) :
    (Internal.sweepEntries fs root dirPrefix maxAgeSec nowSec rep (xs ++ ys)).run s =
      let (rep1, s1) := (Internal.sweepEntries fs root dirPrefix maxAgeSec nowSec rep xs).run s
      (Internal.sweepEntries fs root dirPrefix maxAgeSec nowSec rep1 ys).run s1 := by
  induction xs generalizing rep s with
  | nil => rfl
  | cons x xs ih =>
    dsimp only [List.cons_append, Internal.sweepEntries]
    rw [stateM_bind_run, stateM_bind_run]
    cases hStep : (Internal.sweepEntry fs root dirPrefix maxAgeSec nowSec rep x).run s with
    | mk rep1 s1 => exact ih rep1 s1

private theorem sweepEntries_other_preserves
    (fs : FsApiM (StateM TempMockState)) (hOps : SweepFsOps fs)
    (root dirPrefix childName : String) (maxAgeSec : Nat) (nowSec : Int)
    (hr : root ≠ "") (hcV : pValidEntryName childName = true)
    (names : List String) (hValid : ∀ nm ∈ names, pValidEntryName nm = true) (hNotIn : childName ∉ names)
    (rep : CleanupReport) (s : TempMockState) :
    let child := mockJoin root childName
    let P : String → Prop := fun k => underDir child k = true ∨ normKey k = normKey root
    let (rep', s') := (Internal.sweepEntries fs root dirPrefix maxAgeSec nowSec rep names).run s
    NodesFilteredPres P s s' ∧
    (child ∈ rep'.removed.toList ↔ child ∈ rep.removed.toList) ∧
    (child ∈ rep'.keptLocked.toList ↔ child ∈ rep.keptLocked.toList) ∧
    (child ∈ rep'.keptFresh.toList ↔ child ∈ rep.keptFresh.toList) ∧
    (child ∈ rep'.skipped.toList ↔ child ∈ rep.skipped.toList) ∧
    (rep.failed.isEmpty = false → rep'.failed.isEmpty = false) ∧
    (∀ e ∈ rep.failed.toList, e ∈ rep'.failed.toList) := by
  induction names generalizing rep s with
  | nil =>
    dsimp only [Internal.sweepEntries]
    rw [stateM_pure_run]
    exact ⟨nodesFilteredPres_refl _ s, Iff.rfl, Iff.rfl, Iff.rfl, Iff.rfl, id, fun _ h => h⟩
  | cons nm rest ih =>
    have hnmV : pValidEntryName nm = true := hValid nm (List.mem_cons_self)
    have hrestV : ∀ x ∈ rest, pValidEntryName x = true := fun x hx => hValid x (List.mem_cons_of_mem nm hx)
    have hNe : nm ≠ childName := fun h => hNotIn (h ▸ List.mem_cons_self)
    have hRestNotIn : childName ∉ rest := fun h => hNotIn (List.mem_cons_of_mem nm h)
    dsimp only [Internal.sweepEntries]
    rw [stateM_bind_run]
    have hStep := sweepEntry_other_preserves fs hOps root dirPrefix childName nm maxAgeSec nowSec hr hcV hnmV hNe rep s
    cases h1 : (Internal.sweepEntry fs root dirPrefix maxAgeSec nowSec rep nm).run s with
    | mk rep1 s1 =>
      dsimp only at hStep ⊢
      rw [h1] at hStep
      dsimp only at hStep
      have hTail := ih hrestV hRestNotIn rep1 s1
      cases h2 : (Internal.sweepEntries fs root dirPrefix maxAgeSec nowSec rep1 rest).run s1 with
      | mk rep2 s2 =>
        dsimp only at hTail ⊢
        rw [h2] at hTail
        dsimp only at hTail
        exact ⟨nodesFilteredPres_trans hStep.1 hTail.1,
          hTail.2.1.trans hStep.2.1,
          hTail.2.2.1.trans hStep.2.2.1,
          hTail.2.2.2.1.trans hStep.2.2.2.1,
          hTail.2.2.2.2.1.trans hStep.2.2.2.2.1,
          fun h => hTail.2.2.2.2.2.1 (hStep.2.2.2.2.2.1 h),
          fun e he => hTail.2.2.2.2.2.2 e (hStep.2.2.2.2.2.2 e he)⟩

private theorem cleanupStaleTempDirs_split_exec
    (fs : FsApiM (StateM TempMockState)) (hOps : SweepFsOps fs)
    (s₀ : TempMockState) (root dirPrefix childName : String) (maxAgeSec : Nat)
    (hvr : pValidRoot root = true) (hvp : pValidPrefix dirPrefix = true) (hcV : pValidEntryName childName = true)
    (stRoot : FileStat) (hRoot : mockStatPure s₀ root = .ok stRoot) (hRwx : pHasRwx stRoot)
    (ndChild : MockNode) (hChild : lookupNode s₀.nodes (mockJoin root childName) = some ndChild) :
    let child := mockJoin root childName
    let nowSec := (mockTime.nowTimestamp.run s₀).1.toSecondsSinceUnixEpoch.val
    let P : String → Prop := fun k => underDir child k = true ∨ normKey k = normKey root
    ∃ before after : List String, ∃ repBefore : CleanupReport, ∃ sBefore : TempMockState,
      (∀ nm ∈ before, pValidEntryName nm = true) ∧
      (∀ nm ∈ after, pValidEntryName nm = true) ∧
      childName ∉ before ∧
      childName ∉ after ∧
      NodesFilteredPres P s₀ sBefore ∧
      (child ∈ repBefore.removed.toList ↔ False) ∧
      (child ∈ repBefore.keptLocked.toList ↔ False) ∧
      (child ∈ repBefore.keptFresh.toList ↔ False) ∧
      (child ∈ repBefore.skipped.toList ↔ False) ∧
      (∀ (repMid : CleanupReport) (sMid : TempMockState),
        (Internal.sweepEntry fs root dirPrefix maxAgeSec nowSec repBefore childName).run sBefore = (repMid, sMid) →
        let (repAfter, sFinal) := (Internal.sweepEntries fs root dirPrefix maxAgeSec nowSec repMid after).run sMid
        let finalRep : CleanupReport :=
          { removed := (Internal.sortStrings repAfter.removed.toList).toArray
            keptLocked := (Internal.sortStrings repAfter.keptLocked.toList).toArray
            keptFresh := (Internal.sortStrings repAfter.keptFresh.toList).toArray
            skipped := (Internal.sortStrings repAfter.skipped.toList).toArray
            failed := repAfter.failed }
        ((Internal.mkApiM fs mockTime mockUuid mockEnv).cleanupStaleTempDirs (some root) dirPrefix maxAgeSec).run s₀ =
          (.ok finalRep, sFinal) ∧
        NodesFilteredPres P sMid sFinal ∧
        (pHasPath finalRep.removed child ↔ child ∈ repMid.removed.toList) ∧
        (pHasPath finalRep.keptLocked child ↔ child ∈ repMid.keptLocked.toList) ∧
        (pHasPath finalRep.keptFresh child ↔ child ∈ repMid.keptFresh.toList) ∧
        (pHasPath finalRep.skipped child ↔ child ∈ repMid.skipped.toList) ∧
        (repMid.failed.isEmpty = false → finalRep.failed.isEmpty = false) ∧
        (∀ e ∈ repMid.failed.toList, e ∈ finalRep.failed.toList)) := by
  intro child nowSec P
  have hrNe : root ≠ "" := validRoot_ne_empty root hvr
  have ⟨hListRun, hListNd, hListValid⟩ := mockFs_listDir_run_of_rwx s₀ root stRoot hRoot hRwx
  have hMem : childName ∈ Internal.sortStrings (eraseDupStrings (s₀.nodes.filterMap (fun e => mockParentChild (normKey root) e.1))) :=
    mockFs_listDir_mem_of_lookupNode s₀ root childName hrNe hcV ndChild hChild
  obtain ⟨before, after, hSplit, hNotBefore, hNotAfter⟩ := list_nodup_split _ childName hListNd hMem
  have hBeforeV : ∀ nm ∈ before, pValidEntryName nm = true := fun nm hnm =>
    hListValid nm (by rw [hSplit]; exact List.mem_append_left _ hnm)
  have hAfterV : ∀ nm ∈ after, pValidEntryName nm = true := fun nm hnm =>
    hListValid nm (by rw [hSplit]; exact List.mem_append_right _ (List.mem_cons_of_mem childName hnm))
  have hBeforePres := sweepEntries_other_preserves fs hOps root dirPrefix childName maxAgeSec nowSec hrNe hcV
    before hBeforeV hNotBefore {} s₀
  cases hBeforeRun : (Internal.sweepEntries fs root dirPrefix maxAgeSec nowSec {} before).run s₀ with
  | mk repBefore sBefore =>
    dsimp only at hBeforePres
    rw [hBeforeRun] at hBeforePres
    dsimp only at hBeforePres
    refine ⟨before, after, repBefore, sBefore, hBeforeV, hAfterV, hNotBefore, hNotAfter,
      hBeforePres.1, ?_, ?_, ?_, ?_, ?_⟩
    · simpa using hBeforePres.2.1
    · simpa using hBeforePres.2.2.1
    · simpa using hBeforePres.2.2.2.1
    · simpa using hBeforePres.2.2.2.2.1
    · intro repMid sMid hMid
      have hAfterPres := sweepEntries_other_preserves fs hOps root dirPrefix childName maxAgeSec nowSec hrNe hcV
        after hAfterV hNotAfter repMid sMid
      cases hAfterRun : (Internal.sweepEntries fs root dirPrefix maxAgeSec nowSec repMid after).run sMid with
      | mk repAfter sFinal =>
        dsimp only at hAfterPres ⊢
        rw [hAfterRun] at hAfterPres
        dsimp only at hAfterPres
        have hRunClean :
            ((Internal.mkApiM fs mockTime mockUuid mockEnv).cleanupStaleTempDirs (some root) dirPrefix maxAgeSec).run s₀ =
              (.ok { removed := (Internal.sortStrings repAfter.removed.toList).toArray
                     keptLocked := (Internal.sortStrings repAfter.keptLocked.toList).toArray
                     keptFresh := (Internal.sortStrings repAfter.keptFresh.toList).toArray
                     skipped := (Internal.sortStrings repAfter.skipped.toList).toArray
                     failed := repAfter.failed }, sFinal) := by
          rw [mkApiM_cleanupStaleTempDirs_eq]
          dsimp only [Internal.cleanupStaleTempDirsM, Internal.validPrefix]
          have hResRoot : (Internal.resolveRoot fs mockEnv (some root)).run s₀ = (.ok root, s₀) := by
            dsimp only [Internal.resolveRoot, Internal.validRoot]
            rw [stateM_bind_run, stateM_pure_run]
            dsimp only
            have hvr' : (!root.isEmpty && !(Char.ofNat 0 ∈ root.toList)) = true := hvr
            simp only [hvr', Bool.not_true, Bool.false_eq_true, ↓reduceIte]
            rw [stateM_bind_run, hOps.hStat, mockFs_stat_run, hRoot]
            dsimp only
            simp only [hRwx.1, show (EntryKind.dir != EntryKind.dir) = false from rfl,
              Bool.false_eq_true, ↓reduceIte, stateM_pure_run]
          have hvp' : (!dirPrefix.isEmpty && dirPrefix.toList.head? != some '.' && !('/' ∈ dirPrefix.toList) && !(Char.ofNat 0 ∈ dirPrefix.toList)) = true := hvp
          simp only [hvp', Bool.not_true, Bool.false_eq_true, ↓reduceIte]
          rw [stateM_bind_run, hResRoot]
          dsimp only
          rw [stateM_bind_run]
          have hNowState : (mockTime.nowTimestamp.run s₀).2 = s₀ := rfl
          cases hTime : mockTime.nowTimestamp.run s₀ with
          | mk nowTs sTime =>
            have hsTime : sTime = s₀ := by rw [← hNowState, hTime]
            subst sTime
            have hNowEq : nowTs.toSecondsSinceUnixEpoch.val = nowSec := by
              dsimp only [nowSec]
              rw [hTime]
            dsimp only
            rw [stateM_bind_run, hOps.hListDir, hListRun]
            dsimp only
            rw [hNowEq, stateM_bind_run, hSplit, sweepEntries_append, hBeforeRun]
            dsimp only [Internal.sweepEntries]
            rw [stateM_bind_run, hMid]
            dsimp only
            rw [hAfterRun]
            dsimp only
            exact stateM_pure_run _ _
        refine ⟨hRunClean, hAfterPres.1, ?_, ?_, ?_, ?_, hAfterPres.2.2.2.2.2.1, hAfterPres.2.2.2.2.2.2⟩
        · simpa [hasPath_toArray_mem, mem_sortStrings] using hAfterPres.2.1
        · simpa [hasPath_toArray_mem, mem_sortStrings] using hAfterPres.2.2.1
        · simpa [hasPath_toArray_mem, mem_sortStrings] using hAfterPres.2.2.2.1
        · simpa [hasPath_toArray_mem, mem_sortStrings] using hAfterPres.2.2.2.2.1

private theorem list_find_filter_none {α : Type} (p : α → Bool) (keep : α → Bool) (xs : List α)
    (h : xs.find? p = none) : (xs.filter keep).find? p = none := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.find?_cons] at h
    cases hpx : p x with
    | true => simp [hpx] at h
    | false =>
      rw [hpx] at h
      dsimp only at h
      by_cases hk : keep x = true
      · rw [List.filter_cons, hk]; simp [hpx, ih h]
      · have hkf : keep x = false := Bool.eq_false_iff.mpr hk
        rw [List.filter_cons, hkf]; exact ih h

private theorem nodesFilteredPres_lookupNode_none {P : String → Prop} {s s' : TempMockState}
    (hPres : NodesFilteredPres P s s') (p : String)
    (hNone : lookupNode s.nodes p = none) :
    lookupNode s'.nodes p = none := by
  rcases hPres with ⟨⟨keep, _, hn⟩, _⟩
  unfold lookupNode at hNone ⊢
  rw [hn]
  exact congrArg (Option.map Prod.snd) (list_find_filter_none _ _ s.nodes (by
    cases hf : s.nodes.find? (fun e => normKey e.1 == normKey p) with
    | none => rfl
    | some _ => simp [hf] at hNone))

private theorem nodesFilteredPres_lstat {P : String → Prop} {s s' : TempMockState}
    (hPres : NodesFilteredPres P s s') (p : String)
    (hp : ∀ k, normKey k = normKey p → P k) :
    (mockFs.lstat p).run s' = (((mockFs.lstat p).run s).1, s') := by
  have hLook := nodesFilteredPres_lookupNode hPres p hp
  simp only [mockFs_lstat_run, mockLstatPure, hLook]

private theorem nodesFilteredPres_child_P {root childName : String}
    (hcV : pValidEntryName childName = true) :
    let child := mockJoin root childName
    let lockPath := mockJoin child ".lock"
    let P : String → Prop := fun k => underDir child k = true ∨ normKey k = normKey root
    (∀ k, normKey k = normKey child → P k) ∧
    (∀ k, underDir child k = true → P k) ∧
    (∀ k, normKey k = normKey lockPath → P k) ∧
    (∀ k, normKey k = normKey root → P k) := by
  have ⟨hcNe, _, _, hcSlash⟩ := validEntryName_parts childName hcV
  have hChildNorm : normKey (mockJoin root childName) = mockJoin root childName :=
    normKey_mockJoin root childName hcNe hcSlash
  have hChildNe : mockJoin root childName ≠ "" := mockJoin_ne_empty root childName hcNe
  have hChildNeSlash : mockJoin root childName ≠ "/" := by
    by_cases hRoot : root = ""
    · subst hRoot
      intro hEq
      have hJ : mockJoin "" childName = childName := rfl
      rw [hJ] at hEq
      rw [hEq] at hcSlash
      exact hcSlash (by decide)
    · exact mockJoin_ne_slash root childName hRoot hcNe
  have hUnderLock : underDir (mockJoin root childName) (mockJoin (mockJoin root childName) ".lock") = true :=
    underDir_mockJoin_self (mockJoin root childName) ".lock" hChildNe hChildNorm hChildNeSlash (by decide) (by decide)
  refine ⟨?_, fun k hk => Or.inl hk, ?_, fun k hk => Or.inr hk⟩
  · intro k hk
    refine Or.inl ?_
    rw [underDir_eq_of_normKey_eq _ k (mockJoin root childName) hk]
    exact underDir_refl _ hChildNorm
  · intro k hk
    refine Or.inl ?_
    rw [underDir_eq_of_normKey_eq _ k (mockJoin (mockJoin root childName) ".lock") hk]
    exact hUnderLock

private theorem disjoint_mockJoin_entry_target {dir nm tgt : String}
    (hdNe : dir ≠ "") (hnmV : pValidEntryName nm = true) (htV : pValidEntryName tgt = true) (hNe : nm ≠ tgt) :
    ∀ k, normKey k = normKey (mockJoin dir tgt) →
      underDir (mockJoin dir nm) k = false ∧ normKey k ≠ normKey (mockJoin dir nm) := by
  have ⟨hnmNe, _, _, hnmSlash⟩ := validEntryName_parts nm hnmV
  have ⟨htNe, _, _, htSlash⟩ := validEntryName_parts tgt htV
  have htNorm : normKey (mockJoin dir tgt) = mockJoin dir tgt := normKey_mockJoin dir tgt htNe htSlash
  have hnmNorm : normKey (mockJoin dir nm) = mockJoin dir nm := normKey_mockJoin dir nm hnmNe hnmSlash
  intro k hk
  have hNotUnder : underDir (mockJoin dir nm) k = false := by
    cases hb : underDir (mockJoin dir nm) k with
    | false => rfl
    | true =>
      exfalso
      have hSub : underDir (mockJoin dir nm) (mockJoin dir tgt) = true := by
        rwa [← underDir_eq_of_normKey_eq _ k (mockJoin dir tgt) hk]
      have hu2 : underDir (mockJoin dir tgt) (mockJoin dir tgt) = true := underDir_refl _ htNorm
      exact disjoint_underDir_mockJoin dir nm tgt (mockJoin dir tgt) hdNe hnmNe htNe hnmSlash htSlash hNe hSub hu2
  have hNotEq : normKey k ≠ normKey (mockJoin dir nm) := by
    intro hEq
    have hSub : underDir (mockJoin dir nm) (mockJoin dir tgt) = true := by
      rw [← underDir_eq_of_normKey_eq _ k (mockJoin dir tgt) hk]
      rw [underDir_eq_of_normKey_eq _ k (mockJoin dir nm) hEq]
      exact underDir_refl _ hnmNorm
    have hu2 : underDir (mockJoin dir tgt) (mockJoin dir tgt) = true := underDir_refl _ htNorm
    exact disjoint_underDir_mockJoin dir nm tgt (mockJoin dir tgt) hdNe hnmNe htNe hnmSlash htSlash hNe hSub hu2
  exact ⟨hNotUnder, hNotEq⟩

private theorem removeNonLockChildren_fail_with_lock_intact
    (child payload : String) (hcNe : child ≠ "")
    (hPayEq : payload = mockJoin child "locked_child.txt")
    (fs : FsApiM (StateM TempMockState))
    (hLstat : fs.lstat = mockFs.lstat) (hJoin : fs.join = mockJoin) (hRm : fs.rmtree = mockFs.rmtree)
    (hUnl : ∀ p miss s,
      (fs.unlink p miss).run s =
        if p == payload then (.error { kind := .permissionDenied, path := some p, message := "cannot unlink" }, s)
        else (mockFs.unlink p miss).run s)
    (names : List String) (hValid : ∀ nm ∈ names, pValidEntryName nm = true) (hNd : names.Nodup)
    (hPayMem : "locked_child.txt" ∈ names) (s : TempMockState)
    (hPayNode : ∃ ino c t m, lookupNode s.nodes payload = some (.file ino c t m)) :
    let lockPath := mockJoin child ".lock"
    ∃ te s', (Internal.removeNonLockChildren fs child names).run s = (.error te, s') ∧
      NodesFilteredPres (fun k => normKey k = normKey lockPath) s s' := by
  intro lockPath
  induction names generalizing s with
  | nil => cases hPayMem
  | cons nm rest ih =>
    have hnmV : pValidEntryName nm = true := hValid nm List.mem_cons_self
    have hrestV : ∀ x ∈ rest, pValidEntryName x = true := fun x hx => hValid x (List.mem_cons_of_mem nm hx)
    have ⟨_, hRestNd⟩ := List.nodup_cons.mp hNd
    dsimp only [Internal.removeNonLockChildren]
    by_cases hLock : nm = ".lock"
    · subst hLock
      have hPayInRest : "locked_child.txt" ∈ rest := by
        simp only [List.mem_cons] at hPayMem
        rcases hPayMem with hEq | hMem
        · exact absurd hEq (by decide)
        · exact hMem
      simpa using ih hrestV hRestNd hPayInRest s hPayNode
    · have hLockBne : (nm == ".lock") = false := beq_false_of_ne hLock
      simp only [hLockBne, Bool.false_eq_true, ↓reduceIte, hJoin]
      rw [stateM_bind_run, hLstat, mockFs_lstat_run]
      by_cases hIsPay : nm = "locked_child.txt"
      · subst hIsPay
        rw [← hPayEq]
        rcases hPayNode with ⟨ino, c, t, m, hLookPay⟩
        have hPayLstat : mockLstatPure s payload = .ok (mockNodeStat (.file ino c t m)) := by
          unfold mockLstatPure; rw [hLookPay]
        rw [hPayLstat]
        dsimp only
        have hNotDir : ((mockNodeStat (.file ino c t m)).kind == EntryKind.dir) = false := rfl
        simp only [hNotDir, Bool.false_eq_true, ↓reduceIte]
        rw [stateM_bind_run, hUnl payload true s]
        simp only [beq_self_eq_true, ↓reduceIte]
        exact ⟨_, s, stateM_pure_run _ _, nodesFilteredPres_refl _ s⟩
      · have hPayInRest : "locked_child.txt" ∈ rest := by
          simp only [List.mem_cons] at hPayMem
          rcases hPayMem with hEq | hMem
          · exact absurd hEq.symm hIsPay
          · exact hMem
        have hDisjLock := disjoint_mockJoin_entry_target (dir := child) hcNe hnmV (by decide) hLock
        have hDisjPay := disjoint_mockJoin_entry_target (dir := child) hcNe hnmV (by decide) hIsPay
        have hUnlMock : ∀ miss s1, (fs.unlink (mockJoin child nm) miss).run s1 = (mockFs.unlink (mockJoin child nm) miss).run s1 := by
          intro miss s1
          rw [hUnl]
          have hNePay : (mockJoin child nm == payload) = false := by
            rw [hPayEq, beq_false_of_ne]
            have ⟨_, hNe⟩ := hDisjPay (mockJoin child "locked_child.txt") rfl
            exact fun h => hNe (congrArg normKey h.symm)
          rw [hNePay]; rfl
        have hUnlOps : ∀ p miss s1,
            (fs.unlink p miss).run s1 = (mockFs.unlink p miss).run s1 ∨ ∃ fe, (fs.unlink p miss).run s1 = (.error fe, s1) := by
          intro p miss s1
          rw [hUnl]; split; exact Or.inr ⟨_, rfl⟩; exact Or.inl rfl
        cases hl : mockLstatPure s (mockJoin child nm) with
        | error fe =>
          dsimp only
          by_cases hnf : (fe.kind == .notFound) = true
          · simp only [hnf, ↓reduceIte]
            exact ih hrestV hRestNd hPayInRest s hPayNode
          · simp only [Bool.eq_false_iff.mpr hnf, Bool.false_eq_true, ↓reduceIte]
            exact ⟨_, s, stateM_pure_run _ _, nodesFilteredPres_refl _ s⟩
        | ok st =>
          dsimp only
          by_cases hDir : (st.kind == .dir) = true
          · simp only [hDir, ↓reduceIte]
            rw [stateM_bind_run]
            have h1 := cleanupDirIgnoringNotFound_filteredPres fs hRm (mockJoin child nm) s
            cases hc : (Internal.cleanupDirIgnoringNotFound fs (mockJoin child nm)).run s with
            | mk rc sc =>
              dsimp only at h1 ⊢
              rw [hc] at h1
              dsimp only at h1
              have hPresLock := nodesFilteredPres_mono (fun k hk => (hDisjLock k hk).1) h1
              have hPresPay := nodesFilteredPres_mono (fun k hk => (hDisjPay k (by rwa [← hPayEq])).1) h1
              cases rc with
              | error te => exact ⟨te, sc, stateM_pure_run _ _, hPresLock⟩
              | ok _ =>
                have hPaySc : ∃ ino c t m, lookupNode sc.nodes payload = some (.file ino c t m) := by
                  rcases hPayNode with ⟨ino, c, t, m, hLookPay⟩
                  exact ⟨ino, c, t, m, by rw [nodesFilteredPres_lookupNode hPresPay payload (fun _ hk => hk), hLookPay]⟩
                obtain ⟨te, s', hRec, hPresRec⟩ := ih hrestV hRestNd hPayInRest sc hPaySc
                exact ⟨te, s', hRec, nodesFilteredPres_trans hPresLock hPresRec⟩
          · have hDirF : (st.kind == .dir) = false := Bool.eq_false_iff.mpr hDir
            simp only [hDirF, Bool.false_eq_true, ↓reduceIte]
            rw [stateM_bind_run]
            have h1 := unlink_filteredPres fs hUnlOps (mockJoin child nm) true s
            cases hu : (fs.unlink (mockJoin child nm) true).run s with
            | mk ru su =>
              dsimp only at h1 ⊢
              rw [hu] at h1
              dsimp only at h1
              have hPresLock := nodesFilteredPres_mono (fun k hk => (hDisjLock k hk).2) h1
              have hPresPay := nodesFilteredPres_mono (fun k hk => (hDisjPay k (by rwa [← hPayEq])).2) h1
              cases ru with
              | error fe =>
                dsimp only
                rw [stateM_bind_run, stateM_pure_run]
                dsimp only
                rw [stateM_pure_run]
                exact ⟨_, su, stateM_pure_run _ _, hPresLock⟩
              | ok _ =>
                rw [stateM_bind_run, stateM_pure_run]
                dsimp only
                have hPaySu : ∃ ino c t m, lookupNode su.nodes payload = some (.file ino c t m) := by
                  rcases hPayNode with ⟨ino, c, t, m, hLookPay⟩
                  exact ⟨ino, c, t, m, by rw [nodesFilteredPres_lookupNode hPresPay payload (fun _ hk => hk), hLookPay]⟩
                obtain ⟨te, s', hRec, hPresRec⟩ := ih hrestV hRestNd hPayInRest su hPaySu
                exact ⟨te, s', hRec, nodesFilteredPres_trans hPresLock hPresRec⟩

/-- Spec 11: `cleanupStaleTempDirs` keeps any matching directory with an active lock regardless of age. -/
theorem proof_temp_cleanupStaleTempDirs_liveLockKeptRegardlessOfAge :
    AllPass (test_temp_cleanupStaleTempDirs_liveLockKeptRegardlessOfAge
      (S := TempMockState) Internal.mkApiM mockFs mockTime mockUuid mockEnv) := by
  dsimp only [test_temp_cleanupStaleTempDirs_liveLockKeptRegardlessOfAge, AllPass]
  intro s₀ root dirPrefix childName maxAgeSec ⟨hvr, hvp⟩ hcV hPref ⟨stRoot, hRoot, hRwx⟩ ⟨stChild, hChild, hcDir⟩ ⟨stLock, hLock, hlFile⟩
  have hRootPure : mockStatPure s₀ root = .ok stRoot := by rw [mockFs_stat_run] at hRoot; exact hRoot
  have hChildPure : mockLstatPure s₀ (mockFs.join root childName) = .ok stChild := by
    rw [mockFs_lstat_run] at hChild; exact hChild
  have hLockPure : mockLstatPure s₀ (mockFs.join (mockFs.join root childName) ".lock") = .ok stLock := by
    rw [mockFs_lstat_run] at hLock; exact hLock
  rw [mockFs_join_eq] at hChildPure hLockPure ⊢
  dsimp only [mockTime]
  rw [stateM_bind_run, stateM_get_run, stateM_pure_run]
  dsimp only
  rw [mockFs_lstat_run, hChildPure]
  dsimp only
  rw [allPass_assume]
  intro _
  have hrNe : root ≠ "" := validRoot_ne_empty root hvr
  have ⟨hcNe, _, _, hcSlash⟩ := validEntryName_parts childName hcV
  let child := mockJoin root childName
  let lockPath := mockJoin child ".lock"
  have hChildNorm : normKey child = child := normKey_mockJoin root childName hcNe hcSlash
  have hLockNorm : normKey lockPath = lockPath := normKey_mockJoin child ".lock" (by decide) (by decide)
  obtain ⟨ndChild, hLookChild, _⟩ := lookupNode_of_lstat_ok s₀ child stChild hChildPure
  obtain ⟨ndLock, hLookLock, hStLock⟩ := lookupNode_of_lstat_ok s₀ lockPath stLock hLockPure
  cases ndLock with
  | dir _ _ => simp [mockNodeStat] at hStLock; rw [← hStLock] at hlFile; cases hlFile
  | symlink _ _ => simp [mockNodeStat] at hStLock; rw [← hStLock] at hlFile; cases hlFile
  | file lockIno lockC lockT lockM =>
    by_cases hConf : mockHasConflict s₀.locks lockIno .shared = true
    · rw [mockFs_withFileLock_existing_conflict_run s₀ lockPath .shared false lockIno lockC lockT lockM hLockNorm hLookLock hConf]
      dsimp only
      intro hFalse; cases hFalse
    · have hConfF : mockHasConflict s₀.locks lockIno .shared = false := Bool.eq_false_iff.mpr hConf
      let sLock : TempMockState := { s₀ with locks := (lockIno, .shared) :: s₀.locks }
      have hRootLock : mockStatPure sLock root = .ok stRoot := hRootPure
      have hChildLock : lookupNode sLock.nodes child = some ndChild := hLookChild
      have hChildLockPure : mockLstatPure sLock child = .ok stChild := hChildPure
      have hLockLockPure : mockLstatPure sLock lockPath = .ok stLock := hLockPure
      have hLookLockLock : lookupNode sLock.nodes lockPath = some (.file lockIno lockC lockT lockM) := hLookLock
      obtain ⟨before, after, repBefore, sBefore, _, _, _, _, hBeforePres, hNotRmB, hNotKLB, _, _, hExec⟩ :=
        cleanupStaleTempDirs_split_exec mockFs sweepFsOps_mockFs sLock root dirPrefix childName maxAgeSec
          hvr hvp hcV stRoot hRootLock hRwx ndChild hChildLock
      obtain ⟨hPChild, _, hPLock, _⟩ := nodesFilteredPres_child_P (root := root) hcV
      have hLocksBefore : sBefore.locks = sLock.locks := hBeforePres.2.1
      have hLstatChildBefore : (mockFs.lstat child).run sBefore = (.ok stChild, sBefore) := by
        rw [nodesFilteredPres_lstat hBeforePres child hPChild, mockFs_lstat_run]
        dsimp only
        rw [hChildLockPure]
      have hLstatLockBefore : (mockFs.lstat lockPath).run sBefore = (.ok stLock, sBefore) := by
        rw [nodesFilteredPres_lstat hBeforePres lockPath hPLock, mockFs_lstat_run]
        dsimp only
        rw [hLockLockPure]
      have hLookLockBefore : lookupNode sBefore.nodes lockPath = some (.file lockIno lockC lockT lockM) := by
        rw [nodesFilteredPres_lookupNode hBeforePres lockPath hPLock]; exact hLookLockLock
      have hConfExclBefore : mockHasConflict sBefore.locks lockIno .exclusive = true := by
        rw [hLocksBefore]; simp [sLock, mockHasConflict]; exact Or.inl (Or.inl rfl)
      let nowSec := (mockTime.nowTimestamp.run sLock).1.toSecondsSinceUnixEpoch.val
      let repMid : CleanupReport := { repBefore with keptLocked := repBefore.keptLocked.push child }
      have hSweepMid : (Internal.sweepEntry mockFs root dirPrefix maxAgeSec nowSec repBefore childName).run sBefore =
          (repMid, sBefore) := by
        dsimp only [Internal.sweepEntry]
        rw [mockFs_join_eq]
        dsimp only [child, lockPath] at hLstatChildBefore hLstatLockBefore hLookLockBefore
        have hPrefF : (!dirPrefix.toList.isPrefixOf childName.toList) = false := by simp [hPref]
        simp only [hPrefF, Bool.false_eq_true, ↓reduceIte]
        rw [stateM_bind_run, hLstatChildBefore]
        dsimp only
        have hcDirF : (stChild.kind != EntryKind.dir) = false := by rw [hcDir]; rfl
        simp only [hcDirF, Bool.false_eq_true, ↓reduceIte]
        rw [stateM_bind_run, hLstatLockBefore]
        dsimp only
        have hlFileF : (stLock.kind != EntryKind.file) = false := by rw [hlFile]; rfl
        simp only [hlFileF, Bool.false_eq_true, ↓reduceIte]
        rw [stateM_bind_run, mockFs_tryWithFileLock_existing_conflict_run sBefore (mockJoin (mockJoin root childName) ".lock") .exclusive false
          lockIno lockC lockT lockM hLockNorm hLookLockBefore hConfExclBefore]
        exact stateM_pure_run _ _
      obtain ⟨hCleanRun, hAfterPres, hRmIff, hKLIff, _, _, _, _⟩ := hExec repMid sBefore hSweepMid
      let sFinal := (Internal.sweepEntries mockFs root dirPrefix maxAgeSec nowSec repMid after).run sBefore |>.2
      let repAfter := (Internal.sweepEntries mockFs root dirPrefix maxAgeSec nowSec repMid after).run sBefore |>.1
      let finalRep : CleanupReport :=
        { removed := (Internal.sortStrings repAfter.removed.toList).toArray
          keptLocked := (Internal.sortStrings repAfter.keptLocked.toList).toArray
          keptFresh := (Internal.sortStrings repAfter.keptFresh.toList).toArray
          skipped := (Internal.sortStrings repAfter.skipped.toList).toArray
          failed := repAfter.failed }
      have hTotPres : NodesFilteredPres (fun k => underDir child k = true ∨ normKey k = normKey root) sLock sFinal :=
        nodesFilteredPres_trans hBeforePres hAfterPres
      have hLookLockFin : lookupNode sFinal.nodes lockPath = some (.file lockIno lockC lockT lockM) := by
        rw [nodesFilteredPres_lookupNode hTotPres lockPath hPLock]; exact hLookLockLock
      have hConfExclFin : mockHasConflict sFinal.locks lockIno .exclusive = true := by
        rw [hTotPres.2.1]; simp [sLock, mockHasConflict]; exact Or.inl (Or.inl rfl)
      have hProbeRun : (mockFs.tryWithFileLock lockPath .exclusive false (pure (.ok ()))).run sFinal = (.ok none, sFinal) :=
        mockFs_tryWithFileLock_existing_conflict_run sFinal lockPath .exclusive false
          lockIno lockC lockT lockM hLockNorm hLookLockFin hConfExclFin (pure (.ok ()))
      have hLstatFin : (mockFs.lstat child).run sFinal = (.ok stChild, sFinal) := by
        rw [nodesFilteredPres_lstat hTotPres child hPChild, mockFs_lstat_run]
        dsimp only
        rw [hChildLockPure]
      have hBody :
          (do
            let rep ← (Internal.mkApiM mockFs mockTime mockUuid mockEnv).cleanupStaleTempDirs (some root) dirPrefix maxAgeSec
            let innerProbe ← mockFs.tryWithFileLock lockPath .exclusive false (pure (.ok ()))
            let stillExists ← mockFs.lstat child
            return (.ok (rep, innerProbe, stillExists.isOk) : Except FsError _)).run sLock =
          ((.ok (.ok finalRep, .ok none, true) : Except FsError _), { sFinal with locks := sFinal.locks }) := by
        dsimp only [child, lockPath, sFinal, finalRep, nowSec] at hProbeRun hLstatFin hCleanRun ⊢
        rw [stateM_bind_run, hCleanRun]
        dsimp only
        rw [stateM_bind_run]
        erw [hProbeRun]
        dsimp only
        rw [stateM_bind_run]
        erw [hLstatFin]
        dsimp only
        exact stateM_pure_run _ _
      rw [mockFs_withFileLock_existing_ok_run s₀ lockPath .shared false lockIno lockC lockT lockM hLockNorm hLookLock hConfF]
      dsimp only [sLock, lockPath, child] at hBody ⊢
      erw [hBody]
      dsimp only
      rw [allPass_assert, allPass_assert_end]
      have hKLMem : child ∈ repMid.keptLocked.toList := by simp [repMid, Array.toList_push]
      have hNotRmMem : ¬ (child ∈ repMid.removed.toList) := hNotRmB.mp
      exact ⟨⟨hKLIff.mpr hKLMem, fun h => hNotRmMem (hRmIff.mp h)⟩, ⟨rfl, rfl⟩, trivial⟩

/-- Non-vacuity `CanReach` witness for Spec 11 (`test_temp_cleanupStaleTempDirs_liveLockKeptRegardlessOfAge`). -/
theorem reach_temp_cleanupStaleTempDirs_liveLockKeptRegardlessOfAge :
    CanReach (test_temp_cleanupStaleTempDirs_liveLockKeptRegardlessOfAge
      (S := TempMockState) Internal.mkApiM mockFs mockTime mockUuid mockEnv) := by
  dsimp only [test_temp_cleanupStaleTempDirs_liveLockKeptRegardlessOfAge, CanReach]
  let s₀ : TempMockState :=
    { nodes := [("/tmp", .dir 0 0o755), ("/tmp/tmp-a", .dir 0 0o755), ("/tmp/tmp-a/.lock", .file 1 "" 0 0o644)]
      nowSec := 100 }
  refine ⟨s₀, ?_⟩
  dsimp only
  rw [canReach_nondet]; refine ⟨"/tmp", ?_⟩
  rw [canReach_nondet]; refine ⟨"tmp-", ?_⟩
  rw [canReach_nondet]; refine ⟨"tmp-a", ?_⟩
  rw [canReach_nondet]; refine ⟨10, ?_⟩
  rw [canReach_assume]; refine ⟨⟨by decide, by decide⟩, ?_⟩
  rw [canReach_assume]; refine ⟨by decide, ?_⟩
  rw [canReach_assume]; refine ⟨by decide, ?_⟩
  rw [canReach_assume]; refine ⟨⟨mockNodeStat (.dir 0 0o755), rfl, ⟨rfl, rfl, rfl, rfl⟩⟩, ?_⟩
  rw [canReach_assume]; refine ⟨⟨mockNodeStat (.dir 0 0o755), rfl, rfl⟩, ?_⟩
  rw [canReach_assume]; refine ⟨⟨mockNodeStat (.file 1 "" 0 0o644), rfl, rfl⟩, ?_⟩
  rw [mockFs_lstat_run]
  rw [show mockLstatPure s₀ (mockFs.join "/tmp" "tmp-a") = .ok (mockNodeStat (.dir 0 0o755)) from rfl]
  dsimp only
  have hTime : mockTime.nowTimestamp.run s₀ = (.ofSecondsSinceUnixEpoch (.ofInt 100), s₀) := rfl
  rw [hTime]
  dsimp only
  rw [canReach_assume]; refine ⟨by decide, ?_⟩
  try dsimp only
  have hRes :
      ((mockFs.withFileLock (mockFs.join (mockFs.join "/tmp" "tmp-a") ".lock") .shared false do
        let rep ← (Internal.mkApiM mockFs mockTime mockUuid mockEnv).cleanupStaleTempDirs (some "/tmp") "tmp-" 10
        let innerProbe ← mockFs.tryWithFileLock (mockFs.join (mockFs.join "/tmp" "tmp-a") ".lock") .exclusive false (pure (.ok ()))
        let stillExists ← mockFs.lstat (mockFs.join "/tmp" "tmp-a")
        return (Except.ok (rep, innerProbe, stillExists.isOk))).run s₀).1 =
      Except.ok (Except.ok { removed := #[], keptLocked := #["/tmp/tmp-a"], keptFresh := #[], skipped := #[], failed := #[] }, Except.ok none, true) := by
    rfl
  cases hRun : (mockFs.withFileLock (mockFs.join (mockFs.join "/tmp" "tmp-a") ".lock") .shared false do
        let rep ← (Internal.mkApiM mockFs mockTime mockUuid mockEnv).cleanupStaleTempDirs (some "/tmp") "tmp-" 10
        let innerProbe ← mockFs.tryWithFileLock (mockFs.join (mockFs.join "/tmp" "tmp-a") ".lock") .exclusive false (pure (.ok ()))
        let stillExists ← mockFs.lstat (mockFs.join "/tmp" "tmp-a")
        return (Except.ok (rep, innerProbe, stillExists.isOk))).run s₀ with
  | mk res snd =>
    rw [hRun] at hRes
    dsimp only at hRes
    rw [hRes]
    dsimp only
    rw [canReach_assert, canReach_assert_end]
    exact ⟨by decide, ⟨rfl, rfl⟩, trivial⟩

private theorem mockFs_lstat_notFound_lookup_none (s : TempMockState) (p : String) (e : FsError)
    (hl : ((mockFs.lstat p).run s).1 = .error e) :
    lookupNode s.nodes p = none := by
  rw [mockFs_lstat_run] at hl
  unfold mockLstatPure at hl
  cases hk : lookupNode s.nodes p with
  | none => rfl
  | some nd => simp [hk] at hl

private theorem lookupNode_filter_ne_none (nodes : List (String × MockNode)) (p : String) (hp : normKey p = p) :
    lookupNode (nodes.filter (fun e => normKey e.1 != p)) p = none := by
  unfold lookupNode
  dsimp only
  rw [hp]
  induction nodes with
  | nil => rfl
  | cons x xs ih =>
    rw [List.filter_cons]
    cases hb : (normKey x.1 == p) with
    | false =>
      by_cases hne : (normKey x.1 != p) = true
      · simp only [hne, ↓reduceIte]; rw [List.find?_cons, hb]; exact ih
      · simp only [Bool.eq_false_iff.mpr hne, Bool.false_eq_true, ↓reduceIte]; exact ih
    | true =>
      have hEq : normKey x.1 = p := beq_iff_eq.mp hb
      simp only [hEq, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
      exact ih

private theorem tryWithFileLock_excl_false_conflict (s : TempMockState) (p : String)
    (hp : normKey p = p) (ino : Nat) (c : String) (t : Int) (m : Nat)
    (hLook : lookupNode s.nodes p = some (.file ino c t m))
    (hTry : ((mockFs.tryWithFileLock p .exclusive false (pure (.ok ()))).run s).1 = .ok (some ())) :
    mockHasConflict s.locks ino .exclusive = false := by
  cases hc : mockHasConflict s.locks ino .exclusive with
  | false => rfl
  | true =>
    exfalso
    have hConf := mockFs_tryWithFileLock_existing_conflict_run s p .exclusive false ino c t m hp hLook hc (pure (.ok ()))
    rw [hConf] at hTry
    cases hTry

private theorem list_filter_filter_and {α : Type} (xs : List α) (p q : α → Bool) :
    (xs.filter p).filter q = xs.filter (fun x => p x && q x) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => cases hp : p x <;> cases hq : q x <;> simp [List.filter, hp, hq, ih]

private theorem string_bne_true_of_ne (a b : String) (h : a ≠ b) : (a != b) = true :=
  bne_iff_ne.mpr h

private theorem mockFs_listDir_with_locks (s : TempMockState) (locks' : List (Nat × LockMode))
    (dir : String) :
    let s' := { s with locks := locks' }
    (mockFs.listDir dir).run s' = (((mockFs.listDir dir).run s).1, s') := by
  intro s'
  have hListEq : ((mockFs.listDir dir).run s').1 = ((mockFs.listDir dir).run s).1 := by
    dsimp only [s', mockFs]
    rw [stateM_bind_run, stateM_get_run, stateM_bind_run, stateM_get_run]
    dsimp only
    cases lookupNode s.nodes (normKey dir) with
    | none => rw [stateM_pure_run, stateM_pure_run]
    | some node =>
      dsimp only
      split
      · rw [stateM_pure_run, stateM_pure_run]
      · split
        · rw [stateM_pure_run, stateM_pure_run]
        · rw [stateM_pure_run, stateM_pure_run]
  have hListSt : ((mockFs.listDir dir).run s').2 = s' := by
    dsimp only [s', mockFs]
    rw [stateM_bind_run, stateM_get_run]
    dsimp only
    cases lookupNode s.nodes (normKey dir) with
    | none => exact (stateM_pure_run _ _).symm ▸ rfl
    | some nd =>
      dsimp only
      split
      · rfl
      · split <;> rfl
  exact Prod.ext hListEq hListSt

private theorem spec12_sweepEntry_deadLock (s₀ sBefore : TempMockState)
    (root dirPrefix childName : String) (maxAgeSec : Nat) (nowSec : Int)
    (repBefore : CleanupReport) (stChild stLock : FileStat)
    (lockIno : Nat) (lockC : String) (lockT : Int) (lockM : Nat)
    (childNode : MockNode) (hcDir : pHasRwx stChild) (hlFile : stLock.kind = .file)
    (hvr : pValidRoot root = true) (hcV : pValidEntryName childName = true) (hPref : dirPrefix.toList.isPrefixOf childName.toList = true)
    (hLookChild : lookupNode s₀.nodes (mockJoin root childName) = some childNode)
    (hStChild : mockNodeStat childNode = stChild)
    (hLookLock : lookupNode s₀.nodes (mockJoin (mockJoin root childName) ".lock") = some (.file lockIno lockC lockT lockM))
    (hStLock : mockNodeStat (.file lockIno lockC lockT lockM) = stLock)
    (hListZero : ((mockFs.listDir (mockJoin root childName)).run s₀).1 = .ok #[".lock"])
    (hConfF : mockHasConflict s₀.locks lockIno .exclusive = false)
    (hBeforePres : NodesFilteredPres (fun k => underDir (mockJoin root childName) k = true ∨ normKey k = normKey root) s₀ sBefore) :
    let child := mockJoin root childName
    let lockPath := mockJoin child ".lock"
    ∃ sMid : TempMockState,
      (Internal.sweepEntry mockFs root dirPrefix maxAgeSec nowSec repBefore childName).run sBefore =
        ({ repBefore with removed := repBefore.removed.push child }, sMid) ∧
      NodesFilteredPres (fun k => normKey k = normKey root) sBefore sMid ∧
      lookupNode sMid.nodes child = none ∧
      lookupNode sMid.nodes lockPath = none := by
  intro child lockPath
  have hrNe : root ≠ "" := validRoot_ne_empty root hvr
  have ⟨hcNe, _, _, hcSlash⟩ := validEntryName_parts childName hcV
  have hcFullNe : child ≠ "" := mockJoin_ne_empty root childName hcNe
  have hcFullNorm : normKey child = child := normKey_mockJoin root childName hcNe hcSlash
  have hLockNorm : normKey lockPath = lockPath := normKey_mockJoin child ".lock" (by decide) (by decide)
  obtain ⟨hPChild, hPUnder, hPLock, hPRoot⟩ := nodesFilteredPres_child_P (root := root) hcV
  have hChildBefore : lookupNode sBefore.nodes child = some childNode := by
    rw [nodesFilteredPres_lookupNode hBeforePres child hPChild]; exact hLookChild
  have hLockBefore : lookupNode sBefore.nodes lockPath = some (.file lockIno lockC lockT lockM) := by
    rw [nodesFilteredPres_lookupNode hBeforePres lockPath hPLock]; exact hLookLock
  have hConfBefore : mockHasConflict sBefore.locks lockIno .exclusive = false := by
    rw [hBeforePres.2.1]; exact hConfF
  have hChildPure : mockLstatPure sBefore child = .ok stChild := by
    dsimp only [mockLstatPure]; rw [hChildBefore]; exact congrArg Except.ok hStChild
  have hLockPure : mockLstatPure sBefore lockPath = .ok stLock := by
    dsimp only [mockLstatPure]; rw [hLockBefore]; exact congrArg Except.ok hStLock
  have hListBefore : ((mockFs.listDir child).run sBefore).1 = .ok #[".lock"] := by
    rw [(nodesFilteredPres_listDir hBeforePres child hcFullNe hPChild hPUnder).1]; exact hListZero
  have hLockNeChild : normKey lockPath ≠ child :=
    payload_ne_dir root childName ".lock" hrNe hcNe hcSlash (by decide) (by decide)
  have hRootUnderChild : underDir child (normKey root) = false := by
    simpa [underDir, normKey_idem] using underDir_mockJoin_root_false root childName hrNe hcNe hcSlash
  have hRootNeLock : normKey (normKey root) ≠ lockPath := by
    intro hEq
    have hEq' : normKey (normKey root) = normKey lockPath := by
      simpa [hLockNorm, normKey_idem] using hEq
    have hu : underDir child (normKey root) = true := by
      rw [underDir_eq_of_normKey_eq child (normKey root) lockPath hEq']
      exact underDir_mockJoin_self child ".lock" hcFullNe hcFullNorm (mockJoin_ne_slash root childName hrNe hcNe) (by decide) (by decide)
    rw [hRootUnderChild] at hu
    exact Bool.noConfusion hu
  have hRootNeChild : normKey (normKey root) ≠ child := by
    intro hEq
    have hEq' : normKey (normKey root) = normKey child := by
      simpa [hcFullNorm, normKey_idem] using hEq
    have hu : underDir child (normKey root) = true := by
      rw [underDir_eq_of_normKey_eq child (normKey root) child hEq']
      exact underDir_refl child hcFullNorm
    rw [hRootUnderChild] at hu
    exact Bool.noConfusion hu
  let sLock := { sBefore with locks := (lockIno, .exclusive) :: sBefore.locks }
  have hListLock : (mockFs.listDir child).run sLock = (.ok #[".lock"], sLock) := by
    rw [mockFs_listDir_with_locks sBefore ((lockIno, .exclusive) :: sBefore.locks) child, hListBefore]
  let s1 := { sLock with nodes := sLock.nodes.filter (fun e => normKey e.1 != lockPath) }
  have hUnlinkLock : (mockFs.unlink lockPath true).run sLock = (.ok (), s1) :=
    mockFs_unlink_existing_run sLock lockPath true lockIno lockC lockT lockM hLockNorm hLockBefore
  have hNeLockOfChild : ∀ e : String × MockNode, e ∈ sBefore.nodes → normKey e.1 = normKey child →
      (normKey e.1 != lockPath) = true := fun e _ h =>
    string_bne_true_of_ne (normKey e.1) lockPath (by rw [h, hcFullNorm, ← hLockNorm]; exact ne_comm.mp hLockNeChild)
  have hChildDir : ∃ tChild mChild, childNode = .dir tChild mChild ∧ lookupNode s1.nodes child = some (.dir tChild mChild) := by
    cases childNode with
    | file _ _ _ _ => simp [mockNodeStat] at hStChild; rw [← hStChild] at hcDir; cases hcDir.1
    | symlink _ _ => simp [mockNodeStat] at hStChild; rw [← hStChild] at hcDir; cases hcDir.1
    | dir tC mC =>
      refine ⟨tC, mC, rfl, ?_⟩
      have hNodesEq1 : s1.nodes = sBefore.nodes.filter (fun e => normKey e.1 != lockPath) := rfl
      rw [hNodesEq1, lookupNode_filter_of_preserved sBefore.nodes _ child hNeLockOfChild]
      exact hChildBefore
  rcases hChildDir with ⟨tC, mC, _, hLookChild1⟩
  let s2 := { s1 with nodes := s1.nodes.filter (fun e => normKey e.1 != child) }
  have hRmdir : (mockFs.rmdir child).run s1 = (.ok (), s2) :=
    mockFs_rmdir_dir_run s1 child tC mC hcFullNorm hLookChild1
  have hRemLocked : (Internal.removeLockedTempDir mockFs child lockPath).run sLock = (.ok (.ok ()), s2) := by
    dsimp only [Internal.removeLockedTempDir]
    rw [stateM_bind_run, hListLock]
    dsimp only [Array.toList]
    rw [stateM_bind_run]
    dsimp only [Internal.removeNonLockChildren]
    simp only [beq_self_eq_true, ↓reduceIte]
    rw [stateM_pure_run]
    dsimp only
    rw [stateM_bind_run, hUnlinkLock]
    dsimp only
    rw [stateM_bind_run, hRmdir]
    dsimp only
    exact stateM_pure_run _ _
  let sMid := { s2 with locks := mockRemoveFirstLock lockIno .exclusive s2.locks }
  have hMidLocks : sMid.locks = sBefore.locks := by
    change mockRemoveFirstLock lockIno .exclusive sLock.locks = sBefore.locks
    exact mockRemoveFirstLock_head lockIno .exclusive sBefore.locks
  have hLookChildMid : lookupNode sMid.nodes child = none := by
    change lookupNode (s1.nodes.filter (fun e => normKey e.1 != child)) child = none
    exact lookupNode_filter_ne_none s1.nodes child hcFullNorm
  have hLookLockMid : lookupNode sMid.nodes lockPath = none := by
    have hLookLock1 : lookupNode s1.nodes lockPath = none := by
      change lookupNode (sLock.nodes.filter (fun e => normKey e.1 != lockPath)) lockPath = none
      exact lookupNode_filter_ne_none sLock.nodes lockPath hLockNorm
    change lookupNode (s1.nodes.filter (fun e => normKey e.1 != child)) lockPath = none
    exact lookupNode_filter_none_of_none s1.nodes _ lockPath hLookLock1
  have hNodesEq : sMid.nodes = sBefore.nodes.filter (fun e => (normKey e.1 != lockPath) && (normKey e.1 != child)) :=
    list_filter_filter_and sBefore.nodes (fun e => normKey e.1 != lockPath) (fun e => normKey e.1 != child)
  have hPresMid : NodesFilteredPres (fun k => normKey k = normKey root) sBefore sMid := by
    refine ⟨⟨fun k => (normKey k != lockPath) && (normKey k != child), fun k hk => by
      have hn1 : normKey k ≠ lockPath := by rw [hk, ← normKey_idem root]; exact hRootNeLock
      have hn2 : normKey k ≠ child := by rw [hk, ← normKey_idem root]; exact hRootNeChild
      rw [Bool.and_eq_true]
      exact ⟨string_bne_true_of_ne (normKey k) lockPath hn1, string_bne_true_of_ne (normKey k) child hn2⟩, hNodesEq⟩, hMidLocks, rfl, rfl, rfl, rfl⟩
  refine ⟨sMid, ?_, hPresMid, hLookChildMid, hLookLockMid⟩
  dsimp only [Internal.sweepEntry]
  rw [mockFs_join_eq]
  have hPrefF : (!dirPrefix.toList.isPrefixOf childName.toList) = false := by rw [hPref]; rfl
  simp only [hPrefF, Bool.false_eq_true, ↓reduceIte]
  rw [stateM_bind_run, mockFs_lstat_run, hChildPure]; dsimp only
  have hNotDir : (stChild.kind != .dir) = false := by rw [hcDir.1]; rfl
  simp only [hNotDir, Bool.false_eq_true, ↓reduceIte]
  rw [stateM_bind_run, mockFs_lstat_run, hLockPure]; dsimp only
  have hNotFile : (stLock.kind != .file) = false := by rw [hlFile]; rfl
  simp only [hNotFile, Bool.false_eq_true, ↓reduceIte]
  rw [stateM_bind_run, mockFs_tryWithFileLock_existing_ok_run sBefore lockPath .exclusive false lockIno lockC lockT lockM hLockNorm hLockBefore hConfBefore]
  rw [hRemLocked]
  dsimp only [Except.map]
  exact stateM_pure_run _ _

/-- Spec 12: `cleanupStaleTempDirs` immediately removes a dead locked temp directory regardless of `maxAgeSec`, leaving zero locks held. -/
theorem proof_temp_cleanupStaleTempDirs_deadLockRemovedImmediately :
    AllPass (test_temp_cleanupStaleTempDirs_deadLockRemovedImmediately
      (S := TempMockState) Internal.mkApiM mockFs mockTime mockUuid mockEnv) := by
  dsimp only [test_temp_cleanupStaleTempDirs_deadLockRemovedImmediately, AllPass]
  intro s₀ root dirPrefix childName maxAgeSec ⟨hvr, hvp, _⟩ hcV hPref ⟨stRoot, hRoot, hRwx⟩
    ⟨stChild, hChild, hcDir⟩ ⟨stLock, hLock, hlFile⟩ hListZero hTryExcl
  have hrNe : root ≠ "" := validRoot_ne_empty root hvr
  have ⟨hcNe, _, _, hcSlash⟩ := validEntryName_parts childName hcV
  let child := mockJoin root childName
  let lockPath := mockJoin child ".lock"
  have hChildNorm : normKey child = child := normKey_mockJoin root childName hcNe hcSlash
  have hLockNorm : normKey lockPath = lockPath := normKey_mockJoin child ".lock" (by decide) (by decide)
  have hRootPure : mockStatPure s₀ root = .ok stRoot := by rw [mockFs_stat_run] at hRoot; exact hRoot
  have hChildPure : mockLstatPure s₀ child = .ok stChild := by rw [mockFs_lstat_run, mockFs_join_eq] at hChild; exact hChild
  have hLockPure : mockLstatPure s₀ lockPath = .ok stLock := by rw [mockFs_lstat_run, mockFs_join_eq] at hLock; exact hLock
  rw [mockFs_join_eq] at hListZero hTryExcl ⊢
  obtain ⟨rootNode, hLookRoot, hStRoot⟩ := lookupNode_of_lstat_ok s₀ root stRoot hRootPure
  obtain ⟨childNode, hLookChild, hStChild⟩ := lookupNode_of_lstat_ok s₀ child stChild hChildPure
  obtain ⟨ndLock, hLookLock, hStLock⟩ := lookupNode_of_lstat_ok s₀ lockPath stLock hLockPure
  cases ndLock with
  | dir _ _ => simp [mockNodeStat] at hStLock; rw [← hStLock] at hlFile; cases hlFile
  | symlink _ _ => simp [mockNodeStat] at hStLock; rw [← hStLock] at hlFile; cases hlFile
  | file lockIno lockC lockT lockM =>
    have hConfF := tryWithFileLock_excl_false_conflict s₀ lockPath hLockNorm lockIno lockC lockT lockM hLookLock hTryExcl
    dsimp only [mockTime]
    rw [stateM_bind_run, stateM_get_run, stateM_pure_run]
    dsimp only
    rw [mockFs_lstat_run, hChildPure]
    dsimp only
    rw [allPass_assume]
    intro _
    obtain ⟨before, after, repBefore, sBefore, _, _, _, _, hBeforePres, _, hNotKLB, hNotKFB, _, hExec⟩ :=
      cleanupStaleTempDirs_split_exec mockFs sweepFsOps_mockFs s₀ root dirPrefix childName maxAgeSec
        hvr hvp hcV stRoot hRootPure hRwx childNode hLookChild
    obtain ⟨sMid, hSweepMid, hPresMid, hChildNoneMid, hLockNoneMid⟩ :=
      spec12_sweepEntry_deadLock s₀ sBefore root dirPrefix childName maxAgeSec
        ((mockTime.nowTimestamp.run s₀).1.toSecondsSinceUnixEpoch.val) repBefore stChild stLock
        lockIno lockC lockT lockM childNode hcDir hlFile hvr hcV hPref hLookChild hStChild
        hLookLock hStLock hListZero hConfF hBeforePres
    cases hAfterRun : (Internal.sweepEntries mockFs root dirPrefix maxAgeSec ((mockTime.nowTimestamp.run s₀).1.toSecondsSinceUnixEpoch.val) { repBefore with removed := repBefore.removed.push child } after).run sMid with
    | mk repAfter sFinal =>
      have hExec' := hExec { repBefore with removed := repBefore.removed.push child } sMid hSweepMid
      rw [hAfterRun] at hExec'
      dsimp only at hExec'
      obtain ⟨hCleanRun, hAfterPres, hRmIff, hKLIff, hKFIff, _, _, _⟩ := hExec'
      obtain ⟨hPChild, _, _, hPRoot⟩ := nodesFilteredPres_child_P (root := root) hcV
      let finalRep : CleanupReport :=
        { removed := (Internal.sortStrings repAfter.removed.toList).toArray
          keptLocked := (Internal.sortStrings repAfter.keptLocked.toList).toArray
          keptFresh := (Internal.sortStrings repAfter.keptFresh.toList).toArray
          skipped := (Internal.sortStrings repAfter.skipped.toList).toArray
          failed := repAfter.failed }
      rw [mkApiM_cleanupStaleTempDirs_eq] at hCleanRun
      dsimp only [StateT.run, mockTime] at hCleanRun
      dsimp only [Internal.mkApiM, StateT.run]
      rw [hCleanRun]
      dsimp only [AllPass]
      rw [allPass_assert, allPass_assert, allPass_assert_end]
      have hRmMem : pHasPath finalRep.removed child = true := hRmIff.mpr (by simp [child, Array.toList_push])
      have hNotKL : ¬ (pHasPath finalRep.keptLocked child = true) := fun h => hNotKLB.mp (hKLIff.mp h)
      have hNotKF : ¬ (pHasPath finalRep.keptFresh child = true) := fun h => hNotKFB.mp (hKFIff.mp h)
      have hChildNoneFin : lookupNode sFinal.nodes child = none := nodesFilteredPres_lookupNode_none hAfterPres child hChildNoneMid
      have hLookRootBefore : lookupNode sBefore.nodes (normKey root) = some rootNode := by
        rw [nodesFilteredPres_lookupNode hBeforePres (normKey root) (fun k hk => hPRoot k (by simpa [normKey_idem] using hk))]
        simpa [lookupNode, normKey_idem] using hLookRoot
      have hLookRootMid : lookupNode sMid.nodes (normKey root) = some rootNode := by
        rw [nodesFilteredPres_lookupNode hPresMid (normKey root) (fun k hk => by simpa [normKey_idem] using hk)]
        exact hLookRootBefore
      have hLookRootFin : lookupNode sFinal.nodes (normKey root) = some rootNode := by
        rw [nodesFilteredPres_lookupNode hAfterPres (normKey root) (fun k hk => hPRoot k (by simpa [normKey_idem] using hk))]
        exact hLookRootMid
      have hProbe := probe_exclusive_lock_after_cleanup_run sFinal root childName hrNe hcNe hcSlash
        rootNode stRoot hLookRootFin hStRoot hRwx hChildNoneFin
      refine ⟨?_, ?_, ?_, trivial⟩
      · exact ⟨hRmMem, hNotKL, hNotKF⟩
      · exact mockFs_lstat_isOk_false_of_lookup_none sFinal child hChildNoneFin
      · dsimp only [StateT.run] at hProbe
        exact hProbe

/-- Non-vacuity `CanReach` witness for Spec 12 (`test_temp_cleanupStaleTempDirs_deadLockRemovedImmediately`). -/
theorem reach_temp_cleanupStaleTempDirs_deadLockRemovedImmediately :
    CanReach (test_temp_cleanupStaleTempDirs_deadLockRemovedImmediately
      (S := TempMockState) Internal.mkApiM mockFs mockTime mockUuid mockEnv) := by
  dsimp only [test_temp_cleanupStaleTempDirs_deadLockRemovedImmediately, CanReach]
  let s₀ : TempMockState :=
    { nodes := [("/tmp", .dir 0 0o755), ("/tmp/tmp-a", .dir 0 0o755), ("/tmp/tmp-a/.lock", .file 1 "" 0 0o644)]
      nowSec := 5 }
  refine ⟨s₀, "/tmp", "tmp-", "tmp-a", 10, ⟨by decide, by decide, by decide⟩, by decide, by decide,
    ⟨mockNodeStat (.dir 0 0o755), rfl, ⟨rfl, rfl, rfl, rfl⟩⟩,
    ⟨mockNodeStat (.dir 0 0o755), rfl, ⟨rfl, rfl, rfl, rfl⟩⟩,
    ⟨mockNodeStat (.file 1 "" 0 0o644), rfl, rfl⟩, rfl, rfl, ?_⟩
  rw [show mockTime.nowTimestamp.run s₀ = (.ofSecondsSinceUnixEpoch (.ofInt 5), s₀) from rfl]
  rw [mockFs_lstat_run]
  rw [show mockLstatPure s₀ (mockFs.join "/tmp" "tmp-a") = .ok (mockNodeStat (.dir 0 0o755)) from rfl]
  dsimp only
  rw [canReach_assume]; refine ⟨by decide, ?_⟩
  try dsimp only
  have hRes :
      ((Internal.mkApiM mockFs mockTime mockUuid mockEnv).cleanupStaleTempDirs (some "/tmp") "tmp-" 10).run s₀ =
        (.ok { removed := #["/tmp/tmp-a"], keptLocked := #[], keptFresh := #[], skipped := #[], failed := #[] },
         { nodes := [("/tmp", .dir 0 0o755)], locks := [], nextInode := 1, tmpdir := none, nowSec := 5, nextUuid := 1 }) := rfl
  rw [hRes]
  dsimp only
  rw [canReach_assert, canReach_assert, canReach_assert_end]
  refine ⟨⟨by decide, by decide, by decide⟩, rfl, ?_, trivial⟩
  rfl

/-- Spec 13: for matching unlocked temp directories, `cleanupStaleTempDirs` keeps directories within `age ≤ maxAgeSec` and removes those with `age > maxAgeSec`. -/
theorem proof_temp_cleanupStaleTempDirs_graceWindowAndOldUnlocked :
    AllPass (test_temp_cleanupStaleTempDirs_graceWindowAndOldUnlocked
      (S := TempMockState) Internal.mkApiM mockFs mockTime mockUuid mockEnv) := by
  dsimp only [test_temp_cleanupStaleTempDirs_graceWindowAndOldUnlocked, AllPass]
  intro s₀ root dirPrefix childName maxAgeSec ⟨hvr, hvp⟩ hcV hPref ⟨stRoot, hRoot, hRwx⟩
    ⟨stChild, hChild, hcDir⟩ ⟨eNf, hLock, _⟩
  have hrNe : root ≠ "" := validRoot_ne_empty root hvr
  have ⟨hcNe, _, _, hcSlash⟩ := validEntryName_parts childName hcV
  let child := mockJoin root childName
  let lockPath := mockJoin child ".lock"
  have hRootPure : mockStatPure s₀ root = .ok stRoot := by rw [mockFs_stat_run] at hRoot; exact hRoot
  have hChildPure : mockLstatPure s₀ child = .ok stChild := by rw [mockFs_lstat_run, mockFs_join_eq] at hChild; exact hChild
  have hLockNone : lookupNode s₀.nodes lockPath = none := by
    rw [mockFs_join_eq] at hLock
    exact mockFs_lstat_notFound_lookup_none s₀ lockPath eNf hLock
  rw [mockFs_join_eq]
  obtain ⟨childNode, hLookChild, _⟩ := lookupNode_of_lstat_ok s₀ child stChild hChildPure
  dsimp only [mockTime]
  rw [stateM_bind_run, stateM_get_run, stateM_pure_run]
  dsimp only
  rw [mockFs_lstat_run, hChildPure]
  dsimp only
  let nowSec := (_root_.Std.Time.Timestamp.ofSecondsSinceUnixEpoch (_root_.Std.Time.Second.Offset.ofInt s₀.nowSec)).toSecondsSinceUnixEpoch.val
  let ageSec := nowSec - stChild.modifiedSec
  obtain ⟨before, after, repBefore, sBefore, _, _, _, _, hBeforePres, hNotRmB, _, hNotKFB, _, hExec⟩ :=
    cleanupStaleTempDirs_split_exec mockFs sweepFsOps_mockFs s₀ root dirPrefix childName maxAgeSec
      hvr hvp hcV stRoot hRootPure hRwx childNode hLookChild
  obtain ⟨hPChild, _, hPLock, _⟩ := nodesFilteredPres_child_P (root := root) hcV
  have hChildBefore : (mockFs.lstat child).run sBefore = (.ok stChild, sBefore) := by
    rw [nodesFilteredPres_lstat hBeforePres child hPChild, mockFs_lstat_run]; dsimp only; rw [hChildPure]
  have hLockBeforeNone : lookupNode sBefore.nodes lockPath = none :=
    nodesFilteredPres_lookupNode_none hBeforePres lockPath hLockNone
  have hLockBefore : (mockFs.lstat lockPath).run sBefore = (.error { kind := .notFound, path := some lockPath, message := "not found" }, sBefore) := by
    rw [mockFs_lstat_run]; unfold mockLstatPure; rw [hLockBeforeNone]
  have hPrefF : (!dirPrefix.toList.isPrefixOf childName.toList) = false := by rw [hPref]; rfl
  have hNotDir : (stChild.kind != .dir) = false := by rw [hcDir.1]; rfl
  have hNotNf : (FsErrorKind.notFound != .notFound) = false := rfl
  by_cases hFresh : ageSec ≤ (maxAgeSec : Int)
  · let repMid : CleanupReport := { repBefore with keptFresh := repBefore.keptFresh.push child }
    have hSweepMid : (Internal.sweepEntry mockFs root dirPrefix maxAgeSec nowSec repBefore childName).run sBefore =
        (repMid, sBefore) := by
      dsimp only [Internal.sweepEntry]
      rw [mockFs_join_eq]
      simp only [hPrefF, Bool.false_eq_true, ↓reduceIte]
      rw [stateM_bind_run, hChildBefore]; dsimp only
      simp only [hNotDir, Bool.false_eq_true, ↓reduceIte]
      rw [stateM_bind_run, hLockBefore]; dsimp only
      simp only [hNotNf, Bool.false_eq_true, ↓reduceIte]
      dsimp only [nowSec, ageSec] at hFresh ⊢
      simp only [hFresh, ↓reduceIte]
      exact stateM_pure_run _ _
    obtain ⟨hCleanRun, hAfterPres, hRmIff, _, hKFIff, _, _, _⟩ := hExec repMid sBefore hSweepMid
    let repAfter := (Internal.sweepEntries mockFs root dirPrefix maxAgeSec nowSec repMid after).run sBefore |>.1
    let sFinal := (Internal.sweepEntries mockFs root dirPrefix maxAgeSec nowSec repMid after).run sBefore |>.2
    let finalRep : CleanupReport :=
      { removed := (Internal.sortStrings repAfter.removed.toList).toArray
        keptLocked := (Internal.sortStrings repAfter.keptLocked.toList).toArray
        keptFresh := (Internal.sortStrings repAfter.keptFresh.toList).toArray
        skipped := (Internal.sortStrings repAfter.skipped.toList).toArray
        failed := repAfter.failed }
    rw [mkApiM_cleanupStaleTempDirs_eq] at hCleanRun
    dsimp only [StateT.run, mockTime] at hCleanRun
    dsimp only [Internal.mkApiM, StateT.run]
    rw [hCleanRun]
    dsimp only [AllPass]
    dsimp only [nowSec, ageSec] at hFresh
    simp only [hFresh, ↓reduceIte]
    rw [allPass_assert, allPass_assert_end]
    have hKFMem : pHasPath finalRep.keptFresh child = true := hKFIff.mpr (by simp [repMid, child, Array.toList_push])
    have hNotRm : ¬ (pHasPath finalRep.removed child = true) := fun h => hNotRmB.mp (hRmIff.mp h)
    have hAfterPres' : NodesFilteredPres (fun k => underDir child k = true ∨ normKey k = normKey root) sBefore sFinal := hAfterPres
    have hChildFin : ((mockFs.lstat child).run sFinal).1.isOk = true := by
      rw [nodesFilteredPres_lstat (nodesFilteredPres_trans hBeforePres hAfterPres') child hPChild, mockFs_lstat_run]
      dsimp only; rw [hChildPure]; rfl
    exact ⟨⟨hKFMem, hNotRm⟩, hChildFin, trivial⟩
  · have hStChild : mockNodeStat childNode = stChild := by
      dsimp only [mockLstatPure] at hChildPure
      rw [hLookChild] at hChildPure
      exact Except.ok.inj hChildPure
    have hRmUnder : (Internal.cleanupDirIgnoringNotFound mockFs child).run sBefore =
        (.ok (), { sBefore with nodes := sBefore.nodes.filter (fun e => !underDir child e.1) }) := by
      have hLookChildBefore : lookupNode sBefore.nodes child = some childNode := by
        rw [nodesFilteredPres_lookupNode hBeforePres child hPChild]
        exact hLookChild
      cases childNode with
      | file _ _ _ _ => dsimp only [mockNodeStat] at hStChild; rw [← hStChild] at hcDir; cases hcDir.1
      | symlink _ _ => dsimp only [mockNodeStat] at hStChild; rw [← hStChild] at hcDir; cases hcDir.1
      | dir tC mC =>
        exact cleanupDir_mock_run sBefore child (normKey_mockJoin root childName hcNe hcSlash) ⟨tC, mC, hLookChildBefore⟩
    let sMid := { sBefore with nodes := sBefore.nodes.filter (fun e => !underDir child e.1) }
    let repMid : CleanupReport := { repBefore with removed := repBefore.removed.push child }
    have hSweepMid : (Internal.sweepEntry mockFs root dirPrefix maxAgeSec nowSec repBefore childName).run sBefore =
        (repMid, sMid) := by
      dsimp only [Internal.sweepEntry]
      rw [mockFs_join_eq]
      simp only [hPrefF, Bool.false_eq_true, ↓reduceIte]
      rw [stateM_bind_run, hChildBefore]; dsimp only
      simp only [hNotDir, Bool.false_eq_true, ↓reduceIte]
      rw [stateM_bind_run, hLockBefore]; dsimp only
      simp only [hNotNf, Bool.false_eq_true, ↓reduceIte]
      dsimp only [nowSec, ageSec] at hFresh ⊢
      simp only [hFresh, ↓reduceIte]
      rw [stateM_bind_run, hRmUnder]
      exact stateM_pure_run _ _
    obtain ⟨hCleanRun, hAfterPres, hRmIff, _, hKFIff, _, _, _⟩ := hExec repMid sMid hSweepMid
    let repAfter := (Internal.sweepEntries mockFs root dirPrefix maxAgeSec nowSec repMid after).run sMid |>.1
    let sFinal := (Internal.sweepEntries mockFs root dirPrefix maxAgeSec nowSec repMid after).run sMid |>.2
    let finalRep : CleanupReport :=
      { removed := (Internal.sortStrings repAfter.removed.toList).toArray
        keptLocked := (Internal.sortStrings repAfter.keptLocked.toList).toArray
        keptFresh := (Internal.sortStrings repAfter.keptFresh.toList).toArray
        skipped := (Internal.sortStrings repAfter.skipped.toList).toArray
        failed := repAfter.failed }
    rw [mkApiM_cleanupStaleTempDirs_eq] at hCleanRun
    dsimp only [StateT.run, mockTime] at hCleanRun
    dsimp only [Internal.mkApiM, StateT.run]
    rw [hCleanRun]
    dsimp only [AllPass]
    dsimp only [nowSec, ageSec] at hFresh
    simp only [hFresh, ↓reduceIte]
    rw [allPass_assume]
    intro _
    rw [allPass_assert, allPass_assert_end]
    have hRmMem : pHasPath finalRep.removed child = true := hRmIff.mpr (by simp [repMid, child, Array.toList_push])
    have hNotKF : ¬ (pHasPath finalRep.keptFresh child = true) := fun h => hNotKFB.mp (hKFIff.mp h)
    have hChildNoneMid : lookupNode sMid.nodes child = none :=
      lookupNode_filter_none_of_underDir sBefore.nodes child child (underDir_refl child (normKey_mockJoin root childName hcNe hcSlash))
    have hAfterPres' : NodesFilteredPres (fun k => underDir child k = true ∨ normKey k = normKey root) sMid sFinal := hAfterPres
    have hChildNoneFin : lookupNode sFinal.nodes child = none :=
      nodesFilteredPres_lookupNode_none hAfterPres' child hChildNoneMid
    exact ⟨⟨hRmMem, hNotKF⟩, mockFs_lstat_isOk_false_of_lookup_none sFinal child hChildNoneFin, trivial⟩

/-- Non-vacuity `CanReach` witness for Spec 13 (`test_temp_cleanupStaleTempDirs_graceWindowAndOldUnlocked`). -/
theorem reach_temp_cleanupStaleTempDirs_graceWindowAndOldUnlocked :
    CanReach (test_temp_cleanupStaleTempDirs_graceWindowAndOldUnlocked
      (S := TempMockState) Internal.mkApiM mockFs mockTime mockUuid mockEnv) := by
  dsimp only [test_temp_cleanupStaleTempDirs_graceWindowAndOldUnlocked, CanReach]
  let s₀ : TempMockState :=
    { nodes := [("/tmp", .dir 0 0o755), ("/tmp/tmp-a", .dir 95 0o755)], nowSec := 100 }
  refine ⟨s₀, "/tmp", "tmp-", "tmp-a", 10, ⟨by decide, by decide⟩, by decide, by decide,
    ⟨mockNodeStat (.dir 0 0o755), rfl, ⟨rfl, rfl, rfl, rfl⟩⟩,
    ⟨mockNodeStat (.dir 95 0o755), rfl, ⟨rfl, rfl, rfl, rfl⟩⟩,
    ⟨{ kind := .notFound, path := some "/tmp/tmp-a/.lock", message := "not found" }, rfl, rfl⟩, ?_⟩
  rw [show mockTime.nowTimestamp.run s₀ = (.ofSecondsSinceUnixEpoch (.ofInt 100), s₀) from rfl]
  rw [mockFs_lstat_run]
  rw [show mockLstatPure s₀ (mockFs.join "/tmp" "tmp-a") = .ok (mockNodeStat (.dir 95 0o755)) from rfl]
  dsimp only
  have hRes :
      ((Internal.mkApiM mockFs mockTime mockUuid mockEnv).cleanupStaleTempDirs (some "/tmp") "tmp-" 10).run s₀ =
        (.ok { removed := #[], keptLocked := #[], keptFresh := #["/tmp/tmp-a"], skipped := #[], failed := #[] }, s₀) := rfl
  rw [hRes]
  dsimp only
  have hCond : (_root_.Std.Time.Timestamp.ofSecondsSinceUnixEpoch (_root_.Std.Time.Second.Offset.ofInt 100)).toSecondsSinceUnixEpoch.val -
      (mockNodeStat (.dir 95 0o755)).modifiedSec ≤ (↑10 : Int) := of_decide_eq_true rfl
  split
  · rw [canReach_assert, canReach_assert_end]
    exact ⟨⟨by decide, by decide⟩, rfl, trivial⟩
  · next hNot => exact absurd hCond hNot

/-- Spec 14: `cleanupStaleTempDirs` skips non-matching names, files, and symlinks without removing them, and returns sorted arrays. -/
theorem proof_temp_cleanupStaleTempDirs_scopeAndSymlinkSafety :
    AllPass (test_temp_cleanupStaleTempDirs_scopeAndSymlinkSafety
      (S := TempMockState) Internal.mkApiM mockFs mockTime mockUuid mockEnv) := by
  dsimp only [test_temp_cleanupStaleTempDirs_scopeAndSymlinkSafety, AllPass]
  intro s₀ root dirPrefix entryName maxAgeSec ⟨hvr, hvp⟩ hcV ⟨stRoot, hRoot, hRwx⟩ ⟨stChild, hChild, hSkipCond⟩
  let child := mockJoin root entryName
  have hRootPure : mockStatPure s₀ root = .ok stRoot := by rw [mockFs_stat_run] at hRoot; exact hRoot
  have hChildPure : mockLstatPure s₀ child = .ok stChild := by rw [mockFs_lstat_run, mockFs_join_eq] at hChild; exact hChild
  rw [mockFs_join_eq]
  obtain ⟨childNode, hLookChild, _⟩ := lookupNode_of_lstat_ok s₀ child stChild hChildPure
  obtain ⟨before, after, repBefore, sBefore, _, _, _, _, hBeforePres, hNotRmB, _, _, _, hExec⟩ :=
    cleanupStaleTempDirs_split_exec mockFs sweepFsOps_mockFs s₀ root dirPrefix entryName maxAgeSec
      hvr hvp hcV stRoot hRootPure hRwx childNode hLookChild
  obtain ⟨hPChild, _, _, _⟩ := nodesFilteredPres_child_P (root := root) hcV
  let repMid : CleanupReport := { repBefore with skipped := repBefore.skipped.push child }
  have hSweepMid : (Internal.sweepEntry mockFs root dirPrefix maxAgeSec
      ((mockTime.nowTimestamp.run s₀).1.toSecondsSinceUnixEpoch.val) repBefore entryName).run sBefore =
      (repMid, sBefore) := by
    dsimp only [Internal.sweepEntry]
    rw [mockFs_join_eq]
    rcases hSkipCond with hNotPref | hNotDir
    · have hPrefT : (!dirPrefix.toList.isPrefixOf entryName.toList) = true := by
        cases hb : dirPrefix.toList.isPrefixOf entryName.toList
        · rfl
        · exact absurd hb hNotPref
      simp only [hPrefT, ↓reduceIte]; exact stateM_pure_run _ _
    · by_cases hPref : (!dirPrefix.toList.isPrefixOf entryName.toList) = true
      · simp only [hPref, ↓reduceIte]; exact stateM_pure_run _ _
      · have hPrefF : (!dirPrefix.toList.isPrefixOf entryName.toList) = false := Bool.eq_false_iff.mpr hPref
        simp only [hPrefF, Bool.false_eq_true, ↓reduceIte]
        have hChildBefore : (mockFs.lstat child).run sBefore = (.ok stChild, sBefore) := by
          rw [nodesFilteredPres_lstat hBeforePres child hPChild, mockFs_lstat_run]; dsimp only; rw [hChildPure]
        rw [stateM_bind_run, hChildBefore]; dsimp only
        have hNotDirT : (stChild.kind != .dir) = true := by revert hNotDir; cases stChild.kind <;> decide
        simp only [hNotDirT, ↓reduceIte]; exact stateM_pure_run _ _
  obtain ⟨hCleanRun, hAfterPres, hRmIff, _, _, hSkIff, _, _⟩ := hExec repMid sBefore hSweepMid
  let repAfter := (Internal.sweepEntries mockFs root dirPrefix maxAgeSec ((mockTime.nowTimestamp.run s₀).1.toSecondsSinceUnixEpoch.val) repMid after).run sBefore |>.1
  let sFinal := (Internal.sweepEntries mockFs root dirPrefix maxAgeSec ((mockTime.nowTimestamp.run s₀).1.toSecondsSinceUnixEpoch.val) repMid after).run sBefore |>.2
  let finalRep : CleanupReport :=
    { removed := (Internal.sortStrings repAfter.removed.toList).toArray
      keptLocked := (Internal.sortStrings repAfter.keptLocked.toList).toArray
      keptFresh := (Internal.sortStrings repAfter.keptFresh.toList).toArray
      skipped := (Internal.sortStrings repAfter.skipped.toList).toArray
      failed := repAfter.failed }
  rw [mkApiM_cleanupStaleTempDirs_eq] at hCleanRun
  dsimp only [StateT.run, mockTime] at hCleanRun
  dsimp only [Internal.mkApiM, StateT.run, mockTime]
  rw [hCleanRun]
  dsimp only [AllPass]
  rw [allPass_assert, allPass_assert, allPass_assert_end]
  have hSkMem : pHasPath finalRep.skipped child = true := hSkIff.mpr (by simp [repMid, child, Array.toList_push])
  have hNotRm : ¬ (pHasPath finalRep.removed child = true) := fun h => hNotRmB.mp (hRmIff.mp h)
  have hAfterPres' : NodesFilteredPres (fun k => underDir child k = true ∨ normKey k = normKey root) sBefore sFinal := hAfterPres
  have hChildFin : ((mockFs.lstat child).run sFinal).1.isOk = true := by
    rw [nodesFilteredPres_lstat (nodesFilteredPres_trans hBeforePres hAfterPres') child hPChild, mockFs_lstat_run]
    dsimp only; rw [hChildPure]; rfl
  exact ⟨⟨hSkMem, hNotRm⟩, hChildFin,
    ⟨isSorted_sortStrings _, isSorted_sortStrings _, isSorted_sortStrings _, isSorted_sortStrings _⟩, trivial⟩

/-- Non-vacuity `CanReach` witness for Spec 14 (`test_temp_cleanupStaleTempDirs_scopeAndSymlinkSafety`). -/
theorem reach_temp_cleanupStaleTempDirs_scopeAndSymlinkSafety :
    CanReach (test_temp_cleanupStaleTempDirs_scopeAndSymlinkSafety
      (S := TempMockState) Internal.mkApiM mockFs mockTime mockUuid mockEnv) := by
  dsimp only [test_temp_cleanupStaleTempDirs_scopeAndSymlinkSafety, CanReach]
  let s₀ : TempMockState :=
    { nodes := [("/tmp", .dir 0 0o755), ("/tmp/keep-me", .dir 0 0o755)], nowSec := 100 }
  refine ⟨s₀, "/tmp", "tmp-", "keep-me", 10, ⟨by decide, by decide⟩, by decide,
    ⟨mockNodeStat (.dir 0 0o755), rfl, ⟨rfl, rfl, rfl, rfl⟩⟩,
    ⟨mockNodeStat (.dir 0 0o755), rfl, Or.inl (by decide)⟩, ?_⟩
  have hRes :
      ((Internal.mkApiM mockFs mockTime mockUuid mockEnv).cleanupStaleTempDirs (some "/tmp") "tmp-" 10).run s₀ =
        (.ok { removed := #[], keptLocked := #[], keptFresh := #[], skipped := #["/tmp/keep-me"], failed := #[] }, s₀) := rfl
  rw [hRes]
  dsimp only
  rw [canReach_assert, canReach_assert, canReach_assert_end]
  exact ⟨⟨by decide, by decide⟩, rfl, ⟨by decide, by decide, by decide, by decide⟩, trivial⟩

private theorem spec15_partialFail_exec (s₀ : TempMockState)
    (root dirPrefix childName : String) (maxAgeSec : Nat)
    (hvr : pValidRoot root = true) (hvp : pValidPrefix dirPrefix = true)
    (hcV : pValidEntryName childName = true) (hPref : dirPrefix.toList.isPrefixOf childName.toList = true)
    (stRoot stChild stLock : FileStat)
    (hRootPure : mockStatPure s₀ root = .ok stRoot) (hRwx : pHasRwx stRoot)
    (childNode : MockNode) (hLookChild : lookupNode s₀.nodes (mockJoin root childName) = some childNode)
    (hStChild : mockNodeStat childNode = stChild) (hcDir : pHasRwx stChild)
    (lockIno : Nat) (lockC : String) (lockT : Int) (lockM : Nat)
    (hLookLock : lookupNode s₀.nodes (mockJoin (mockJoin root childName) ".lock") = some (.file lockIno lockC lockT lockM))
    (hStLock : mockNodeStat (.file lockIno lockC lockT lockM) = stLock) (hlFile : stLock.kind = .file)
    (payIno : Nat) (payC : String) (payT : Int) (payM : Nat)
    (hLookPay : lookupNode s₀.nodes (mockJoin (mockJoin root childName) "locked_child.txt") = some (.file payIno payC payT payM))
    (hConfF : mockHasConflict s₀.locks lockIno .exclusive = false) :
    let child := mockJoin root childName
    let lockPath := mockJoin child ".lock"
    let payload := mockJoin child "locked_child.txt"
    let fsFailChild : FsApiM (StateM TempMockState) :=
      { mockFs with
        unlink := fun p miss =>
          if p == payload then pure (.error { kind := .permissionDenied, path := some p, message := "cannot unlink" })
          else mockFs.unlink p miss }
    ∃ rep s₁,
      ((Internal.mkApiM fsFailChild mockTime mockUuid mockEnv).cleanupStaleTempDirs (some root) dirPrefix maxAgeSec).run s₀ = (.ok rep, s₁) ∧
      ¬ pHasPath rep.removed child = true ∧
      ¬ pHasPath rep.keptFresh child = true ∧
      (!rep.failed.isEmpty) = true ∧
      ((mockFs.lstat lockPath).run s₁).1.isOk = true ∧
      ((mockFs.tryWithFileLock lockPath .exclusive false (pure (.ok ()))).run s₁).1 = .ok (some ()) := by
  intro child lockPath payload fsFailChild
  have hrNe : root ≠ "" := validRoot_ne_empty root hvr
  have ⟨hcNe, _, _, hcSlash⟩ := validEntryName_parts childName hcV
  have hcFullNe : child ≠ "" := mockJoin_ne_empty root childName hcNe
  have hLockNorm : normKey lockPath = lockPath := normKey_mockJoin child ".lock" (by decide) (by decide)
  have hFsJoin : fsFailChild.join = mockJoin := by dsimp only [fsFailChild, mockFs]; try rfl
  have hFsLstat : fsFailChild.lstat = mockFs.lstat := by dsimp only [fsFailChild]; try rfl
  have hFsStat : fsFailChild.stat = mockFs.stat := by dsimp only [fsFailChild]; try rfl
  have hFsList : fsFailChild.listDir = mockFs.listDir := by dsimp only [fsFailChild]; try rfl
  have hFsRm : fsFailChild.rmtree = mockFs.rmtree := by dsimp only [fsFailChild]; try rfl
  have hFsRmdir : fsFailChild.rmdir = mockFs.rmdir := by dsimp only [fsFailChild]; try rfl
  have hFsTry : ∀ {α : Type}, @fsFailChild.tryWithFileLock α = @mockFs.tryWithFileLock α :=
    fun {_} => by dsimp only [fsFailChild]; try rfl
  have hOpsFail : SweepFsOps fsFailChild :=
    ⟨hFsJoin, hFsStat, hFsLstat, hFsList, hFsTry, hFsRm, hFsRmdir, fun p miss s => by
      dsimp only [fsFailChild]
      split
      · exact Or.inr ⟨_, rfl⟩
      · exact Or.inl rfl⟩
  obtain ⟨before, after, repBefore, sBefore, _, _, _, _, hBeforePres, hNotRmB, _, hNotKFB, _, hExec⟩ :=
    cleanupStaleTempDirs_split_exec fsFailChild hOpsFail s₀ root dirPrefix childName maxAgeSec
      hvr hvp hcV stRoot hRootPure hRwx childNode hLookChild
  obtain ⟨hPChild, hPUnder, hPLock, _⟩ := nodesFilteredPres_child_P (root := root) hcV
  have hLookLockBefore : lookupNode sBefore.nodes lockPath = some (.file lockIno lockC lockT lockM) := by
    rw [nodesFilteredPres_lookupNode hBeforePres lockPath hPLock]; exact hLookLock
  have hConfBefore : mockHasConflict sBefore.locks lockIno .exclusive = false := by
    rw [hBeforePres.2.1]; exact hConfF
  have hChildLstatBefore : (mockFs.lstat child).run sBefore = (.ok stChild, sBefore) := by
    rw [nodesFilteredPres_lstat hBeforePres child hPChild, mockFs_lstat_run]
    dsimp only [mockLstatPure]; rw [hLookChild]; exact Prod.ext (congrArg Except.ok hStChild) rfl
  have hLockLstatBefore : (mockFs.lstat lockPath).run sBefore = (.ok stLock, sBefore) := by
    rw [nodesFilteredPres_lstat hBeforePres lockPath hPLock, mockFs_lstat_run]
    dsimp only [mockLstatPure]; rw [hLookLock]; exact Prod.ext (congrArg Except.ok hStLock) rfl
  let sLockBefore := { sBefore with locks := (lockIno, .exclusive) :: sBefore.locks }
  have hChildStatBefore : mockStatPure sBefore child = .ok stChild := by
    dsimp only [mockStatPure, mockLstatPure]
    rw [nodesFilteredPres_lookupNode hBeforePres child hPChild, hLookChild]
    exact congrArg Except.ok hStChild
  have ⟨hListChildBefore, hNdNames, hValidNames⟩ :=
    mockFs_listDir_run_of_rwx sBefore child stChild hChildStatBefore hcDir
  have hPayUnder : underDir child payload = true :=
    underDir_mockJoin_self child "locked_child.txt" hcFullNe (normKey_mockJoin root childName hcNe hcSlash)
      (mockJoin_ne_slash root childName hrNe hcNe) (by decide) (by decide)
  have hPPay : ∀ k, normKey k = normKey payload → underDir child k = true ∨ normKey k = normKey root :=
    fun k hk => hPUnder k (by rw [underDir_eq_of_normKey_eq _ k payload hk]; exact hPayUnder)
  have hPayBefore : lookupNode sBefore.nodes payload = some (.file payIno payC payT payM) := by
    rw [nodesFilteredPres_lookupNode hBeforePres payload hPPay]
    exact hLookPay
  have hPayMem : "locked_child.txt" ∈
      Internal.sortStrings (eraseDupStrings (sBefore.nodes.filterMap (fun e => mockParentChild (normKey child) e.1))) :=
    mockFs_listDir_mem_of_lookupNode sBefore child "locked_child.txt" hcFullNe (by decide) (.file payIno payC payT payM) hPayBefore
  let names := Internal.sortStrings (eraseDupStrings (sBefore.nodes.filterMap (fun e => mockParentChild (normKey child) e.1)))
  obtain ⟨te, sInner, hFailRun, hLockPresInner⟩ :=
    removeNonLockChildren_fail_with_lock_intact child payload hcFullNe rfl fsFailChild hFsLstat hFsJoin hFsRm
      (fun p miss s => by dsimp only [fsFailChild]; split <;> rfl)
      names hValidNames hNdNames hPayMem sLockBefore ⟨payIno, payC, payT, payM, hPayBefore⟩
  have hListLock : (mockFs.listDir child).run sLockBefore = (.ok names.toArray, sLockBefore) := by
    rw [mockFs_listDir_with_locks sBefore ((lockIno, .exclusive) :: sBefore.locks) child, congrArg Prod.fst hListChildBefore]
  have hRemLocked : (Internal.removeLockedTempDir fsFailChild child lockPath).run sLockBefore = (.ok (.error te), sInner) := by
    dsimp only [Internal.removeLockedTempDir]
    rw [hFsList, stateM_bind_run, hListLock]
    dsimp only [Array.toList]
    rw [stateM_bind_run, hFailRun]
    exact stateM_pure_run _ _
  let sMid := { sInner with locks := mockRemoveFirstLock lockIno .exclusive sInner.locks }
  let repMid : CleanupReport := { repBefore with failed := repBefore.failed.push te }
  have hSweepMid : (Internal.sweepEntry fsFailChild root dirPrefix maxAgeSec
      ((mockTime.nowTimestamp.run s₀).1.toSecondsSinceUnixEpoch.val) repBefore childName).run sBefore =
      (repMid, sMid) := by
    dsimp only [Internal.sweepEntry]
    rw [hFsJoin]
    have hPrefF : (!dirPrefix.toList.isPrefixOf childName.toList) = false := by rw [hPref]; rfl
    simp only [hPrefF, Bool.false_eq_true, ↓reduceIte]
    rw [hFsLstat, stateM_bind_run, hChildLstatBefore]; dsimp only
    have hNotDir : (stChild.kind != .dir) = false := by rw [hcDir.1]; rfl
    simp only [hNotDir, Bool.false_eq_true, ↓reduceIte]
    rw [stateM_bind_run, hLockLstatBefore]; dsimp only
    have hNotFile : (stLock.kind != .file) = false := by rw [hlFile]; rfl
    simp only [hNotFile, Bool.false_eq_true, ↓reduceIte]
    rw [hFsTry, stateM_bind_run, mockFs_tryWithFileLock_existing_ok_run sBefore lockPath .exclusive false lockIno lockC lockT lockM hLockNorm hLookLockBefore hConfBefore]
    rw [hRemLocked]
    dsimp only [Except.map]
    exact stateM_pure_run _ _
  cases hAfterRun : (Internal.sweepEntries fsFailChild root dirPrefix maxAgeSec ((mockTime.nowTimestamp.run s₀).1.toSecondsSinceUnixEpoch.val) repMid after).run sMid with
  | mk repAfter sFinal =>
    have hExec' := hExec repMid sMid hSweepMid
    rw [hAfterRun] at hExec'
    dsimp only at hExec'
    obtain ⟨hCleanRun, hAfterPres, hRmIff, _, hKFIff, _, hFailNonEmpty, _⟩ := hExec'
    let finalRep : CleanupReport :=
      { removed := (Internal.sortStrings repAfter.removed.toList).toArray
        keptLocked := (Internal.sortStrings repAfter.keptLocked.toList).toArray
        keptFresh := (Internal.sortStrings repAfter.keptFresh.toList).toArray
        skipped := (Internal.sortStrings repAfter.skipped.toList).toArray
        failed := repAfter.failed }
    have hNotRm : ¬ (pHasPath finalRep.removed child = true) := fun h => hNotRmB.mp (hRmIff.mp h)
    have hNotKF : ¬ (pHasPath finalRep.keptFresh child = true) := fun h => hNotKFB.mp (hKFIff.mp h)
    have hMidFail : repMid.failed.isEmpty = false := by
      simp only [repMid, Array.isEmpty, Array.size_push]
      exact decide_eq_false (Nat.succ_ne_zero _)
    have hFinFail : (!finalRep.failed.isEmpty) = true := by
      rw [hFailNonEmpty hMidFail]; rfl
    have hLockMidLocks : sMid.locks = sBefore.locks := by
      change mockRemoveFirstLock lockIno .exclusive sInner.locks = sBefore.locks
      rw [hLockPresInner.2.1]; exact mockRemoveFirstLock_head lockIno .exclusive sBefore.locks
    have hPresLock0B : NodesFilteredPres (fun k => normKey k = normKey lockPath) s₀ sBefore :=
      nodesFilteredPres_mono hPLock hBeforePres
    have hPresLockBM : NodesFilteredPres (fun k => normKey k = normKey lockPath) sBefore sMid :=
      ⟨hLockPresInner.1, hLockMidLocks, hLockPresInner.2.2.1, hLockPresInner.2.2.2.1, hLockPresInner.2.2.2.2.1, hLockPresInner.2.2.2.2.2⟩
    have hPresLockMF : NodesFilteredPres (fun k => normKey k = normKey lockPath) sMid sFinal :=
      nodesFilteredPres_mono hPLock hAfterPres
    have hPresLock0F := nodesFilteredPres_trans hPresLock0B (nodesFilteredPres_trans hPresLockBM hPresLockMF)
    have hLookLockFin : lookupNode sFinal.nodes lockPath = some (.file lockIno lockC lockT lockM) := by
      rw [nodesFilteredPres_lookupNode hPresLock0F lockPath (fun _ hk => hk)]; exact hLookLock
    have hLockFinIsOk : ((mockFs.lstat lockPath).run sFinal).1.isOk = true := by
      rw [mockFs_lstat_run]; unfold mockLstatPure; rw [hLookLockFin]; rfl
    have hConfFin : mockHasConflict sFinal.locks lockIno .exclusive = false := by
      rw [hPresLock0F.2.1]; exact hConfF
    have hTryFin : ((mockFs.tryWithFileLock lockPath .exclusive false (pure (.ok ()))).run sFinal).1 = .ok (some ()) := by
      rw [mockFs_tryWithFileLock_existing_ok_run sFinal lockPath .exclusive false lockIno lockC lockT lockM hLockNorm hLookLockFin hConfFin]
      rfl
    refine ⟨finalRep, sFinal, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact hCleanRun
    · exact hNotRm
    · exact hNotKF
    · exact hFinFail
    · exact hLockFinIsOk
    · exact hTryFin

/-- Spec 15: `cleanupStaleTempDirs` rejects non-regular `.lock` files into `failed` and preserves `.lock` intact and unlocked if deleting a payload fails. -/
theorem proof_temp_cleanupStaleTempDirs_nonRegularLockAndPartialFailureSafety :
    AllPass (test_temp_cleanupStaleTempDirs_nonRegularLockAndPartialFailureSafety
      (S := TempMockState) Internal.mkApiM mockFs mockTime mockUuid mockEnv) := by
  dsimp only [test_temp_cleanupStaleTempDirs_nonRegularLockAndPartialFailureSafety, AllPass]
  intro s₀ root dirPrefix childName maxAgeSec ⟨hvr, hvp⟩ hcV hPref ⟨stRoot, hRoot, hRwx⟩ ⟨stChild, hChild, hcDir⟩
  let child := mockJoin root childName
  let lockPath := mockJoin child ".lock"
  have hRootPure : mockStatPure s₀ root = .ok stRoot := by rw [mockFs_stat_run] at hRoot; exact hRoot
  have hChildPure : mockLstatPure s₀ child = .ok stChild := by rw [mockFs_lstat_run, mockFs_join_eq] at hChild; exact hChild
  rw [mockFs_join_eq]
  obtain ⟨childNode, hLookChild, hStChild⟩ := lookupNode_of_lstat_ok s₀ child stChild hChildPure
  rw [mockFs_lstat_run]
  cases hlLock : mockLstatPure s₀ lockPath with
  | error fe =>
    dsimp only
    intro hFalse; cases hFalse
  | ok stLock =>
    dsimp only
    by_cases hNotFile : (stLock.kind != .file) = true
    · simp only [hNotFile, ↓reduceIte]
      obtain ⟨before, after, repBefore, sBefore, _, _, _, _, hBeforePres, hNotRmB, _, hNotKFB, _, hExec⟩ :=
        cleanupStaleTempDirs_split_exec mockFs sweepFsOps_mockFs s₀ root dirPrefix childName maxAgeSec
          hvr hvp hcV stRoot hRootPure hRwx childNode hLookChild
      obtain ⟨hPChild, _, hPLock, _⟩ := nodesFilteredPres_child_P (root := root) hcV
      have hChildBefore : (mockFs.lstat child).run sBefore = (.ok stChild, sBefore) := by
        rw [nodesFilteredPres_lstat hBeforePres child hPChild, mockFs_lstat_run]; dsimp only; rw [hChildPure]
      have hLockBefore : (mockFs.lstat lockPath).run sBefore = (.ok stLock, sBefore) := by
        rw [nodesFilteredPres_lstat hBeforePres lockPath hPLock, mockFs_lstat_run]; dsimp only; rw [hlLock]
      let errExp : TempError := { kind := .invalidInput, path := some lockPath, message := "lock entry is not a regular file" }
      let repMid : CleanupReport := { repBefore with failed := repBefore.failed.push errExp }
      have hSweepMid : (Internal.sweepEntry mockFs root dirPrefix maxAgeSec
          ((mockTime.nowTimestamp.run s₀).1.toSecondsSinceUnixEpoch.val) repBefore childName).run sBefore =
          (repMid, sBefore) := by
        dsimp only [Internal.sweepEntry]
        rw [mockFs_join_eq]
        have hPrefF : (!dirPrefix.toList.isPrefixOf childName.toList) = false := by rw [hPref]; rfl
        have hNotDir : (stChild.kind != .dir) = false := by rw [hcDir.1]; rfl
        simp only [hPrefF, Bool.false_eq_true, ↓reduceIte]
        rw [stateM_bind_run, hChildBefore]; dsimp only
        simp only [hNotDir, Bool.false_eq_true, ↓reduceIte]
        rw [stateM_bind_run, hLockBefore]; dsimp only
        simp only [hNotFile, ↓reduceIte]
        exact stateM_pure_run _ _
      obtain ⟨hCleanRun, hAfterPres, hRmIff, _, hKFIff, _, _, hFailMem⟩ := hExec repMid sBefore hSweepMid
      let repAfter := (Internal.sweepEntries mockFs root dirPrefix maxAgeSec ((mockTime.nowTimestamp.run s₀).1.toSecondsSinceUnixEpoch.val) repMid after).run sBefore |>.1
      let sFinal := (Internal.sweepEntries mockFs root dirPrefix maxAgeSec ((mockTime.nowTimestamp.run s₀).1.toSecondsSinceUnixEpoch.val) repMid after).run sBefore |>.2
      let finalRep : CleanupReport :=
        { removed := (Internal.sortStrings repAfter.removed.toList).toArray
          keptLocked := (Internal.sortStrings repAfter.keptLocked.toList).toArray
          keptFresh := (Internal.sortStrings repAfter.keptFresh.toList).toArray
          skipped := (Internal.sortStrings repAfter.skipped.toList).toArray
          failed := repAfter.failed }
      rw [mkApiM_cleanupStaleTempDirs_eq] at hCleanRun
      dsimp only [StateT.run, mockTime] at hCleanRun
      dsimp only [Internal.mkApiM, StateT.run, mockTime]
      rw [hCleanRun]
      dsimp only [AllPass]
      rw [allPass_assert, allPass_assert, allPass_assert_end]
      have hNotRm : ¬ (pHasPath finalRep.removed child = true) := fun h => hNotRmB.mp (hRmIff.mp h)
      have hNotKF : ¬ (pHasPath finalRep.keptFresh child = true) := fun h => hNotKFB.mp (hKFIff.mp h)
      have hErrInFin : errExp ∈ finalRep.failed.toList := hFailMem errExp (by simp [repMid, Array.toList_push])
      have hAnyErr : finalRep.failed.any (fun e => e.kind == .invalidInput && e.path == some lockPath) = true := by
        rw [← Array.any_toList, List.any_eq_true]
        exact ⟨errExp, hErrInFin, by simp [errExp]; rfl⟩
      have hAfterPres' : NodesFilteredPres (fun k => underDir child k = true ∨ normKey k = normKey root) sBefore sFinal := hAfterPres
      have hChildFin : ((mockFs.lstat child).run sFinal).1.isOk = true := by
        rw [nodesFilteredPres_lstat (nodesFilteredPres_trans hBeforePres hAfterPres') child hPChild, mockFs_lstat_run]
        dsimp only; rw [hChildPure]; rfl
      exact ⟨⟨hNotRm, hNotKF⟩, hAnyErr, hChildFin, trivial⟩
    · have hNotFileF : (stLock.kind != .file) = false := Bool.eq_false_iff.mpr hNotFile
      have hlFile : stLock.kind = .file := by revert hNotFileF; cases stLock.kind <;> decide
      simp only [hNotFileF, Bool.false_eq_true, ↓reduceIte]
      intro ⟨stP, hPay, hpFile⟩ hTryExcl
      have hPayPure : mockLstatPure s₀ (mockJoin child "locked_child.txt") = .ok stP := by
        rw [mockFs_lstat_run] at hPay; exact hPay
      obtain ⟨ndPay, hLookPay, hStPay⟩ := lookupNode_of_lstat_ok s₀ (mockJoin child "locked_child.txt") stP hPayPure
      obtain ⟨ndLock, hLookLock, hStLock⟩ := lookupNode_of_lstat_ok s₀ lockPath stLock hlLock
      cases ndLock with
      | dir _ _ => simp [mockNodeStat] at hStLock; rw [← hStLock] at hlFile; cases hlFile
      | symlink _ _ => simp [mockNodeStat] at hStLock; rw [← hStLock] at hlFile; cases hlFile
      | file lockIno lockC lockT lockM =>
        cases ndPay with
        | dir _ _ => simp [mockNodeStat] at hStPay; rw [← hStPay] at hpFile; cases hpFile
        | symlink _ _ => simp [mockNodeStat] at hStPay; rw [← hStPay] at hpFile; cases hpFile
        | file payIno payC payT payM =>
          have hLockNorm : normKey lockPath = lockPath := normKey_mockJoin child ".lock" (by decide) (by decide)
          have hConfF := tryWithFileLock_excl_false_conflict s₀ lockPath hLockNorm lockIno lockC lockT lockM hLookLock hTryExcl
          obtain ⟨rep, s₁, hRun, h1, h2, h3, h4, h5⟩ := spec15_partialFail_exec s₀ root dirPrefix childName maxAgeSec hvr hvp hcV hPref
            stRoot stChild stLock hRootPure hRwx childNode hLookChild hStChild hcDir
            lockIno lockC lockT lockM hLookLock hStLock hlFile payIno payC payT payM hLookPay hConfF
          rw [mkApiM_cleanupStaleTempDirs_eq] at hRun
          dsimp only [StateT.run, mockTime] at hRun
          have hJoinEq : mockFs.join = mockJoin := rfl
          rw [hJoinEq] at hRun
          dsimp only [Internal.mkApiM, StateT.run, mockTime]
          rw [hRun]
          dsimp only [AllPass]
          rw [allPass_assert, allPass_assert, allPass_assert, allPass_assert_end]
          exact ⟨⟨h1, h2⟩, h3, h4, h5, trivial⟩

/-- Non-vacuity `CanReach` witness for Spec 15 (`test_temp_cleanupStaleTempDirs_nonRegularLockAndPartialFailureSafety`). -/
theorem reach_temp_cleanupStaleTempDirs_nonRegularLockAndPartialFailureSafety :
    CanReach (test_temp_cleanupStaleTempDirs_nonRegularLockAndPartialFailureSafety
      (S := TempMockState) Internal.mkApiM mockFs mockTime mockUuid mockEnv) := by
  dsimp only [test_temp_cleanupStaleTempDirs_nonRegularLockAndPartialFailureSafety, CanReach]
  let s₀ : TempMockState :=
    { nodes := [("/tmp", .dir 0 0o755), ("/tmp/tmp-a", .dir 0 0o755), ("/tmp/tmp-a/.lock", .symlink "/etc/passwd" 0)],
      nowSec := 100 }
  refine ⟨s₀, "/tmp", "tmp-", "tmp-a", 10, ⟨by decide, by decide⟩, by decide, by decide,
    ⟨mockNodeStat (.dir 0 0o755), rfl, ⟨rfl, rfl, rfl, rfl⟩⟩,
    ⟨mockNodeStat (.dir 0 0o755), rfl, ⟨rfl, rfl, rfl, rfl⟩⟩, ?_⟩
  rw [mockFs_lstat_run]
  rw [show mockLstatPure s₀ (mockFs.join (mockFs.join "/tmp" "tmp-a") ".lock") = .ok (mockNodeStat (.symlink "/etc/passwd" 0)) from rfl]
  dsimp only
  have hNotFile : ((mockNodeStat (.symlink "/etc/passwd" 0)).kind != .file) = true := rfl
  simp only [hNotFile, ↓reduceIte]
  have hRes :
      ((Internal.mkApiM mockFs mockTime mockUuid mockEnv).cleanupStaleTempDirs (some "/tmp") "tmp-" 10).run s₀ =
        (.ok { removed := #[], keptLocked := #[], keptFresh := #[], skipped := #[],
               failed := #[{ kind := .invalidInput, path := some "/tmp/tmp-a/.lock", message := "lock entry is not a regular file" }] }, s₀) := rfl
  rw [hRes]
  dsimp only
  rw [canReach_assert, canReach_assert, canReach_assert_end]
  simp only [mockFs_join_eq]
  rw [show mockJoin "/tmp" "tmp-a" = "/tmp/tmp-a" from rfl,
      show mockJoin "/tmp/tmp-a" ".lock" = "/tmp/tmp-a/.lock" from rfl]
  refine ⟨⟨by decide, by decide⟩, ?_, rfl, trivial⟩
  rw [← Array.any_toList, List.any_eq_true]
  exact ⟨_, List.Mem.head _, rfl⟩

end LeanSwe.Temp.Proofs
