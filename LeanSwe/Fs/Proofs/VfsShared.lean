import LeanSwe.Fs.Proofs.PurePathProofs

open Core
open Core.NondetTest
open LeanSwe.Fs

namespace LeanSwe.Fs.Proofs

open LeanSwe.Fs.ProofsInternal

/-- Node stored in the pure in-memory VFS model. -/
inductive VfsNode where
  /-- Regular file storing bytes and POSIX permission bits. -/
  | file (data : ByteArray) (mode : Nat)
  /-- Directory storing POSIX permission bits. -/
  | dir (mode : Nat)
  /-- Symbolic link storing target path and mode bits. -/
  | symlink (target : String) (mode : Nat)
  deriving BEq, DecidableEq


/-- Structural directory tree backing `VfsState` (makes orphan paths unrepresentable). -/
inductive VfsTree where
  /-- Regular file storing bytes and POSIX permission bits. -/
  | file (data : ByteArray) (mode : Nat)
  /-- Directory storing POSIX permission bits and child lookup. -/
  | dir (mode : Nat) (children : String → Option VfsTree)
  /-- Symbolic link storing target path and mode bits. -/
  | symlink (target : String) (mode : Nat)


end LeanSwe.Fs.Proofs

namespace LeanSwe.Fs.ProofsInternal

open LeanSwe.Fs.Proofs

/-- Helper declaration shared across `LeanSwe.Fs.Proofs` submodules. -/
def vfsTreeTopNode : VfsTree → VfsNode
  | .file bs m => .file bs m
  | .dir m _ => .dir m
  | .symlink t m => .symlink t m


/-- Helper declaration shared across `LeanSwe.Fs.Proofs` submodules. -/
def vfsEmptyDir (mode : Nat) : VfsTree :=
  .dir mode (fun _ => none)


/-- Helper declaration shared across `LeanSwe.Fs.Proofs` submodules. -/
def vfsTreeGet (t : VfsTree) : List String → Option VfsTree
  | [] => some t
  | seg :: rest =>
    match t with
    | .dir _ ch =>
      match ch seg with
      | none => none
      | some sub => vfsTreeGet sub rest
    | _ => none


/-- Helper declaration shared across `LeanSwe.Fs.Proofs` submodules. -/
def vfsTreeSet (t : VfsTree) (segs : List String) (v : Option VfsTree) : VfsTree :=
  match segs with
  | [] => v.getD t
  | [last] =>
    match t with
    | .dir m ch => .dir m (fun s => if s == last then v else ch s)
    | _ => t
  | seg :: rest =>
    match t with
    | .dir m ch =>
      .dir m (fun s =>
        if s == seg then
          match ch seg with
          | some sub => some (vfsTreeSet sub rest v)
          | none => none
        else ch s)
    | _ => t


end LeanSwe.Fs.ProofsInternal

namespace LeanSwe.Fs.Proofs

open LeanSwe.Fs.ProofsInternal

/-- Pure in-memory VFS state used to discharge `SpecTests` over `StateM VfsState`. -/
structure VfsState where
  /-- Root directory tree of the VFS. -/
  tree : VfsTree
  /-- Canonical paths tracked for directory listing. -/
  keys : List String
  /-- Current working directory (normalized absolute path). -/
  cwd : String
  /-- Monotonic counter for temporary sibling filenames. -/
  nonce : Nat
  /-- Active advisory locks `(handleId, canonicalPath, mode)`. -/
  locks : List (Nat × String × LockMode) := []
  /-- Monotonic counter for allocated lock handle IDs. -/
  nextLockId : Nat := 1


end LeanSwe.Fs.Proofs

namespace LeanSwe.Fs.ProofsInternal

open LeanSwe.Fs.Proofs

/-- Helper declaration shared across `LeanSwe.Fs.Proofs` submodules. -/
def vfsAbsNorm (cwd path : String) : String :=
  Internal.normPath (if Internal.isAbsolute path then path else Internal.join cwd path)


/-- Helper declaration shared across `LeanSwe.Fs.Proofs` submodules. -/
def vfsSplitSegs (absNorm : String) : List String :=
  match absNorm.toList with
  | '/' :: rest =>
    (Internal.splitCharList '/' rest).filterMap fun cs =>
      if cs.isEmpty then none else some (String.ofList cs)
  | _ => []


/-- Helper declaration shared across `LeanSwe.Fs.Proofs` submodules. -/
def isCanonPath (k : String) : Bool :=
  Internal.isAbsolute k && (Internal.normPath k == k)


/-- Helper declaration shared across `LeanSwe.Fs.Proofs` submodules. -/
def vfsTreeNodes (t : VfsTree) (k : String) : Option VfsNode :=
  if isCanonPath k then (vfsTreeGet t (vfsSplitSegs k)).map vfsTreeTopNode else none


end LeanSwe.Fs.ProofsInternal

namespace LeanSwe.Fs.Proofs

open LeanSwe.Fs.ProofsInternal

/-- Canonical path lookup view derived from `VfsState.tree`. -/
def VfsState.nodes (st : VfsState) : String → Option VfsNode :=
  vfsTreeNodes st.tree


end LeanSwe.Fs.Proofs

namespace LeanSwe.Fs.ProofsInternal

open LeanSwe.Fs.Proofs

/-- Helper declaration shared across `LeanSwe.Fs.Proofs` submodules. -/
def vfsChildPath (cur seg : String) : String :=
  if cur == "/" then "/" ++ seg else cur ++ "/" ++ seg


/-- Helper declaration shared across `LeanSwe.Fs.Proofs` submodules. -/
def vfsResolveSegs (nodes : String → Option VfsNode) (cur : String)
    (segs : List String) (followLast : Bool) : Nat → Except FsError (String × VfsNode)
  | 0 => .error { kind := .ioError, path := some cur, message := "too many levels of symbolic links" }
  | fuel + 1 =>
    match segs with
    | [] =>
      match nodes cur with
      | none => .error { kind := .notFound, path := some cur, message := s!"no such file or directory: {cur}" }
      | some (.symlink target m) =>
        if followLast then
          let par := (Internal.parent cur).getD "/"
          let nextAbs := Internal.normPath (if Internal.isAbsolute target then target else Internal.join par target)
          vfsResolveSegs nodes "/" (vfsSplitSegs nextAbs) true fuel
        else
          .ok (cur, .symlink target m)
      | some node => .ok (cur, node)
    | seg :: rest =>
      match nodes cur with
      | none => .error { kind := .notFound, path := some cur, message := s!"no such file or directory: {cur}" }
      | some (.dir mode) =>
        if (mode / 64) % 2 == 0 then
          .error { kind := .permissionDenied, path := some cur, message := s!"permission denied: {cur}" }
        else
          vfsResolveSegs nodes (vfsChildPath cur seg) rest followLast fuel
      | some (.symlink target _) =>
        let par := (Internal.parent cur).getD "/"
        let nextAbs := Internal.normPath (if Internal.isAbsolute target then target else Internal.join par target)
        vfsResolveSegs nodes "/" (vfsSplitSegs nextAbs ++ seg :: rest) followLast fuel
      | some (.file _ _) =>
        .error { kind := .notADirectory, path := some cur, message := s!"not a directory: {cur}" }


/-- Helper declaration shared across `LeanSwe.Fs.Proofs` submodules. -/
def vfsToStat : VfsNode → FileStat
  | .file bs m =>
    { kind := .file, byteSize := bs.size, mode := m,
      modifiedSec := 0, modifiedNsec := 0, accessedSec := 0, accessedNsec := 0 }
  | .dir m =>
    { kind := .dir, byteSize := 0, mode := m,
      modifiedSec := 0, modifiedNsec := 0, accessedSec := 0, accessedNsec := 0 }
  | .symlink _ m =>
    { kind := .symlink, byteSize := 0, mode := m,
      modifiedSec := 0, modifiedNsec := 0, accessedSec := 0, accessedNsec := 0 }


/-- Helper declaration shared across `LeanSwe.Fs.Proofs` submodules. -/
def vfsStatPure (st : VfsState) (follow : Bool) (path : String) : Except FsError FileStat :=
  match vfsResolveSegs st.nodes "/" (vfsSplitSegs (vfsAbsNorm st.cwd path)) follow 1024 with
  | .error e => .error e
  | .ok (_, node) => .ok (vfsToStat node)


/-- Helper declaration shared across `LeanSwe.Fs.Proofs` submodules. -/
def vfsRealPathPure (st : VfsState) (path : String) : Except FsError String :=
  match vfsResolveSegs st.nodes "/" (vfsSplitSegs (vfsAbsNorm st.cwd path)) true 1024 with
  | .error e => .error e
  | .ok (canon, _) => .ok canon


/-- Helper declaration shared across `LeanSwe.Fs.Proofs` submodules. -/
def vfsCreateDirPure (st : VfsState) (path : String) : Except FsError Unit × VfsState :=
  let abs := vfsAbsNorm st.cwd path
  match vfsResolveSegs st.nodes "/" (vfsSplitSegs abs) false 1024 with
  | .ok _ => (.error { kind := .alreadyExists, path := some path, message := s!"already exists: {path}" }, st)
  | .error e =>
    if e.kind != .notFound then
      (.error e, st)
    else
      match Internal.splitLastAux (vfsSplitSegs abs) [] with
      | none =>
        (.error { kind := .notFound, path := some path, message := s!"invalid path: {path}" }, st)
      | some (parSegs, lastSeg) =>
        match vfsResolveSegs st.nodes "/" parSegs true 512 with
        | .error pe => (.error pe, st)
        | .ok (parCanon, .dir parMode) =>
          if (parMode / 128) % 2 == 0 || (parMode / 64) % 2 == 0 then
            (.error { kind := .permissionDenied, path := some path, message := s!"permission denied: {path}" }, st)
          else
            let newKey := vfsChildPath parCanon lastSeg
            match st.nodes newKey with
            | some _ => (.error { kind := .alreadyExists, path := some path, message := s!"already exists: {path}" }, st)
            | none =>
              (.ok (), { st with
                tree := vfsTreeSet st.tree (vfsSplitSegs newKey) (some (vfsEmptyDir 0o755))
                keys := newKey :: st.keys })
        | .ok (parCanon, _) =>
          (.error { kind := .notADirectory, path := some parCanon, message := s!"not a directory: {parCanon}" }, st)


/-- Helper declaration shared across `LeanSwe.Fs.Proofs` submodules. -/
def vfsReadDirPure (st : VfsState) (path : String) : Except FsError (Array String) :=
  match vfsResolveSegs st.nodes "/" (vfsSplitSegs (vfsAbsNorm st.cwd path)) true 1024 with
  | .error e => .error e
  | .ok (canon, .dir mode) =>
    if (mode / 256) % 2 == 0 then
      .error { kind := .permissionDenied, path := some path, message := s!"permission denied: {path}" }
    else
      let prefixChars := (if canon == "/" then "/" else canon ++ "/").toList
      let children := st.keys.eraseDups.filterMap fun k =>
        if (st.nodes k).isSome then
          if k != canon && prefixChars.isPrefixOf k.toList then
            let restChars := k.toList.drop prefixChars.length
            if !restChars.isEmpty && !('/' ∈ restChars) then some (String.ofList restChars) else none
          else none
        else none
      .ok children.toArray
  | .ok (_, _) => .error { kind := .notADirectory, path := some path, message := s!"not a directory: {path}" }


/-- Helper declaration shared across `LeanSwe.Fs.Proofs` submodules. -/
def vfsWriteBytesPure (st : VfsState) (path : String) (bs : ByteArray) :
    Except FsError Unit × VfsState :=
  let abs := vfsAbsNorm st.cwd path
  match Internal.splitLastAux (vfsSplitSegs abs) [] with
  | none => (.error { kind := .isADirectory, path := some path, message := s!"is a directory: {path}" }, st)
  | some (parSegs, lastSeg) =>
    match vfsResolveSegs st.nodes "/" parSegs true 512 with
    | .error pe => (.error pe, st)
    | .ok (parCanon, .dir parMode) =>
      if (parMode / 128) % 2 == 0 || (parMode / 64) % 2 == 0 then
        (.error { kind := .permissionDenied, path := some path, message := s!"permission denied: {path}" }, st)
      else
        let targetKey := vfsChildPath parCanon lastSeg
        match vfsResolveSegs st.nodes "/" (vfsSplitSegs abs) true 1024 with
        | .ok (_, .dir _) => (.error { kind := .isADirectory, path := some path, message := s!"is a directory: {path}" }, st)
        | _ =>
          let finalKey := match st.nodes targetKey with
            | some (.symlink tgt _) => vfsAbsNorm parCanon tgt
            | _ => targetKey
          (.ok (), { st with
            tree := vfsTreeSet st.tree (vfsSplitSegs finalKey) (some (.file bs 0o644))
            keys := finalKey :: st.keys })
    | .ok (parCanon, _) =>
      (.error { kind := .notADirectory, path := some parCanon, message := s!"not a directory: {parCanon}" }, st)


/-- Helper declaration shared across `LeanSwe.Fs.Proofs` submodules. -/
def maxLockId : List (Nat × String × LockMode) → Nat
  | [] => 0
  | (i, _, _) :: rest => max i (maxLockId rest)


/-- Helper declaration shared across `LeanSwe.Fs.Proofs` submodules. -/
def freshLockId (st : VfsState) : Nat :=
  max (maxLockId st.locks) st.nextLockId + 1


/-- Helper declaration shared across `LeanSwe.Fs.Proofs` submodules. -/
def hasLockConflict (locks : List (Nat × String × LockMode)) (canon : String)
    (mode : LockMode) : Bool :=
  locks.any fun (_, p, m) => p == canon && (mode == .exclusive || m == .exclusive)


/-- Helper declaration shared across `LeanSwe.Fs.Proofs` submodules. -/
def isValidLockPath (path : String) : Bool :=
  let chars := path.toList
  !chars.isEmpty && !(chars.length > 1 && chars.getLast? == some '/')


/-- Helper declaration shared across `LeanSwe.Fs.Proofs` submodules. -/
def vfsAcquireLockPure (st : VfsState) (path : String) (mode : LockMode)
    (createIfMissing : Bool) (_nonBlocking : Bool) : Except FsError LockHandle × VfsState :=
  if !isValidLockPath path then
    (.error { kind := .invalidInput, path := some path, message := "invalid lock path" }, st)
  else
    let abs := vfsAbsNorm st.cwd path
    match vfsResolveSegs st.nodes "/" (vfsSplitSegs abs) false 1024 with
    | .ok (canon, .file _ _) =>
      if hasLockConflict st.locks canon mode then
        (.error { kind := .wouldBlock, path := some path, message := "resource temporarily unavailable" }, st)
      else
        let id := freshLockId st
        (.ok { handleId := id, path := path, mode := mode },
          { st with locks := (id, canon, mode) :: st.locks, nextLockId := id })
    | .ok (_, .dir _) =>
      (.error { kind := .isADirectory, path := some path, message := s!"is a directory: {path}" }, st)
    | .ok (_, .symlink _ _) =>
      (.error { kind := .invalidInput, path := some path, message := s!"symlink rejected for lock: {path}" }, st)
    | .error e =>
      if e.kind != .notFound then
        (.error e, st)
      else if !createIfMissing then
        (.error e, st)
      else
        match Internal.splitLastAux (vfsSplitSegs abs) [] with
        | none =>
          (.error { kind := .isADirectory, path := some path, message := s!"is a directory: {path}" }, st)
        | some (parSegs, lastSeg) =>
          match vfsResolveSegs st.nodes "/" parSegs true 512 with
          | .error pe => (.error pe, st)
          | .ok (parCanon, .dir parMode) =>
            if (parMode / 128) % 2 == 0 || (parMode / 64) % 2 == 0 then
              (.error { kind := .permissionDenied, path := some path, message := s!"permission denied: {path}" }, st)
            else
              let newKey := vfsChildPath parCanon lastSeg
              if hasLockConflict st.locks newKey mode then
                (.error { kind := .wouldBlock, path := some path, message := "resource temporarily unavailable" }, st)
              else
                let id := freshLockId st
                (.ok { handleId := id, path := path, mode := mode },
                  { st with
                    tree := vfsTreeSet st.tree (vfsSplitSegs newKey) (some (.file ByteArray.empty 0o644))
                    keys := newKey :: st.keys
                    locks := (id, newKey, mode) :: st.locks
                    nextLockId := id })
          | .ok (parCanon, _) =>
            (.error { kind := .notADirectory, path := some parCanon, message := s!"not a directory: {parCanon}" }, st)


/-- Helper declaration shared across `LeanSwe.Fs.Proofs` submodules. -/
def vfsReleaseLockPure (st : VfsState) (handle : LockHandle) :
    Except FsError Unit × VfsState :=
  if handle.handleId == 0 then
    (.error { kind := .invalidInput, path := some handle.path, message := "invalid lock handle" }, st)
  else if st.locks.any (fun (id, _, _) => id == handle.handleId) then
    (.ok (), { st with locks := st.locks.filter (fun (id, _, _) => id != handle.handleId) })
  else
    (.error { kind := .invalidInput, path := some handle.path, message := "unknown lock handle" }, st)


/-- Helper declaration shared across `LeanSwe.Fs.Proofs` submodules. -/
def isValidRawPath (path : String) : Bool :=
  let cs := path.toList
  !cs.isEmpty && !(Char.ofNat 0 ∈ cs) && !(cs.length > 1 && cs.getLast? == some '/')


/-- Helper declaration shared across `LeanSwe.Fs.Proofs` submodules. -/
def vfsReadBytesPure (st : VfsState) (path : String) : Except FsError ByteArray :=
  if !isValidRawPath path then
    .error { kind := .invalidInput, path := some path, message := s!"invalid path: {path}" }
  else
    let abs := vfsAbsNorm st.cwd path
    match vfsResolveSegs st.nodes "/" (vfsSplitSegs abs) true 1024 with
    | .error e => .error e
    | .ok (_, .file bs _) => .ok bs
    | .ok (_, .dir _) => .error { kind := .isADirectory, path := some path, message := s!"is a directory: {path}" }
    | .ok (_, _) => .error { kind := .notFound, path := some path, message := s!"not found: {path}" }


/-- Helper declaration shared across `LeanSwe.Fs.Proofs` submodules. -/
def vfsCreateFileNewPure (st : VfsState) (path : String) (bs : ByteArray) :
    Except FsError Unit × VfsState :=
  if !isValidRawPath path then
    (.error { kind := .invalidInput, path := some path, message := s!"invalid path: {path}" }, st)
  else
    let abs := vfsAbsNorm st.cwd path
    match vfsResolveSegs st.nodes "/" (vfsSplitSegs abs) false 1024 with
    | .ok _ =>
      (.error { kind := .alreadyExists, path := some path, message := s!"already exists: {path}" }, st)
    | .error e =>
      if e.kind != .notFound then
        (.error e, st)
      else
        match Internal.splitLastAux (vfsSplitSegs abs) [] with
        | none =>
          (.error { kind := .alreadyExists, path := some path, message := s!"already exists: {path}" }, st)
        | some (parSegs, lastSeg) =>
          match vfsResolveSegs st.nodes "/" parSegs true 1024 with
          | .error pe => (.error pe, st)
          | .ok (parCanon, .dir parMode) =>
            if (parMode / 128) % 2 == 0 || (parMode / 64) % 2 == 0 then
              (.error { kind := .permissionDenied, path := some path, message := s!"permission denied: {path}" }, st)
            else
              let newKey := vfsChildPath parCanon lastSeg
              (.ok (), { st with
                tree := vfsTreeSet st.tree (vfsSplitSegs newKey) (some (.file bs 0o644))
                keys := newKey :: st.keys })
          | .ok (parCanon, _) =>
            (.error { kind := .notADirectory, path := some parCanon, message := s!"not a directory: {parCanon}" }, st)


/-- Helper declaration shared across `LeanSwe.Fs.Proofs` submodules. -/
def vfsRenamePure (st : VfsState) (src dst : String) : Except FsError Unit × VfsState :=
  if !isValidRawPath src then
    (.error { kind := .invalidInput, path := some src, message := s!"invalid path: {src}" }, st)
  else if !isValidRawPath dst then
    (.error { kind := .invalidInput, path := some dst, message := s!"invalid path: {dst}" }, st)
  else
    let srcAbs := vfsAbsNorm st.cwd src
    let dstAbs := vfsAbsNorm st.cwd dst
    match vfsResolveSegs st.nodes "/" (vfsSplitSegs srcAbs) false 1024 with
    | .error e => (.error e, st)
    | .ok (srcCanon, srcNode) =>
      match Internal.splitLastAux (vfsSplitSegs dstAbs) [] with
      | none => (.error { kind := .isADirectory, path := some dst, message := s!"is a directory: {dst}" }, st)
      | some (dstParSegs, dstLastSeg) =>
        match vfsResolveSegs st.nodes "/" dstParSegs true 512 with
        | .error pe => (.error pe, st)
        | .ok (dstParCanon, .dir parMode) =>
          if (parMode / 128) % 2 == 0 || (parMode / 64) % 2 == 0 then
            (.error { kind := .permissionDenied, path := some dst, message := s!"permission denied: {dst}" }, st)
          else
            let dstKey := vfsChildPath dstParCanon dstLastSeg
            let srcIsDir := match srcNode with | .dir _ => true | _ => false
            let dstIsDir := match st.nodes dstKey with | some (.dir _) => true | _ => false
            if dstIsDir && !srcIsDir then
              (.error { kind := .isADirectory, path := some dst, message := s!"is a directory: {dst}" }, st)
            else if srcCanon == dstKey then
              (.ok (), st)
            else
              let moved := vfsTreeGet st.tree (vfsSplitSegs srcCanon)
              let tr₁ := vfsTreeSet st.tree (vfsSplitSegs srcCanon) none
              (.ok (), { st with
                tree := vfsTreeSet tr₁ (vfsSplitSegs dstKey) moved
                keys := dstKey :: st.keys })
        | .ok (dstParCanon, _) =>
          (.error { kind := .notADirectory, path := some dstParCanon, message := s!"not a directory: {dstParCanon}" }, st)


end LeanSwe.Fs.ProofsInternal

namespace LeanSwe.Fs.Proofs

open LeanSwe.Fs.ProofsInternal

/-- Pure single-step `RawFsOpsM (StateM VfsState)` backed by `VfsState`. -/
def vfsOps : RawFsOpsM (StateM VfsState) :=
  { mapRawError := Fs.Raw.Internal.mapRawError
    stat := fun follow path st => (vfsStatPure st follow path, st)
    readDir := fun path st => (vfsReadDirPure st path, st)
    createDir := fun path st => vfsCreateDirPure st path
    removeDir := fun path st =>
      let abs := vfsAbsNorm st.cwd path
      match vfsResolveSegs st.nodes "/" (vfsSplitSegs abs) false 1024 with
      | .error e => (.error e, st)
      | .ok (canon, .dir _) =>
        if canon == "/" then (.error { kind := .permissionDenied, path := some path, message := "cannot remove root" }, st)
        else (.ok (), { st with tree := vfsTreeSet st.tree (vfsSplitSegs canon) none })
      | .ok (_, _) => (.error { kind := .notADirectory, path := some path, message := s!"not a directory: {path}" }, st)
    unlinkFile := fun path st =>
      let abs := vfsAbsNorm st.cwd path
      match vfsResolveSegs st.nodes "/" (vfsSplitSegs abs) false 1024 with
      | .error e => (.error e, st)
      | .ok (_, .dir _) => (.error { kind := .isADirectory, path := some path, message := s!"is a directory: {path}" }, st)
      | .ok (canon, _) => (.ok (), { st with tree := vfsTreeSet st.tree (vfsSplitSegs canon) none })
    readBytes := fun path st => (vfsReadBytesPure st path, st)
    writeBytes := fun path bs st => vfsWriteBytesPure st path bs
    createFileNew := fun path bs st => vfsCreateFileNewPure st path bs
    appendText := fun path s st =>
      let abs := vfsAbsNorm st.cwd path
      match vfsResolveSegs st.nodes "/" (vfsSplitSegs abs) true 1024 with
      | .ok (canon, .file bs m) =>
        (.ok (), { st with tree := vfsTreeSet st.tree (vfsSplitSegs canon) (some (.file (bs ++ s.toUTF8) m)) })
      | .ok (_, .dir _) => (.error { kind := .isADirectory, path := some path, message := s!"is a directory: {path}" }, st)
      | _ => vfsWriteBytesPure st path s.toUTF8
    rename := fun src dst st => vfsRenamePure st src dst
    chmod := fun path mode st =>
      let abs := vfsAbsNorm st.cwd path
      match vfsResolveSegs st.nodes "/" (vfsSplitSegs abs) true 1024 with
      | .error e => (.error e, st)
      | .ok (canon, _) =>
        let updated := match vfsTreeGet st.tree (vfsSplitSegs canon) with
          | some (.file bs _) => some (.file bs mode)
          | some (.dir _ ch) => some (.dir mode ch)
          | some (.symlink t _) => some (.symlink t mode)
          | none => none
        (.ok (), { st with tree := vfsTreeSet st.tree (vfsSplitSegs canon) updated })
    symlink := fun target linkPath st =>
      let abs := vfsAbsNorm st.cwd linkPath
      match vfsResolveSegs st.nodes "/" (vfsSplitSegs abs) false 1024 with
      | .ok _ => (.error { kind := .alreadyExists, path := some linkPath, message := s!"already exists: {linkPath}" }, st)
      | .error e =>
        if e.kind != .notFound then (.error e, st)
        else (.ok (), { st with
          tree := vfsTreeSet st.tree (vfsSplitSegs abs) (some (.symlink target 0o777))
          keys := abs :: st.keys })
    readLink := fun path st =>
      let abs := vfsAbsNorm st.cwd path
      match vfsResolveSegs st.nodes "/" (vfsSplitSegs abs) false 1024 with
      | .error e => (.error e, st)
      | .ok (_, .symlink target _) => (.ok target, st)
      | .ok (_, _) => (.error { kind := .invalidInput, path := some path, message := s!"not a symlink: {path}" }, st)
    realPath := fun path st => (vfsRealPathPure st path, st)
    cwd := fun st => (.ok st.cwd, st)
    monotonicNonce := fun st => (st.nonce, { st with nonce := st.nonce + 1 })
    acquireLock := fun path mode createIfMissing nonBlocking st =>
      vfsAcquireLockPure st path mode createIfMissing nonBlocking
    releaseLock := fun handle st => vfsReleaseLockPure st handle }


/-- Generic `FsApiM (StateM VfsState)` built directly from `Internal.mkApiM vfsOps`. -/
def vfsApi : FsApiM (StateM VfsState) :=
  Internal.mkApiM vfsOps


end LeanSwe.Fs.Proofs

namespace LeanSwe.Fs.ProofsInternal

open LeanSwe.Fs.Proofs

/-- Helper declaration shared across `LeanSwe.Fs.Proofs` submodules. -/
theorem vfsResolveSegs_insert_fresh (nodes : String → Option VfsNode) (p : String) (v : VfsNode)
    (hp : nodes p = none) :
    ∀ fuel cur segs follow res,
      vfsResolveSegs nodes cur segs follow fuel = .ok res →
      vfsResolveSegs (fun k => if k == p then some v else nodes k) cur segs follow fuel = .ok res := by
  intro fuel
  induction fuel with
  | zero => intro _ _ _ _ h; simp [vfsResolveSegs] at h
  | succ fuel ih =>
    intro cur segs follow res hOk
    simp only [vfsResolveSegs] at hOk ⊢
    cases segs with
    | nil =>
      cases hNode : nodes cur with
      | none => simp [hNode] at hOk
      | some nd =>
        have hNe : cur ≠ p := fun heq => by subst heq; simp [hp] at hNode
        have hBeq : (cur == p) = false := beq_false_of_ne hNe
        simp only [hBeq, Bool.false_eq_true, ↓reduceIte]
        simp only [hNode] at hOk
        cases nd with
        | symlink target m =>
          cases follow
          · exact hOk
          · exact ih "/" _ true res hOk
        | file _ _ => exact hOk
        | dir _ => exact hOk
    | cons seg rest =>
      cases hNode : nodes cur with
      | none => simp [hNode] at hOk
      | some nd =>
        have hNe : cur ≠ p := fun heq => by subst heq; simp [hp] at hNode
        have hBeq : (cur == p) = false := beq_false_of_ne hNe
        simp only [hBeq, Bool.false_eq_true, ↓reduceIte]
        simp only [hNode] at hOk
        cases nd with
        | file _ _ => simp at hOk
        | dir mode =>
          by_cases hExec : ((mode / 64) % 2 == 0) = true
          · simp [hExec] at hOk
          · have hExecFalse : ((mode / 64) % 2 == 0) = false := Bool.eq_false_iff.mpr hExec
            simp only [hExecFalse, Bool.false_eq_true, ↓reduceIte]
            simp only [hExecFalse, Bool.false_eq_true, ↓reduceIte] at hOk
            exact ih (vfsChildPath cur seg) rest follow res hOk
        | symlink target _ =>
          exact ih "/" _ follow res hOk


/-- Helper declaration shared across `LeanSwe.Fs.Proofs` submodules. -/
theorem vfsResolveSegs_fuel_mono (nodes : String → Option VfsNode) :
    ∀ fuel₁ fuel₂ cur segs follow res,
      fuel₁ ≤ fuel₂ →
      vfsResolveSegs nodes cur segs follow fuel₁ = .ok res →
      vfsResolveSegs nodes cur segs follow fuel₂ = .ok res := by
  intro fuel₁
  induction fuel₁ with
  | zero => intro _ _ _ _ _ _ h; simp [vfsResolveSegs] at h
  | succ f1 ih =>
    intro fuel₂ cur segs follow res hle hOk
    cases fuel₂ with
    | zero => omega
    | succ f2 =>
      have hle' : f1 ≤ f2 := Nat.le_of_succ_le_succ hle
      simp only [vfsResolveSegs] at hOk ⊢
      cases segs with
      | nil =>
        cases hNode : nodes cur with
        | none => simp [hNode] at hOk
        | some nd =>
          simp only [hNode] at hOk ⊢
          cases nd with
          | symlink target m =>
            cases follow
            · exact hOk
            · exact ih f2 "/" _ true res hle' hOk
          | file _ _ => exact hOk
          | dir _ => exact hOk
      | cons seg rest =>
        cases hNode : nodes cur with
        | none => simp [hNode] at hOk
        | some nd =>
          simp only [hNode] at hOk ⊢
          cases nd with
          | file _ _ => simp at hOk
          | dir mode =>
            by_cases hExec : ((mode / 64) % 2 == 0) = true
            · simp [hExec] at hOk
            · have hExecFalse : ((mode / 64) % 2 == 0) = false := Bool.eq_false_iff.mpr hExec
              simp only [hExecFalse, Bool.false_eq_true, ↓reduceIte] at hOk ⊢
              exact ih f2 (vfsChildPath cur seg) rest follow res hle' hOk
          | symlink target _ =>
            exact ih f2 "/" _ follow res hle' hOk


/-- Helper declaration shared across `LeanSwe.Fs.Proofs` submodules. -/
theorem splitLastAux_spec {α : Type} (xs acc : List α) (init : List α) (last : α) :
    Internal.splitLastAux xs acc = some (init, last) →
    acc.reverse ++ xs = init ++ [last] := by
  induction xs generalizing acc with
  | nil => simp [Internal.splitLastAux]
  | cons x rest ih =>
    cases rest with
    | nil =>
      simp only [Internal.splitLastAux, Option.some.injEq, Prod.mk.injEq]
      rintro ⟨rfl, rfl⟩
      simp
    | cons y ys =>
      intro h
      have ih' := ih (x :: acc) h
      simpa using ih'


/-- Helper declaration shared across `LeanSwe.Fs.Proofs` submodules. -/
theorem vfsSplitSegs_joinSlashChars_valid (parts : List (List Char))
    (hParts : ∀ s ∈ parts, !s.isEmpty ∧ '/' ∉ s) :
    vfsSplitSegs (String.ofList ('/' :: Internal.joinSlashChars parts)) = parts.map String.ofList := by
  unfold vfsSplitSegs
  simp only [String.toList_ofList]
  cases parts with
  | nil => simp [Internal.joinSlashChars, Internal.splitCharList]
  | cons hd tl =>
    have hSplit := splitCharList_joinSlashChars (hd :: tl) (by simp) (fun s hs => (hParts s hs).2)
    rw [hSplit]
    simp only [List.filterMap_cons, List.map_cons]
    have hMap : ∀ xs : List (List Char), (∀ s ∈ xs, !s.isEmpty) →
        List.filterMap (fun cs => if cs.isEmpty then none else some (String.ofList cs)) xs = xs.map String.ofList := by
      intro xs hxs
      induction xs with
      | nil => rfl
      | cons x xt ihx =>
        rcases x with _ | ⟨c, cs⟩
        · have := hxs [] (by simp); simp at this
        · have hTail : List.filterMap (fun cs => if cs.isEmpty then none else some (String.ofList cs)) xt =
              xt.map String.ofList := ihx (fun y hy => hxs y (by simp [hy]))
          simpa using congrArg (String.ofList (c :: cs) :: ·) hTail
    rcases hd with _ | ⟨hc, hcs⟩
    · have := hParts [] (by simp); simp at this
    · have hTl : List.filterMap (fun cs => if cs.isEmpty then none else some (String.ofList cs)) tl =
          tl.map String.ofList := hMap tl (fun s hs => (hParts s (by simp [hs])).1)
      simpa using congrArg (String.ofList (hc :: hcs) :: ·) hTl


/-- Helper declaration shared across `LeanSwe.Fs.Proofs` submodules. -/
theorem vfsSplitSegs_normPath_valid (p : String) :
    ∀ s ∈ vfsSplitSegs (Internal.normPath p), Internal.validFileName s = true := by
  by_cases hAbs : Internal.isAbsChars p.toList = true
  · have hElem := collapseChars_elems_valid true (Internal.splitCharList '/' p.toList) []
      (fun _ h => by simp at h) (splitCharList_no_sep '/' p.toList)
    have hStack := collapseChars_validStack true (Internal.splitCharList '/' p.toList) []
      trivial (splitCharList_no_sep '/' p.toList)
    have hOrd : ValidOrder true (Internal.collapseChars true (Internal.splitCharList '/' p.toList) []) := by
      simpa using validStack_to_validOrder true _ hStack
    have hSp : vfsSplitSegs (Internal.normPath p) =
        (Internal.collapseChars true (Internal.splitCharList '/' p.toList) []).map String.ofList := by
      simp only [Internal.normPath, hAbs, ↓reduceIte]
      exact vfsSplitSegs_joinSlashChars_valid _ (fun s hs => ⟨(hElem s hs).1, (hElem s hs).2.2⟩)
    rw [hSp]
    intro seg hMem
    simp only [List.mem_map] at hMem
    rcases hMem with ⟨cs, hCsMem, rfl⟩
    have he := hElem cs hCsMem
    have hnd := hOrd cs hCsMem
    have hNeNil : cs ≠ [] := by cases cs <;> simp_all
    have hNeDot : cs ≠ ['.'] := by
      have := he.2.1
      cases hd : (cs == ['.']) <;> simp_all [beq_iff_eq]
    have hSlash : '/' ∉ cs := he.2.2
    have hEmpF : (String.ofList cs).toList.isEmpty = false := by
      rcases cs with _ | ⟨c, cs'⟩
      · exact absurd rfl hNeNil
      · simp
    have hBneDot : (String.ofList cs != ".") = true := by
      apply bne_iff_ne.mpr
      intro hEq
      apply hNeDot
      simpa using congrArg String.toList hEq
    have hBneDotDot : (String.ofList cs != "..") = true := by
      apply bne_iff_ne.mpr
      intro hEq
      apply hnd
      simpa [show "..".toList = ['.', '.'] by decide] using congrArg String.toList hEq
    simp only [Internal.validFileName, Bool.and_eq_true, Bool.not_eq_true']
    refine ⟨⟨⟨hEmpF, by simp [hSlash]⟩, ?_⟩, ?_⟩
    · exact bne_iff_ne.mpr (by simpa using hNeDot)
    · exact bne_iff_ne.mpr (by simpa [show "..".toList = ['.', '.'] by decide] using hnd)
  · have hNotAbs : Internal.isAbsChars p.toList = false := Bool.eq_false_iff.mpr hAbs
    have hElem := collapseChars_elems_valid false (Internal.splitCharList '/' p.toList) []
      (fun _ h => by simp at h) (splitCharList_no_sep '/' p.toList)
    simp only [Internal.normPath, hNotAbs, Bool.false_eq_true, ↓reduceIte]
    cases hParts : Internal.collapseChars false (Internal.splitCharList '/' p.toList) [] with
    | nil =>
      intro s hs
      simp only [List.isEmpty_nil, ↓reduceIte] at hs
      have hDot : vfsSplitSegs "." = [] := by decide
      rw [hDot] at hs
      simp at hs
    | cons hd tl =>
      have hHd := hElem hd (by rw [hParts]; simp)
      have hHdNe : hd ≠ [] := by cases hd <;> simp_all
      have hNA : Internal.isAbsChars (Internal.joinSlashChars (hd :: tl)) = false :=
        isAbsChars_joinSlashChars_head hHdNe hHd.2.2
      intro s hs
      simp only [List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte] at hs
      unfold vfsSplitSegs at hs
      cases hList : (String.ofList (Internal.joinSlashChars (hd :: tl))).toList with
      | nil => simp [hList] at hs
      | cons c cs =>
        by_cases hc : c = '/'
        · subst hc
          have : Internal.isAbsChars (Internal.joinSlashChars (hd :: tl)) = true := by
            simp only [String.toList_ofList] at hList
            simp [hList, Internal.isAbsChars]
          simp [hNA] at this
        · simp [hList, hc] at hs


/-- Helper declaration shared across `LeanSwe.Fs.Proofs` submodules. -/
theorem isCanonPath_normPath_parts (k : String) (hk : isCanonPath k = true) :
    let parts := (vfsSplitSegs k).map String.toList
    k = String.ofList ('/' :: Internal.joinSlashChars parts) ∧
    (∀ s ∈ parts, !s.isEmpty ∧ s != ['.'] ∧ '/' ∉ s ∧ s ≠ ['.', '.']) := by
  simp only [isCanonPath, Bool.and_eq_true, beq_iff_eq] at hk
  rcases hk with ⟨hAbs, hNorm⟩
  have hAbsChars : Internal.isAbsChars k.toList = true := hAbs
  have hElem := collapseChars_elems_valid true (Internal.splitCharList '/' k.toList) []
    (fun _ h => by simp at h) (splitCharList_no_sep '/' k.toList)
  have hStack := collapseChars_validStack true (Internal.splitCharList '/' k.toList) []
    trivial (splitCharList_no_sep '/' k.toList)
  have hOrd : ValidOrder true (Internal.collapseChars true (Internal.splitCharList '/' k.toList) []) := by
    simpa using validStack_to_validOrder true _ hStack
  have hKEq : k = String.ofList ('/' :: Internal.joinSlashChars
      (Internal.collapseChars true (Internal.splitCharList '/' k.toList) [])) := by
    calc k = Internal.normPath k := hNorm.symm
      _ = String.ofList ('/' :: Internal.joinSlashChars
          (Internal.collapseChars true (Internal.splitCharList '/' k.toList) [])) := by
        simp only [Internal.normPath, hAbsChars, ↓reduceIte]
  have hSp : vfsSplitSegs k =
      (Internal.collapseChars true (Internal.splitCharList '/' k.toList) []).map String.ofList := by
    calc vfsSplitSegs k
        = vfsSplitSegs (String.ofList ('/' :: Internal.joinSlashChars
            (Internal.collapseChars true (Internal.splitCharList '/' k.toList) []))) := congrArg vfsSplitSegs hKEq
      _ = (Internal.collapseChars true (Internal.splitCharList '/' k.toList) []).map String.ofList :=
        vfsSplitSegs_joinSlashChars_valid _ (fun s hs => ⟨(hElem s hs).1, (hElem s hs).2.2⟩)
  have hPartsEq : (vfsSplitSegs k).map String.toList =
      Internal.collapseChars true (Internal.splitCharList '/' k.toList) [] := by
    rw [hSp, List.map_map]
    simp [Function.comp_def]
  refine ⟨?_, ?_⟩
  · rw [hPartsEq]; exact hKEq
  · intro s hs
    rw [hPartsEq] at hs
    exact ⟨(hElem s hs).1, (hElem s hs).2.1, (hElem s hs).2.2, hOrd s hs⟩


/-- Helper declaration shared across `LeanSwe.Fs.Proofs` submodules. -/
theorem isCanonPath_of_parts (parts : List (List Char))
    (hParts : ∀ s ∈ parts, !s.isEmpty ∧ s != ['.'] ∧ '/' ∉ s ∧ s ≠ ['.', '.']) :
    isCanonPath (String.ofList ('/' :: Internal.joinSlashChars parts)) = true := by
  simp only [isCanonPath, Bool.and_eq_true, beq_iff_eq]
  refine ⟨by simp [Internal.isAbsolute, Internal.isAbsChars], ?_⟩
  simp only [Internal.normPath, String.toList_ofList, Internal.isAbsChars, ↓reduceIte]
  have hSplitNil : Internal.splitCharList '/' ('/' :: Internal.joinSlashChars parts) =
      [] :: Internal.splitCharList '/' (Internal.joinSlashChars parts) := by
    simp [Internal.splitCharList]
  have hStepNil : Internal.collapseChars true ([] :: Internal.splitCharList '/' (Internal.joinSlashChars parts)) [] =
      Internal.collapseChars true (Internal.splitCharList '/' (Internal.joinSlashChars parts)) [] := by
    simp [Internal.collapseChars]
  rw [hSplitNil, hStepNil]
  cases parts with
  | nil => simp [Internal.joinSlashChars, Internal.splitCharList, Internal.collapseChars]
  | cons hd tl =>
    have hSp := splitCharList_joinSlashChars (hd :: tl) (by simp) (fun s hs => (hParts s hs).2.2.1)
    have hNoop := collapseChars_noop true (hd :: tl) []
      (fun s hs => ⟨(hParts s hs).1, (hParts s hs).2.1⟩)
      (Or.inl (fun s hs => (hParts s hs).2.2.2))
    rw [hSp, hNoop]
    simp


/-- Helper declaration shared across `LeanSwe.Fs.Proofs` submodules. -/
theorem validFileName_charList (seg : String) (h : Internal.validFileName seg = true) :
    !seg.toList.isEmpty ∧ seg.toList != ['.'] ∧ '/' ∉ seg.toList ∧ seg.toList ≠ ['.', '.'] := by
  simp only [Internal.validFileName, Bool.and_eq_true, Bool.not_eq_true', bne_iff_ne, ne_eq,
    decide_eq_false_iff_not] at h
  rcases h with ⟨⟨⟨hEmp, hSlash⟩, hDot⟩, hDotDot⟩
  have hNeNil : seg.toList ≠ [] := by
    intro hn
    rw [hn] at hEmp
    simp at hEmp
  have hNotEmp : (!seg.toList.isEmpty) = true := by cases htl : seg.toList <;> simp_all
  have hNotDotL : (seg.toList != ['.']) = true := by
    apply bne_iff_ne.mpr
    intro heq
    apply hDot
    rw [← String.ofList_toList (s := seg), heq]
    rfl
  have hNotDD : seg.toList ≠ ['.', '.'] := by
    intro heq
    apply hDotDot
    rw [← String.ofList_toList (s := seg), heq]
    rfl
  exact ⟨hNotEmp, hNotDotL, hSlash, hNotDD⟩


/-- Helper declaration shared across `LeanSwe.Fs.Proofs` submodules. -/
theorem joinSlashChars_append_singleton (xs : List (List Char)) (hxs : xs ≠ []) (last : List Char) :
    Internal.joinSlashChars (xs ++ [last]) = Internal.joinSlashChars xs ++ '/' :: last := by
  induction xs with
  | nil => exact absurd rfl hxs
  | cons hd tl ih =>
    cases tl with
    | nil => simp [Internal.joinSlashChars]
    | cons b bs =>
      have hSub : b :: (bs ++ [last]) = (b :: bs) ++ [last] := rfl
      simp only [List.cons_append, Internal.joinSlashChars]
      rw [hSub, ih (by simp)]
      simp [List.append_assoc]


/-- Helper declaration shared across `LeanSwe.Fs.Proofs` submodules. -/
theorem vfsChildPath_valid (cur seg : String)
    (hCur : isCanonPath cur = true) (hSeg : Internal.validFileName seg = true) :
    isCanonPath (vfsChildPath cur seg) = true ∧
    vfsSplitSegs (vfsChildPath cur seg) = vfsSplitSegs cur ++ [seg] := by
  obtain ⟨hCurEq, hParts⟩ := isCanonPath_normPath_parts cur hCur
  have hSegL := validFileName_charList seg hSeg
  have hNewParts : ∀ s ∈ (vfsSplitSegs cur).map String.toList ++ [seg.toList],
      !s.isEmpty ∧ s != ['.'] ∧ '/' ∉ s ∧ s ≠ ['.', '.'] := by
    intro s hs
    simp only [List.mem_append, List.mem_singleton] at hs
    rcases hs with hs | rfl
    · exact hParts s hs
    · exact hSegL
  have hChildEq : vfsChildPath cur seg =
      String.ofList ('/' :: Internal.joinSlashChars ((vfsSplitSegs cur).map String.toList ++ [seg.toList])) := by
    cases hSp : vfsSplitSegs cur with
    | nil =>
      have hCurRoot : cur = "/" := by
        rw [hCurEq, hSp]
        rfl
      simp only [vfsChildPath, hCurRoot, beq_self_eq_true, ↓reduceIte, Internal.joinSlashChars, List.nil_append, List.map_nil]
      apply String.ext_iff.mpr
      simp [String.toList_append, show "/".toList = ['/'] by decide]
    | cons sh st =>
      have hCurNeRoot : cur ≠ "/" := by
        intro heq
        have : vfsSplitSegs cur = [] := by rw [heq]; decide
        simp [this] at hSp
      have hBeqF : (cur == "/") = false := beq_false_of_ne hCurNeRoot
      simp only [vfsChildPath, hBeqF, Bool.false_eq_true, ↓reduceIte]
      have hApp := joinSlashChars_append_singleton ((sh :: st).map String.toList) (by simp) seg.toList
      rw [hCurEq]
      simp only [hSp, List.map_cons] at hApp ⊢
      apply String.ext_iff.mpr
      simp only [String.toList_append, String.toList_ofList, show "/".toList = ['/'] by decide]
      rw [hApp]
      simp [List.append_assoc]
  refine ⟨?_, ?_⟩
  · rw [hChildEq]; exact isCanonPath_of_parts _ hNewParts
  · rw [hChildEq, vfsSplitSegs_joinSlashChars_valid _ (fun s hs => ⟨(hNewParts s hs).1, (hNewParts s hs).2.2.1⟩)]
    simp [List.map_append, List.map_map, Function.comp_def]


/-- Helper declaration shared across `LeanSwe.Fs.Proofs` submodules. -/
theorem vfsResolveSegs_isCanon (nodes : String → Option VfsNode) :
    ∀ fuel cur segs follow res,
      isCanonPath cur = true →
      (∀ s ∈ segs, Internal.validFileName s = true) →
      vfsResolveSegs nodes cur segs follow fuel = .ok res →
      isCanonPath res.1 = true := by
  intro fuel
  induction fuel with
  | zero => intro _ _ _ _ _ _ h; simp [vfsResolveSegs] at h
  | succ fuel ih =>
    intro cur segs follow res hCur hSegs hOk
    simp only [vfsResolveSegs] at hOk
    cases segs with
    | nil =>
      cases hNd : nodes cur with
      | none => simp [hNd] at hOk
      | some nd =>
        simp only [hNd] at hOk
        cases nd with
        | file _ _ => simp only [Except.ok.injEq] at hOk; subst hOk; exact hCur
        | dir _ => simp only [Except.ok.injEq] at hOk; subst hOk; exact hCur
        | symlink target _ =>
          cases follow
          · simp only [Bool.false_eq_true, ↓reduceIte, Except.ok.injEq] at hOk; subst hOk; exact hCur
          · simp only [↓reduceIte] at hOk
            exact ih "/" _ true res (by decide) (vfsSplitSegs_normPath_valid _) hOk
    | cons seg rest =>
      cases hNd : nodes cur with
      | none => simp [hNd] at hOk
      | some nd =>
        simp only [hNd] at hOk
        cases nd with
        | file _ _ => simp at hOk
        | dir mode =>
          by_cases hm : ((mode / 64) % 2 == 0) = true
          · simp [hm] at hOk
          · have hmf : ((mode / 64) % 2 == 0) = false := Bool.eq_false_iff.mpr hm
            simp only [hmf, Bool.false_eq_true, ↓reduceIte] at hOk
            have hValidSeg := hSegs seg (by simp)
            exact ih (vfsChildPath cur seg) rest follow res
              (vfsChildPath_valid cur seg hCur hValidSeg).1
              (fun s hs => hSegs s (by simp [hs]))
              hOk
        | symlink target _ =>
          apply ih "/" _ follow res (by decide) _ hOk
          intro s hs
          simp only [List.mem_append] at hs
          rcases hs with hs | hs
          · exact vfsSplitSegs_normPath_valid _ s hs
          · exact hSegs s (by simp [hs])


/-- Helper declaration shared across `LeanSwe.Fs.Proofs` submodules. -/
theorem vfsSplitSegs_inj_canon (k₁ k₂ : String)
    (h1 : isCanonPath k₁ = true) (h2 : isCanonPath k₂ = true)
    (hSp : vfsSplitSegs k₁ = vfsSplitSegs k₂) : k₁ = k₂ := by
  have hEq1 := (isCanonPath_normPath_parts k₁ h1).1
  have hEq2 := (isCanonPath_normPath_parts k₂ h2).1
  rw [hEq1, hEq2, hSp]


/-- Helper declaration shared across `LeanSwe.Fs.Proofs` submodules. -/
theorem vfsResolveSegs_ok_node (nodes : String → Option VfsNode) :
    ∀ fuel cur segs follow canon nd,
      vfsResolveSegs nodes cur segs follow fuel = .ok (canon, nd) →
      nodes canon = some nd := by
  intro fuel
  induction fuel with
  | zero => intro _ _ _ _ _ h; simp [vfsResolveSegs] at h
  | succ fuel ih =>
    intro cur segs follow canon nd hOk
    simp only [vfsResolveSegs] at hOk
    cases segs with
    | nil =>
      cases hNd : nodes cur with
      | none => simp [hNd] at hOk
      | some nd' =>
        simp only [hNd] at hOk
        cases nd' with
        | symlink _ _ =>
          cases follow
          · simp only [Bool.false_eq_true, ↓reduceIte, Except.ok.injEq, Prod.mk.injEq] at hOk
            rcases hOk with ⟨rfl, rfl⟩
            exact hNd
          · simp only [↓reduceIte] at hOk
            exact ih "/" _ true canon nd hOk
        | file _ _ =>
          simp only [Except.ok.injEq, Prod.mk.injEq] at hOk
          rcases hOk with ⟨rfl, rfl⟩
          exact hNd
        | dir _ =>
          simp only [Except.ok.injEq, Prod.mk.injEq] at hOk
          rcases hOk with ⟨rfl, rfl⟩
          exact hNd
    | cons seg rest =>
      cases hNd : nodes cur with
      | none => simp [hNd] at hOk
      | some nd' =>
        simp only [hNd] at hOk
        cases nd' with
        | file _ _ => simp at hOk
        | dir mode =>
          by_cases hm : ((mode / 64) % 2 == 0) = true
          · simp [hm] at hOk
          · have hmf : ((mode / 64) % 2 == 0) = false := Bool.eq_false_iff.mpr hm
            simp only [hmf, Bool.false_eq_true, ↓reduceIte] at hOk
            exact ih (vfsChildPath cur seg) rest follow canon nd hOk
        | symlink _ _ => exact ih "/" _ follow canon nd hOk


/-- Helper declaration shared across `LeanSwe.Fs.Proofs` submodules. -/
theorem list_getLast?_append {α : Type} :
    ∀ xs ys : List α, ys ≠ [] → (xs ++ ys).getLast? = ys.getLast? := by
  intro xs ys hne
  induction xs with
  | nil => rfl
  | cons x xt ih =>
    rw [List.cons_append, List.getLast?_cons, ih]
    cases hY : ys with
    | nil => exact absurd hY hne
    | cons z zs => rw [List.getLast?_cons]; rfl


/-- Helper declaration shared across `LeanSwe.Fs.Proofs` submodules. -/
theorem parent_name_vfsChildPath (c child : String)
    (hc : isCanonPath c = true) (hcNe : c ≠ "/") (hchild : Internal.validFileName child = true) :
    Internal.parent (c ++ "/" ++ child) = some c ∧ Internal.name (c ++ "/" ++ child) = some child := by
  obtain ⟨hCEq, hParts⟩ := isCanonPath_normPath_parts c hc
  have hChildL := validFileName_charList child hchild
  have hBeqF : (c == "/") = false := beq_false_of_ne hcNe
  have hChildV : vfsChildPath c child = c ++ "/" ++ child := by
    simp [vfsChildPath, hBeqF]
  have ⟨hChildCanon, hChildSp⟩ := vfsChildPath_valid c child hc hchild
  rw [hChildV] at hChildCanon hChildSp
  obtain ⟨hDstEq, hDstParts⟩ := isCanonPath_normPath_parts (c ++ "/" ++ child) hChildCanon
  have hPartsNe : (vfsSplitSegs c).map String.toList ≠ [] := by
    intro hEmp
    cases hSp : vfsSplitSegs c with
    | nil =>
      have : c = "/" := by rw [hCEq, hSp]; rfl
      exact hcNe this
    | cons _ _ => simp [hSp] at hEmp
  have hNewParts : (vfsSplitSegs (c ++ "/" ++ child)).map String.toList =
      (vfsSplitSegs c).map String.toList ++ [child.toList] := by
    rw [hChildSp, List.map_append, List.map_singleton]
  rw [hNewParts] at hDstEq hDstParts
  have hSplitAll :
      Internal.splitCharList '/' ('/' :: Internal.joinSlashChars ((vfsSplitSegs c).map String.toList ++ [child.toList])) =
      [] :: ((vfsSplitSegs c).map String.toList ++ [child.toList]) := by
    unfold Internal.splitCharList
    simp only [beq_self_eq_true, ↓reduceIte]
    rw [splitCharList_joinSlashChars _ (by simp [hPartsNe]) (fun s hs => (hDstParts s hs).2.2.1)]
  have hClean :
      Internal.cleanCharSegments (c ++ "/" ++ child) =
      (true, (vfsSplitSegs c).map String.toList ++ [child.toList]) := by
    have hCleEq : Internal.cleanCharSegments (c ++ "/" ++ child) =
        Internal.cleanCharSegments (String.ofList ('/' :: Internal.joinSlashChars
          ((vfsSplitSegs c).map String.toList ++ [child.toList]))) :=
      congrArg Internal.cleanCharSegments hDstEq
    rw [hCleEq]
    unfold Internal.cleanCharSegments Internal.isAbsChars
    simp only [String.toList_ofList, hSplitAll, List.filter_cons, List.isEmpty_nil,
      Bool.not_true, Bool.false_and, Bool.false_eq_true, ↓reduceIte, Prod.mk.injEq, true_and]
    rw [List.filter_eq_self.mpr]
    intro s hs
    exact Bool.and_eq_true _ _ |>.mpr ⟨(hDstParts s hs).1, (hDstParts s hs).2.1⟩
  have hLast := splitLastAux_append_singleton ((vfsSplitSegs c).map String.toList) [] child.toList
  have hSpPar : Internal.splitParentName (c ++ "/" ++ child) = some (some c, child) := by
    unfold Internal.splitParentName
    rw [hClean]
    dsimp only
    rw [hLast]
    rcases hP : (vfsSplitSegs c).map String.toList with _ | ⟨hd, tl⟩
    · exact absurd hP hPartsNe
    · simp only [List.reverse_nil, List.nil_append, String.ofList_toList, Option.some.injEq,
        Prod.mk.injEq, and_true]
      rw [← hP]
      exact hCEq.symm
  simp [Internal.parent, Internal.name, hSpPar]


/-- Helper declaration shared across `LeanSwe.Fs.Proofs` submodules. -/
theorem vfsAbsNorm_abs (cwd p : String) (hp : Internal.isAbsolute p = true) :
    vfsAbsNorm cwd p = Internal.normPath p := by
  simp [vfsAbsNorm, hp]


end LeanSwe.Fs.ProofsInternal
