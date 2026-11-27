import LeanSwe.Fs.Impl.Ambient

namespace LeanSwe.Fs.Internal

open LeanSwe.Fs
  (FsErrorKind FsError EntryKind FileStat WalkEntry FsRawError LockMode FsApi FsApiM
   EntryName RelPath SubtreeM SubtreeOpenerM)

/-- Execute `action` and unconditionally close `dh`, preserving `action`'s return value. -/
def bracketCloseDirM {m : Type → Type} {α : Type} [Monad m] [MonadFinally m]
    {dirH lockH : Type} (ops : RawDirOpsM m dirH lockH) (dh : dirH) (action : m α) : m α := do
  let (res, _) ← tryFinally' action (fun _ => ops.closeDir dh)
  pure res

/-- Execute `action` while holding `lockHandle`, always releasing `lockHandle` afterward. -/
def bracketDirLockM {m : Type → Type} {α : Type} [Monad m] [MonadFinally m]
    {dirH lockH : Type} (ops : RawDirOpsM m dirH lockH) (lockHandle : lockH) (action : m (Except FsError α)) :
    m (Except FsError α) := do
  let (actRes, relRes) ← tryFinally' action (fun _ => ops.releaseLock lockHandle)
  match actRes with
  | .error e => pure (.error e)
  | .ok a =>
    match relRes with
    | .ok () => pure (.ok a)
    | .error re => pure (.error re)

/-- Descend from open handle `cur` through `segs`, passing the reached handle to `act` and always closing every non-root intermediate handle (`isRoot = false`). -/
def walkDescendAuxM {m : Type → Type} {α : Type} [Monad m] [MonadFinally m]
    {dirH lockH : Type} (ops : RawDirOpsM m dirH lockH) (isRoot : Bool) (cur : dirH) :
    List EntryName → (dirH → m (Except FsError α)) → m (Except FsError α)
  | [], act =>
    if isRoot then
      act cur
    else
      bracketCloseDirM ops cur (act cur)
  | seg :: rest, act => do
    let rNext ←
      if isRoot then
        ops.openDirAt cur seg
      else
        bracketCloseDirM ops cur (ops.openDirAt cur seg)
    match rNext with
    | .error e => pure (.error e)
    | .ok nextDh => walkDescendAuxM ops false nextDh rest act

/-- Descend through `segs` from root directory handle `dh` using `O(1)` open handles and closing every handle opened during descent. -/
def walkDescendM {m : Type → Type} {α : Type} [Monad m] [MonadFinally m]
    {dirH lockH : Type} (ops : RawDirOpsM m dirH lockH) (dh : dirH) (segs : List EntryName)
    (act : dirH → m (Except FsError α)) : m (Except FsError α) :=
  walkDescendAuxM ops true dh segs act

/-- Ensure intermediate parent directories exist (`0o755`) along `segs` without following symlinks, then run `leafAct` on the final parent handle. -/
def mkdirWalkM {m : Type → Type} [Monad m] [MonadFinally m]
    {dirH lockH : Type} (ops : RawDirOpsM m dirH lockH) (isRoot : Bool) (cur : dirH) :
    List EntryName → (dirH → m (Except FsError Unit)) → m (Except FsError Unit)
  | [], leafAct =>
    if isRoot then
      leafAct cur
    else
      bracketCloseDirM ops cur (leafAct cur)
  | seg :: rest, leafAct => do
    let step : m (Except FsError dirH) := do
      match ← ops.openDirAt cur seg with
      | .ok nextDh => pure (.ok nextDh)
      | .error e =>
        if e.kind == .notFound then
          match ← ops.createDirAt cur seg with
          | .ok () => ops.openDirAt cur seg
          | .error ce =>
            if ce.kind == .alreadyExists then ops.openDirAt cur seg
            else pure (.error ce)
        else
          pure (.error e)
    let rNext ←
      if isRoot then
        step
      else
        bracketCloseDirM ops cur step
    match rNext with
    | .error e => pure (.error e)
    | .ok nextDh => mkdirWalkM ops false nextDh rest leafAct

/-- Retry temporary sibling creation up to `attempts` times on `.alreadyExists`, atomically rename onto `leaf`, and clean up the temporary file on rename failure. -/
def atomicWriteAtAuxM {m : Type → Type} [Monad m] {dirH lockH : Type} (ops : RawDirOpsM m dirH lockH)
    (parDh : dirH) (leaf : EntryName) (bytes : ByteArray) : Nat → m (Except FsError Unit)
  | 0 =>
    pure (.error { kind := .alreadyExists, path := some leaf.val, message := "temporary file name collision limit exceeded" })
  | attempts + 1 => do
    let tmp ← ops.freshTempName
    match ← ops.createFileAt parDh tmp bytes with
    | .ok () =>
      match ← ops.renameAt parDh tmp parDh leaf with
      | .ok () => pure (.ok ())
      | .error e =>
        let _ ← ops.unlinkAt parDh tmp false
        pure (.error e)
    | .error e =>
      if e.kind == .alreadyExists && attempts > 0 then
        atomicWriteAtAuxM ops parDh leaf bytes attempts
      else
        pure (.error e)

/-- Sort immediate `EntryName` entries lexicographically ascending. -/
@[reducible] def sortEntryNames (names : Array EntryName) : List EntryName :=
  names.toList.mergeSort (fun a b => a.val ≤ b.val)

/-- Classify sorted child names under `dirDh` via `lstatAt` into directory names and non-directory filenames without descending into symlinks. -/
def classifyChildrenM {m : Type → Type} [Monad m] {dirH lockH : Type} (ops : RawDirOpsM m dirH lockH) (dirDh : dirH) :
    List EntryName → List EntryName → List String → m (Except FsError (List EntryName × List String))
  | [], dirsAcc, filesAcc => pure (.ok (dirsAcc.reverse, filesAcc.reverse))
  | n :: rest, dirsAcc, filesAcc => do
    match ← ops.lstatAt dirDh n with
    | .error e => pure (.error e)
    | .ok info =>
      if info.kind == .dir then
        classifyChildrenM ops dirDh rest (n :: dirsAcc) filesAcc
      else
        classifyChildrenM ops dirDh rest dirsAcc (n.val :: filesAcc)

mutual
  /-- Traverse sorted subdirectories in pre-order DFS starting from `(relSegs, relLabel)`. -/
  def walkChildrenM {m : Type → Type} [Monad m] [MonadFinally m]
      {dirH lockH : Type} (ops : RawDirOpsM m dirH lockH) (rootDh : dirH) (relSegs : List EntryName)
      (relLabel : String) (fuel : Nat) (acc : Array WalkEntry) :
      List EntryName → m (Except FsError (Array WalkEntry))
    | [] => pure (.ok acc)
    | d :: rest => do
      let nextLabel := if relLabel == "." then d.val else relLabel ++ "/" ++ d.val
      match ← walkRecM ops rootDh (relSegs ++ [d]) nextLabel acc fuel with
      | .error e => pure (.error e)
      | .ok acc' => walkChildrenM ops rootDh relSegs relLabel fuel acc' rest

  /-- Bounded pre-order directory walk using `O(1)` open handles and `fuel` depth limit. -/
  def walkRecM {m : Type → Type} [Monad m] [MonadFinally m]
      {dirH lockH : Type} (ops : RawDirOpsM m dirH lockH) (rootDh : dirH)
      (relSegs : List EntryName) (relLabel : String) (acc : Array WalkEntry) :
      Nat → m (Except FsError (Array WalkEntry))
    | 0 =>
      pure (.error { kind := .ioError, path := some relLabel, message := s!"maximum directory depth exceeded: {relLabel}" })
    | fuel + 1 => do
      let rRead ← walkDescendM ops rootDh relSegs fun dirDh => do
        match ← ops.readDirAt dirDh with
        | .error e => pure (.error e)
        | .ok rawNames => classifyChildrenM ops dirDh (sortEntryNames rawNames) [] []
      match rRead with
      | .error e => pure (.error e)
      | .ok (dirs, files) =>
        let entry : WalkEntry := {
          root := relLabel
          dirs := (dirs.map (·.val)).toArray
          files := files.toArray }
        walkChildrenM ops rootDh relSegs relLabel fuel (acc.push entry) dirs
end

/-- Unlink leading non-directory entries in `items` while holding one open directory handle, stopping before the first directory child `d` and returning remaining items so `dirDh` is closed before recursing. -/
def rmtreeNonDirPrefixM {m : Type → Type} [Monad m] {dirH lockH : Type} (ops : RawDirOpsM m dirH lockH) (dirDh : dirH) :
    List EntryName → m (Except FsError (Option (EntryName × List EntryName)))
  | [] => pure (.ok none)
  | c :: rest => do
    match ← ops.lstatAt dirDh c with
    | .error e =>
      if e.kind == .notFound then rmtreeNonDirPrefixM ops dirDh rest
      else pure (.error e)
    | .ok info =>
      if info.kind == .dir then
        pure (.ok (some (c, rest)))
      else
        match ← ops.unlinkAt dirDh c false with
        | .ok () => rmtreeNonDirPrefixM ops dirDh rest
        | .error e =>
          if e.kind == .notFound then rmtreeNonDirPrefixM ops dirDh rest
          else pure (.error e)

/-- Process remaining entries inside directory `dirSegs` in bounded batches, closing open directory handles before calling `subDirFn` on any child directory. -/
def rmtreeProcessM {m : Type → Type} [Monad m] [MonadFinally m]
    {dirH lockH : Type} (ops : RawDirOpsM m dirH lockH) (rootDh : dirH) (dirSegs : List EntryName)
    (subDirFn : EntryName → m (Except FsError Unit)) :
    Nat → List EntryName → m (Except FsError Unit)
  | _, [] => pure (.ok ())
  | 0, _ => pure (.ok ())
  | steps + 1, items => do
    let rBatch ← walkDescendM ops rootDh dirSegs fun dirDh =>
      rmtreeNonDirPrefixM ops dirDh items
    match rBatch with
    | .error e => pure (.error e)
    | .ok none => pure (.ok ())
    | .ok (some (subDir, rest)) => do
      match ← subDirFn subDir with
      | .error e => pure (.error e)
      | .ok () => rmtreeProcessM ops rootDh dirSegs subDirFn steps rest

/-- Recursively delete child directory `leaf` under `parSegs` with bounded recursion depth `fuel` and `O(1)` open handles. -/
def rmtreeDirAtM {m : Type → Type} [Monad m] [MonadFinally m]
    {dirH lockH : Type} (ops : RawDirOpsM m dirH lockH) (rootDh : dirH) (parSegs : List EntryName) (leaf : EntryName) :
    Nat → m (Except FsError Unit)
  | 0 =>
    pure (.error { kind := .ioError, path := some leaf.val, message := s!"maximum directory recursion depth exceeded: {leaf.val}" })
  | fuel + 1 => do
    let dirSegs := parSegs ++ [leaf]
    let rRead ← walkDescendM ops rootDh dirSegs fun dirDh => ops.readDirAt dirDh
    match rRead with
    | .error e => pure (.error e)
    | .ok rawNames =>
      let sorted := sortEntryNames rawNames
      match ← rmtreeProcessM ops rootDh dirSegs (fun subDir => rmtreeDirAtM ops rootDh dirSegs subDir fuel) sorted.length sorted with
      | .error e => pure (.error e)
      | .ok () => walkDescendM ops rootDh parSegs fun parDh => ops.unlinkAt parDh leaf true

/-- Implement `SubtreeM m` operations confined to open root directory handle `dh`. -/
def subtreeOpsM {m : Type → Type} [Monad m] [MonadFinally m]
    {dirH lockH : Type} (ops : RawDirOpsM m dirH lockH) (dh : dirH) : SubtreeM m :=
  { lstat := fun rel =>
      match splitLastAux rel.segments [] with
      | none => ops.fstatDir dh
      | some (pre, leaf) => walkDescendM ops dh pre fun parDh => ops.lstatAt parDh leaf
    readRegular := fun rel =>
      match splitLastAux rel.segments [] with
      | none => do
        match ← ops.fstatDir dh with
        | .error e => pure (.error e)
        | .ok info =>
          if info.kind == .dir then
            pure (.error { kind := .isADirectory, path := some ".", message := "is a directory: ." })
          else
            pure (.error { kind := .notADirectory, path := some ".", message := "not a directory: ." })
      | some (pre, leaf) => walkDescendM ops dh pre fun parDh => ops.readRegularAt parDh leaf
    atomicWriteBytes := fun rel bytes =>
      match splitLastAux rel.segments [] with
      | none => pure (.error { kind := .invalidInput, path := some ".", message := "cannot atomically write subtree root" })
      | some (pre, leaf) => walkDescendM ops dh pre fun parDh => atomicWriteAtAuxM ops parDh leaf bytes 16
    mkdir := fun rel parents existOk =>
      match splitLastAux rel.segments [] with
      | none => do
        match ← ops.fstatDir dh with
        | .error e => pure (.error e)
        | .ok info =>
          if info.kind != .dir then
            pure (.error { kind := .notADirectory, path := some ".", message := "not a directory: ." })
          else if existOk then
            pure (.ok ())
          else
            pure (.error { kind := .alreadyExists, path := some ".", message := "directory already exists: ." })
      | some (pre, leaf) =>
        let leafAct : dirH → m (Except FsError Unit) := fun parDh => do
          match ← ops.createDirAt parDh leaf with
          | .ok () => pure (.ok ())
          | .error e =>
            if existOk && (e.kind == .alreadyExists || e.kind == .permissionDenied) then
              match ← ops.lstatAt parDh leaf with
              | .error _ => pure (.error e)
              | .ok info =>
                if info.kind == .dir then pure (.ok ())
                else if e.kind == .alreadyExists then pure (.error e)
                else pure (.error { kind := .alreadyExists, path := some leaf.val, message := s!"already exists: {leaf.val}" })
            else
              pure (.error e)
        if parents then
          mkdirWalkM ops true dh pre leafAct
        else
          walkDescendM ops dh pre leafAct
    unlink := fun rel missingOk =>
      match splitLastAux rel.segments [] with
      | none => pure (.error { kind := .invalidInput, path := some ".", message := "cannot unlink subtree root" })
      | some (pre, leaf) => do
        match ← walkDescendM ops dh pre fun parDh => ops.unlinkAt parDh leaf false with
        | .ok () => pure (.ok ())
        | .error e =>
          if e.kind == .notFound && missingOk then pure (.ok ())
          else pure (.error e)
    rmdir := fun rel =>
      match splitLastAux rel.segments [] with
      | none => pure (.error { kind := .invalidInput, path := some ".", message := "cannot remove subtree root" })
      | some (pre, leaf) => walkDescendM ops dh pre fun parDh => ops.unlinkAt parDh leaf true
    rmtree := fun rel ignoreMissing =>
      match splitLastAux rel.segments [] with
      | none => pure (.error { kind := .invalidInput, path := some ".", message := "cannot recursively remove subtree root" })
      | some (pre, leaf) => do
        let rLeaf ← walkDescendM ops dh pre fun parDh => ops.lstatAt parDh leaf
        match rLeaf with
        | .error e =>
          if e.kind == .notFound && ignoreMissing then pure (.ok ())
          else pure (.error e)
        | .ok info =>
          if info.kind != .dir then
            pure (.error { kind := .notADirectory, path := some leaf.val, message := s!"not a directory: {leaf.val}" })
          else
            rmtreeDirAtM ops dh pre leaf 4096
    symlink := fun target rel =>
      match splitLastAux rel.segments [] with
      | none => pure (.error { kind := .invalidInput, path := some ".", message := "cannot replace subtree root with symlink" })
      | some (pre, leaf) =>
        if target.isEmpty || Char.ofNat 0 ∈ target.toList then
          pure (.error { kind := .invalidInput, path := some target, message := "invalid symlink target" })
        else
          walkDescendM ops dh pre fun parDh => ops.symlinkAt target parDh leaf
    listDir := fun rel =>
      walkDescendM ops dh rel.segments fun dirDh => do
        match ← ops.readDirAt dirDh with
        | .error e => pure (.error e)
        | .ok names => pure (.ok (sortEntryNames names).toArray)
    walk := fun rel =>
      walkRecM ops dh rel.segments "." #[] 4096
    withFileLock := fun {_α} rel mode createIfMissing action =>
      match splitLastAux rel.segments [] with
      | none => pure (.error { kind := .invalidInput, path := some ".", message := "cannot lock subtree root" })
      | some (pre, leaf) => do
        let rLock ← walkDescendM ops dh pre fun parDh =>
          ops.acquireLockAt parDh leaf mode createIfMissing false
        match rLock with
        | .error e => pure (.error e)
        | .ok lockHandle =>
          bracketDirLockM ops lockHandle action
    tryWithFileLock := fun {_α} rel mode createIfMissing action =>
      match splitLastAux rel.segments [] with
      | none => pure (.error { kind := .invalidInput, path := some ".", message := "cannot lock subtree root" })
      | some (pre, leaf) => do
        let rLock ← walkDescendM ops dh pre fun parDh =>
          ops.acquireLockAt parDh leaf mode createIfMissing true
        match rLock with
        | .error e =>
          if e.kind == .wouldBlock then pure (.ok none)
          else pure (.error e)
        | .ok lockHandle =>
          bracketDirLockM ops lockHandle do
            match ← action with
            | .ok a => pure (.ok (some a))
            | .error e => pure (.error e) }

end LeanSwe.Fs.Internal
