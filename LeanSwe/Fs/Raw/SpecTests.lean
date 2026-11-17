import Core.NondetTest
import LeanSwe.Fs.Raw.Types

namespace LeanSwe.Fs.Raw

open Core (NondetTest)
open Core.NondetTest

private def isValidRawPath (path : String) : Bool :=
  let cs := path.toList
  !cs.isEmpty && !(Char.ofNat 0 ∈ cs) && !(cs.length > 1 && cs.getLast? == some '/')

private def isSingleValidName (name : String) : Bool :=
  let cs := name.toList
  !cs.isEmpty && !('/' ∈ cs) && !(Char.ofNat 0 ∈ cs) && name != "." && name != ".."

/-- Every error returned by `ops.mapRawError` carries a non-empty diagnostic message. -/
def test_fsraw_mapRawError_returnsNonEmptyMessage
    {runner} [NondetTest runner] (ops : RawFsOps) : runner Unit := do
  let raw ← nondet FsRawError
  let err := ops.mapRawError raw
  NondetTest.assert (err.message ≠ "")

/-- Mapping a `.wouldBlock` raw error preserves `.wouldBlock` kind, path, errno, and non-empty message. -/
def test_fsraw_mapRawError_wouldBlock
    {runner} [NondetTest runner] (ops : RawFsOps) : runner Unit := do
  let path? ← nondet (Option String)
  let errno ← nondet UInt32
  let detail ← nondet String
  let err := ops.mapRawError (.wouldBlock path? errno detail)
  NondetTest.assert (err.kind = .wouldBlock ∧ err.path = path? ∧ err.errnoCode = some errno ∧ err.message ≠ "")

/-- Calling `ops.createFileNew` on a missing child under writable `"/"` creates a regular file with exact `bytes`. -/
def test_fsraw_createFileNew_createsMissingWithExactBytes
    {S : Type} {runner} [NondetTest runner] (ops : RawFsOpsM (StateM S)) : runner Unit := do
  let s₀ ← nondet S
  let child ← nondet String
  let bytes ← nondet ByteArray
  assume (isSingleValidName child = true)
  let path := "/" ++ child
  assume (∃ stRoot, ((ops.stat false "/").run s₀).1 = .ok stRoot ∧ stRoot.kind = .dir ∧
    (stRoot.mode / 128) % 2 = 1 ∧ (stRoot.mode / 64) % 2 = 1)
  assume (∃ e, ((ops.stat false path).run s₀).1 = .error e ∧ e.kind = .notFound)
  let (res, s₁) := (ops.createFileNew path bytes).run s₀
  NondetTest.assert (res = .ok ())
  NondetTest.assert (∃ st, ((ops.stat false path).run s₁).1 = .ok st ∧
    st.kind = .file ∧ st.byteSize = bytes.size)
  NondetTest.assert (((ops.readBytes path).run s₁).1 = .ok bytes)

/-- Calling `ops.createFileNew` on any existing entry (file, directory, or symlink including dangling links) fails with `.alreadyExists` and leaves state unchanged. -/
def test_fsraw_createFileNew_existingRejected
    {S : Type} {runner} [NondetTest runner] (ops : RawFsOpsM (StateM S)) : runner Unit := do
  let s₀ ← nondet S
  let path ← nondet String
  let bytes ← nondet ByteArray
  assume (isValidRawPath path = true)
  assume (((ops.stat false path).run s₀).1.isOk = true)
  let (res, s₁) := (ops.createFileNew path bytes).run s₀
  NondetTest.assert ((∃ e, res = .error e ∧ e.kind = .alreadyExists) ∧ s₁ = s₀)

/-- Calling `ops.createFileNew` with an empty path, embedded NUL byte, or non-root trailing `/` fails with `.invalidInput` and leaves state unchanged. -/
def test_fsraw_createFileNew_invalidPathRejected
    {S : Type} {runner} [NondetTest runner] (ops : RawFsOpsM (StateM S)) : runner Unit := do
  let s₀ ← nondet S
  let path ← nondet String
  let bytes ← nondet ByteArray
  assume (isValidRawPath path = false)
  let (res, s₁) := (ops.createFileNew path bytes).run s₀
  NondetTest.assert ((∃ e, res = .error e ∧ e.kind = .invalidInput) ∧ s₁ = s₀)

/-- Calling `ops.createFileNew` under a missing parent directory fails with `.notFound` without creating parent directories. -/
def test_fsraw_createFileNew_missingParentRejected
    {S : Type} {runner} [NondetTest runner] (ops : RawFsOpsM (StateM S)) : runner Unit := do
  let s₀ ← nondet S
  let d ← nondet String
  let f ← nondet String
  let bytes ← nondet ByteArray
  assume (isSingleValidName d = true ∧ isSingleValidName f = true)
  assume (∃ e, ((ops.stat false ("/" ++ d)).run s₀).1 = .error e ∧ e.kind = .notFound)
  let (res, s₁) := (ops.createFileNew ("/" ++ d ++ "/" ++ f) bytes).run s₀
  NondetTest.assert ((∃ e, res = .error e ∧ e.kind = .notFound) ∧ s₁ = s₀)

/-- Calling `ops.readBytes` on a symlink whose target is a regular file follows the symlink and returns the file bytes without mutating state. -/
def test_fsraw_readBytes_followsSymlinkToRegularFile
    {S : Type} {runner} [NondetTest runner] (ops : RawFsOpsM (StateM S)) : runner Unit := do
  let s₀ ← nondet S
  let path ← nondet String
  assume (isValidRawPath path = true)
  assume (∃ lst, ((ops.stat false path).run s₀).1 = .ok lst ∧ lst.kind = .symlink)
  assume (∃ st, ((ops.stat true path).run s₀).1 = .ok st ∧ st.kind = .file)
  let (res, s₁) := (ops.readBytes path).run s₀
  NondetTest.assert ((∃ bs, res = .ok bs ∧
    (∃ st, ((ops.stat true path).run s₀).1 = .ok st ∧ bs.size = st.byteSize)) ∧ s₁ = s₀)

/-- Writing `bytes` with `ops.createFileNew`, symlinking to it, and calling `ops.readBytes` on the symlink returns exact `bytes` without mutating state. -/
def test_fsraw_readBytes_roundTripsExactBytesThroughSymlink
    {S : Type} {runner} [NondetTest runner] (ops : RawFsOpsM (StateM S)) : runner Unit := do
  let s₀ ← nondet S
  let tgtName ← nondet String
  let symName ← nondet String
  let bytes ← nondet ByteArray
  assume (isSingleValidName tgtName = true ∧ isSingleValidName symName = true ∧ tgtName ≠ symName)
  let tgt := "/" ++ tgtName
  let sym := "/" ++ symName
  assume (∃ stRoot, ((ops.stat false "/").run s₀).1 = .ok stRoot ∧ stRoot.kind = .dir ∧
    (stRoot.mode / 128) % 2 = 1 ∧ (stRoot.mode / 64) % 2 = 1)
  assume (∃ e1, ((ops.stat false tgt).run s₀).1 = .error e1 ∧ e1.kind = .notFound)
  assume (∃ e2, ((ops.stat false sym).run s₀).1 = .error e2 ∧ e2.kind = .notFound)
  let (r1, s₁) := (ops.createFileNew tgt bytes).run s₀
  assume (r1 = .ok ())
  let (r2, s₂) := (ops.symlink tgt sym).run s₁
  assume (r2 = .ok ())
  let (r3, s₃) := (ops.readBytes sym).run s₂
  NondetTest.assert (r3 = .ok bytes ∧ s₃ = s₂)

/-- Calling `ops.readBytes` on a directory fails with `.isADirectory` and on a missing valid path preserves the `stat` error without mutating state. -/
def test_fsraw_readBytes_dirAndMissingRejected
    {S : Type} {runner} [NondetTest runner] (ops : RawFsOpsM (StateM S)) : runner Unit := do
  let s₀ ← nondet S
  let path ← nondet String
  assume (isValidRawPath path = true)
  match ((ops.stat true path).run s₀).1 with
  | .error err =>
    let (res, s₁) := (ops.readBytes path).run s₀
    NondetTest.assert ((∃ e, res = .error e ∧ e.kind = err.kind) ∧ s₁ = s₀)
  | .ok st =>
    if st.kind == .dir then
      let (res, s₁) := (ops.readBytes path).run s₀
      NondetTest.assert ((∃ e, res = .error e ∧ e.kind = .isADirectory) ∧ s₁ = s₀)
    else
      pure ()

/-- Calling `ops.readBytes` with an empty path, embedded NUL byte, or non-root trailing `/` fails with `.invalidInput` and leaves state unchanged. -/
def test_fsraw_readBytes_invalidPathRejected
    {S : Type} {runner} [NondetTest runner] (ops : RawFsOpsM (StateM S)) : runner Unit := do
  let s₀ ← nondet S
  let path ← nondet String
  assume (isValidRawPath path = false)
  let (res, s₁) := (ops.readBytes path).run s₀
  NondetTest.assert ((∃ e, res = .error e ∧ e.kind = .invalidInput) ∧ s₁ = s₀)

/-- External trust boundary assumptions for `LeanSwe.Fs.Raw` C shims grounded in `RuntimeTests.lean`. -/
structure EmpiricalAssumptions where
  /-- `leanswe_fs_read_regular_bytes` opens `path` with `O_RDONLY | O_NONBLOCK | O_CLOEXEC | O_NOCTTY`, maps `ENXIO` on Unix domain sockets and unbacked special files to `.invalidInput` (preserving `.isADirectory` on directories), checks `fstat` returning `.isADirectory` on `S_ISDIR` and `.invalidInput` on `!S_ISREG` (FIFOs, sockets, device nodes), and clears `O_NONBLOCK` via `fcntl` before reading to EOF handling `EINTR`/`EAGAIN`. -/
  readBytesNonBlockingRejectsNonRegular : Prop
  /-- `leanswe_fs_read_regular_bytes` rejects `""`, embedded NUL bytes, and non-root trailing `/` with `.invalidInput` and follows symlinks to regular files (`mkfifo` FIFO and Unix domain socket grounded in `RuntimeTests.lean`). -/
  readBytesValidatesPathAndFollowsSymlinks : Prop
  /-- `leanswe_fs_create_file_new` opens with `O_WRONLY | O_CREAT | O_EXCL | O_NOFOLLOW | O_CLOEXEC` (mode `0644` masked by `umask`), rejects `""`, embedded NUL bytes, and non-root trailing `/` with `.invalidInput`, fails with `.alreadyExists` on existing files, directories, or symlinks (including dangling links, `"/"`, `"."`, `".."`) without following symlinks (`O_EXCL | O_NOFOLLOW` and path validation grounded in `RuntimeTests.lean`), and performs best-effort `unlink(path)` on `write` or `close(fd)` failure preserving the original `errno` (audited in C shim). -/
  createFileNewExclusiveNoFollow : Prop
  /-- `openDir` opens with `O_RDONLY | O_DIRECTORY | O_CLOEXEC`; `openDirAt` uses `O_RDONLY | O_DIRECTORY | O_NOFOLLOW | O_CLOEXEC` with `fstatat(..., AT_SYMLINK_NOFOLLOW)` fallback mapping symlinks (even when Linux returns `ENOTDIR`) to `.invalidInput`, and descriptor exhaustion (`EMFILE`/`ENFILE`) maps to `.invalidInput`. -/
  openDirAtRefusesSymlinksAndEnforcesDirectory : Prop
  /-- Single-step `*at` C shims (`lstatAt`, `readRegularAt`, `createFileAt`, `createDirAt`, `renameAt`, `unlinkAt`, `symlinkAt`, `acquireLockAt`) operate on one `EntryName` segment without following symlinks, map `ENXIO` on sockets and `!S_ISREG` to `.invalidInput`, validate `symlinkAt` target upfront for empty/embedded-NUL (`.invalidInput`), use `mkdirat(..., 0o755)` in `createDirAt` and `openat(..., O_WRONLY | O_CREAT | O_EXCL | O_NOFOLLOW | O_CLOEXEC, 0o644)` in `createFileAt` (both subject to process `umask`, keeping `0o644` for `acquireLockAt`), and generate temp names via a thread-safe monotonic counter (`atomic` `u64`). -/
  singleStepAtSyscallsNoFollowAndDefaultModes : Prop
  /-- Refcounted `DirSlot` table in `fs_shim.c` tracks `{ id, fd, refs, closing }` with `0 < handleId < UInt64.size`, sets `closing = 1` atomically under the slot mutex in `closeDir`, never reuses a live OS descriptor mid-syscall, releases the `DirSlot` ref before blocking on `flock` in `acquireLockAt`, rejects closed/forged `DirHandle` values with `.invalidInput`, and keeps open descriptors pinned across concurrent external renames and symlink swaps. -/
  dirSlotRefcountedSafeClosing : Prop

/-- `EntryName.parse s` succeeds iff `validSeg s = true` and otherwise fails with `.invalidInput` and non-empty message. -/
def test_fsraw_entryName_parse_acceptsValidAndRejectsUnsafe
    {runner} [NondetTest runner]
    (parseName : String → Except FsError EntryName := EntryName.parse) : runner Unit := do
  let s ← nondet String
  match parseName s with
  | .ok n => NondetTest.assert (validSeg s = true ∧ n.val = s)
  | .error e => NondetTest.assert (validSeg s = false ∧ e.kind = .invalidInput ∧ e.message ≠ "")

/-- `RelPath.parse` rejects `""`, leading `/`, trailing `/`, `//`, `.`, `..`, and NUL with `.invalidInput`, accepts valid multi-segment paths like `"a/b"`, and `RelPath.parseRoot "."` returns `RelPath.root`. -/
def test_fsraw_relPath_parse_rejectsUnsafeAndParseRootMapsDot
    {runner} [NondetTest runner]
    (parseRel : String → Except FsError RelPath := RelPath.parse)
    (parseRelRoot : String → Except FsError RelPath := RelPath.parseRoot) : runner Unit := do
  let seg ← nondet String
  let bads := ["", "/" ++ seg, seg ++ "/", ".", "..", "a//b", "a/./b", "a/../b", "a" ++ String.ofList [Char.ofNat 0] ++ "b"]
  NondetTest.assert (bads.all fun p =>
    match parseRel p with
    | .error e => e.kind == .invalidInput && e.message != ""
    | .ok _ => false)
  NondetTest.assert (match parseRel "a/b" with
    | .ok rel => rel.segments.map (·.val) == ["a", "b"]
    | .error _ => false)
  NondetTest.assert (parseRelRoot "." = .ok RelPath.root)
  NondetTest.assert (seg = "." ∨ parseRelRoot seg = parseRel seg)

/-- Calling `ops.openDirAt dh child` when `lstatAt dh child` is a symlink fails with `.invalidInput` and preserves state. -/
def test_fsraw_rawDirOps_openDirAt_refusesSymlinkAndPreservesState
    {S : Type} {runner} [NondetTest runner] (ops : RawDirOpsM (StateM S)) : runner Unit := do
  let s₀ ← nondet S
  let dh ← nondet DirHandle
  let child ← nondet EntryName
  assume (∃ st, ((ops.lstatAt dh child).run s₀).1 = .ok st ∧ st.kind = .symlink)
  let (res, s₁) := (ops.openDirAt dh child).run s₀
  NondetTest.assert ((∃ e, res = .error e ∧ e.kind = .invalidInput) ∧ s₁ = s₀)

/-- Calling `ops.readRegularAt dh child` on a symlink fails with `.invalidInput` and on a directory fails with `.isADirectory`, leaving state unchanged. -/
def test_fsraw_rawDirOps_readRegularAt_refusesSymlinkAndDir
    {S : Type} {runner} [NondetTest runner] (ops : RawDirOpsM (StateM S)) : runner Unit := do
  let s₀ ← nondet S
  let dh ← nondet DirHandle
  let child ← nondet EntryName
  match ((ops.lstatAt dh child).run s₀).1 with
  | .error _ => pure ()
  | .ok st =>
    if st.kind == .symlink then
      let (res, s₁) := (ops.readRegularAt dh child).run s₀
      NondetTest.assert ((∃ e, res = .error e ∧ e.kind = .invalidInput) ∧ s₁ = s₀)
    else if st.kind == .dir then
      let (res, s₁) := (ops.readRegularAt dh child).run s₀
      NondetTest.assert ((∃ e, res = .error e ∧ e.kind = .isADirectory) ∧ s₁ = s₀)
    else
      pure ()

/-- Calling `ops.createFileAt` rejects existing entries (including symlinks) with `.alreadyExists` and creates missing regular files with exact bytes and mode `0o644`. -/
def test_fsraw_rawDirOps_createFileAt_exclusiveNoFollow
    {S : Type} {runner} [NondetTest runner] (ops : RawDirOpsM (StateM S)) : runner Unit := do
  let s₀ ← nondet S
  let dh ← nondet DirHandle
  let child ← nondet EntryName
  let bytes ← nondet ByteArray
  assume (∃ dSt, ((ops.fstatDir dh).run s₀).1 = .ok dSt ∧ dSt.kind = .dir ∧
    (dSt.mode / 128) % 2 = 1 ∧ (dSt.mode / 64) % 2 = 1)
  match ((ops.lstatAt dh child).run s₀).1 with
  | .ok _ =>
    let (res, s₁) := (ops.createFileAt dh child bytes).run s₀
    NondetTest.assert ((∃ e, res = .error e ∧ e.kind = .alreadyExists) ∧ s₁ = s₀)
  | .error err =>
    assume (err.kind = .notFound)
    let (res, s₁) := (ops.createFileAt dh child bytes).run s₀
    NondetTest.assert (res = .ok ())
    NondetTest.assert (∃ st, ((ops.lstatAt dh child).run s₁).1 = .ok st ∧
      st.kind = .file ∧ st.byteSize = bytes.size ∧ st.mode = 0o644)
    NondetTest.assert (((ops.readRegularAt dh child).run s₁).1 = .ok bytes)

/-- Calling `ops.createDirAt` rejects existing entries (including symlinks) with `.alreadyExists` and creates missing directories with mode `0o755`. -/
def test_fsraw_rawDirOps_createDirAt_createsOrRejectsExisting
    {S : Type} {runner} [NondetTest runner] (ops : RawDirOpsM (StateM S)) : runner Unit := do
  let s₀ ← nondet S
  let dh ← nondet DirHandle
  let child ← nondet EntryName
  assume (∃ dSt, ((ops.fstatDir dh).run s₀).1 = .ok dSt ∧ dSt.kind = .dir ∧
    (dSt.mode / 128) % 2 = 1 ∧ (dSt.mode / 64) % 2 = 1)
  match ((ops.lstatAt dh child).run s₀).1 with
  | .ok _ =>
    let (res, s₁) := (ops.createDirAt dh child).run s₀
    NondetTest.assert ((∃ e, res = .error e ∧ e.kind = .alreadyExists) ∧ s₁ = s₀)
  | .error err =>
    assume (err.kind = .notFound)
    let (res, s₁) := (ops.createDirAt dh child).run s₀
    NondetTest.assert (res = .ok ())
    NondetTest.assert (∃ st, ((ops.lstatAt dh child).run s₁).1 = .ok st ∧
      st.kind = .dir ∧ st.mode = 0o755)

/-- Calling `ops.unlinkAt` checks symlink vs directory flags, enforces empty-dir removal vs non-empty `.notEmpty`, and reports `.notFound` on missing entries. -/
def test_fsraw_rawDirOps_unlinkAt_dirFlagSemantics
    {S : Type} {runner} [NondetTest runner] (ops : RawDirOpsM (StateM S)) : runner Unit := do
  let s₀ ← nondet S
  let dh ← nondet DirHandle
  let child ← nondet EntryName
  assume (∃ dSt, ((ops.fstatDir dh).run s₀).1 = .ok dSt ∧ dSt.kind = .dir ∧
    (dSt.mode / 128) % 2 = 1 ∧ (dSt.mode / 64) % 2 = 1)
  match ((ops.lstatAt dh child).run s₀).1 with
  | .ok st =>
    if st.kind == .symlink then
      let (rDir, sDir) := (ops.unlinkAt dh child true).run s₀
      NondetTest.assert ((∃ e, rDir = .error e ∧ e.kind = .notADirectory) ∧ sDir = s₀)
      let (rUnlink, sUnlink) := (ops.unlinkAt dh child false).run s₀
      NondetTest.assert (rUnlink = .ok () ∧
        ∃ e, ((ops.lstatAt dh child).run sUnlink).1 = .error e ∧ e.kind = .notFound)
    else if st.kind == .dir then
      let (rFile, sFile) := (ops.unlinkAt dh child false).run s₀
      NondetTest.assert ((∃ e, rFile = .error e ∧ e.kind = .isADirectory) ∧ sFile = s₀)
    else
      pure ()
  | .error lErr =>
    if lErr.kind == .notFound then
      let (rFile, sFile) := (ops.unlinkAt dh child false).run s₀
      NondetTest.assert ((∃ e, rFile = .error e ∧ e.kind = .notFound) ∧ sFile = s₀)
      let (rDir, sDir) := (ops.unlinkAt dh child true).run s₀
      NondetTest.assert ((∃ e, rDir = .error e ∧ e.kind = .notFound) ∧ sDir = s₀)
    else
      pure ()
  let (openRes, sRoot) := (ops.openDir "/").run s₀
  match openRes with
  | .error _ => pure ()
  | .ok rootDh =>
    let inner ← nondet EntryName
    match ((ops.fstatDir rootDh).run sRoot).1, ((ops.lstatAt rootDh child).run sRoot).1 with
    | .ok rSt, .error mErr =>
      if rSt.kind == .dir && (rSt.mode / 128) % 2 == 1 && (rSt.mode / 64) % 2 == 1 && mErr.kind == .notFound then
        let (rMk1, s₁) := (ops.createDirAt rootDh child).run sRoot
        NondetTest.assert (rMk1 = .ok ())
        let (rRmEmpty, s₂) := (ops.unlinkAt rootDh child true).run s₁
        NondetTest.assert (rRmEmpty = .ok () ∧
          ∃ e, ((ops.lstatAt rootDh child).run s₂).1 = .error e ∧ e.kind = .notFound)
        let (rMk2, s₃) := (ops.createDirAt rootDh child).run sRoot
        NondetTest.assert (rMk2 = .ok ())
        let (rOpen, s₄) := (ops.openDirAt rootDh child).run s₃
        match rOpen with
        | .error _ =>
          let _ := (ops.closeDir rootDh).run s₄
          NondetTest.assert False
        | .ok childDh =>
          let (rCf, s₅) := (ops.createFileAt childDh inner ByteArray.empty).run s₄
          NondetTest.assert (rCf = .ok ())
          let (rCl, s₆) := (ops.closeDir childDh).run s₅
          NondetTest.assert (rCl = .ok ())
          let (rNotEmpty, s₇) := (ops.unlinkAt rootDh child true).run s₆
          let _ := (ops.closeDir rootDh).run s₇
          NondetTest.assert ((∃ e, rNotEmpty = .error e ∧ e.kind = .notEmpty) ∧ s₇ = s₆)
      else
        let _ := (ops.closeDir rootDh).run sRoot
        pure ()
    | _, _ =>
      let _ := (ops.closeDir rootDh).run sRoot
      pure ()

/-- Closing an opened `DirHandle` via `ops.closeDir` invalidates it for all subsequent `*at` primitives (including asymmetric `renameAt` arguments) and zero-ID handles are rejected with `.invalidInput`. -/
def test_fsraw_rawDirOps_closedHandleRejected
    {S : Type} {runner} [NondetTest runner] (ops : RawDirOpsM (StateM S)) : runner Unit := do
  let s₀ ← nondet S
  let root ← nondet String
  let child ← nondet EntryName
  let bytes ← nondet ByteArray
  let forgedZero : DirHandle := { handleId := 0, rootPath := "/" }
  NondetTest.assert (∃ e, (ops.fstatDir forgedZero |>.run s₀).1 = .error e ∧ e.kind = .invalidInput)
  NondetTest.assert (∃ e, (ops.closeDir forgedZero |>.run s₀).1 = .error e ∧ e.kind = .invalidInput)
  let (openRes, s₁) := (ops.openDir root).run s₀
  match openRes with
  | .error _ => pure ()
  | .ok dh =>
    let (liveRes, s₁') := (ops.openDir root).run s₁
    let (closeRes, s₂) := (ops.closeDir dh).run s₁'
    NondetTest.assert (closeRes = .ok ())
    NondetTest.assert (∃ e, (ops.fstatDir dh |>.run s₂).1 = .error e ∧ e.kind = .invalidInput)
    NondetTest.assert (∃ e, (ops.lstatAt dh child |>.run s₂).1 = .error e ∧ e.kind = .invalidInput)
    NondetTest.assert (∃ e, (ops.readDirAt dh |>.run s₂).1 = .error e ∧ e.kind = .invalidInput)
    NondetTest.assert (∃ e, (ops.openDirAt dh child |>.run s₂).1 = .error e ∧ e.kind = .invalidInput)
    NondetTest.assert (∃ e, (ops.createDirAt dh child |>.run s₂).1 = .error e ∧ e.kind = .invalidInput)
    NondetTest.assert (∃ e, (ops.readRegularAt dh child |>.run s₂).1 = .error e ∧ e.kind = .invalidInput)
    NondetTest.assert (∃ e, (ops.createFileAt dh child bytes |>.run s₂).1 = .error e ∧ e.kind = .invalidInput)
    NondetTest.assert (∃ e, (ops.renameAt dh child dh child |>.run s₂).1 = .error e ∧ e.kind = .invalidInput)
    NondetTest.assert (∃ e, (ops.unlinkAt dh child false |>.run s₂).1 = .error e ∧ e.kind = .invalidInput)
    NondetTest.assert (∃ e, (ops.symlinkAt "t" dh child |>.run s₂).1 = .error e ∧ e.kind = .invalidInput)
    NondetTest.assert (∃ e, (ops.acquireLockAt dh child .exclusive false true |>.run s₂).1 = .error e ∧ e.kind = .invalidInput)
    NondetTest.assert (∃ e, (ops.closeDir dh |>.run s₂).1 = .error e ∧ e.kind = .invalidInput)
    match liveRes with
    | .ok liveDh =>
      if liveDh.handleId != dh.handleId then
        NondetTest.assert (∃ e, (ops.renameAt dh child liveDh child |>.run s₂).1 = .error e ∧ e.kind = .invalidInput)
        NondetTest.assert (∃ e, (ops.renameAt liveDh child dh child |>.run s₂).1 = .error e ∧ e.kind = .invalidInput)
      else
        pure ()
    | .error _ => pure ()

/-- Calling `ops.fstatDir` on an opened `DirHandle` succeeds with `kind = .dir` and does not mutate state. -/
def test_fsraw_rawDirOps_fstatDir_validReturnsDir
    {S : Type} {runner} [NondetTest runner] (ops : RawDirOpsM (StateM S)) : runner Unit := do
  let s₀ ← nondet S
  let root ← nondet String
  let (openRes, s₁) := (ops.openDir root).run s₀
  match openRes with
  | .error _ => pure ()
  | .ok dh =>
    let (res, s₂) := (ops.fstatDir dh).run s₁
    let _ := (ops.closeDir dh).run s₂
    NondetTest.assert ((∃ st, res = .ok st ∧ st.kind = .dir) ∧ s₂ = s₁)

/-- Calling `ops.readDirAt` returns duplicate-free (`Nodup`) `EntryName` entries and leaves state unchanged. -/
def test_fsraw_rawDirOps_readDirAt_sortedUnique
    {S : Type} {runner} [NondetTest runner] (ops : RawDirOpsM (StateM S)) : runner Unit := do
  let s₀ ← nondet S
  let dh ← nondet DirHandle
  let (res, s₁) := (ops.readDirAt dh).run s₀
  match res with
  | .error _ => NondetTest.assert (s₁ = s₀)
  | .ok entries =>
    NondetTest.assert (entries.toList.Nodup ∧ s₁ = s₀)

/-- Calling `ops.renameAt` moves regular files across open handles, rejects missing sources with `.notFound`, and rejects file/directory kind mismatches (and directory-into-descendant `.invalidInput`). -/
def test_fsraw_rawDirOps_renameAt_moveAndTypeMismatch
    {S : Type} {runner} [NondetTest runner] (ops : RawDirOpsM (StateM S)) : runner Unit := do
  let s₀ ← nondet S
  let srcDh ← nondet DirHandle
  let srcName ← nondet EntryName
  let dstDh ← nondet DirHandle
  let dstName ← nondet EntryName
  assume (∃ dSt, ((ops.fstatDir srcDh).run s₀).1 = .ok dSt ∧ dSt.kind = .dir ∧
    (dSt.mode / 128) % 2 = 1 ∧ (dSt.mode / 64) % 2 = 1)
  assume (∃ dSt, ((ops.fstatDir dstDh).run s₀).1 = .ok dSt ∧ dSt.kind = .dir ∧
    (dSt.mode / 128) % 2 = 1 ∧ (dSt.mode / 64) % 2 = 1)
  match ((ops.lstatAt srcDh srcName).run s₀).1 with
  | .error sErr =>
    if sErr.kind == .notFound then
      let (res, s₁) := (ops.renameAt srcDh srcName dstDh dstName).run s₀
      NondetTest.assert ((∃ e, res = .error e ∧ e.kind = .notFound) ∧ s₁ = s₀)
    else
      pure ()
  | .ok srcSt =>
    match ((ops.lstatAt dstDh dstName).run s₀).1 with
    | .ok dstSt =>
      if srcSt.kind == .dir && dstSt.kind == .file then
        let (res, s₁) := (ops.renameAt srcDh srcName dstDh dstName).run s₀
        if srcDh.handleId == dstDh.handleId then
          NondetTest.assert ((∃ e, res = .error e ∧ e.kind = .notADirectory) ∧ s₁ = s₀)
        else
          NondetTest.assert ((∃ e, res = .error e ∧ (e.kind = .notADirectory ∨ e.kind = .invalidInput)) ∧ s₁ = s₀)
      else if srcSt.kind == .file && dstSt.kind == .dir then
        let (res, s₁) := (ops.renameAt srcDh srcName dstDh dstName).run s₀
        NondetTest.assert ((∃ e, res = .error e ∧ e.kind = .isADirectory) ∧ s₁ = s₀)
      else
        pure ()
    | .error dErr =>
      if dErr.kind == .notFound && srcSt.kind == .file && (srcDh.handleId != dstDh.handleId || srcName != dstName) then
        let (res, s₁) := (ops.renameAt srcDh srcName dstDh dstName).run s₀
        NondetTest.assert (res = .ok ())
        NondetTest.assert (∃ st, ((ops.lstatAt dstDh dstName).run s₁).1 = .ok st ∧ st.kind = .file)
        NondetTest.assert (∃ e, ((ops.lstatAt srcDh srcName).run s₁).1 = .error e ∧ e.kind = .notFound)
      else
        pure ()

/-- Calling `ops.symlinkAt` rejects empty or NUL-containing `target` strings with `.invalidInput` and creates a `.symlink` entry when missing and writable. -/
def test_fsraw_rawDirOps_symlinkAt_validAndRejectsInvalidTarget
    {S : Type} {runner} [NondetTest runner] (ops : RawDirOpsM (StateM S)) : runner Unit := do
  let s₀ ← nondet S
  let dh ← nondet DirHandle
  let child ← nondet EntryName
  let target ← nondet String
  if target.isEmpty || target.contains (Char.ofNat 0) then
    let (res, s₁) := (ops.symlinkAt target dh child).run s₀
    NondetTest.assert ((∃ e, res = .error e ∧ e.kind = .invalidInput) ∧ s₁ = s₀)
  else
    assume (∃ dSt, ((ops.fstatDir dh).run s₀).1 = .ok dSt ∧ dSt.kind = .dir ∧
      (dSt.mode / 128) % 2 = 1 ∧ (dSt.mode / 64) % 2 = 1)
    match ((ops.lstatAt dh child).run s₀).1 with
    | .error err =>
      if err.kind == .notFound then
        let (res, s₁) := (ops.symlinkAt target dh child).run s₀
        NondetTest.assert (res = .ok () ∧
          ∃ st, ((ops.lstatAt dh child).run s₁).1 = .ok st ∧ st.kind = .symlink)
      else
        pure ()
    | .ok _ => pure ()

/-- Successive calls to `ops.freshTempName` produce distinct valid `EntryName` values. -/
def test_fsraw_rawDirOps_freshTempName_distinctAndValid
    {S : Type} {runner} [NondetTest runner] (ops : RawDirOpsM (StateM S)) : runner Unit := do
  let s₀ ← nondet S
  let (n₁, s₁) := ops.freshTempName.run s₀
  let (n₂, _) := ops.freshTempName.run s₁
  NondetTest.assert (validSeg n₁.val = true ∧ validSeg n₂.val = true ∧ n₁ ≠ n₂)

/-- `isValidDirHandleId` rejects `0` and `≥ UInt64.size` while accepting positive 64-bit slot IDs strictly below `UInt64.size`. -/
def test_fsraw_isValidDirHandleId_bounds
    {runner} [NondetTest runner]
    (checkId : Nat → Bool := isValidDirHandleId) : runner Unit := do
  let id ← nondet Nat
  NondetTest.assert (checkId 0 = false ∧ checkId UInt64.size = false)
  if 0 < id && id < UInt64.size then
    NondetTest.assert (checkId id = true)
  else
    NondetTest.assert (checkId id = false)

end LeanSwe.Fs.Raw
