import LeanSwe.Fs.Raw.Types

/-!
# Fs.Raw Package Internal Implementation

Implements the minimal single-step `RawFsOpsM IO` primitives over Lean's `IO.FS`
and an injected `PosixRawOps` bridge for POSIX calls in `c/fs_shim.c`.
Placed under `namespace LeanSwe.Fs.Raw.Internal` with zero `@[extern]` declarations.
-/

namespace LeanSwe.Fs.Raw.Internal

open LeanSwe.Fs.Raw (FsErrorKind FsError EntryKind FileStat FsRawError RawFsOpsM RawFsOps)

/-- Audited POSIX FFI operations injected by `LeanSwe.Fs.Raw.Interface`. -/
structure PosixRawOps where
  /-- Set file mode bits (`chmod`). -/
  chmod : String → UInt32 → IO Unit
  /-- Create symbolic link `(target, linkPath)`. -/
  symlink : String → String → IO Unit
  /-- Read symbolic link target path. -/
  readLink : String → IO String
  /-- Read POSIX mode bits (`st_mode & 0o7777`), optionally following symlinks. -/
  statMode : String → Bool → IO UInt32

/-- Return `msg` if non-empty, or `fallback` otherwise. -/
def nonEmptyMsg (fallback msg : String) : String :=
  if msg.isEmpty then fallback else msg

/-- Classify common Linux/macOS `errno` codes used across `otherError` and `inappropriateType`. -/
def classifyErrno (code : UInt32) (defaultKind : FsErrorKind) : FsErrorKind :=
  match code.toNat with
  | 1 | 13 => .permissionDenied
  | 2 => .notFound
  | 17 => .alreadyExists
  | 20 => .notADirectory
  | 21 => .isADirectory
  | 22 | 36 => .invalidInput
  | 39 | 66 => .notEmpty
  | _ => defaultKind

/-- Convert a pure `FsRawError` record into a normalized `FsError` with non-empty message. -/
def mapRawError : FsRawError → FsError
  | .noFileOrDirectory path code detail =>
    { kind := .notFound
      path := some path
      errnoCode := some code
      message := nonEmptyMsg s!"no such file or directory: {path}" detail }
  | .alreadyExists path? code detail =>
    { kind := .alreadyExists
      path := path?
      errnoCode := some code
      message := nonEmptyMsg "file or directory already exists" detail }
  | .permissionDenied path? code detail =>
    { kind := .permissionDenied
      path := path?
      errnoCode := some code
      message := nonEmptyMsg "permission denied" detail }
  | .inappropriateType path? code detail =>
    { kind := classifyErrno code .ioError
      path := path?
      errnoCode := some code
      message := nonEmptyMsg "inappropriate file type" detail }
  | .invalidArgument path? code detail =>
    { kind := .invalidInput
      path := path?
      errnoCode := some code
      message := nonEmptyMsg "invalid argument" detail }
  | .unsupportedOperation code detail =>
    { kind := .unsupported
      path := none
      errnoCode := some code
      message := nonEmptyMsg "unsupported filesystem operation" detail }
  | .otherError code detail =>
    { kind := classifyErrno code .ioError
      path := none
      errnoCode := some code
      message := nonEmptyMsg s!"os error {code}" detail }
  | .userError detail =>
    { kind := .ioError
      path := none
      errnoCode := none
      message := nonEmptyMsg "filesystem error" detail }

/-- Convert a Lean `IO.Error` into `FsRawError`. -/
def ioErrorToRaw (fallbackPath : Option String) : IO.Error → FsRawError
  | .noFileOrDirectory p code detail => .noFileOrDirectory p code detail
  | .alreadyExists p? code detail => .alreadyExists (p? <|> fallbackPath) code detail
  | .permissionDenied p? code detail => .permissionDenied (p? <|> fallbackPath) code detail
  | .inappropriateType p? code detail => .inappropriateType (p? <|> fallbackPath) code detail
  | .invalidArgument p? code detail => .invalidArgument (p? <|> fallbackPath) code detail
  | .unsupportedOperation code detail => .unsupportedOperation code detail
  | .unsatisfiedConstraints code detail => .otherError code detail
  | .illegalOperation code detail => .otherError code detail
  | .resourceBusy code detail => .otherError code detail
  | .resourceVanished code detail => .otherError code detail
  | .hardwareFault code detail => .otherError code detail
  | .protocolError code detail => .otherError code detail
  | .timeExpired code detail => .otherError code detail
  | .interrupted p code detail => .otherError code s!"{p}: {detail}"
  | .resourceExhausted p? code detail => .invalidArgument (p? <|> fallbackPath) code detail
  | .noSuchThing p? _ _ => .noFileOrDirectory (p?.or fallbackPath |>.getD "") 2 "no such file or directory"
  | .unexpectedEof => .userError "unexpected end of file"
  | .otherError code detail => .otherError code detail
  | .userError detail => .userError detail

/-- Normalize an `IO.Error` into an `FsError`, preserving `fallbackPath` if missing. -/
def mapIoError (fallbackPath : Option String) (err : IO.Error) : FsError :=
  let mapped := mapRawError (ioErrorToRaw fallbackPath err)
  { mapped with path := mapped.path <|> fallbackPath }

/-- Run an `IO α` action, capturing exceptions into `Except FsError α`. -/
def catchFs {α : Type} (path? : Option String) (act : IO α) : IO (Except FsError α) := do
  try
    return .ok (← act)
  catch err =>
    return .error (mapIoError path? err)

/-- Map Lean's `IO.FS.FileType` to `EntryKind`. -/
def toEntryKind : IO.FS.FileType → EntryKind
  | .file => .file
  | .dir => .dir
  | .symlink => .symlink
  | .other => .other

/-- Build the concrete `RawFsOps` bundle from injected POSIX C-ABI hooks. -/
def mkRawOps (posix : PosixRawOps) : RawFsOps :=
  { mapRawError := mapRawError
    stat := fun follow path => catchFs (some path) do
      let fp := System.FilePath.mk path
      let md ← if follow then fp.metadata else fp.symlinkMetadata
      let mode ← posix.statMode path follow
      return {
        kind := toEntryKind md.type
        byteSize := md.byteSize.toNat
        mode := mode.toNat
        modifiedSec := md.modified.sec
        modifiedNsec := md.modified.nsec.toNat
        accessedSec := md.accessed.sec
        accessedNsec := md.accessed.nsec.toNat }
    readDir := fun path => catchFs (some path) do
      let entries ← (System.FilePath.mk path).readDir
      return entries.map (·.fileName)
    createDir := fun path => catchFs (some path) (IO.FS.createDir (System.FilePath.mk path))
    removeDir := fun path => catchFs (some path) (IO.FS.removeDir (System.FilePath.mk path))
    unlinkFile := fun path => catchFs (some path) (IO.FS.removeFile (System.FilePath.mk path))
    readBytes := fun path => catchFs (some path) (IO.FS.readBinFile (System.FilePath.mk path))
    writeBytes := fun path b => catchFs (some path) (IO.FS.writeBinFile (System.FilePath.mk path) b)
    appendText := fun path content => catchFs (some path) do
      let h ← IO.FS.Handle.mk (System.FilePath.mk path) .append
      h.putStr content
      h.flush
    rename := fun s d => catchFs (some s) (IO.FS.rename (System.FilePath.mk s) (System.FilePath.mk d))
    chmod := fun path mode => catchFs (some path) (posix.chmod path (UInt32.ofNat mode))
    symlink := fun target linkPath => catchFs (some linkPath) (posix.symlink target linkPath)
    readLink := fun path => catchFs (some path) (posix.readLink path)
    realPath := fun path => catchFs (some path) do
      let rp ← IO.FS.realPath (System.FilePath.mk path)
      return rp.toString
    cwd := catchFs none do
      let d ← IO.currentDir
      return d.toString
    monotonicNonce := IO.monoNanosNow }

/-- Temporary directory bracket modeled after Python `tempfile.TemporaryDirectory`. -/
def withTempDir {α : Type} (f : String → IO (Except FsError α)) : IO (Except FsError α) := do
  match ← catchFs none (IO.FS.withTempDir fun dir => f dir.toString) with
  | .error e => return .error e
  | .ok inner => return inner

end LeanSwe.Fs.Raw.Internal
