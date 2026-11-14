import LeanSwe.Fs.Raw.Types

/-!
# Fs Package Types

Public data structs, error enums, and generic `FsApiM` bundle for `LeanSwe.Fs`.
Re-exports shared primitive types from `LeanSwe.Fs.Raw.Types` and stays free of
OS and implementation internals so `SpecTests` depend only on this module.
-/

namespace LeanSwe.Fs

export LeanSwe.Fs.Raw
  (FsErrorKind FsError EntryKind FileStat FsRawError RawFsOpsM RawFsOps)

/-- Single yielded directory node from `walk` (analogous to Python `os.walk` triples). -/
structure WalkEntry where
  /-- Directory path relative to walk root (`"."` for the walk root itself). -/
  root : String
  /-- Sorted immediate child directory names. -/
  dirs : Array String
  /-- Sorted immediate child non-directory entry names. -/
  files : Array String
  deriving Repr, BEq, DecidableEq

/-- Public operations exported by `LeanSwe.Fs`, parameterized over effect monad `m`. -/
structure FsApiM (m : Type → Type) where
  /-- Join two paths using `/` (`Path.joinpath`). -/
  join : String → String → String
  /-- Join an array of path segments left-to-right. -/
  joinMany : Array String → String
  /-- Lexically normalize `.` and `..` segments and redundant `/` separators (`os.path.normpath`). -/
  normPath : String → String
  /-- Return parent directory path, or `none` when at root or single component. -/
  parent : String → Option String
  /-- Return final path component name, if present. -/
  name : String → Option String
  /-- Return final path component without its last suffix (`Path.stem`). -/
  stem : String → Option String
  /-- Return final `.ext` suffix of filename (`Path.suffix`), or `""` when none. -/
  suffix : String → String
  /-- Return all `.ext` suffixes of filename (`Path.suffixes`). -/
  suffixes : String → Array String
  /-- Replace the final path component (`Path.with_name`). -/
  withName : String → String → Except FsError String
  /-- Replace or strip the last suffix (`Path.with_suffix`). -/
  withSuffix : String → String → Except FsError String
  /-- Return `true` iff `path` begins with `/`. -/
  isAbsolute : String → Bool
  /-- Compute lexical path of `path` relative to `base` (`Path.relative_to`). -/
  relativeTo : String → String → Except FsError String
  /-- Convert a raw OS error record into a normalized `FsError` with non-empty message. -/
  mapRawError : FsRawError → FsError
  /-- Read entire UTF-8 text file (`Path.read_text`). -/
  readText : String → m (Except FsError String)
  /-- Write or overwrite UTF-8 text file (`Path.write_text`). -/
  writeText : String → String → m (Except FsError Unit)
  /-- Append UTF-8 text to file, creating it if absent. -/
  appendText : String → String → m (Except FsError Unit)
  /-- Read entire binary file (`Path.read_bytes`). -/
  readBytes : String → m (Except FsError ByteArray)
  /-- Write or overwrite binary file (`Path.write_bytes`). -/
  writeBytes : String → ByteArray → m (Except FsError Unit)
  /-- Atomically write text via a sibling temporary file and `rename`. -/
  atomicWriteText : String → String → m (Except FsError Unit)
  /-- Create empty file if missing (`Path.touch`). -/
  touch : String → Bool → m (Except FsError Unit)
  /-- Create directory, optionally creating parents or succeeding if present (`Path.mkdir`). -/
  mkdir : String → Bool → Bool → m (Except FsError Unit)
  /-- Remove file or symlink (`Path.unlink`). -/
  unlink : String → Bool → m (Except FsError Unit)
  /-- Remove empty directory (`Path.rmdir`). -/
  rmdir : String → m (Except FsError Unit)
  /-- Recursively delete directory tree (`shutil.rmtree`). -/
  rmtree : String → Bool → m (Except FsError Unit)
  /-- Rename or replace file/directory (`os.replace`). -/
  rename : String → String → m (Except FsError Unit)
  /-- Copy file contents (`shutil.copyfile`). -/
  copyFile : String → String → m (Except FsError Unit)
  /-- Recursively copy directory tree (`shutil.copytree`). -/
  copyTree : String → String → Bool → m (Except FsError Unit)
  /-- Check whether `path` exists, following symlinks (`Path.exists`). -/
  pathExists : String → m (Except FsError Bool)
  /-- Check whether `path` refers to a regular file, following symlinks (`Path.is_file`). -/
  isFile : String → m (Except FsError Bool)
  /-- Check whether `path` refers to a directory, following symlinks (`Path.is_dir`). -/
  isDir : String → m (Except FsError Bool)
  /-- Check whether `path` itself is a symbolic link (`Path.is_symlink`). -/
  isSymlink : String → m (Except FsError Bool)
  /-- Inspect metadata following symlinks (`os.stat`). -/
  stat : String → m (Except FsError FileStat)
  /-- Inspect metadata without following symlinks (`os.lstat`). -/
  lstat : String → m (Except FsError FileStat)
  /-- Set POSIX permission mode bits (`os.chmod`). -/
  chmod : String → Nat → m (Except FsError Unit)
  /-- Create symbolic link at `linkPath` pointing to `target` (`os.symlink`). -/
  symlink : String → String → m (Except FsError Unit)
  /-- Read symbolic link target (`os.readlink`). -/
  readLink : String → m (Except FsError String)
  /-- Resolve symlinks and return canonical absolute path (`Path.resolve`). -/
  resolve : String → m (Except FsError String)
  /-- Return current working directory (`os.getcwd`). -/
  cwd : m (Except FsError String)
  /-- Return sorted immediate child names in directory (`os.listdir`). -/
  listDir : String → m (Except FsError (Array String))
  /-- Top-down directory walk yielding sorted children (`os.walk`). -/
  walk : String → m (Except FsError (Array WalkEntry))
  /-- Find sorted relative paths under `root` matching glob `pattern` (`Path.glob`). -/
  glob : String → String → m (Except FsError (Array String))
  /-- Recursively match glob `pattern` under `root` (`Path.rglob`). -/
  rglob : String → String → m (Except FsError (Array String))

/-- Concrete `IO` filesystem API bundle for `LeanSwe.Fs`. -/
abbrev FsApi := FsApiM IO

end LeanSwe.Fs
