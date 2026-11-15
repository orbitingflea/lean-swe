namespace LeanSwe.Tar

/-- Format a `ByteArray` as a Lean `List UInt8` representation for `Repr` instances. -/
def reprByteArray (bs : ByteArray) : Std.Format :=
  repr bs.toList

/-- Maximum byte size allowed for a single PAX (`'x'`) extended header payload (`1 MiB`). -/
def maxPaxHeaderBytes : Nat := 1024 * 1024

/-- Archive entry kind supported in `LeanSwe.Tar` v1. -/
inductive EntryKind where
  /-- Regular file entry (`typeflag = '0'` or `'\0'`). -/
  | regular
  /-- Directory entry (`typeflag = '5'`). -/
  | directory
  /-- Symbolic link entry (`typeflag = '2'`). -/
  | symlink
  deriving Repr, BEq, DecidableEq, Inhabited

/-- Single USTAR/PAX tar archive entry. -/
structure TarEntry where
  /-- Archive entry path (canonicalized relative or opt-in absolute path). -/
  path : String
  /-- Entry kind (`regular`, `directory`, or `symlink`). -/
  kind : EntryKind
  /-- POSIX file mode bits (low 12 bits `mode &&& 0o7777` are preserved on wire). -/
  mode : UInt32 := 0o644
  /-- Numeric owner user ID (`< 2^64`). -/
  uid : Nat := 0
  /-- Numeric owner group ID (`< 2^64`). -/
  gid : Nat := 0
  /-- Modification timestamp in whole seconds since Unix epoch (`< 2^64`). -/
  mtime : Nat := 0
  /-- Owner user name (UTF-8 without NUL bytes). -/
  uname : String := ""
  /-- Owner group name (UTF-8 without NUL bytes). -/
  gname : String := ""
  /-- Regular file payload bytes (must be empty for `directory` and `symlink`). -/
  data : ByteArray := ByteArray.empty
  /-- Symbolic link target path (must be empty for `regular` and `directory`). -/
  linkTarget : String := ""
  deriving Inhabited

instance : Repr TarEntry where
  reprPrec e _ :=
    "{" ++
      " path := " ++ repr e.path ++
      ", kind := " ++ repr e.kind ++
      ", mode := " ++ repr e.mode ++
      ", uid := " ++ repr e.uid ++
      ", gid := " ++ repr e.gid ++
      ", mtime := " ++ repr e.mtime ++
      ", uname := " ++ repr e.uname ++
      ", gname := " ++ repr e.gname ++
      ", data := " ++ reprByteArray e.data ++
      ", linkTarget := " ++ repr e.linkTarget ++
    " }"

instance : BEq TarEntry where
  beq a b :=
    a.path == b.path &&
    a.kind == b.kind &&
    a.mode == b.mode &&
    a.uid == b.uid &&
    a.gid == b.gid &&
    a.mtime == b.mtime &&
    a.uname == b.uname &&
    a.gname == b.gname &&
    a.data.toList == b.data.toList &&
    a.linkTarget == b.linkTarget

/-- Options controlling tar archive serialization (`packWith`). -/
structure PackOptions where
  /-- Allow leading `'/'` in entry paths and symlink targets. -/
  allowAbsolute : Bool := false
  /-- Allow `".."` traversal segments in paths and escaping symlink targets. -/
  allowParentTraversal : Bool := false
  /-- Zero non-deterministic metadata (`uid`, `gid`, `mtime`, `uname`, `gname`) during packing. -/
  deterministic : Bool := false
  deriving Repr, BEq, DecidableEq, Inhabited

/-- Options controlling tar archive deserialization and safety limits (`unpackWith`). -/
structure UnpackOptions where
  /-- Allow leading `'/'` in entry paths and symlink targets. -/
  allowAbsolute : Bool := false
  /-- Allow `".."` traversal segments in paths and escaping symlink targets. -/
  allowParentTraversal : Bool := false
  /-- Maximum number of non-PAX entries permitted in an archive. -/
  maxEntries : Nat := 100000
  /-- Maximum sum of decoded `entry.data.size` bytes permitted across all entries (`256 MiB`). -/
  maxTotalBytes : Nat := 256 * 1024 * 1024
  deriving Repr, BEq, DecidableEq, Inhabited

/-- Machine-checkable error categories for `LeanSwe.Tar`. -/
inductive TarErrorKind where
  /-- Path or symlink target was empty, root-only, contained NUL, or had empty/trailing-slash violations. -/
  | invalidPath
  /-- Path or symlink target violated safety policy (leading `'/'`, `"."`, `".."`, or symlink escape). -/
  | unsafePath
  /-- Archive contained two entries resolving to the same normalized path. -/
  | duplicatePath
  /-- Malformed USTAR/PAX header, syntax, NUL in metadata, or invalid trailer structure. -/
  | invalidHeader
  /-- USTAR 512-byte header unsigned checksum did not match stored checksum. -/
  | checksumMismatch
  /-- Input was empty, not 512-byte aligned, ended prematurely, or lacked a two-zero-block trailer. -/
  | truncatedArchive
  /-- Archive contained an unsupported tar entry typeflag or `GNU.sparse.*` / `'g'` header. -/
  | unsupportedEntry
  /-- Numeric header or PAX field was negative or exceeded 64-bit (`2^64`) / 32-bit mode bounds. -/
  | sizeOverflow
  /-- USTAR or PAX text field contained invalid UTF-8 bytes. -/
  | invalidEncoding
  /-- Archive exceeded `maxEntries`, `maxTotalBytes`, or `maxPaxHeaderBytes`. -/
  | resourceLimitExceeded
  deriving Repr, BEq, DecidableEq, Inhabited

/-- Typed error returned by `LeanSwe.Tar` operations. -/
structure TarError where
  /-- Machine-checkable error category. -/
  kind : TarErrorKind
  /-- Non-empty human-readable diagnostic message. -/
  message : String
  /-- Best-effort entry path associated with the failure, when available. -/
  entryPath : Option String := none
  /-- Best-effort byte offset in the archive where the failure occurred, when available. -/
  offset : Option Nat := none
  deriving Repr, BEq, DecidableEq, Inhabited

/-- Public pure operations exported by `LeanSwe.Tar`. -/
structure TarApi where
  /-- Serialize `entries` into a USTAR/PAX tar byte array using default `PackOptions`. -/
  pack : List TarEntry → Except TarError ByteArray
  /-- Serialize `entries` into a USTAR/PAX tar byte array using explicit `PackOptions`. -/
  packWith : PackOptions → List TarEntry → Except TarError ByteArray
  /-- Deserialize a USTAR/PAX tar byte array using default `UnpackOptions`. -/
  unpack : ByteArray → Except TarError (List TarEntry)
  /-- Deserialize a USTAR/PAX tar byte array using explicit `UnpackOptions` and safety bounds. -/
  unpackWith : UnpackOptions → ByteArray → Except TarError (List TarEntry)

end LeanSwe.Tar
