namespace LeanSwe.Compress

/-- Supported stream compression codecs wrapped by `LeanSwe.Compress`. -/
inductive Codec where
  /-- Zstandard format (`zstd`). -/
  | zstd
  /-- XZ / LZMA2 format (`xz`). -/
  | xz
  /-- GNU gzip format (`gzip`). -/
  | gzip
  deriving Repr, BEq, DecidableEq, Inhabited

/-- Configuration options for `compressWith`. -/
structure CompressOptions where
  /-- Optional compression level (`1..19` for `zstd`, `0..9` for `xz`, `1..9` for `gzip`); `none` uses tool default. -/
  level : Option Nat := none
  /-- Optional worker thread count (`0..4294967295` for `zstd`, `0..16384` for `xz`, where `0` auto-detects cores; rejected for `gzip`); `none` uses tool default. -/
  threads : Option Nat := none
  /-- Subprocess wall-clock timeout in milliseconds (must be greater than `0`). -/
  timeoutMs : Nat := 30000
  /-- Optional maximum allowed input size in bytes; `none` disables the input size cap. -/
  maxInputBytes : Option Nat := none
  /-- Maximum allowed `stdout` bytes returned on success (must be greater than `0`); `LeanSwe.Process` enforces `maxOutputBytes + 4096` combined `stdout + stderr` pipe bytes to accommodate diagnostic `stderr`. -/
  maxOutputBytes : Nat := 64 * 1024 * 1024
  deriving Repr, BEq, DecidableEq, Inhabited

/-- Configuration options for `decompressWith`. -/
structure DecompressOptions where
  /-- Subprocess wall-clock timeout in milliseconds (must be greater than `0`). -/
  timeoutMs : Nat := 30000
  /-- Optional maximum allowed compressed input size in bytes; `none` disables the input size cap. -/
  maxInputBytes : Option Nat := none
  /-- Maximum allowed `stdout` bytes returned on success to guard against decompression bombs (must be greater than `0`); `LeanSwe.Process` enforces `maxOutputBytes + 4096` combined `stdout + stderr` pipe bytes to accommodate diagnostic `stderr`. -/
  maxOutputBytes : Nat := 64 * 1024 * 1024
  deriving Repr, BEq, DecidableEq, Inhabited

/-- Closed classification of errors returned by `LeanSwe.Compress`. -/
inductive CompressErrorKind where
  /-- Required codec CLI binary is missing (`notFound`) or not executable (`permissionDenied`). -/
  | toolNotFound
  /-- Invalid codec option (`level`, `threads`), zero `timeoutMs` or `maxOutputBytes`, or `input.size > maxInputBytes`. -/
  | invalidInput
  /-- Compressed input has invalid magic, is truncated, fails CRC/checksum validation, or has trailing non-zero garbage. -/
  | corruptData
  /-- Decompression bomb or captured output exceeded limits (`stdout.size > maxOutputBytes` or combined `stdout + stderr > maxOutputBytes + 4096`). -/
  | outputLimitExceeded
  /-- Codec subprocess exceeded `timeoutMs`. -/
  | timedOut
  /-- Codec subprocess exited with a non-zero status on compression or was terminated by a signal. -/
  | commandFailed
  /-- Underlying OS pipe, spawn, or reap I/O failure. -/
  | ioError
  deriving Repr, BEq, DecidableEq, Inhabited

/-- Normalized error returned by `LeanSwe.Compress` operations. -/
structure CompressError where
  /-- Machine-checkable error category. -/
  kind : CompressErrorKind
  /-- Codec associated with the failure, when applicable. -/
  codec : Option Codec := none
  /-- Child process exit code when available. -/
  exitCode : Option Int := none
  /-- Decoded non-empty valid UTF-8 stderr output when available. -/
  stderr : Option String := none
  /-- Non-empty human-readable diagnostic message. -/
  message : String
  deriving Repr, BEq, DecidableEq, Inhabited

/-- Public compression and decompression API bundle parameterized over effect monad `m`. -/
structure CompressApiM (m : Type → Type) where
  /-- Compress `input` with `codec` using default `CompressOptions`. -/
  compress : Codec → ByteArray → m (Except CompressError ByteArray)
  /-- Decompress `input` with `codec` using default `DecompressOptions`. -/
  decompress : Codec → ByteArray → m (Except CompressError ByteArray)
  /-- Compress `input` with `codec` using explicit `CompressOptions`. -/
  compressWith : Codec → CompressOptions → ByteArray → m (Except CompressError ByteArray)
  /-- Decompress `input` with `codec` using explicit `DecompressOptions`. -/
  decompressWith : Codec → DecompressOptions → ByteArray → m (Except CompressError ByteArray)
  /-- Return `true` iff the CLI binary for `codec` is installed, executable, and succeeds on `--version`. -/
  isToolAvailable : Codec → m Bool

/-- Concrete `IO` API bundle for `LeanSwe.Compress`. -/
abbrev CompressApi := CompressApiM IO

end LeanSwe.Compress
