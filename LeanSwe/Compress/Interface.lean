import LeanSwe.Process.Interface
import LeanSwe.Compress.Types
import LeanSwe.Compress.Impl

namespace LeanSwe.Compress

/-- Default `CompressApi` backed by `LeanSwe.Process.defaultApi`. -/
def defaultApi : CompressApi :=
  Internal.mkApiM LeanSwe.Process.defaultApi

/-- Compress `input` with `codec` using default `CompressOptions`. -/
@[inline] def compress (codec : Codec) (input : ByteArray) :
    IO (Except CompressError ByteArray) :=
  defaultApi.compress codec input

/-- Decompress `input` with `codec` using default `DecompressOptions`. -/
@[inline] def decompress (codec : Codec) (input : ByteArray) :
    IO (Except CompressError ByteArray) :=
  defaultApi.decompress codec input

/-- Compress `input` with `codec` using explicit `CompressOptions`. -/
@[inline] def compressWith (codec : Codec) (opts : CompressOptions) (input : ByteArray) :
    IO (Except CompressError ByteArray) :=
  defaultApi.compressWith codec opts input

/-- Decompress `input` with `codec` using explicit `DecompressOptions`. -/
@[inline] def decompressWith (codec : Codec) (opts : DecompressOptions) (input : ByteArray) :
    IO (Except CompressError ByteArray) :=
  defaultApi.decompressWith codec opts input

/-- Return `true` iff the CLI binary for `codec` is installed, executable, and succeeds on `--version`. -/
@[inline] def isToolAvailable (codec : Codec) : IO Bool :=
  defaultApi.isToolAvailable codec

end LeanSwe.Compress
