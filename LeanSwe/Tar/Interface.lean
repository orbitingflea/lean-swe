import LeanSwe.Tar.Types
import LeanSwe.Tar.Impl

namespace LeanSwe.Tar

/-- Default `TarApi` record bundling the pure `LeanSwe.Tar` operations. -/
def defaultApi : TarApi :=
  Impl.makeTarApi

/-- Serialize `entries` into a USTAR/PAX tar byte array using default `PackOptions`. -/
@[inline] def pack (entries : List TarEntry) : Except TarError ByteArray :=
  Impl.pack entries

/-- Serialize `entries` into a USTAR/PAX tar byte array using explicit `PackOptions`. -/
@[inline] def packWith (opts : PackOptions) (entries : List TarEntry) : Except TarError ByteArray :=
  Impl.packWith opts entries

/-- Deserialize a USTAR/PAX tar byte array using default `UnpackOptions`. -/
@[inline] def unpack (bytes : ByteArray) : Except TarError (List TarEntry) :=
  Impl.unpack bytes

/-- Deserialize a USTAR/PAX tar byte array using explicit `UnpackOptions` and safety bounds. -/
@[inline] def unpackWith (opts : UnpackOptions) (bytes : ByteArray) : Except TarError (List TarEntry) :=
  Impl.unpackWith opts bytes

end LeanSwe.Tar
