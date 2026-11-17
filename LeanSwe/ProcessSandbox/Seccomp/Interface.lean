import LeanSwe.ProcessSandbox.Seccomp.Types
import LeanSwe.ProcessSandbox.Seccomp.Impl

namespace LeanSwe.ProcessSandbox.Seccomp

/-- Default `SeccompApi` backed by `LeanSwe.ProcessSandbox.Seccomp.Impl`. -/
def defaultApi : SeccompApi :=
  { compileSeccompBpf := Impl.compileSeccompBpf
    encodeSeccompBpf := Impl.encodeSeccompBpf }

/-- Compile the architecture-specific `seccomp` classic BPF filter program for `arch`. -/
@[inline] def compileSeccompBpf (arch : SeccompArch) : Array SockFilter :=
  defaultApi.compileSeccompBpf arch

/-- Serialize an `Array SockFilter` into contiguous `8 * n`-byte little-endian `struct sock_filter` wire bytes. -/
@[inline] def encodeSeccompBpf (prog : Array SockFilter) : ByteArray :=
  defaultApi.encodeSeccompBpf prog

end LeanSwe.ProcessSandbox.Seccomp
