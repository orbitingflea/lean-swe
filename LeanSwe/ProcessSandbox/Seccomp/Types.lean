import LeanSwe.ProcessSandbox.Seccomp.Model

namespace LeanSwe.ProcessSandbox.Seccomp

export LeanSwe.ProcessSandbox.Model (SeccompArch SockFilter)

/-- Pure `seccomp` classic BPF compiler and little-endian wire serializer API exported by `LeanSwe.ProcessSandbox.Seccomp`. -/
structure SeccompApi where
  /-- Compile the architecture-specific `seccomp` classic BPF instruction array for a sandboxed guest. -/
  compileSeccompBpf : SeccompArch → Array SockFilter
  /-- Serialize an `Array SockFilter` into contiguous `8 * n`-byte little-endian `struct sock_filter` wire bytes. -/
  encodeSeccompBpf : Array SockFilter → ByteArray

end LeanSwe.ProcessSandbox.Seccomp
