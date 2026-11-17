import LeanSwe.ProcessSandbox.Seccomp.Model

namespace LeanSwe.ProcessSandbox.Seccomp.Impl

open LeanSwe.ProcessSandbox.Model

/-- Emit the 4-instruction `seccomp` prologue verifying `seccomp_data.arch == auditArchOf arch` and loading `seccomp_data.nr`. -/
def archHeaderBlock (arch : SeccompArch) : List SockFilter :=
  [ bpfStmt BPF_LD_W_ABS SECCOMP_OFFSET_ARCH
  , bpfJump BPF_JMP_JEQ_K (auditArchOf arch) 1 0
  , bpfStmt BPF_RET_K SECCOMP_RET_ERRNO_EPERM
  , bpfStmt BPF_LD_W_ABS SECCOMP_OFFSET_NR
  ]

/-- Emit the `x86_64` `__X32_SYSCALL_BIT` guard (`nr ≥ 0x40000000 -> EPERM`); empty on `aarch64`. -/
def x32GuardBlock : SeccompArch → List SockFilter
  | .x86_64 =>
    [ bpfJump BPF_JMP_JGE_K X32_SYSCALL_BIT 0 1
    , bpfStmt BPF_RET_K SECCOMP_RET_ERRNO_EPERM
    ]
  | .aarch64 => []

/-- Emit the 2-instruction `clone3` check returning `ENOSYS` for glibc `clone` fallback. -/
def clone3Block (nr : UInt32) : List SockFilter :=
  [ bpfJump BPF_JMP_JEQ_K nr 0 1
  , bpfStmt BPF_RET_K SECCOMP_RET_ERRNO_ENOSYS
  ]

/-- Emit the 6-instruction syscall mask guard: if `nr` matches, reject with `EPERM` when `(word(argOff) &&& mask) != 0` and allow otherwise. -/
def guardMaskBlock (nr argOff mask : UInt32) : List SockFilter :=
  [ bpfJump BPF_JMP_JEQ_K nr 0 5
  , bpfStmt BPF_LD_W_ABS argOff
  , bpfStmt BPF_ALU_AND_K mask
  , bpfJump BPF_JMP_JEQ_K 0 1 0
  , bpfStmt BPF_RET_K SECCOMP_RET_ERRNO_EPERM
  , bpfStmt BPF_RET_K SECCOMP_RET_ALLOW
  ]

/-- Emit the 6-instruction `socket` guard rejecting `AF_UNIX` and `AF_SMC` with `EPERM` and allowing all other domains. -/
def socketBlock (nr : UInt32) : List SockFilter :=
  [ bpfJump BPF_JMP_JEQ_K nr 0 5
  , bpfStmt BPF_LD_W_ABS (seccompArgLowOffset 0)
  , bpfJump BPF_JMP_JEQ_K LINUX_AF_UNIX 1 0
  , bpfJump BPF_JMP_JEQ_K LINUX_AF_SMC 0 1
  , bpfStmt BPF_RET_K SECCOMP_RET_ERRNO_EPERM
  , bpfStmt BPF_RET_K SECCOMP_RET_ALLOW
  ]

/-- Emit the 11-instruction `socketpair` guard allowing `(AF_UNIX, SOCK_STREAM | SOCK_SEQPACKET, proto == 0)` and rejecting all others with `EPERM`. -/
def socketpairBlock (nr : UInt32) : List SockFilter :=
  [ bpfJump BPF_JMP_JEQ_K nr 0 10
  , bpfStmt BPF_LD_W_ABS (seccompArgLowOffset 0)
  , bpfJump BPF_JMP_JEQ_K LINUX_AF_UNIX 0 6
  , bpfStmt BPF_LD_W_ABS (seccompArgLowOffset 2)
  , bpfJump BPF_JMP_JEQ_K 0 0 4
  , bpfStmt BPF_LD_W_ABS (seccompArgLowOffset 1)
  , bpfStmt BPF_ALU_AND_K LINUX_SOCK_TYPE_MASK_CLEAR_FLAGS
  , bpfJump BPF_JMP_JEQ_K LINUX_SOCK_STREAM 2 0
  , bpfJump BPF_JMP_JEQ_K LINUX_SOCK_SEQPACKET 1 0
  , bpfStmt BPF_RET_K SECCOMP_RET_ERRNO_EPERM
  , bpfStmt BPF_RET_K SECCOMP_RET_ALLOW
  ]

/-- Emit the 2-instruction unconditional `nr -> EPERM` check block. -/
def denyNrBlock (nr : UInt32) : List SockFilter :=
  [ bpfJump BPF_JMP_JEQ_K nr 0 1
  , bpfStmt BPF_RET_K SECCOMP_RET_ERRNO_EPERM
  ]

/-- Emit the concatenated `EPERM` check blocks for a list of denied syscall numbers. -/
def denyListBlock (nrs : List UInt32) : List SockFilter :=
  nrs.flatMap denyNrBlock

/-- Assemble the full `seccomp` classic BPF instruction list for `arch`. -/
def compileSeccompBpfList (arch : SeccompArch) : List SockFilter :=
  let nrs := syscallNumbersFor arch
  archHeaderBlock arch ++
  x32GuardBlock arch ++
  clone3Block nrs.clone3 ++
  guardMaskBlock nrs.clone (seccompArgLowOffset 0) CLONE_NEW_NS_MASK ++
  socketBlock nrs.socket ++
  socketpairBlock nrs.socketpair ++
  guardMaskBlock nrs.sendto (seccompArgLowOffset 3) LINUX_MSG_FASTOPEN ++
  guardMaskBlock nrs.sendmsg (seccompArgLowOffset 2) LINUX_MSG_FASTOPEN ++
  guardMaskBlock nrs.sendmmsg (seccompArgLowOffset 3) LINUX_MSG_FASTOPEN ++
  denyListBlock (denySyscallNumbers nrs) ++
  [bpfStmt BPF_RET_K SECCOMP_RET_ALLOW]

/-- Compile the architecture-specific `seccomp` classic BPF filter program for `arch`. -/
def compileSeccompBpf (arch : SeccompArch) : Array SockFilter :=
  (compileSeccompBpfList arch).toArray

/-- Encode one `SockFilter` instruction as 8 little-endian Linux `struct sock_filter` bytes. -/
def encodeSockFilterList (insn : SockFilter) : List UInt8 :=
  let c := insn.code.toNat
  let k := insn.k.toNat
  [ UInt8.ofNat (c % 256)
  , UInt8.ofNat ((c / 256) % 256)
  , insn.jt
  , insn.jf
  , UInt8.ofNat (k % 256)
  , UInt8.ofNat ((k / 256) % 256)
  , UInt8.ofNat ((k / 65536) % 256)
  , UInt8.ofNat ((k / 16777216) % 256)
  ]

/-- Serialize an `Array SockFilter` into contiguous `8 * prog.size`-byte little-endian `struct sock_filter` bytes. -/
def encodeSeccompBpf (prog : Array SockFilter) : ByteArray :=
  ByteArray.mk (prog.toList.flatMap encodeSockFilterList).toArray

end LeanSwe.ProcessSandbox.Seccomp.Impl
