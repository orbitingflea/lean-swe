import LeanSwe.ProcessSandbox.Seccomp.Model
import LeanSwe.ProcessSandbox.Seccomp.Interface

namespace LeanSwe.ProcessSandbox.Seccomp.RuntimeTests

open LeanSwe.ProcessSandbox.Model

private def assertTrue (cond : Bool) (msg : String) : IO Unit := do
  if !cond then
    throw (IO.userError s!"ASSERTION FAILED: {msg}")

private def assertVerdict (prog : Array SockFilter) (inp : SeccompData) (expected : UInt32)
    (msg : String) : IO Unit := do
  let got := evalBpf prog inp
  if got != some expected then
    throw (IO.userError
      s!"ASSERTION FAILED: {msg} (got {repr got}, expected {repr (some expected)})")

private def cloneNewNsBits : Array UInt32 :=
  #[ 0x00020000
   , 0x02000000
   , 0x04000000
   , 0x08000000
   , 0x10000000
   , 0x20000000
   , 0x40000000 ]

private def testArchCompiledFilter (arch : SeccompArch) : IO Unit := do
  let prog := compileSeccompBpf arch
  let bytes := encodeSeccompBpf prog
  let nrs := syscallNumbersFor arch
  let nativeArch := auditArchOf arch

  assertTrue (0 < prog.size && prog.size ≤ SECCOMP_MAX_INSNS)
    s!"{repr arch} compiled program size out of bounds: {prog.size}"
  assertTrue (isValidLinuxSeccompProg prog)
    s!"{repr arch} compiled program failed isValidLinuxSeccompProg"
  assertTrue (bytes.size == 8 * prog.size)
    s!"{repr arch} encoded size {bytes.size} != 8 * {prog.size}"
  assertTrue (bytes == encodeSeccompBpfModel prog)
    s!"{repr arch} encodeSeccompBpf diverged from encodeSeccompBpfModel"

  assertVerdict prog { nr := 0, arch := 0 } SECCOMP_RET_ERRNO_EPERM
    s!"{repr arch} wrong arch must return EPERM"
  assertVerdict prog { nr := nrs.clone3, arch := nativeArch } SECCOMP_RET_ERRNO_ENOSYS
    s!"{repr arch} clone3 must return ENOSYS"

  assertVerdict prog
    { nr := nrs.clone, arch := nativeArch, args := { a0 := CLONE_NEW_NS_MASK.toUInt64 } }
    SECCOMP_RET_ERRNO_EPERM
    s!"{repr arch} clone with CLONE_NEW_NS_MASK must return EPERM"
  for bit in cloneNewNsBits do
    assertVerdict prog
      { nr := nrs.clone, arch := nativeArch, args := { a0 := bit.toUInt64 } }
      SECCOMP_RET_ERRNO_EPERM
      s!"{repr arch} clone with individual CLONE_NEW* bit {bit} must return EPERM"
  assertVerdict prog
    { nr := nrs.clone, arch := nativeArch, args := { a0 := 0x81fdffff } }
    SECCOMP_RET_ALLOW
    s!"{repr arch} clone with non-namespace bits 0x81fdffff must return ALLOW"
  assertVerdict prog
    { nr := nrs.clone
    , arch := nativeArch
    , args :=
        { a0 := 17
        , a1 := CLONE_NEW_NS_MASK.toUInt64
        , a2 := CLONE_NEW_NS_MASK.toUInt64
        , a3 := CLONE_NEW_NS_MASK.toUInt64 } }
    SECCOMP_RET_ALLOW
    s!"{repr arch} clone(SIGCHLD) with CLONE_NEW* in a1/a2/a3 must return ALLOW"

  assertVerdict prog
    { nr := nrs.socket, arch := nativeArch, args := { a0 := LINUX_AF_UNIX.toUInt64 } }
    SECCOMP_RET_ERRNO_EPERM
    s!"{repr arch} socket(AF_UNIX) must return EPERM"
  assertVerdict prog
    { nr := nrs.socket, arch := nativeArch, args := { a0 := LINUX_AF_SMC.toUInt64 } }
    SECCOMP_RET_ERRNO_EPERM
    s!"{repr arch} socket(AF_SMC) must return EPERM"
  assertVerdict prog
    { nr := nrs.socket
    , arch := nativeArch
    , args :=
        { a0 := 2
        , a1 := LINUX_AF_UNIX.toUInt64
        , a2 := LINUX_AF_SMC.toUInt64
        , a3 := LINUX_AF_UNIX.toUInt64 } }
    SECCOMP_RET_ALLOW
    s!"{repr arch} socket(AF_INET) with AF_UNIX/AF_SMC in a1/a2/a3 must return ALLOW"

  assertVerdict prog
    { nr := nrs.socketpair
    , arch := nativeArch
    , args := { a0 := LINUX_AF_UNIX.toUInt64, a1 := LINUX_SOCK_STREAM.toUInt64, a2 := 0, a3 := 1 } }
    SECCOMP_RET_ALLOW
    s!"{repr arch} socketpair(AF_UNIX, SOCK_STREAM, 0) must return ALLOW"
  assertVerdict prog
    { nr := nrs.socketpair
    , arch := nativeArch
    , args := { a0 := LINUX_AF_UNIX.toUInt64, a1 := LINUX_SOCK_SEQPACKET.toUInt64, a2 := 0 } }
    SECCOMP_RET_ALLOW
    s!"{repr arch} socketpair(AF_UNIX, SOCK_SEQPACKET, 0) must return ALLOW"
  assertVerdict prog
    { nr := nrs.socketpair
    , arch := nativeArch
    , args :=
        { a0 := LINUX_AF_UNIX.toUInt64
        , a1 := (LINUX_SOCK_STREAM ||| LINUX_SOCK_NONBLOCK).toUInt64
        , a2 := 0 } }
    SECCOMP_RET_ALLOW
    s!"{repr arch} socketpair(AF_UNIX, SOCK_STREAM|NONBLOCK, 0) must return ALLOW"
  assertVerdict prog
    { nr := nrs.socketpair
    , arch := nativeArch
    , args :=
        { a0 := LINUX_AF_UNIX.toUInt64
        , a1 := (LINUX_SOCK_SEQPACKET ||| LINUX_SOCK_NONBLOCK ||| LINUX_SOCK_CLOEXEC).toUInt64
        , a2 := 0 } }
    SECCOMP_RET_ALLOW
    s!"{repr arch} socketpair(AF_UNIX, SOCK_SEQPACKET|NONBLOCK|CLOEXEC, 0) must return ALLOW"
  assertVerdict prog
    { nr := nrs.socketpair
    , arch := nativeArch
    , args := { a0 := LINUX_AF_UNIX.toUInt64, a1 := LINUX_SOCK_DGRAM.toUInt64, a2 := 0 } }
    SECCOMP_RET_ERRNO_EPERM
    s!"{repr arch} socketpair(AF_UNIX, SOCK_DGRAM, 0) must return EPERM"
  assertVerdict prog
    { nr := nrs.socketpair
    , arch := nativeArch
    , args := { a0 := LINUX_AF_UNIX.toUInt64, a1 := LINUX_SOCK_STREAM.toUInt64, a2 := 1, a3 := 0 } }
    SECCOMP_RET_ERRNO_EPERM
    s!"{repr arch} socketpair(AF_UNIX, SOCK_STREAM, 1) must return EPERM"
  assertVerdict prog
    { nr := nrs.socketpair
    , arch := nativeArch
    , args := { a0 := 2, a1 := LINUX_SOCK_STREAM.toUInt64, a2 := 0 } }
    SECCOMP_RET_ERRNO_EPERM
    s!"{repr arch} socketpair(AF_INET, SOCK_STREAM, 0) must return EPERM"

  assertVerdict prog
    { nr := nrs.sendto, arch := nativeArch, args := { a3 := LINUX_MSG_FASTOPEN.toUInt64 } }
    SECCOMP_RET_ERRNO_EPERM
    s!"{repr arch} sendto(MSG_FASTOPEN) must return EPERM"
  assertVerdict prog
    { nr := nrs.sendto
    , arch := nativeArch
    , args :=
        { a0 := LINUX_MSG_FASTOPEN.toUInt64
        , a1 := LINUX_MSG_FASTOPEN.toUInt64
        , a2 := LINUX_MSG_FASTOPEN.toUInt64
        , a3 := 0 } }
    SECCOMP_RET_ALLOW
    s!"{repr arch} sendto with flags=0 and MSG_FASTOPEN in a0/a1/a2 must return ALLOW"

  assertVerdict prog
    { nr := nrs.sendmsg, arch := nativeArch, args := { a2 := LINUX_MSG_FASTOPEN.toUInt64 } }
    SECCOMP_RET_ERRNO_EPERM
    s!"{repr arch} sendmsg(MSG_FASTOPEN) must return EPERM"
  assertVerdict prog
    { nr := nrs.sendmsg
    , arch := nativeArch
    , args :=
        { a0 := LINUX_MSG_FASTOPEN.toUInt64
        , a1 := LINUX_MSG_FASTOPEN.toUInt64
        , a2 := 0
        , a3 := LINUX_MSG_FASTOPEN.toUInt64 } }
    SECCOMP_RET_ALLOW
    s!"{repr arch} sendmsg with flags=0 and MSG_FASTOPEN in a0/a1/a3 must return ALLOW"

  assertVerdict prog
    { nr := nrs.sendmmsg, arch := nativeArch, args := { a3 := LINUX_MSG_FASTOPEN.toUInt64 } }
    SECCOMP_RET_ERRNO_EPERM
    s!"{repr arch} sendmmsg(MSG_FASTOPEN) must return EPERM"
  assertVerdict prog
    { nr := nrs.sendmmsg
    , arch := nativeArch
    , args :=
        { a0 := LINUX_MSG_FASTOPEN.toUInt64
        , a1 := LINUX_MSG_FASTOPEN.toUInt64
        , a2 := LINUX_MSG_FASTOPEN.toUInt64
        , a3 := 0 } }
    SECCOMP_RET_ALLOW
    s!"{repr arch} sendmmsg with flags=0 and MSG_FASTOPEN in a0/a1/a2 must return ALLOW"

  for nr in denySyscallNumbers nrs do
    assertVerdict prog { nr := nr, arch := nativeArch } SECCOMP_RET_ERRNO_EPERM
      s!"{repr arch} denied syscall {nr} must return EPERM"

private def testWireEncoding : IO Unit := do
  let sample : SockFilter := { code := 0x1234, jt := 0xab, jf := 0xcd, k := 0xdeadbeef }
  let encoded := encodeSeccompBpf #[sample]
  let expected := ByteArray.mk #[0x34, 0x12, 0xab, 0xcd, 0xef, 0xbe, 0xad, 0xde]
  assertTrue (encoded == expected)
    s!"little-endian encoding mismatch: got {repr encoded.data.toList}"
  assertTrue (encodeSeccompBpf (compileSeccompBpf .x86_64) != encodeSeccompBpf (compileSeccompBpf .aarch64))
    "x86_64 and aarch64 compiled filters must differ"
  let x86Prog := compileSeccompBpf .x86_64
  assertVerdict x86Prog { nr := X32_SYSCALL_BIT, arch := AUDIT_ARCH_X86_64 } SECCOMP_RET_ERRNO_EPERM
    "x86_64 x32 syscall must return EPERM"
  assertVerdict x86Prog { nr := 0, arch := AUDIT_ARCH_X86_64 } SECCOMP_RET_ALLOW
    "x86_64 read(0) must return ALLOW"
  let armProg := compileSeccompBpf .aarch64
  assertVerdict armProg { nr := X32_SYSCALL_BIT, arch := AUDIT_ARCH_AARCH64 } SECCOMP_RET_ALLOW
    "aarch64 has no x32 syscall bit so nr=0x40000000 must return ALLOW"
  assertVerdict armProg { nr := 63, arch := AUDIT_ARCH_AARCH64 } SECCOMP_RET_ALLOW
    "aarch64 read(63) must return ALLOW"

/-- Run all `LeanSwe.ProcessSandbox.Seccomp` runtime unit checks. -/
def runAll : IO Unit := do
  testArchCompiledFilter .x86_64
  testArchCompiledFilter .aarch64
  testWireEncoding

end LeanSwe.ProcessSandbox.Seccomp.RuntimeTests
