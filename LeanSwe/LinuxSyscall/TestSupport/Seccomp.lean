import LeanSwe.LinuxSyscall.Sandbox.Interface

namespace LeanSwe.LinuxSyscall.TestSupport.Seccomp

private def pushU16LE (b : ByteArray) (v : UInt16) : ByteArray :=
  (b.push (v &&& 0xff).toUInt8).push ((v >>> 8) &&& 0xff).toUInt8

private def pushU32LE (b : ByteArray) (v : UInt32) : ByteArray :=
  (((b.push (v &&& 0xff).toUInt8).push ((v >>> 8) &&& 0xff).toUInt8).push
    ((v >>> 16) &&& 0xff).toUInt8).push ((v >>> 24) &&& 0xff).toUInt8

private def pushBpfInsn (b : ByteArray) (code : UInt16) (jt jf : UInt8) (k : UInt32) : ByteArray :=
  pushU32LE (((pushU16LE b code).push jt).push jf) k

/-- Encode a portable `x86_64`+`aarch64` cBPF filter returning `SECCOMP_RET_ERRNO | err` for the listed syscall numbers (`3 + x86Nrs.size + armNrs.size ≤ 255`). -/
def encodeSeccompErrnoBpf (x86Nrs armNrs : Array UInt32) (err : LeanSwe.LinuxSyscall.Errno) : ByteArray := Id.run do
  let nX := x86Nrs.size
  let nA := armNrs.size
  let mut b := ByteArray.empty
  b := pushBpfInsn b 0x0020 0 0 4
  b := pushBpfInsn b 0x0015 1 0 0xc000003e
  b := pushBpfInsn b 0x0015 (UInt8.ofNat (2 + nX)) (UInt8.ofNat (3 + nX + nA)) 0xc00000b7
  b := pushBpfInsn b 0x0020 0 0 0
  for i in [:nX] do
    b := pushBpfInsn b 0x0015 (UInt8.ofNat (2 + nX + nA - i)) 0 x86Nrs[i]!
  b := pushBpfInsn b 0x0006 0 0 0x7fff0000
  b := pushBpfInsn b 0x0020 0 0 0
  for j in [:nA] do
    b := pushBpfInsn b 0x0015 (UInt8.ofNat (nA - j)) 0 armNrs[j]!
  b := pushBpfInsn b 0x0006 0 0 0x7fff0000
  b := pushBpfInsn b 0x0006 0 0 (0x00050000 ||| (err &&& 0xffff))
  return b

/-- Encode a portable (`x86_64`/`aarch64`) `SECCOMP_RET_ERRNO` cBPF filter returning `eno` for the masked `TimeRand` syscalls (`syscallMask` bits: `bit 0 = clock_gettime`, `bit 1 = clock_nanosleep`, `bit 2 = getrandom`). -/
def encodeTimeRandSeccompErrnoBpf (eno : LeanSwe.LinuxSyscall.Errno) (syscallMask : UInt32 := 7) : ByteArray := Id.run do
  let mut x86Nrs : Array UInt32 := #[]
  let mut armNrs : Array UInt32 := #[]
  if (syscallMask &&& 1) != 0 then
    x86Nrs := x86Nrs.push 228
    armNrs := armNrs.push 113
  if (syscallMask &&& 2) != 0 then
    x86Nrs := x86Nrs.push 230
    armNrs := armNrs.push 115
  if (syscallMask &&& 4) != 0 then
    x86Nrs := x86Nrs.push 318
    armNrs := armNrs.push 278
  encodeSeccompErrnoBpf x86Nrs armNrs eno

/-- Install a portable (`x86_64`/`aarch64`) `TSYNC` `SECCOMP_RET_ERRNO` filter returning `eno` (`1..4095`, rejecting `EFAULT`) on the masked `TimeRand` syscalls (`syscallMask` in `1..7`: `bit 0 = clock_gettime`, `bit 1 = clock_nanosleep`, `bit 2 = getrandom`). Returns `0` on success, `EINVAL` on invalid inputs, `EAGAIN` if `TSYNC` returns a conflicting thread ID, or the kernel errno on syscall failure. -/
def installTimeRandSeccompErrno (eno : LeanSwe.LinuxSyscall.Errno) (syscallMask : UInt32 := 7) : IO UInt32 := do
  if eno == 0 || eno > 4095 || eno == LeanSwe.LinuxSyscall.Errno.EFAULT || syscallMask == 0 || syscallMask > 7 then
    return LeanSwe.LinuxSyscall.Errno.EINVAL
  match ← LeanSwe.LinuxSyscall.Sandbox.prctl .setNoNewPrivs with
  | .error e => return e
  | .ok _ =>
    let bpf := encodeTimeRandSeccompErrnoBpf eno syscallMask
    match ← LeanSwe.LinuxSyscall.Sandbox.seccomp .setModeFilter { tsync := true } bpf with
    | .ok rc => return if rc == 0 then 0 else LeanSwe.LinuxSyscall.Errno.EAGAIN
    | .error e => return e

end LeanSwe.LinuxSyscall.TestSupport.Seccomp
