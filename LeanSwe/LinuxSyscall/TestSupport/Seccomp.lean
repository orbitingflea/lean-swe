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

/-- Install a portable (`x86_64`/`aarch64`) `TSYNC` `SECCOMP_RET_ERRNO` filter returning `eno` (`1..4095`) on `clock_gettime`, `clock_nanosleep`, and `getrandom` for forked `RuntimeTests` child probes. -/
def installTimeRandSeccompErrno (eno : LeanSwe.LinuxSyscall.Errno) : IO UInt32 := do
  if eno == 0 || eno > 4095 then
    return LeanSwe.LinuxSyscall.Errno.EINVAL
  match ← LeanSwe.LinuxSyscall.Sandbox.prctl .setNoNewPrivs with
  | .error e => return e
  | .ok _ =>
    let bpf := encodeSeccompErrnoBpf #[228, 230, 318] #[113, 115, 278] eno
    match ← LeanSwe.LinuxSyscall.Sandbox.seccomp .setModeFilter { tsync := true } bpf with
    | .ok _ => return 0
    | .error e => return e

end LeanSwe.LinuxSyscall.TestSupport.Seccomp
