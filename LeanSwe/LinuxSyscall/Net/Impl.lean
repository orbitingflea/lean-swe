import LeanSwe.LinuxSyscall.Net.Types

namespace LeanSwe.LinuxSyscall.Net

open LeanSwe.LinuxSyscall

namespace Internal

/-- Monad-parameterized low-level C-ABI syscall hooks for all 15 `Net` syscalls. -/
abbrev PosixNetOpsM := Net.PosixNetOpsM

/-- Concrete `IO` specialization of `PosixNetOpsM` supplied by `Interface.lean` and backed by `net_shim.c`. -/
abbrev PosixNetOps := Net.PosixNetOps

/-- Construct `NetOpsM m fd` from low-level `PosixNetOpsM m fd` hooks, enforcing curated TCP/UDP/`AF_UNIX` protocol scope, `AF_UNIX` path bounds, `SCM_RIGHTS` batch caps (`1..32`), embedded-NUL checks, and `IFNAMSIZ` bounds directly in Lean. -/
def mkNetOpsM {m : Type → Type} {fd : Type} [Monad m] (raw : PosixNetOpsM m fd) : NetOpsM m fd :=
  { socket := fun domain sockType flags proto =>
      match validateSocketArgs domain sockType proto with
      | some e => pure (.error e)
      | none => raw.socket domain.toTag sockType.toTag flags.toBits proto
    socketpair := fun domain sockType flags =>
      match validateSocketpairArgs domain sockType with
      | some e => pure (.error e)
      | none => raw.socketpair domain.toTag sockType.toTag flags.toBits
    bind := fun fd addr =>
      if !addr.isValidTarget then pure (.error Errno.EINVAL)
      else raw.bind fd addr.toRawTuple
    listen := raw.listen
    accept4 := fun fd flags => do
      match ← raw.accept4 fd flags.toBits with
      | .ok (cfd, rawSa) => return .ok (cfd, SockAddr.ofRawTuple rawSa)
      | .error e => return .error e
    connect := fun fd addr =>
      if !addr.isValidTarget then pure (.error Errno.EINVAL)
      else raw.connect fd addr.toRawTuple
    getsockopt := fun fd opt =>
      raw.getsockopt fd opt.toTag
    setsockopt := fun fd opt val =>
      raw.setsockopt fd opt.toTag val
    getsockname := fun fd => do
      match ← raw.getsockname fd with
      | .ok rawSa => return .ok (SockAddr.ofRawTuple rawSa)
      | .error e => return .error e
    recvfrom := fun fd maxBytes flags =>
      raw.recvfrom fd maxBytes flags.toBits
    sendto := fun fd data flags =>
      raw.sendto fd data flags.toBits
    shutdown := fun fd how =>
      raw.shutdown fd how.toTag
    sendmsg := fun fd fds =>
      if !isValidScmCount fds.size then pure (.error Errno.EINVAL)
      else raw.sendmsg fd fds
    recvmsg := fun fd maxFds =>
      if !isValidScmCount maxFds.toNat then pure (.error Errno.EINVAL)
      else raw.recvmsg fd maxFds
    ioctl := fun fd op ifname =>
      if !isValidIfname ifname then pure (.error Errno.EINVAL)
      else
        let (tag, arg) := op.toRaw
        raw.ioctl fd tag arg ifname }

/-- Construct the concrete `IO` `NetOps` capability record from `PosixNetOps`. -/
def mkNetOps (raw : PosixNetOps) : NetOps :=
  mkNetOpsM raw

end Internal

end LeanSwe.LinuxSyscall.Net
