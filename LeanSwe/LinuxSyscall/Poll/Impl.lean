import LeanSwe.LinuxSyscall.Poll.Types

namespace LeanSwe.LinuxSyscall.Poll

open LeanSwe.LinuxSyscall

namespace Internal

/-- Monad-parameterized low-level C-ABI syscall hooks for `Poll` (`ppoll`, `eventfd2`). -/
abbrev PosixPollOpsM := Poll.PosixPollOpsM

/-- Concrete `IO` specialization of `PosixPollOpsM` supplied by `Interface.lean` and backed by `poll_shim.c`. -/
abbrev PosixPollOps := Poll.PosixPollOps

/-- Construct `PollOpsM m fd` from low-level `PosixPollOpsM m fd` hooks, enforcing `Timespec` validity, `MAX_POLL_NFDS` bounds, and event-mask codecs directly in Lean. -/
def mkPollOpsM {m : Type → Type} {fd : Type} [Monad m] (raw : PosixPollOpsM m fd) : PollOpsM m fd :=
  { ppoll := fun entries timeout => do
      let (hasTimeout, secBits, nsec) ← match timeout with
        | none => pure ((0 : UInt8), (0 : UInt64), (0 : UInt32))
        | some ts =>
          if !ts.isValid then
            return .error Errno.EINVAL
          else
            pure ((1 : UInt8), ts.sec.toUInt64, ts.nsec)
      if entries.size > MAX_POLL_NFDS then
        return .error Errno.EINVAL
      let (fds, reqBytes) := encodePollRequests entries
      match ← raw.ppoll fds reqBytes hasTimeout secBits nsec with
      | .error e => return .error e
      | .ok revBytes =>
        if revBytes.size != entries.size then
          return .error Errno.EIO
        else
          return .ok (decodePollRevents revBytes)
    eventfd2 := fun initval flags =>
      raw.eventfd2 initval flags.toBits }

/-- Construct the concrete `IO` `PollOps` capability record from `PosixPollOps`. -/
def mkPollOps (raw : PosixPollOps) : PollOps :=
  mkPollOpsM raw

end Internal

end LeanSwe.LinuxSyscall.Poll
