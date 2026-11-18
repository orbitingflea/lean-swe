import LeanSwe.LinuxSyscall.TimeRand.Types

namespace LeanSwe.LinuxSyscall.TimeRand

open LeanSwe.LinuxSyscall

namespace Internal

/-- Alias of `PosixTimeRandOpsM` for low-level C-ABI hook wiring. -/
abbrev PosixTimeRandOpsM := LeanSwe.LinuxSyscall.TimeRand.PosixTimeRandOpsM

/-- Alias of `PosixTimeRandOps` for `IO` C-ABI hook wiring. -/
abbrev PosixTimeRandOps := LeanSwe.LinuxSyscall.TimeRand.PosixTimeRandOps

/-- Construct the public `TimeRandOpsM m` capability record from low-level `PosixTimeRandOpsM m` hooks, encoding portable `ClockId`, `abstime`, `Timespec`, and `GrndFlags` in Lean. -/
def mkTimeRandOpsM {m : Type → Type} [Monad m] (raw : PosixTimeRandOpsM m) : TimeRandOpsM m :=
  { clock_gettime := fun clk => do
      match ← raw.clock_gettime clk.toRaw with
      | .ok (sec, nsec) => return .ok { sec, nsec }
      | .error e => return .error e
    clock_nanosleep := fun clk abstime req =>
      raw.clock_nanosleep clk.toRaw (if abstime then 1 else 0) req.sec req.nsec
    getrandom := fun len flags =>
      raw.getrandom len flags.toBits }

/-- Construct the `IO` `TimeRandOps` capability record from `PosixTimeRandOps` hooks. -/
abbrev mkTimeRandOps {m : Type → Type} [Monad m] (raw : PosixTimeRandOpsM m) : TimeRandOpsM m :=
  mkTimeRandOpsM raw

end Internal

end LeanSwe.LinuxSyscall.TimeRand
