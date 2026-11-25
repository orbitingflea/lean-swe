import LeanSwe.LinuxSyscall.Sandbox.Types

namespace LeanSwe.LinuxSyscall.Sandbox

namespace Internal

open LeanSwe.LinuxSyscall

/-- Construct the public `SandboxOpsM m fd` bundle from thin `PosixSandboxOpsM m fd` hooks, enforcing embedded-NUL, `MFD_NAME_MAX`, `seccomp` buffer-length and return-verdict safety (`hasSafeSeccompRetBytes`), and `landlock_create_ruleset` pointer/flag safety in pure Lean. -/
def mkSandboxOps {m : Type → Type} [Monad m] {fd : Type} (raw : PosixSandboxOpsM m fd) :
    SandboxOpsM m fd :=
  { landlockCreateRuleset := fun attr? flags =>
      match attr? with
      | none =>
        if flags == 0 then
          pure (.error Errno.EINVAL)
        else do
          match ← raw.landlockQuery flags with
          | .ok v => return .ok (.version v)
          | .error e => return .error e
      | some attr =>
        if flags != 0 then
          pure (.error Errno.EINVAL)
        else do
          match ← raw.landlockCreate attr.handledAccessFs attr.handledAccessNet with
          | .ok h => return .ok (.ruleset h)
          | .error e => return .error e
    landlockAddRule := fun ruleset rule =>
      match rule with
      | .pathBeneath parentFd allowedAccess =>
        raw.landlockAddPathBeneath ruleset parentFd allowedAccess
      | .netPort port allowedAccess =>
        raw.landlockAddNetPort ruleset port allowedAccess
    landlockRestrictSelf := raw.landlockRestrictSelf
    seccomp := fun op flags filterBytes =>
      match op with
      | .getActionAvail action =>
        if flags.toBits != 0 then
          pure (.error Errno.EINVAL)
        else
          raw.seccompGetActionAvail action
      | .setModeFilter =>
        if !isValidSeccompFilterByteLen filterBytes.size ||
            !hasSafeSeccompRetBytes filterBytes then
          pure (.error Errno.EINVAL)
        else
          raw.seccompSetFilter flags.toBits filterBytes
    prctl := fun op =>
      let (tag, arg) := op.toRaw
      raw.prctl tag arg
    setrlimit := fun res cur max =>
      raw.setrlimit res.toTag cur max
    memfdCreate := fun name flags =>
      if name.size > MFD_NAME_MAX || hasEmbeddedNul name then
        pure (.error Errno.EINVAL)
      else
        raw.memfdCreate name flags.toBits }

/-- Monadic `HandleId`-specialized `SandboxOpsM` builder for `Core.ObeysStepFrom`. -/
def mkSandboxOpsM {m : Type → Type} [Monad m]
    (raw : PosixSandboxOpsM m HandleId) : SandboxOpsM m HandleId :=
  mkSandboxOps raw

end Internal

end LeanSwe.LinuxSyscall.Sandbox
