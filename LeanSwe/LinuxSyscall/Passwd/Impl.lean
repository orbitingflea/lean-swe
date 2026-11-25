import LeanSwe.LinuxSyscall.Passwd.Types

namespace LeanSwe.LinuxSyscall.Passwd

open LeanSwe.LinuxSyscall

namespace Internal

/-- Validate a raw C-ABI result against the caller's entry invariant `pred`, returning `Errno.EIO` on inconsistent/corrupt NSS records. -/
def validateRawPasswdResult (pred : PasswdEntry → Bool) :
    Except Errno (Option RawPasswdTuple) → Except Errno (Option PasswdEntry)
  | .error e => .error e
  | .ok none => .ok none
  | .ok (some t) =>
    let entry : PasswdEntry :=
      { name := t.1
        uid := t.2.1
        gid := t.2.2.1
        gecos := t.2.2.2.1
        homeDir := t.2.2.2.2.1
        shell := t.2.2.2.2.2 }
    if pred entry then .ok (some entry) else .error Errno.EIO

/-- Ordered scratch buffer sizes (`4096 → 8192 → 16384 → 32768 → 65536`) tried on `ERANGE`. -/
def passwdRetryBufSizes : List UInt32 :=
  [4096, 8192, 16384, 32768, 65536]

/-- Total bounded structural-recursion retry loop over `sizes`, doubling scratch capacity on `Errno.ERANGE` and validating returned entries against `pred`. -/
def retryPasswdLookup {m : Type → Type} [Monad m]
    (once : UInt32 → m (Except Errno (Option RawPasswdTuple)))
    (pred : PasswdEntry → Bool) :
    List UInt32 → m (Except Errno (Option PasswdEntry))
  | [] => return .error Errno.ERANGE
  | [sz] => do
    return validateRawPasswdResult pred (← once sz)
  | sz :: rest => do
    match ← once sz with
    | .error e =>
      if e == Errno.ERANGE then
        retryPasswdLookup once pred rest
      else
        return .error e
    | .ok opt => return validateRawPasswdResult pred (.ok opt)

/-- Construct the public `PasswdOpsM m` capability record from `PosixPasswdOpsM m`, validating names, returned entry invariants, and doubling scratch buffers `4096..65536` on `ERANGE` in Lean. -/
def mkPasswdOpsM {m : Type → Type} [Monad m] (raw : PosixPasswdOpsM m) : PasswdOpsM m :=
  { getpwuid := fun uid =>
      retryPasswdLookup
        (raw.getpwuidOnce uid)
        (fun entry => entry.hasNoEmbeddedNul && entry.uid == uid)
        passwdRetryBufSizes
    getpwnam := fun name =>
      if !validPasswdName name then
        return .error Errno.EINVAL
      else if name.size > MAX_PASSWD_NAME_BYTES then
        return .error Errno.ENAMETOOLONG
      else
        retryPasswdLookup
          (raw.getpwnamOnce name)
          (fun entry => entry.hasNoEmbeddedNul && entry.name == name)
          passwdRetryBufSizes }

/-- Construct a `PasswdOpsM m` capability record from `PosixPasswdOpsM m` hooks. -/
abbrev mkPasswdOps {m : Type → Type} [Monad m] (raw : PosixPasswdOpsM m) : PasswdOpsM m :=
  mkPasswdOpsM raw

end Internal

end LeanSwe.LinuxSyscall.Passwd
