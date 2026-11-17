import LeanSwe.ProcessSandbox.Types
import LeanSwe.ProcessSandbox.Model

namespace LeanSwe.ProcessSandbox.Internal

open LeanSwe.ProcessSandbox
open LeanSwe.ProcessSandbox.Model

/-- Return `err` with `fallback` when `err.message` is empty. -/
def ensureNonEmptyMsg (fallback : String) (err : SandboxError) : SandboxError :=
  if err.message.isEmpty then { err with message := fallback } else err

/-- Validate and normalize a `BoxSpec` at the public API boundary. -/
def validateSpec (spec : BoxSpec) : Except SandboxError ValidBoxSpec :=
  validateSpecPure spec

/-- Stage 2 compile-only placeholder replaced in Stage 4 by `LeanSwe.ProcessSandbox.Impl.Seccomp.compileSeccompBpf`. -/
def compileSeccompBpf (_arch : SeccompArch) : Array SockFilter :=
  #[]

/-- Stage 2 compile-only placeholder replaced in Stage 4 by `LeanSwe.ProcessSandbox.Impl.Seccomp.encodeSeccompBpf`. -/
def encodeSeccompBpf (_prog : Array SockFilter) : ByteArray :=
  ByteArray.empty

/-- Run `spec` inside a freshly compiled, sealed, and cgroup-bounded sandbox using `MonadFinally` brackets for leak-free teardown. -/
def runGeneric {m : Type → Type} [Monad m] [MonadFinally m]
    (raw : RawProcessSandboxOpsM m) (spec : BoxSpec) : m (Except SandboxError SandboxResult) := do
  match validateSpecPure spec with
  | .error e => return .error (ensureNonEmptyMsg "invalid sandbox specification" e)
  | .ok valid =>
    let req : PreflightReq :=
      { needMemoryCgroup := valid.limits.memoryMaxBytes.isSome
        needPidsCgroup := valid.limits.pidsMax.isSome }
    match ← raw.preflight req with
    | .error e =>
      return .error { ensureNonEmptyMsg "sandbox unavailable" e with kind := .unavailable }
    | .ok () =>
      match ← raw.discoverHostPreset with
      | .error e =>
        return .error (ensureNonEmptyMsg "host runtime preset discovery failed" e)
      | .ok preset =>
        let plan := compilePlan valid preset
        match ← raw.sealPlan plan with
        | .error e =>
          return .error (ensureNonEmptyMsg "failed to seal sandbox plan" e)
        | .ok ph =>
          let (res, _) ← tryFinally' (do
            match ← raw.spawnBox ph with
            | .error e =>
              return .error (ensureNonEmptyMsg "failed to spawn sandbox" e)
            | .ok bh =>
              let (boxRes, _) ← tryFinally' (do
                let fwdRes : Except SandboxError (Option PortForwarderHandle) ←
                  if plan.portForwards.isEmpty then
                    pure (.ok none)
                  else do
                    match ← raw.startPortForwarders bh plan.portForwards with
                    | .error e =>
                      pure (.error (ensureNonEmptyMsg "failed to start port forwarders" e))
                    | .ok fh =>
                      pure (.ok (some fh))
                match fwdRes with
                | .error e => return .error e
                | .ok fwdOpt =>
                  let (ioRes, _) ← tryFinally'
                    (raw.readBoxOutput bh valid.stdin valid.limits.timeoutMs valid.limits.maxOutputBytes)
                    (fun _ =>
                      match fwdOpt with
                      | some fh => do
                        let _ ← raw.stopPortForwarders fh
                        pure ()
                      | none => pure ())
                  match ioRes with
                  | .error e =>
                    return .error (ensureNonEmptyMsg "sandbox I/O failed" e)
                  | .ok out =>
                    return .ok out
              ) (fun _ => do
                let _ ← raw.killProcessGroup bh
                let _ ← raw.pidfdKill bh
                let _ ← raw.reapBox bh
                pure ())
              return boxRes
          ) (fun _ => do
            let _ ← raw.closePlan ph
            pure ())
          return res

/-- Probe whether the host supports `ProcessSandbox.run` with default `memory` and `pids` cgroup controllers. -/
def isAvailableGeneric {m : Type → Type} [Monad m] (raw : RawProcessSandboxOpsM m) : m Bool := do
  match ← raw.preflight { needMemoryCgroup := true, needPidsCgroup := true } with
  | .ok () => return true
  | .error _ => return false

/-- Construct a `ProcessSandboxApiM m` from injected `RawProcessSandboxOpsM m` operations. -/
def mkApiM {m : Type → Type} [Monad m] [MonadFinally m]
    (raw : RawProcessSandboxOpsM m) : ProcessSandboxApiM m :=
  { validateSpec := validateSpec
    compileSeccompBpf := compileSeccompBpf
    encodeSeccompBpf := encodeSeccompBpf
    run := runGeneric raw
    isAvailable := isAvailableGeneric raw }

end LeanSwe.ProcessSandbox.Internal
