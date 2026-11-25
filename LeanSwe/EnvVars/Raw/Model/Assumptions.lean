import Core.NondetTest
import LeanSwe.EnvVars.Raw.Types

namespace LeanSwe.EnvVars.Raw

/-- Formal POSIX `environ(7)` / `getenv(3)` boundary assumption consumed by upper-layer
    `LeanSwe.EnvVars.Proofs.envvars_listEnv_consistent_with_getEnv`: whenever `ops.listEnv` succeeds with `pairs`,
    every listed key is a valid POSIX key (`k ≠ ""`, `'=' ∉ k`, NUL `∉ k`) and for every valid POSIX key `k`,
    `ops.getEnv k` returns the value of the first matching entry in `pairs` (`none` when absent). -/
def assume_envvarsraw_listEnv_consistentWithGetEnv
    {runner} [Core.NondetTest runner] (ops : RawEnvVarsOpsM Id) : runner Unit := do
  let pairs ← Core.NondetTest.nondet (Array (String × String))
  let k ← Core.NondetTest.nondet String
  Core.NondetTest.assume (ops.listEnv = .ok pairs)
  Core.NondetTest.assume (k ≠ "" ∧ '=' ∉ k.toList ∧ Char.ofNat 0 ∉ k.toList)
  Core.NondetTest.assert
    (pairs.toList.all (fun p => !p.1.isEmpty && !('=' ∈ p.1.toList) && !(Char.ofNat 0 ∈ p.1.toList)) = true ∧
     ops.getEnv k = .ok ((pairs.toList.find? (fun p => p.1 == k)).map Prod.snd))

end LeanSwe.EnvVars.Raw
