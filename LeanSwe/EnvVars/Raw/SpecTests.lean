import Core.NondetTest
import Core.Assumptions
import LeanSwe.EnvVars.Raw.Types

namespace LeanSwe.EnvVars.Raw

open Core (NondetTest AssumptionObligation ErrorObligation)
open Core.NondetTest

/-- Every error returned by `ops.mapRawError` carries a non-empty diagnostic message. -/
def test_envvarsraw_mapRawError_returnsNonEmptyMessage
    {runner} [NondetTest runner] (ops : RawEnvVarsOps) : runner Unit := do
  let raw ← nondet EnvVarsRawError
  let err := ops.mapRawError raw
  NondetTest.assert (err.message ≠ "")

/-- `ops.mapRawError` maps each `EnvVarsRawError` constructor to its expected `EnvVarsErrorKind`, `key`, and `errnoCode`. -/
def test_envvarsraw_mapRawError_preservesKindAndMetadata
    {runner} [NondetTest runner] (ops : RawEnvVarsOps) : runner Unit := do
  let raw ← nondet EnvVarsRawError
  let err := ops.mapRawError raw
  match raw with
  | .invalidEncoding key? _ =>
    NondetTest.assert (err.kind = .invalidEncoding ∧ err.key = key? ∧ err.errnoCode = none)
  | .invalidArgument key? code _ =>
    NondetTest.assert (err.kind = .invalidKey ∧ err.key = key? ∧ err.errnoCode = some code)
  | .otherError code _ =>
    NondetTest.assert (err.kind = .ioError ∧ err.key = none ∧ err.errnoCode = some code)
  | .userError _ =>
    NondetTest.assert (err.kind = .ioError ∧ err.key = none ∧ err.errnoCode = none)

/-- `(mkRaw posix).mapRawError` agrees identically with `ops.mapRawError` for every `posix` backend. -/
def test_envvarsraw_mapRawError_consistentAcrossBackends
    {runner} [NondetTest runner]
    (ops : RawEnvVarsOps) (mkRaw : PosixRawOpsM Id → RawEnvVarsOpsM Id) : runner Unit := do
  let posix ← nondet (PosixRawOpsM Id)
  let raw ← nondet EnvVarsRawError
  NondetTest.assert ((mkRaw posix).mapRawError raw = ops.mapRawError raw)

/-- `getEnv` returns `.ok none` without consulting `posix.getEnvBytes` or `posix.listEnvironBytes`
    when `key` is empty, contains `'='`, or contains NUL. -/
def test_envvarsraw_getEnv_nonPosixKeyReturnsNoneWithoutLookup
    {runner} [NondetTest runner] (mkRaw : PosixRawOpsM Id → RawEnvVarsOpsM Id) : runner Unit := do
  let key ← nondet String
  let leaked ← nondet (Option ByteArray)
  let envSnap ← nondet (Array ByteArray)
  assume (key = "" ∨ '=' ∈ key.toList ∨ Char.ofNat 0 ∈ key.toList)
  let posix : PosixRawOpsM Id :=
    { getEnvBytes := fun _ => leaked
      listEnvironBytes := envSnap }
  NondetTest.assert ((mkRaw posix).getEnv key = .ok none)

/-- For any valid POSIX key absent from `posix.getEnvBytes`, `getEnv` returns `.ok none` regardless of `posix.listEnvironBytes`. -/
def test_envvarsraw_getEnv_unsetReturnsNone
    {runner} [NondetTest runner] (mkRaw : PosixRawOpsM Id → RawEnvVarsOpsM Id) : runner Unit := do
  let key ← nondet String
  let envSnap ← nondet (Array ByteArray)
  assume (key ≠ "" ∧ '=' ∉ key.toList ∧ Char.ofNat 0 ∉ key.toList)
  let posix : PosixRawOpsM Id :=
    { getEnvBytes := fun _ => none
      listEnvironBytes := envSnap }
  NondetTest.assert ((mkRaw posix).getEnv key = .ok none)

/-- For any valid POSIX key and UTF-8 `val` (including `""`, `'='`-containing strings, and multi-byte UTF-8),
    `getEnv` decodes `val.toUTF8` back to `.ok (some val)` regardless of `posix.listEnvironBytes`. -/
def test_envvarsraw_getEnv_validUtf8DecodesExactValue
    {runner} [NondetTest runner] (mkRaw : PosixRawOpsM Id → RawEnvVarsOpsM Id) : runner Unit := do
  let key ← nondet String
  let val ← nondet String
  let envSnap ← nondet (Array ByteArray)
  assume (key ≠ "" ∧ '=' ∉ key.toList ∧ Char.ofNat 0 ∉ key.toList)
  let posix : PosixRawOpsM Id :=
    { getEnvBytes := fun k => if k == key then some val.toUTF8 else none
      listEnvironBytes := envSnap }
  NondetTest.assert ((mkRaw posix).getEnv key = .ok (some val))

/-- Under Option A, when `posix.getEnvBytes` returns invalid UTF-8 bytes (`String.fromUTF8? rawVal = none`) for a
    valid POSIX key, `getEnv` fails with `.invalidEncoding (some key) detail` (`detail ≠ ""`) regardless of `posix.listEnvironBytes`. -/
def test_envvarsraw_getEnv_invalidUtf8ReturnsInvalidEncoding
    {runner} [NondetTest runner] (mkRaw : PosixRawOpsM Id → RawEnvVarsOpsM Id) : runner Unit := do
  let key ← nondet String
  let rawVal ← nondet ByteArray
  let envSnap ← nondet (Array ByteArray)
  assume (key ≠ "" ∧ '=' ∉ key.toList ∧ Char.ofNat 0 ∉ key.toList)
  assume (String.fromUTF8? rawVal = none)
  let posix : PosixRawOpsM Id :=
    { getEnvBytes := fun k => if k == key then some rawVal else none
      listEnvironBytes := envSnap }
  let res := (mkRaw posix).getEnv key
  NondetTest.assert (∃ detail, res = .error (.invalidEncoding (some key) detail) ∧ detail ≠ "")

/-- `listEnv` splits each `NAME=VALUE` byte slice strictly on the first `'='` (`0x3D`), preserving empty values,
    `'='` inside values, duplicate keys, and exact `environ` order (`#[]` when empty), independent of `posix.getEnvBytes`. -/
def test_envvarsraw_listEnv_splitsFirstEqualsAndPreservesOrder
    {runner} [NondetTest runner] (mkRaw : PosixRawOpsM Id → RawEnvVarsOpsM Id) : runner Unit := do
  let getSnap ← nondet (String → Option ByteArray)
  let pairs ← nondet (List (String × String))
  assume (pairs.all fun p => !p.1.isEmpty && !('=' ∈ p.1.toList))
  let rawEntries := (pairs.map fun (k, v) => (k ++ "=" ++ v).toUTF8).toArray
  let posix : PosixRawOpsM Id :=
    { getEnvBytes := getSnap
      listEnvironBytes := rawEntries }
  NondetTest.assert ((mkRaw posix).listEnv = .ok pairs.toArray)

/-- Across any interleaving of valid `NAME=VALUE` entries and malformed `environ` slices lacking `'='` (`0x3D`)
    or starting with `'='` (including malformed-only arrays and invalid UTF-8 bytes inside skipped entries),
    `listEnv` skips every malformed slice and returns the exact valid entries in order, independent of `posix.getEnvBytes`. -/
def test_envvarsraw_listEnv_skipsMissingEqualsAndEmptyKey
    {runner} [NondetTest runner] (mkRaw : PosixRawOpsM Id → RawEnvVarsOpsM Id) : runner Unit := do
  let getSnap ← nondet (String → Option ByteArray)
  let items ← nondet (List (ByteArray ⊕ (String × String)))
  assume (items.all fun
    | .inl mal => !(mal.data.toList.contains 0x3D) || mal.data.toList.head? == some 0x3D
    | .inr (k, _) => !k.isEmpty && !('=' ∈ k.toList))
  let rawEntries := (items.map fun
    | .inl mal => mal
    | .inr (k, v) => (k ++ "=" ++ v).toUTF8).toArray
  let expected := (items.filterMap fun
    | .inl _ => none
    | .inr kv => some kv).toArray
  let posix : PosixRawOpsM Id :=
    { getEnvBytes := getSnap
      listEnvironBytes := rawEntries }
  NondetTest.assert ((mkRaw posix).listEnv = .ok expected)

/-- After any prefix of valid `NAME=VALUE` entries and skipped malformed slices (lacking `'='` or starting with `'='`),
    when the first non-skipped `environ` entry has invalid UTF-8 bytes in its key slice, `listEnv` fails with
    `.invalidEncoding none detail` (`detail ≠ ""`), independent of `posix.getEnvBytes` and any trailing entries. -/
def test_envvarsraw_listEnv_invalidUtf8KeyReturnsNoneKeyError
    {runner} [NondetTest runner] (mkRaw : PosixRawOpsM Id → RawEnvVarsOpsM Id) : runner Unit := do
  let getSnap ← nondet (String → Option ByteArray)
  let pre ← nondet (List (ByteArray ⊕ (String × String)))
  let badKey ← nondet ByteArray
  let valBytes ← nondet ByteArray
  let tail ← nondet (List ByteArray)
  assume (pre.all fun
    | .inl mal => !(mal.data.toList.contains 0x3D) || mal.data.toList.head? == some 0x3D
    | .inr (k, _) => !k.isEmpty && !('=' ∈ k.toList))
  assume (badKey.size > 0 ∧ !(badKey.data.toList.contains 0x3D) ∧ String.fromUTF8? badKey = none)
  let preBytes := pre.map fun
    | .inl mal => mal
    | .inr (k, v) => (k ++ "=" ++ v).toUTF8
  let badEntry := badKey ++ ByteArray.mk #[0x3D] ++ valBytes
  let posix : PosixRawOpsM Id :=
    { getEnvBytes := getSnap
      listEnvironBytes := (preBytes ++ (badEntry :: tail)).toArray }
  let res := (mkRaw posix).listEnv
  NondetTest.assert (∃ detail, res = .error (.invalidEncoding none detail) ∧ detail ≠ "")

/-- After any prefix of valid `NAME=VALUE` entries and skipped malformed slices (lacking `'='` or starting with `'='`),
    when the first non-skipped `environ` entry has a valid UTF-8 key `key` and invalid UTF-8 value bytes,
    `listEnv` fails with `.invalidEncoding (some key) detail` (`detail ≠ ""`), independent of `posix.getEnvBytes` and trailing entries. -/
def test_envvarsraw_listEnv_invalidUtf8ValueReturnsSomeKeyError
    {runner} [NondetTest runner] (mkRaw : PosixRawOpsM Id → RawEnvVarsOpsM Id) : runner Unit := do
  let getSnap ← nondet (String → Option ByteArray)
  let pre ← nondet (List (ByteArray ⊕ (String × String)))
  let key ← nondet String
  let badVal ← nondet ByteArray
  let tail ← nondet (List ByteArray)
  assume (pre.all fun
    | .inl mal => !(mal.data.toList.contains 0x3D) || mal.data.toList.head? == some 0x3D
    | .inr (k, _) => !k.isEmpty && !('=' ∈ k.toList))
  assume (key ≠ "" ∧ '=' ∉ key.toList)
  assume (String.fromUTF8? badVal = none)
  let preBytes := pre.map fun
    | .inl mal => mal
    | .inr (k, v) => (k ++ "=" ++ v).toUTF8
  let badEntry := key.toUTF8 ++ ByteArray.mk #[0x3D] ++ badVal
  let posix : PosixRawOpsM Id :=
    { getEnvBytes := getSnap
      listEnvironBytes := (preBytes ++ (badEntry :: tail)).toArray }
  let res := (mkRaw posix).listEnv
  NondetTest.assert (∃ detail, res = .error (.invalidEncoding (some key) detail) ∧ detail ≠ "")

/-- Unconditionally across every `entries` array, every `(k, v)` returned by a succeeding `listEnv`
    has a non-empty, `'='`-free key (`k ≠ ""`, `'=' ∉ k.toList`). -/
def test_envvarsraw_listEnv_outputKeysWellFormed
    {runner} [NondetTest runner] (mkRaw : PosixRawOpsM Id → RawEnvVarsOpsM Id) : runner Unit := do
  let getSnap ← nondet (String → Option ByteArray)
  let entries ← nondet (Array ByteArray)
  let pairs ← nondet (Array (String × String))
  assume ((mkRaw { getEnvBytes := getSnap, listEnvironBytes := entries }).listEnv = .ok pairs)
  NondetTest.assert (pairs.toList.all fun p => !p.1.isEmpty && !('=' ∈ p.1.toList))

/-- Whenever all input byte slices in `entries` are NUL-free (`0 ∉ b.data.toList`, as guaranteed for C strings
    from `environ(7)`), every `(k, v)` returned by a succeeding `listEnv` has NUL-free `k` and NUL-free `v`
    in addition to `k ≠ ""` and `'=' ∉ k.toList`. -/
def test_envvarsraw_listEnv_nulFreeInputsPreserveNulFreedom
    {runner} [NondetTest runner] (mkRaw : PosixRawOpsM Id → RawEnvVarsOpsM Id) : runner Unit := do
  let getSnap ← nondet (String → Option ByteArray)
  let entries ← nondet (Array ByteArray)
  let pairs ← nondet (Array (String × String))
  assume (entries.toList.all fun b => !(b.data.toList.contains 0))
  assume ((mkRaw { getEnvBytes := getSnap, listEnvironBytes := entries }).listEnv = .ok pairs)
  NondetTest.assert (pairs.toList.all fun p =>
    !p.1.isEmpty && !('=' ∈ p.1.toList) &&
    !(Char.ofNat 0 ∈ p.1.toList) && !(Char.ofNat 0 ∈ p.2.toList))

/-- Formal POSIX `environ(7)` / `getenv(3)` boundary assumption consumed by upper-layer
    `LeanSwe.EnvVars.Proofs.envvars_listEnv_consistent_with_getEnv`: whenever `ops.listEnv` succeeds with `pairs`,
    every listed key is a valid POSIX key (`k ≠ ""`, `'=' ∉ k`, NUL `∉ k`) and for every valid POSIX key `k`,
    `ops.getEnv k` returns the value of the first matching entry in `pairs` (`none` when absent). -/
def assume_envvarsraw_listEnv_consistentWithGetEnv
    {runner} [NondetTest runner] (ops : RawEnvVarsOpsM Id) : runner Unit := do
  let pairs ← nondet (Array (String × String))
  let k ← nondet String
  assume (ops.listEnv = .ok pairs)
  assume (k ≠ "" ∧ '=' ∉ k.toList ∧ Char.ofNat 0 ∉ k.toList)
  NondetTest.assert
    (pairs.toList.all (fun p => !p.1.isEmpty && !('=' ∈ p.1.toList) && !(Char.ofNat 0 ∈ p.1.toList)) = true ∧
     ops.getEnv k = .ok ((pairs.toList.find? (fun p => p.1 == k)).map Prod.snd))

/-- Frozen thin-boundary assumptions for `LeanSwe.EnvVars.Raw` over POSIX `getenv(3)` and `environ(7)`
    (`c/envvars_shim.c` raw byte data-passing + 1 formal consistency invariant consumed by `LeanSwe.EnvVars.Proofs`). -/
def externalAssumptions : List AssumptionObligation :=
  [ { name := "LeanSwe.EnvVars.Raw.assume_envvarsraw_getEnv_unsetReturnsNone"
      subject := "LeanSwe.EnvVars.Raw.getEnv"
      formalPred? := none }
  , { name := "LeanSwe.EnvVars.Raw.assume_envvarsraw_getEnv_preservesSetBytesAndRejectsInvalidUtf8"
      subject := "LeanSwe.EnvVars.Raw.getEnv"
      formalPred? := none }
  , { name := "LeanSwe.EnvVars.Raw.assume_envvarsraw_listEnv_copiesEnvironOrderAndSkipsMalformed"
      subject := "LeanSwe.EnvVars.Raw.listEnv"
      formalPred? := none }
  , { name := "LeanSwe.EnvVars.Raw.assume_envvarsraw_listEnv_consistentWithGetEnv"
      subject := "LeanSwe.EnvVars.Raw.listEnv"
      formalPred? := some "LeanSwe.EnvVars.Raw.assume_envvarsraw_listEnv_consistentWithGetEnv" } ]

/-- Declared error-coverage matrix for `LeanSwe.EnvVars.Raw` requests (`EnvVarsRawErrorKind`). -/
def errorCoverage : List (ErrorObligation EnvVarsRawErrorKind) :=
  [ { request := "LeanSwe.EnvVars.Raw.getEnv"
      errorKind := .invalidEncoding
      justification := .tested "LeanSwe.EnvVars.Raw.RuntimeTests.err_envvarsraw_getEnv_invalidEncoding" .real }
  , { request := "LeanSwe.EnvVars.Raw.getEnv"
      errorKind := .invalidArgument
      justification := .provedImpossible "LeanSwe.EnvVars.Raw.Proofs.raw_getEnv_never_invalidArgument" }
  , { request := "LeanSwe.EnvVars.Raw.getEnv"
      errorKind := .otherError
      justification := .provedImpossible "LeanSwe.EnvVars.Raw.Proofs.raw_getEnv_never_otherError" }
  , { request := "LeanSwe.EnvVars.Raw.getEnv"
      errorKind := .userError
      justification := .provedImpossible "LeanSwe.EnvVars.Raw.Proofs.raw_getEnv_never_userError" }
  , { request := "LeanSwe.EnvVars.Raw.listEnv"
      errorKind := .invalidEncoding
      justification := .tested "LeanSwe.EnvVars.Raw.RuntimeTests.err_envvarsraw_listEnv_invalidEncoding" .real }
  , { request := "LeanSwe.EnvVars.Raw.listEnv"
      errorKind := .invalidArgument
      justification := .provedImpossible "LeanSwe.EnvVars.Raw.Proofs.raw_listEnv_never_invalidArgument" }
  , { request := "LeanSwe.EnvVars.Raw.listEnv"
      errorKind := .otherError
      justification := .provedImpossible "LeanSwe.EnvVars.Raw.Proofs.raw_listEnv_never_otherError" }
  , { request := "LeanSwe.EnvVars.Raw.listEnv"
      errorKind := .userError
      justification := .provedImpossible "LeanSwe.EnvVars.Raw.Proofs.raw_listEnv_never_userError" } ]

end LeanSwe.EnvVars.Raw
