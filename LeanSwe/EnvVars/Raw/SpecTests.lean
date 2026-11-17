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

/-- `getEnv` returns `.ok none` without consulting `posix.getEnvBytes` when `key` is empty, contains `'='`, or contains NUL. -/
def test_envvarsraw_getEnv_nonPosixKeyReturnsNoneWithoutLookup
    {runner} [NondetTest runner] (mkRaw : PosixRawOpsM Id → RawEnvVarsOpsM Id) : runner Unit := do
  let key ← nondet String
  let leaked ← nondet (Option ByteArray)
  assume (key = "" ∨ '=' ∈ key.toList ∨ Char.ofNat 0 ∈ key.toList)
  let posix : PosixRawOpsM Id :=
    { getEnvBytes := fun _ => leaked
      listEnvironBytes := #[] }
  NondetTest.assert ((mkRaw posix).getEnv key = .ok none)

/-- For any valid POSIX key absent from `posix.getEnvBytes`, `getEnv` returns `.ok none`. -/
def test_envvarsraw_getEnv_unsetReturnsNone
    {runner} [NondetTest runner] (mkRaw : PosixRawOpsM Id → RawEnvVarsOpsM Id) : runner Unit := do
  let key ← nondet String
  assume (key ≠ "" ∧ '=' ∉ key.toList ∧ Char.ofNat 0 ∉ key.toList)
  let posix : PosixRawOpsM Id :=
    { getEnvBytes := fun _ => none
      listEnvironBytes := #[] }
  NondetTest.assert ((mkRaw posix).getEnv key = .ok none)

/-- For any valid POSIX key and UTF-8 `val` (including `""`, `'='`-containing strings, and multi-byte UTF-8),
    `getEnv` decodes `val.toUTF8` back to `.ok (some val)`. -/
def test_envvarsraw_getEnv_validUtf8DecodesExactValue
    {runner} [NondetTest runner] (mkRaw : PosixRawOpsM Id → RawEnvVarsOpsM Id) : runner Unit := do
  let key ← nondet String
  let val ← nondet String
  assume (key ≠ "" ∧ '=' ∉ key.toList ∧ Char.ofNat 0 ∉ key.toList)
  let posix : PosixRawOpsM Id :=
    { getEnvBytes := fun k => if k == key then some val.toUTF8 else none
      listEnvironBytes := #[] }
  NondetTest.assert ((mkRaw posix).getEnv key = .ok (some val))

/-- Under Option A, when `posix.getEnvBytes` returns invalid UTF-8 bytes (`String.fromUTF8? rawVal = none`) for a
    valid POSIX key, `getEnv` fails with `.invalidEncoding (some key) detail` (`detail ≠ ""`) rather than substituting `U+FFFD`. -/
def test_envvarsraw_getEnv_invalidUtf8ReturnsInvalidEncoding
    {runner} [NondetTest runner] (mkRaw : PosixRawOpsM Id → RawEnvVarsOpsM Id) : runner Unit := do
  let key ← nondet String
  let rawVal ← nondet ByteArray
  assume (key ≠ "" ∧ '=' ∉ key.toList ∧ Char.ofNat 0 ∉ key.toList)
  assume (String.fromUTF8? rawVal = none)
  let posix : PosixRawOpsM Id :=
    { getEnvBytes := fun k => if k == key then some rawVal else none
      listEnvironBytes := #[] }
  let res := (mkRaw posix).getEnv key
  NondetTest.assert (∃ detail, res = .error (.invalidEncoding (some key) detail) ∧ detail ≠ "")

/-- `listEnv` splits each `NAME=VALUE` byte slice strictly on the first `'='` (`0x3D`), preserving empty values,
    `'='` inside values, duplicate keys, and exact `environ` order (`#[]` when empty). -/
def test_envvarsraw_listEnv_splitsFirstEqualsAndPreservesOrder
    {runner} [NondetTest runner] (mkRaw : PosixRawOpsM Id → RawEnvVarsOpsM Id) : runner Unit := do
  let pairs ← nondet (List (String × String))
  assume (pairs.all fun p => !p.1.isEmpty && !('=' ∈ p.1.toList))
  let rawEntries := (pairs.map fun (k, v) => (k ++ "=" ++ v).toUTF8).toArray
  let posix : PosixRawOpsM Id :=
    { getEnvBytes := fun _ => none
      listEnvironBytes := rawEntries }
  NondetTest.assert ((mkRaw posix).listEnv = .ok pairs.toArray)

/-- `listEnv` silently skips malformed `environ` entries lacking `'='` (`0x3D`) or starting with `'='` (empty key),
    even when those skipped entries contain invalid UTF-8 bytes. -/
def test_envvarsraw_listEnv_skipsMissingEqualsAndEmptyKey
    {runner} [NondetTest runner] (mkRaw : PosixRawOpsM Id → RawEnvVarsOpsM Id) : runner Unit := do
  let noEq ← nondet ByteArray
  let afterEq ← nondet ByteArray
  let k1 ← nondet String
  let v1 ← nondet String
  let k2 ← nondet String
  let v2 ← nondet String
  assume (!(noEq.data.toList.contains 0x3D))
  assume (k1 ≠ "" ∧ '=' ∉ k1.toList)
  assume (k2 ≠ "" ∧ '=' ∉ k2.toList)
  let emptyKeyEntry := ByteArray.mk #[0x3D] ++ afterEq
  let rawEntries := #[(k1 ++ "=" ++ v1).toUTF8, noEq, emptyKeyEntry, (k2 ++ "=" ++ v2).toUTF8]
  let posix : PosixRawOpsM Id :=
    { getEnvBytes := fun _ => none
      listEnvironBytes := rawEntries }
  NondetTest.assert ((mkRaw posix).listEnv = .ok #[(k1, v1), (k2, v2)])

/-- When the first non-skipped `environ` entry has invalid UTF-8 bytes in its key slice, `listEnv` fails with
    `.invalidEncoding none detail` (`detail ≠ ""`). -/
def test_envvarsraw_listEnv_invalidUtf8KeyReturnsNoneKeyError
    {runner} [NondetTest runner] (mkRaw : PosixRawOpsM Id → RawEnvVarsOpsM Id) : runner Unit := do
  let pre ← nondet (List (String × String))
  let badKey ← nondet ByteArray
  let valBytes ← nondet ByteArray
  let tail ← nondet (List ByteArray)
  assume (pre.all fun p => !p.1.isEmpty && !('=' ∈ p.1.toList))
  assume (badKey.size > 0 ∧ !(badKey.data.toList.contains 0x3D) ∧ String.fromUTF8? badKey = none)
  let preBytes := pre.map fun (k, v) => (k ++ "=" ++ v).toUTF8
  let badEntry := badKey ++ ByteArray.mk #[0x3D] ++ valBytes
  let posix : PosixRawOpsM Id :=
    { getEnvBytes := fun _ => none
      listEnvironBytes := (preBytes ++ (badEntry :: tail)).toArray }
  let res := (mkRaw posix).listEnv
  NondetTest.assert (∃ detail, res = .error (.invalidEncoding none detail) ∧ detail ≠ "")

/-- When the first non-skipped `environ` entry has a valid UTF-8 key `key` and invalid UTF-8 value bytes,
    `listEnv` fails with `.invalidEncoding (some key) detail` (`detail ≠ ""`). -/
def test_envvarsraw_listEnv_invalidUtf8ValueReturnsSomeKeyError
    {runner} [NondetTest runner] (mkRaw : PosixRawOpsM Id → RawEnvVarsOpsM Id) : runner Unit := do
  let pre ← nondet (List (String × String))
  let key ← nondet String
  let badVal ← nondet ByteArray
  let tail ← nondet (List ByteArray)
  assume (pre.all fun p => !p.1.isEmpty && !('=' ∈ p.1.toList))
  assume (key ≠ "" ∧ '=' ∉ key.toList)
  assume (String.fromUTF8? badVal = none)
  let preBytes := pre.map fun (k, v) => (k ++ "=" ++ v).toUTF8
  let badEntry := key.toUTF8 ++ ByteArray.mk #[0x3D] ++ badVal
  let posix : PosixRawOpsM Id :=
    { getEnvBytes := fun _ => none
      listEnvironBytes := (preBytes ++ (badEntry :: tail)).toArray }
  let res := (mkRaw posix).listEnv
  NondetTest.assert (∃ detail, res = .error (.invalidEncoding (some key) detail) ∧ detail ≠ "")

/-- Every entry `(k, v)` returned by a succeeding `listEnv` has a non-empty, `'='`-free key, and when all input
    byte slices are NUL-free (`0 ∉ b.data.toList`, as guaranteed by C strings from `environ(7)`), every key is NUL-free. -/
def test_envvarsraw_listEnv_outputKeysWellFormed
    {runner} [NondetTest runner] (mkRaw : PosixRawOpsM Id → RawEnvVarsOpsM Id) : runner Unit := do
  let entries ← nondet (Array ByteArray)
  let pairs ← nondet (Array (String × String))
  assume (entries.toList.all fun b => !(b.data.toList.contains 0))
  assume ((mkRaw { getEnvBytes := fun _ => none, listEnvironBytes := entries }).listEnv = .ok pairs)
  NondetTest.assert (pairs.toList.all fun p =>
    !p.1.isEmpty && !('=' ∈ p.1.toList) && !(Char.ofNat 0 ∈ p.1.toList))

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

private def stubMapRawError : EnvVarsRawError → EnvVarsError
  | .invalidEncoding key? _ =>
    { kind := .invalidEncoding, key := key?, errnoCode := none, message := "stub" }
  | .invalidArgument key? code _ =>
    { kind := .invalidKey, key := key?, errnoCode := some code, message := "stub" }
  | .otherError code _ =>
    { kind := .ioError, key := none, errnoCode := some code, message := "stub" }
  | .userError _ =>
    { kind := .ioError, key := none, errnoCode := none, message := "stub" }

private def stubRawOps : RawEnvVarsOps :=
  { mapRawError := stubMapRawError
    getEnv := fun _ => pure (.ok none)
    listEnv := pure (.ok #[]) }

private def stubSplitFirstEqBytes (revPre : List UInt8) : List UInt8 → Option (ByteArray × ByteArray)
  | [] => none
  | b :: bs =>
    if b == 0x3D then
      if revPre.isEmpty then none
      else some (ByteArray.mk revPre.reverse.toArray, ByteArray.mk bs.toArray)
    else
      stubSplitFirstEqBytes (b :: revPre) bs

private def stubDecodeEntries : List ByteArray → Except EnvVarsRawError (List (String × String))
  | [] => .ok []
  | entry :: rest =>
    match stubSplitFirstEqBytes [] entry.data.toList with
    | none => stubDecodeEntries rest
    | some (kBytes, vBytes) =>
      match String.fromUTF8? kBytes with
      | none => .error (.invalidEncoding none "invalid UTF-8 in environment key")
      | some k =>
        match String.fromUTF8? vBytes with
        | none => .error (.invalidEncoding (some k) "invalid UTF-8 in environment value")
        | some v =>
          match stubDecodeEntries rest with
          | .error e => .error e
          | .ok tail => .ok ((k, v) :: tail)

private def stubMkRaw (posix : PosixRawOpsM Id) : RawEnvVarsOpsM Id :=
  { mapRawError := stubMapRawError
    getEnv := fun key =>
      if key.isEmpty || ('=' ∈ key.toList) || (Char.ofNat 0 ∈ key.toList) then
        .ok none
      else
        match posix.getEnvBytes key with
        | none => .ok none
        | some bs =>
          match String.fromUTF8? bs with
          | some s => .ok (some s)
          | none => .error (.invalidEncoding (some key) "invalid UTF-8 in environment value")
    listEnv := (stubDecodeEntries posix.listEnvironBytes.toList).map List.toArray }

private def buggyEmptyErrRaw (base : RawEnvVarsOps) : RawEnvVarsOps :=
  { base with mapRawError := fun _ => { kind := .ioError, message := "" } }

private def buggyWrongKindRaw (base : RawEnvVarsOps) : RawEnvVarsOps :=
  { base with
    mapRawError := fun
      | .invalidEncoding key? _ => { kind := .ioError, key := key?, message := "bad kind" }
      | other => base.mapRawError other }

example : ¬ Core.AllPass (test_envvarsraw_mapRawError_returnsNonEmptyMessage (buggyEmptyErrRaw stubRawOps)) := by
  intro h
  have h0 := h (.userError "boom")
  simp [buggyEmptyErrRaw, assert] at h0

example : ¬ Core.AllPass (test_envvarsraw_mapRawError_preservesKindAndMetadata (buggyWrongKindRaw stubRawOps)) := by
  intro h
  have h0 := h (.invalidEncoding (some "PATH") "bad utf8")
  simp [buggyWrongKindRaw, assert] at h0

example : ¬ Core.AllPass (test_envvarsraw_mapRawError_consistentAcrossBackends stubRawOps fun posix =>
    { stubMkRaw posix with mapRawError := fun _ => { kind := .ioError, message := "diverged" } }) := by
  intro h
  have h0 := h { getEnvBytes := fun _ => none, listEnvironBytes := #[] } (.invalidEncoding (some "K") "x")
  simp [stubRawOps, stubMapRawError, assert] at h0

example : ¬ Core.AllPass (test_envvarsraw_getEnv_nonPosixKeyReturnsNoneWithoutLookup fun posix =>
    { stubMkRaw posix with
      getEnv := fun key =>
        match posix.getEnvBytes key with
        | none => .ok none
        | some bs => .ok (String.fromUTF8? bs) }) := by
  intro h
  have h0 := h "A=B" (some "leaked".toUTF8) (Or.inr (Or.inl (by decide)))
  simp [assert] at h0
  cases h0

example : ¬ Core.AllPass (test_envvarsraw_getEnv_nonPosixKeyReturnsNoneWithoutLookup fun posix =>
    { stubMkRaw posix with
      getEnv := fun key =>
        if '=' ∈ key.toList then .ok none
        else
          match posix.getEnvBytes key with
          | none => .ok none
          | some bs => .ok (String.fromUTF8? bs) }) := by
  intro h
  have h0 := h (String.ofList ['P', Char.ofNat 0]) (some "leaked".toUTF8) (Or.inr (Or.inr (by decide)))
  simp [assert] at h0
  cases h0

example : ¬ Core.AllPass (test_envvarsraw_getEnv_unsetReturnsNone fun posix =>
    { stubMkRaw posix with getEnv := fun _ => .ok (some "") }) := by
  intro h
  have h0 := h "PATH" (by decide)
  simp [assert] at h0
  cases h0

example : ¬ Core.AllPass (test_envvarsraw_getEnv_validUtf8DecodesExactValue fun posix =>
    { stubMkRaw posix with getEnv := fun _ => .ok none }) := by
  intro h
  have h0 := h "KEY" "a=b=c" (by decide)
  simp [assert] at h0
  cases h0

example : ¬ Core.AllPass (test_envvarsraw_getEnv_invalidUtf8ReturnsInvalidEncoding fun posix =>
    { stubMkRaw posix with
      getEnv := fun key =>
        match posix.getEnvBytes key with
        | none => .ok none
        | some bs => .ok (some (String.fromUTF8Lossy bs)) }) := by
  intro h
  have h0 := h "BAD_VAL" (ByteArray.mk #[0xFF, 0xFE]) (by decide) rfl
  simp [assert] at h0

example : ¬ Core.AllPass (test_envvarsraw_getEnv_invalidUtf8ReturnsInvalidEncoding fun posix =>
    { stubMkRaw posix with
      getEnv := fun _ => .error (.invalidEncoding none "dropped key") }) := by
  intro h
  have h0 := h "BAD_VAL" (ByteArray.mk #[0xED, 0xA0, 0x80]) (by decide) rfl
  simp [assert] at h0
  rcases h0 with ⟨_, h1, _⟩
  cases h1

private def stubSplitLastEqBytes (bs : List UInt8) : Option (ByteArray × ByteArray) :=
  match stubSplitFirstEqBytes [] bs.reverse with
  | none => none
  | some (revVal, revKey) =>
    if revKey.data.toList.isEmpty then none
    else some (ByteArray.mk revKey.data.toList.reverse.toArray, ByteArray.mk revVal.data.toList.reverse.toArray)

example : ¬ Core.AllPass (test_envvarsraw_listEnv_splitsFirstEqualsAndPreservesOrder fun posix =>
    { stubMkRaw posix with
      listEnv := .ok ((posix.listEnvironBytes.toList.filterMap fun entry =>
        match stubSplitLastEqBytes entry.data.toList with
        | none => none
        | some (kb, vb) =>
          match String.fromUTF8? kb, String.fromUTF8? vb with
          | some k, some v => some (k, v)
          | _, _ => none).toArray) }) := by
  intro h
  have h0 := h [("KEY", "a=b=c"), ("EMPTY", "")] (by decide)
  dsimp only [assert] at h0
  injection h0.1 with h1
  exact absurd h1 (by decide)

example : ¬ Core.AllPass (test_envvarsraw_listEnv_skipsMissingEqualsAndEmptyKey fun posix =>
    { stubMkRaw posix with
      listEnv := .error (.invalidEncoding none "failed on malformed entry") }) := by
  intro h
  have h0 := h (ByteArray.mk #[0xFF, 0xFE]) (ByteArray.mk #[0xFF]) "A" "1" "B" "2"
    rfl (by decide) (by decide)
  simp [assert] at h0

example : ¬ Core.AllPass (test_envvarsraw_listEnv_invalidUtf8KeyReturnsNoneKeyError fun posix =>
    { stubMkRaw posix with listEnv := .ok #[] }) := by
  intro h
  have h0 := h [] (ByteArray.mk #[0xFF]) "1".toUTF8 [] rfl ⟨by decide, rfl, rfl⟩
  simp [assert] at h0

example : ¬ Core.AllPass (test_envvarsraw_listEnv_invalidUtf8KeyReturnsNoneKeyError fun posix =>
    { stubMkRaw posix with listEnv := .error (.invalidEncoding (some "bogus") "wrong key option") }) := by
  intro h
  have h0 := h [] (ByteArray.mk #[0xC0, 0x80]) "1".toUTF8 [] rfl ⟨by decide, rfl, rfl⟩
  simp [assert] at h0
  rcases h0 with ⟨_, h1, _⟩
  cases h1

example : ¬ Core.AllPass (test_envvarsraw_listEnv_invalidUtf8ValueReturnsSomeKeyError fun posix =>
    { stubMkRaw posix with listEnv := .error (.invalidEncoding none "lost key") }) := by
  intro h
  have h0 := h [] "BAD_VAL" (ByteArray.mk #[0xF4, 0x90, 0x80, 0x80]) [] rfl (by decide) rfl
  simp [assert] at h0
  rcases h0 with ⟨_, h1, _⟩
  cases h1

example : ¬ Core.AllPass (test_envvarsraw_listEnv_outputKeysWellFormed fun posix =>
    { stubMkRaw posix with listEnv := .ok #[("A=B", "1")] }) := by
  intro h
  have h0 := h #[] #[("A=B", "1")] rfl rfl
  simp [assert] at h0

example : ¬ Core.AllPass (assume_envvarsraw_listEnv_consistentWithGetEnv
    { mapRawError := stubMapRawError
      getEnv := fun k => if k == "DUP" then .ok (some "second") else .ok none
      listEnv := .ok #[("DUP", "first"), ("DUP", "second")] }) := by
  intro h
  have h0 := h #[("DUP", "first"), ("DUP", "second")] "DUP" rfl (by decide)
  simp [assert] at h0
  injection h0 with h1
  exact absurd h1 (by decide)

end LeanSwe.EnvVars.Raw
