import Core.NondetTest
import Core.Assumptions
import LeanSwe.EnvVars.Raw.Types
import LeanSwe.EnvVars.Raw.SpecTests

/-! Compile-time negative specification mutants for `LeanSwe.EnvVars.Raw`. -/

namespace LeanSwe.EnvVars.Raw

open Core (NondetTest AssumptionObligation ErrorObligation)
open Core.NondetTest

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

private def stubSplitLastEqBytes (bs : List UInt8) : Option (ByteArray × ByteArray) :=
  match stubSplitFirstEqBytes [] bs.reverse with
  | none => none
  | some (revVal, revKey) =>
    if revKey.data.toList.isEmpty then none
    else some (ByteArray.mk revKey.data.toList.reverse.toArray, ByteArray.mk revVal.data.toList.reverse.toArray)

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
  have h0 := h "A=B" (some "leaked".toUTF8) #[] (Or.inr (Or.inl (by decide)))
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
  have h0 := h (String.ofList ['P', Char.ofNat 0]) (some "leaked".toUTF8) #[] (Or.inr (Or.inr (by decide)))
  simp [assert] at h0
  cases h0

example : ¬ Core.AllPass (test_envvarsraw_getEnv_unsetReturnsNone fun posix =>
    { stubMkRaw posix with getEnv := fun _ => .ok (some "") }) := by
  intro h
  have h0 := h "PATH" #[] (by decide)
  simp [assert] at h0
  cases h0

example : ¬ Core.AllPass (test_envvarsraw_getEnv_validUtf8DecodesExactValue fun posix =>
    { stubMkRaw posix with getEnv := fun _ => .ok none }) := by
  intro h
  have h0 := h "KEY" "a=b=c" #[] (by decide)
  simp [assert] at h0
  cases h0

example : ¬ Core.AllPass (test_envvarsraw_getEnv_validUtf8DecodesExactValue fun posix =>
    { stubMkRaw posix with
      getEnv := fun key =>
        if posix.listEnvironBytes.size > 0 then
          .error (.invalidEncoding none "coupled to listEnvironBytes")
        else
          (stubMkRaw posix).getEnv key }) := by
  intro h
  have h0 := h "KEY" "ok" #[ByteArray.mk #[0xFF]] (by decide)
  simp [assert] at h0

example : ¬ Core.AllPass (test_envvarsraw_getEnv_invalidUtf8ReturnsInvalidEncoding fun posix =>
    { stubMkRaw posix with
      getEnv := fun key =>
        match posix.getEnvBytes key with
        | none => .ok none
        | some bs => .ok (some (String.fromUTF8Lossy bs)) }) := by
  intro h
  have h0 := h "BAD_VAL" (ByteArray.mk #[0xFF, 0xFE]) #[] (by decide) rfl
  simp [assert] at h0

example : ¬ Core.AllPass (test_envvarsraw_getEnv_invalidUtf8ReturnsInvalidEncoding fun posix =>
    { stubMkRaw posix with
      getEnv := fun _ => .error (.invalidEncoding none "dropped key") }) := by
  intro h
  have h0 := h "BAD_VAL" (ByteArray.mk #[0xED, 0xA0, 0x80]) #[] (by decide) rfl
  simp [assert] at h0
  rcases h0 with ⟨_, h1, _⟩
  cases h1

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
  have h0 := h (fun _ => none) [("KEY", "a=b=c"), ("EMPTY", "")] (by decide)
  dsimp only [assert] at h0
  injection h0.1 with h1
  exact absurd h1 (by decide)

example : ¬ Core.AllPass (test_envvarsraw_listEnv_splitsFirstEqualsAndPreservesOrder fun posix =>
    { stubMkRaw posix with
      listEnv :=
        if (posix.getEnvBytes "SENTINEL").isSome then
          .error (.invalidEncoding none "coupled to getEnvBytes")
        else
          (stubMkRaw posix).listEnv }) := by
  intro h
  have h0 := h (fun _ => some (ByteArray.mk #[0xFF])) [("KEY", "1")] (by decide)
  simp [assert] at h0

example : ¬ Core.AllPass (test_envvarsraw_listEnv_skipsMissingEqualsAndEmptyKey fun posix =>
    { stubMkRaw posix with
      listEnv :=
        if posix.listEnvironBytes.size == 1 then
          .error (.invalidEncoding none "failed on single malformed entry")
        else
          (stubMkRaw posix).listEnv }) := by
  intro h
  have h0 := h (fun _ => none) [.inl (ByteArray.mk #[0xFF])] rfl
  simp [assert] at h0

example : ¬ Core.AllPass (test_envvarsraw_listEnv_skipsMissingEqualsAndEmptyKey fun posix =>
    { stubMkRaw posix with
      listEnv :=
        if posix.listEnvironBytes.size == 1 then
          .ok #[("GHOST_LEAK", "1")]
        else
          (stubMkRaw posix).listEnv }) := by
  intro h
  have h0 := h (fun _ => none) [.inl "=EMPTY".toUTF8] rfl
  dsimp only [assert] at h0
  injection h0.1 with h1
  exact absurd h1 (by decide)

example : ¬ Core.AllPass (test_envvarsraw_listEnv_invalidUtf8KeyReturnsNoneKeyError fun posix =>
    { stubMkRaw posix with listEnv := .ok #[] }) := by
  intro h
  have h0 := h (fun _ => none) [] (ByteArray.mk #[0xFF]) "1".toUTF8 [] rfl ⟨by decide, rfl, rfl⟩
  simp [assert] at h0

example : ¬ Core.AllPass (test_envvarsraw_listEnv_invalidUtf8KeyReturnsNoneKeyError fun posix =>
    { stubMkRaw posix with listEnv := .error (.invalidEncoding (some "bogus") "wrong key option") }) := by
  intro h
  have h0 := h (fun _ => none) [.inl "=SKIP".toUTF8] (ByteArray.mk #[0xC0, 0x80]) "1".toUTF8 [] rfl ⟨by decide, rfl, rfl⟩
  simp [assert] at h0
  rcases h0 with ⟨_, h1, _⟩
  cases h1

example : ¬ Core.AllPass (test_envvarsraw_listEnv_invalidUtf8ValueReturnsSomeKeyError fun posix =>
    { stubMkRaw posix with
      listEnv :=
        if posix.listEnvironBytes.toList.any (fun b => (String.fromUTF8? b).isNone) then
          .error (.invalidEncoding none "checked UTF-8 before skipping malformed entry")
        else
          (stubMkRaw posix).listEnv }) := by
  intro h
  have h0 := h (fun _ => none) [.inl (ByteArray.mk #[0xFF])] "BAD_VAL" (ByteArray.mk #[0xFF]) []
    rfl (by decide) rfl
  dsimp only [assert] at h0
  rcases h0.1 with ⟨_, h1, _⟩
  cases h1

example : ¬ Core.AllPass (test_envvarsraw_listEnv_invalidUtf8ValueReturnsSomeKeyError fun posix =>
    { stubMkRaw posix with
      listEnv :=
        let badLast := posix.listEnvironBytes.toList.findSome? fun entry =>
          match stubSplitLastEqBytes entry.data.toList with
          | none => none
          | some (kb, vb) =>
            match String.fromUTF8? kb with
            | none => some (EnvVarsRawError.invalidEncoding none "bad key")
            | some k =>
              match String.fromUTF8? vb with
              | none => some (EnvVarsRawError.invalidEncoding (some k) "bad val")
              | some _ => none
        match badLast with
        | some err => .error err
        | none => (stubMkRaw posix).listEnv }) := by
  intro h
  have h0 := h (fun _ => none) [] "KEY" (ByteArray.mk #[0x61, 0x3D, 0xFF]) []
    rfl (by decide) rfl
  dsimp only [assert] at h0
  rcases h0.1 with ⟨_, h1, _⟩
  injection h1 with h2
  injection h2 with h3
  exact absurd h3 (by decide)

example : ¬ Core.AllPass (test_envvarsraw_listEnv_invalidUtf8ValueReturnsSomeKeyError fun posix =>
    { stubMkRaw posix with
      listEnv := (stubDecodeEntries posix.listEnvironBytes.toList.reverse).map List.toArray }) := by
  intro h
  have h0 := h (fun _ => none) [] "BAD_VAL" (ByteArray.mk #[0xFF]) [ByteArray.mk #[0xFF, 0x3D, 0x31]]
    rfl (by decide) rfl
  dsimp only [assert] at h0
  rcases h0.1 with ⟨_, h1, _⟩
  cases h1

example : ¬ Core.AllPass (test_envvarsraw_listEnv_outputKeysWellFormed fun posix =>
    { stubMkRaw posix with listEnv := .ok #[("A=B", "1")] }) := by
  intro h
  have h0 := h (fun _ => none) #[ByteArray.mk #[0]] #[("A=B", "1")] rfl
  simp [assert] at h0

example : ¬ Core.AllPass (test_envvarsraw_listEnv_nulFreeInputsPreserveNulFreedom fun posix =>
    { stubMkRaw posix with listEnv := .ok #[("KEY", String.ofList ['a', Char.ofNat 0])] }) := by
  intro h
  have h0 := h (fun _ => none) #[] #[("KEY", String.ofList ['a', Char.ofNat 0])] rfl rfl
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

example : ¬ Core.AllPass (test_envvarsraw_mkRaw_matchesModel fun posix =>
    { stubMkRaw posix with getEnv := fun _ => .ok (some "bug") }) := by
  intro h
  have h0 := h {} "K" (.userError "x")
  simp [Bind.bind, assert, Model.rawGetEnvModel, Model.posixGetEnvBytesModel, Model.isValidPosixKeyModel,
    Model.hasInvalidKeyCharModel, Model.findFirstKeyValue] at h0
  cases h0.1

example : ¬ Core.AllPass (test_envvarsraw_modelSatisfiesConsistentWithGetEnv fun _ =>
    { mapRawError := stubMapRawError
      getEnv := fun _ => .ok none
      listEnv := .ok #[("DUP", "1")] }) := by
  intro h
  have h0 := h {} #[("DUP", "1")] "DUP" rfl rfl (by decide)
  dsimp [test_envvarsraw_modelSatisfiesConsistentWithGetEnv, assert] at h0
  cases h0.1.2

end LeanSwe.EnvVars.Raw
