import Core.NondetTest
import LeanSwe.Fs.Types

/-!
# Fs SpecTests

Human-audited behavioral specifications for `LeanSwe.Fs.FsApi` written in
`Core.NondetTest`. Pure path and error-mapping contracts are verified via
machine-checked proofs in `Proofs.lean`, while OS/C-ABI syscall effects are
grounded in `RuntimeTests.lean`.
-/

namespace LeanSwe.Fs

open Core (NondetTest)
open Core.NondetTest

/-- Every error returned by `api.mapRawError` carries a non-empty diagnostic message. -/
def test_fs_mapRawError_returnsNonEmptyMessage
    {runner} [NondetTest runner] (api : FsApi) : runner Unit := do
  let raw ← nondet FsRawError
  let err := api.mapRawError raw
  assert (err.message ≠ "")

/-- Lexical normalization `api.normPath` is idempotent on all path strings. -/
def test_fs_normPath_idempotent
    {runner} [NondetTest runner] (api : FsApi) : runner Unit := do
  let path ← nondet String
  assert (api.normPath (api.normPath path) = api.normPath path)

/-- Lexical normalization `api.normPath` never returns an empty string. -/
def test_fs_normPath_neverEmpty
    {runner} [NondetTest runner] (api : FsApi) : runner Unit := do
  let path ← nondet String
  assert (api.normPath path ≠ "")

/-- Joining an absolute `sub` path overrides `base` (`Path.joinpath(base, "/x") = "/x"`). -/
def test_fs_join_absOverridesBase
    {runner} [NondetTest runner] (api : FsApi) : runner Unit := do
  let base ← nondet String
  let sub ← nondet String
  assume (api.isAbsolute sub = true)
  assert (api.join base sub = sub)

/-- When `api.withName path newName` succeeds, the resulting path's `name` equals `newName`. -/
def test_fs_withName_updatesName
    {runner} [NondetTest runner] (api : FsApi) : runner Unit := do
  let path ← nondet String
  let newName ← nondet String
  match api.withName path newName with
  | .error _ => assume False
  | .ok updated => assert (api.name updated = some newName)

/-- When `api.withSuffix path ext` succeeds on a single-dot extension, `api.suffix` equals `ext`. -/
def test_fs_withSuffix_updatesSuffix
    {runner} [NondetTest runner] (api : FsApi) : runner Unit := do
  let path ← nondet String
  let ext ← nondet String
  assume (ext.toList.head? = some '.')
  assume (!('.' ∈ ext.toList.tail))
  match api.withSuffix path ext with
  | .error _ => assume False
  | .ok updated => assert (api.suffix updated = ext)

/-- Negative mutation check: `mapRawError` returning an empty message must fail `SpecTests`. -/
private def buggyEmptyErrApi (base : FsApi) : FsApi :=
  { base with mapRawError := fun _ => { kind := .ioError, message := "" } }

/-- Negative mutation check: broken `normPath` ignoring idempotence must fail `SpecTests`. -/
private def buggyNormApi (base : FsApi) : FsApi :=
  { base with normPath := fun p => p ++ "/a" }

/-- Negative mutation check: `withName` returning wrong filename must fail `SpecTests`. -/
private def buggyWithNameApi (base : FsApi) : FsApi :=
  { base with
    withName := fun _ _ => .ok "/wrong"
    name := fun _ => some "wrong" }

private def stubFsApi : FsApi :=
  { join := fun _ s => s
    joinMany := fun _ => ""
    normPath := fun _ => "."
    parent := fun _ => none
    name := fun _ => none
    stem := fun _ => none
    suffix := fun _ => ""
    suffixes := fun _ => #[]
    withName := fun _ _ => .error { kind := .invalidInput, message := "stub" }
    withSuffix := fun _ _ => .error { kind := .invalidInput, message := "stub" }
    isAbsolute := fun s => s.startsWith "/"
    relativeTo := fun _ _ => .error { kind := .invalidInput, message := "stub" }
    mapRawError := fun _ => { kind := .ioError, message := "stub" }
    readText := fun _ => pure (.ok "")
    writeText := fun _ _ => pure (.ok ())
    appendText := fun _ _ => pure (.ok ())
    readBytes := fun _ => pure (.ok ByteArray.empty)
    writeBytes := fun _ _ => pure (.ok ())
    atomicWriteText := fun _ _ => pure (.ok ())
    touch := fun _ _ => pure (.ok ())
    mkdir := fun _ _ _ => pure (.ok ())
    unlink := fun _ _ => pure (.ok ())
    rmdir := fun _ => pure (.ok ())
    rmtree := fun _ _ => pure (.ok ())
    rename := fun _ _ => pure (.ok ())
    copyFile := fun _ _ => pure (.ok ())
    copyTree := fun _ _ _ => pure (.ok ())
    pathExists := fun _ => pure (.ok false)
    isFile := fun _ => pure (.ok false)
    isDir := fun _ => pure (.ok false)
    isSymlink := fun _ => pure (.ok false)
    stat := fun _ => pure (.error { kind := .notFound, message := "stub" })
    lstat := fun _ => pure (.error { kind := .notFound, message := "stub" })
    chmod := fun _ _ => pure (.ok ())
    symlink := fun _ _ => pure (.ok ())
    readLink := fun _ => pure (.error { kind := .notFound, message := "stub" })
    resolve := fun _ => pure (.error { kind := .notFound, message := "stub" })
    cwd := pure (.ok ".")
    listDir := fun _ => pure (.ok #[])
    walk := fun _ => pure (.ok #[])
    glob := fun _ _ => pure (.ok #[])
    rglob := fun _ _ => pure (.ok #[]) }

example : ¬ Core.AllPass (test_fs_mapRawError_returnsNonEmptyMessage (buggyEmptyErrApi stubFsApi)) := by
  intro h
  have h0 := h (.userError "boom")
  simp [buggyEmptyErrApi, assert] at h0

example : ¬ Core.AllPass (test_fs_normPath_idempotent (buggyNormApi stubFsApi)) := by
  intro h
  have h0 := h "x"
  simp [buggyNormApi, assert] at h0

example : ¬ Core.AllPass (test_fs_withName_updatesName (buggyWithNameApi stubFsApi)) := by
  intro h
  have h0 := h "/a/b" "c"
  simp [buggyWithNameApi, assert] at h0

end LeanSwe.Fs
