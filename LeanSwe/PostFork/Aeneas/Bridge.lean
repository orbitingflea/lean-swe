import LeanSwe.PostFork.Aeneas.Model
import LeanSwe.PostFork.Aeneas.Funs

open _root_.Aeneas _root_.Aeneas.Std Result

namespace LeanSwe.PostFork.Aeneas.Bridge

open LeanSwe.LinuxSyscall
open LeanSwe.PostFork
open LeanSwe.PostFork.World
open LeanSwe.PostFork.Aeneas.Model

/-- Convert a pure `FailureStage` into its Aeneas wire byte (`1..7`). -/
def stageToU8 : FailureStage → Std.U8
  | .validate => 1#u8
  | .processGroup => 2#u8
  | .signalReset => 3#u8
  | .fdSetup => 4#u8
  | .closeUnkept => 5#u8
  | .chdir => 6#u8
  | .execve => 7#u8
  | .wireTruncated => 7#u8

/-- Convert a pure host `UInt32` bitmask into `Aeneas.Std.U32`. -/
def mkU32 (v : UInt32) : Std.U32 :=
  ⟨v.toBitVec⟩

/-- Compute the Aeneas child flag mask corresponding to `(spec, withBarrier)`. -/
def specFlagsU32 {fd : Type} (spec : ChildSpecM fd) (withBarrier : Bool) : Std.U32 :=
  mkU32 (LeanSwe.PostFork.Model.flagsOfSpec spec withBarrier)

/-- Convert an `Aeneas.Std.U8` byte list into a pure `ByteArray`. -/
def bytesToByteArray (bs : List Std.U8) : ByteArray :=
  ByteArray.mk (bs.map (fun b => UInt8.ofNat b.bv.toNat)).toArray

/-- Project an `FdRef Std.I32` into its concrete child descriptor `Std.I32`. -/
def fdRefToStdI32 : FdRef Std.I32 → Std.I32
  | .handle h => h
  | .raw n => ⟨n.toBitVec⟩

/-- Project a `StdioPlan Std.I32` into the `(stdin_fd, stdout_fd, stderr_fd)` triple passed to `run_child`. -/
def stdioToStdI32Triple : StdioPlan Std.I32 → Std.I32 × Std.I32 × Std.I32
  | .inherit => ((-1)#i32, (-1)#i32, (-1)#i32)
  | .redirect sIn sOut sErr _ => (fdRefToStdI32 sIn, fdRefToStdI32 sOut, fdRefToStdI32 sErr)

/-- Pure string/env/argv hygiene portion of `Model.validateSpecWith`. -/
def specStringHygieneOk {fd : Type} (spec : ChildSpecM fd) : Bool :=
  let cwdOk := match spec.cwd with | some d => !LeanSwe.PostFork.Model.hasEmbeddedNulStr d | none => true
  let pathOk := !spec.path.isEmpty && !LeanSwe.PostFork.Model.hasEmbeddedNulStr spec.path
  let argvOk := spec.argv.all LeanSwe.PostFork.Model.ArgToken.isValid
  let envOk := spec.env.all LeanSwe.PostFork.Model.isValidEnvBinding &&
    spec.rawEnv.all LeanSwe.PostFork.Model.isValidRawEnvEntry
  pathOk && cwdOk && argvOk && envOk

/-- Collect all `FdRef` entries referenced in `stdio`, `closeFds`, and `fdPolicy.keepFds`. -/
def allSpecFdRefs {fd : Type} (spec : ChildSpecM fd) : List (FdRef fd) :=
  let stdioList := match spec.stdio with
    | .inherit => []
    | .redirect a b c _ => [a, b, c]
  stdioList ++ spec.closeFds.toList ++ (LeanSwe.PostFork.Model.FdPolicy.keepFds spec.fdPolicy).toList

/-- Host invariant on pinned `RawFd` handles: every `.handle h` is `>= 3` and distinct from caller `.raw n` slots. -/
def specHandlesValid (spec : ChildSpecM Std.I32) : Bool :=
  let refs := allSpecFdRefs spec
  let handles := refs.filterMap (fun r => match r with | .handle h => some h | .raw _ => none)
  let raws := refs.filterMap (fun r => match r with | .raw n => some (⟨n.toBitVec⟩ : Std.I32) | .handle _ => none)
  handles.all (fun h => decide (3#i32 ≤ h) && !(raws.any (· == h)))

/-- Host invariant that newly allocated internal `repW` and optional `syncR` pipes are non-negative and disjoint from caller descriptors. -/
def internalPipesDisjoint
    (withBarrier hasRedir : Bool)
    (syncR inFd outFd errFd repW : Std.I32)
    (closeList keepList : List Std.I32) : Bool :=
  decide (0#i32 ≤ repW) &&
  !sliceContainsNonnegSpec closeList repW.val &&
  !sliceContainsNonnegSpec keepList repW.val &&
  (!withBarrier ||
    (decide (0#i32 ≤ syncR) &&
      repW != syncR &&
      !sliceContainsNonnegSpec closeList syncR.val &&
      !sliceContainsNonnegSpec keepList syncR.val)) &&
  (!hasRedir ||
    (!fdInStdioSpec repW inFd outFd errFd &&
      (!withBarrier || !fdInStdioSpec syncR inFd outFd errFd)))

private theorem flagsOfSpec_valid_combos {fd : Type} (spec : ChildSpecM fd) (withBarrier : Bool) :
    validFlagsSpec (specFlagsU32 spec withBarrier) = true := by
  dsimp only [validFlagsSpec, flagSet, specFlagsU32, mkU32,
    LeanSwe.PostFork.Model.flagsOfSpec,
    LeanSwe.PostFork.Model.FLAG_SET_PGID,
    LeanSwe.PostFork.Model.FLAG_RESET_SIGPIPE,
    LeanSwe.PostFork.Model.FLAG_HAS_SYNC_BARRIER,
    LeanSwe.PostFork.Model.FLAG_REDIRECT_STDIO,
    LeanSwe.PostFork.Model.FLAG_CLOSE_UNKEPT_ABOVE2,
    LeanSwe.PostFork.Model.FLAG_CLOSE_STDIO_SOURCES,
    FLAG_CLOSE_STDIO_SOURCES, FLAG_REDIRECT_STDIO, FLAG_CLOSE_UNKEPT_ABOVE2]
  cases spec.processGroup <;> cases spec.sigpipe <;> cases withBarrier <;>
    cases spec.stdio with
    | inherit =>
      cases spec.fdPolicy <;> (simp only; decide)
    | redirect _ _ _ closeSrcs =>
      cases closeSrcs <;> cases spec.fdPolicy <;> (simp only; decide)

/-- Every `ChildSpecM` configuration produces valid `validFlagsSpec` child setup flags via `flagsOfSpec`. -/
theorem flagsOfSpec_always_valid {fd : Type} (spec : ChildSpecM fd) (withBarrier : Bool) :
    validFlagsSpec (specFlagsU32 spec withBarrier) = true :=
  flagsOfSpec_valid_combos spec withBarrier

end LeanSwe.PostFork.Aeneas.Bridge
