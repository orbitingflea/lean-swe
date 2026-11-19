import Fuzz.Common.Rng
import Fuzz.Common.Shrink
import Fuzz.Common.Coverage
import Fuzz.Common.Suite
import LeanSwe.EnvVars.Raw.Types
import LeanSwe.EnvVars.Raw.Model
import LeanSwe.EnvVars.Raw.Interface
import LeanSwe.EnvVars.Types
import LeanSwe.EnvVars.Model
import LeanSwe.EnvVars.Interface

namespace Fuzz.EnvVars

open Fuzz.Common
open LeanSwe.EnvVars
open LeanSwe.EnvVars.Raw.Model

@[extern "leanswe_fuzz_host_snapshot"]
private opaque rawFuzzHostSnapshot : BaseIO Unit

@[extern "leanswe_fuzz_host_restore"]
private opaque rawFuzzHostRestore : BaseIO Unit

@[extern "leanswe_fuzz_setenv_bytes"]
private opaque rawFuzzSetEnvBytes (k : @& ByteArray) (v : @& ByteArray) (ovw : UInt8) : BaseIO UInt32

@[extern "leanswe_fuzz_unsetenv_bytes"]
private opaque rawFuzzUnsetEnvBytes (k : @& ByteArray) : BaseIO UInt32

@[extern "leanswe_fuzz_clearenv"]
private opaque rawFuzzClearEnv : BaseIO Unit

@[extern "leanswe_fuzz_raw_begin"]
private opaque rawFuzzBegin (cap : UInt32) : BaseIO Unit

@[extern "leanswe_fuzz_raw_set"]
private opaque rawFuzzSet (idx : UInt32) (slice : @& ByteArray) : BaseIO UInt32

@[extern "leanswe_fuzz_raw_install"]
private opaque rawFuzzInstall (useNullPtr : UInt8) : BaseIO Unit

@[extern "leanswe_fuzz_raw_end"]
private opaque rawFuzzEnd : BaseIO Unit

private def formatByteArrayRepr (bs : ByteArray) : String :=
  let lim := min bs.size 24
  let hex := (bs.extract 0 lim).data.toList.map fun b =>
    let hi := b.toNat / 16
    let lo := b.toNat % 16
    let d := fun n : Nat => if n < 10 then Char.ofNat (48 + n) else Char.ofNat (87 + n)
    String.ofList [d hi, d lo]
  let suffix := if bs.size > lim then "..." else ""
  s!"bytes[{bs.size}:0x{String.intercalate "" hex}{suffix}]"

private def exceptEq {ε α : Type} [BEq ε] [BEq α] : Except ε α → Except ε α → Bool
  | .ok a, .ok b => a == b
  | .error e1, .error e2 => e1 == e2
  | _, _ => false

private def formatExcept {ε α : Type} [Repr ε] [Repr α] : Except ε α → String
  | .ok a => s!".ok ({repr a})"
  | .error e => s!".error ({repr e})"

private inductive RawPostOp where
  | setEnv (k v : ByteArray) (overwrite : Bool)
  | unsetEnv (k : ByteArray)
  | clearEnv
  | queryGet (key : String)
  | queryList
  | queryHome
  deriving BEq, DecidableEq, Inhabited

private def reprRawPostOp : RawPostOp → String
  | .setEnv k v ovw => s!"setEnv {formatByteArrayRepr k} {formatByteArrayRepr v} {ovw}"
  | .unsetEnv k => s!"unsetEnv {formatByteArrayRepr k}"
  | .clearEnv => "clearEnv"
  | .queryGet key => s!"queryGet {repr key}"
  | .queryList => "queryList"
  | .queryHome => "queryHome"

private inductive EnvFuzzOp where
  | setEnv (k v : ByteArray) (overwrite : Bool)
  | unsetEnv (k : ByteArray)
  | clearEnv
  | queryGet (key : String)
  | queryList
  | queryHome
  | querySplitPath (path : String)
  | queryMapRawErr (raw : EnvVarsRawError)
  | rawTable (entries : Array ByteArray) (useNullPtr : Bool) (extraQueries : Array String) (postOps : Array RawPostOp)
  deriving BEq, DecidableEq

private def reprEnvFuzzOp : EnvFuzzOp → String
  | .setEnv k v ovw => s!"setEnv {formatByteArrayRepr k} {formatByteArrayRepr v} {ovw}"
  | .unsetEnv k => s!"unsetEnv {formatByteArrayRepr k}"
  | .clearEnv => "clearEnv"
  | .queryGet key => s!"queryGet {repr key}"
  | .queryList => "queryList"
  | .queryHome => "queryHome"
  | .querySplitPath p =>
    let lim := min p.length 48
    let preview := String.ofList (p.toList.take lim) ++ (if p.length > lim then "..." else "")
    s!"querySplitPath len={p.length} path={repr preview}"
  | .queryMapRawErr r => s!"queryMapRawErr {repr r}"
  | .rawTable es useNull qs post =>
    let esRepr := String.intercalate ", " (es.toList.map formatByteArrayRepr)
    let postRepr := String.intercalate ", " (post.toList.map reprRawPostOp)
    s!"rawTable entries=[{esRepr}] null={useNull} qs={repr qs} post=[{postRepr}]"

private def withRestoredHostEnviron {α : Type} (act : IO α) : IO α := do
  rawFuzzHostSnapshot
  try
    act
  finally
    rawFuzzHostRestore

private def hasDupKeys (pairs : Array (String × String)) : Bool := Id.run do
  let mut seen : List String := []
  for (k, _) in pairs do
    if seen.contains k then
      return true
    seen := k :: seen
  return false

private def shrinkStepSizes (n : Nat) : List Nat := Id.run do
  if n == 0 then
    return []
  let mut steps : Array Nat := #[]
  let mut step := n / 2
  while step > 1 do
    steps := steps.push step
    if n % 2 == 0 && step % 2 == 1 && step + 1 < n then
      steps := steps.push (step + 1)
    step := step / 2
  if n > 2 then
    steps := steps.push 2
  steps := steps.push 1
  return steps.toList.eraseDups

private def shrinkDeleteIntervals (n : Nat) : Array (Nat × Nat) := Id.run do
  let mut ivs : Array (Nat × Nat) := #[]
  if n <= 1 then
    return ivs
  let half := n / 2
  ivs := ivs.push (half, n)
  ivs := ivs.push (0, half)
  if n % 2 == 0 && half % 2 == 1 && half + 1 < n then
    ivs := ivs.push (half + 1, n)
    ivs := ivs.push (0, half - 1)
  if n > 128 then
    for k in [8, 16] do
      for ci in List.range k do
        let s0 := (ci * n) / k
        let e0 := ((ci + 1) * n) / k
        let sEven := s0 - (s0 % 2)
        let eEven := e0 - (e0 % 2)
        if sEven < eEven && eEven - sEven < n then
          ivs := ivs.push (sEven, eEven)
        if s0 < e0 && e0 - s0 < n then
          ivs := ivs.push (s0, e0)
  for step in shrinkStepSizes n do
    if step < n then
      ivs := ivs.push (n - step, n)
      ivs := ivs.push (0, step)
      if step + 1 < n then
        if n ≤ 256 && step == 2 then
          let mut p := 2
          while p + 2 < n do
            ivs := ivs.push (p, p + 2)
            p := p + 2
          for pos in [1 : n - 2] do
            if pos % 2 == 1 then
              ivs := ivs.push (pos, pos + 2)
        else if n ≤ 256 && step == 1 then
          for pos in [1 : n - 1] do
            ivs := ivs.push (pos, pos + 1)
        else
          for qi in [1 : 8] do
            let rawPos := (qi * (n - step)) / 8
            let pos := if step % 2 == 0 then rawPos - (rawPos % 2) else rawPos
            if pos > 0 && pos + step < n then
              ivs := ivs.push (pos, pos + step)
          if step % 2 == 1 then
            ivs := ivs.push (1, 1 + step)
            ivs := ivs.push (n - 1 - step, n - 1)
          else
            if 2 + step < n then
              ivs := ivs.push (2, 2 + step)
            if n - step >= 2 then
              ivs := ivs.push (n - 2 - step, n - 2)
            if n - step >= 4 then
              ivs := ivs.push (n - 4 - step, n - 4)
  return ivs

private def shrinkString (s : String) : List String := Id.run do
  let cs := s.toList.toArray
  let n := cs.size
  if n == 0 then
    return []
  let mut out : Array String := #[""]
  if s != "a" && s.utf8ByteSize > 1 then
    out := out.push "a"
  if n > 1 then
    for (st, en) in shrinkDeleteIntervals n do
      out := out.push (String.ofList ((cs.extract 0 st).toList ++ (cs.extract en n).toList))
  return out.toList.eraseDups.filter fun c => c.utf8ByteSize < s.utf8ByteSize

private def shrinkBytes (bs : ByteArray) : List ByteArray := Id.run do
  let n := bs.size
  if n == 0 then
    return []
  let mut out : Array ByteArray := #[ByteArray.empty]
  if let some s := String.fromUTF8? bs then
    for s' in shrinkString s do
      out := out.push s'.toUTF8
  if n > 1 then
    for (st, en) in shrinkDeleteIntervals n do
      out := out.push (bs.extract 0 st ++ bs.extract en n)
  return out.toList.eraseDups.filter (·.size < n)

private def shrinkRawSlice (sl : ByteArray) : List ByteArray :=
  match splitFirstEqBytesModel sl with
  | some (k, v) =>
    let kCands := (shrinkBytes k).filter fun k' => !k'.isEmpty && !k'.data.any (· == 0x3D)
    let ks := kCands.map fun k' => k' ++ ByteArray.mk #[0x3D] ++ v
    let vs := (shrinkBytes v).map fun v' => k ++ ByteArray.mk #[0x3D] ++ v'
    ks ++ vs ++ [ByteArray.empty, k]
  | none => shrinkBytes sl

private def shrinkArrayElems {α : Type} [Inhabited α] (xs : Array α) (shrinkOne : α → List α) : List (Array α) := Id.run do
  let mut out : Array (Array α) := #[]
  if !xs.isEmpty then
    out := out.push #[]
    if xs.size > 1 then
      let half := xs.size / 2
      out := out.push (xs.extract 0 half)
      out := out.push (xs.extract half xs.size)
      for i in List.range xs.size do
        out := out.push (xs.extract 0 i ++ xs.extract (i + 1) xs.size)
    for i in List.range xs.size do
      for x' in shrinkOne xs[i]! do
        out := out.push (xs.set! i x')
  return out.toList

private def shrinkOptStr : Option String → List (Option String)
  | none => []
  | some s => none :: (shrinkString s).map some

private def shrinkRawErr : EnvVarsRawError → List EnvVarsRawError
  | .invalidEncoding k? d =>
    (shrinkOptStr k?).map (.invalidEncoding · d) ++
    (shrinkString d).map (.invalidEncoding k?)
  | .invalidArgument k? code d =>
    (shrinkOptStr k?).map (.invalidArgument · code d) ++
    (if code != 0 then [.invalidArgument k? 0 d] else []) ++
    (shrinkString d).map (.invalidArgument k? code)
  | .otherError code d =>
    (if code != 0 then [.otherError 0 d] else []) ++
    (shrinkString d).map (.otherError code)
  | .userError d => (shrinkString d).map .userError

private def shrinkRawPostOp : RawPostOp → List RawPostOp
  | .setEnv k v ovw =>
    (if ovw then [.setEnv k v false] else []) ++
    (shrinkBytes k).map (fun k' => .setEnv k' v ovw) ++
    (shrinkBytes v).map (fun v' => .setEnv k v' ovw)
  | .unsetEnv k => (shrinkBytes k).map .unsetEnv
  | .queryGet k => (shrinkString k).map .queryGet
  | _ => []

private def shrinkOp : EnvFuzzOp → List EnvFuzzOp
  | .setEnv k v ovw =>
    (if ovw then [.setEnv k v false] else []) ++
    (shrinkBytes k).map (fun k' => .setEnv k' v ovw) ++
    (shrinkBytes v).map (fun v' => .setEnv k v' ovw)
  | .unsetEnv k => (shrinkBytes k).map .unsetEnv
  | .queryGet k => (shrinkString k).map .queryGet
  | .querySplitPath p => (shrinkString p).map .querySplitPath
  | .queryMapRawErr r => (shrinkRawErr r).map .queryMapRawErr
  | .rawTable es useNull qs post =>
    let esCands := (shrinkArrayElems es shrinkRawSlice).map fun es' => .rawTable es' useNull qs post
    let qsCands := (shrinkArrayElems qs shrinkString).map fun qs' => .rawTable es useNull qs' post
    let postCands := (shrinkArrayElems post shrinkRawPostOp).map fun post' => .rawTable es useNull qs post'
    let nullCands := if !useNull && es.isEmpty then [.rawTable #[] true qs post] else []
    nullCands ++ esCands ++ qsCands ++ postCands
  | _ => []

private def rawErrTag : EnvVarsRawError → String
  | .invalidEncoding none _ => "invalidEncoding_nokey"
  | .invalidEncoding (some _) _ => "invalidEncoding_key"
  | .invalidArgument .. => "invalidArgument"
  | .otherError .. => "otherError"
  | .userError .. => "userError"

private def envErrTag (e : EnvVarsError) : String :=
  match e.kind with
  | .invalidKey => "invalidKey"
  | .notFound => "notFound"
  | .invalidEncoding => "invalidEncoding"
  | .ioError => "ioError"

private def exceptOptClass {ε α : Type} (errTag : ε → String) : Except ε (Option α) → String
  | .ok none => "ok_none"
  | .ok (some _) => "ok_some"
  | .error e => "err_" ++ errTag e

private def exceptValClass {ε α : Type} (errTag : ε → String) : Except ε α → String
  | .ok _ => "ok"
  | .error e => "err_" ++ errTag e

private def execSetEnvStep
    (customSetEnv? : Option (EnvironState → ByteArray → ByteArray → Bool → IO (UInt32 × EnvironState)))
    (st : EnvironState) (curIsNull : Bool) (tr : CoverageTracker)
    (k v : ByteArray) (ovw : Bool) : IO (Except String (EnvironState × Bool × CoverageTracker)) := do
  let (rc, stNext) ← match customSetEnv? with
    | some fn => fn st k v ovw
    | none => do
      let rc ← rawFuzzSetEnvBytes k v (if ovw then 1 else 0)
      pure (rc, st)
  match posixSetEnvBytesModel st k v ovw with
  | .error expCode =>
    if rc != expCode then
      return .error s!"SETENV_ERR_MISMATCH:{expCode}:{rc}: k={formatByteArrayRepr k}"
    let eb :=
      if k.isEmpty then "err.EINVAL_empty"
      else if k.data.any (· == 0x3D) then "err.EINVAL_eq"
      else if k.data.any (· == 0) then "err.EINVAL_nul_key"
      else "err.EINVAL_nul_val"
    return .ok (st, curIsNull, tr.record "setenv" eb)
  | .ok sNext =>
    if rc != 0 then
      return .error s!"SETENV_UNEXPECTED_ERR:0:{rc}: k={formatByteArrayRepr k}"
    let existed := (findFirstKeyIdxList 0 st.entries.toList k).isSome
    let b := if !existed then "ok.insert" else if ovw then "ok.overwrite" else "ok.keep_existing"
    let stFinal := if customSetEnv?.isSome then stNext else sNext
    return .ok (stFinal, false, tr.record "setenv" b)

private def execUnsetEnvStep (st : EnvironState) (curIsNull : Bool) (tr : CoverageTracker)
    (k : ByteArray) : IO (Except String (EnvironState × Bool × CoverageTracker)) := do
  let rc ← rawFuzzUnsetEnvBytes k
  match posixUnsetEnvBytesModel st k with
  | .error expCode =>
    if rc != expCode then
      return .error s!"UNSETENV_ERR_MISMATCH:{expCode}:{rc}: k={formatByteArrayRepr k}"
    let ub :=
      if k.isEmpty then "err.EINVAL_empty"
      else if k.data.any (· == 0x3D) then "err.EINVAL_eq"
      else "err.EINVAL_nul"
    return .ok (st, curIsNull, tr.record "unsetenv" ub)
  | .ok sNext =>
    if rc != 0 then
      return .error s!"UNSETENV_UNEXPECTED_ERR:0:{rc}: k={formatByteArrayRepr k}"
    let existed := st.entries.any (fun e => entryHasKeyBytes e k)
    return .ok (sNext, curIsNull, tr.record "unsetenv" (if existed then "ok.present" else "ok.absent"))

private def execQueryGetStep
    (customQueryGet? : Option (EnvironState → String → IO (Except EnvVarsError (Option String))))
    (st : EnvironState) (tr : CoverageTracker) (key : String) : IO (Except String CoverageTracker) := do
  let mut t := tr
  let actualRawGet ← LeanSwe.EnvVars.Raw.getEnv key
  let modelRawGet := rawGetEnvModel st key
  if !exceptEq actualRawGet modelRawGet then
    return .error s!"RAW_GET_MISMATCH:{exceptOptClass rawErrTag modelRawGet}:{exceptOptClass rawErrTag actualRawGet}: key={repr key} model={formatExcept modelRawGet} actual={formatExcept actualRawGet}"
  match actualRawGet with
  | .ok (some _) => t := t.record "raw_getEnv" "ok.some"
  | .ok none =>
    t := t.record "raw_getEnv" (if !isValidPosixKeyModel key then "ok.none_invalid_key" else "ok.none_unset")
  | .error (.invalidEncoding _ _) => t := t.record "raw_getEnv" "err.invalidEncoding"
  | .error e => return .error s!"RAW_GET_UNEXPECTED_ERROR:ok:{rawErrTag e}: key={repr key} err={repr e}"
  let actualGet ← match customQueryGet? with
    | some fn => fn st key
    | none => LeanSwe.EnvVars.getEnv key
  let modelGet := Model.getEnvModel st key
  if !exceptEq actualGet modelGet then
    return .error s!"GET_MISMATCH:{exceptOptClass envErrTag modelGet}:{exceptOptClass envErrTag actualGet}: key={repr key} model={formatExcept modelGet} actual={formatExcept actualGet}"
  match actualGet with
  | .ok (some _) => t := t.record "getEnv" "ok.some"
  | .ok none => t := t.record "getEnv" "ok.none"
  | .error e =>
    if e.kind == .invalidKey then
      let b := if key.isEmpty then "err.invalidKey_empty"
               else if '=' ∈ key.toList then "err.invalidKey_eq"
               else "err.invalidKey_nul"
      t := t.record "getEnv" b
    else
      t := t.record "getEnv" "err.invalidEncoding"
  return .ok t

private def execQueryListStep (st : EnvironState) (curIsNull : Bool) (tr : CoverageTracker) :
    IO (Except String CoverageTracker) := do
  let mut t := tr
  let actualRawList ← LeanSwe.EnvVars.Raw.listEnv
  let modelRawList := rawListEnvModel st
  if !exceptEq actualRawList modelRawList then
    return .error s!"RAW_LIST_MISMATCH:{exceptValClass rawErrTag modelRawList}:{exceptValClass rawErrTag actualRawList}: model={formatExcept modelRawList} actual={formatExcept actualRawList}"
  match actualRawList with
  | .error (.invalidEncoding none _) => t := t.record "raw_listEnv" "err.invalidEncoding_key"
  | .error (.invalidEncoding (some _) _) => t := t.record "raw_listEnv" "err.invalidEncoding_val"
  | .error e => return .error s!"RAW_LIST_UNEXPECTED_ERROR:ok:{rawErrTag e}: {repr e}"
  | .ok pairs =>
    let emptyBucket := if curIsNull then "ok.empty_null_ptr" else "ok.empty_nonnull"
    t := t.record "raw_listEnv" (if st.entries.isEmpty then emptyBucket else "ok.entries")
    if st.entries.any (fun e => (splitFirstEqBytesModel e).isNone) then
      t := t.record "raw_listEnv" "ok.skipped_malformed"
    if hasDupKeys pairs then
      t := t.record "raw_listEnv" "ok.duplicate_keys"
  let actualList ← LeanSwe.EnvVars.listEnv
  let modelList := Model.listEnvModel st
  if !exceptEq actualList modelList then
    return .error s!"LIST_MISMATCH:{exceptValClass envErrTag modelList}:{exceptValClass envErrTag actualList}: model={formatExcept modelList} actual={formatExcept actualList}"
  match actualList with
  | .ok _ => t := t.record "listEnv" "ok"
  | .error e =>
    t := t.record "listEnv" (if e.key.isNone then "err.invalidEncoding_key" else "err.invalidEncoding_val")
  return .ok t

private def execQueryHomeStep (st : EnvironState) (tr : CoverageTracker) : IO (Except String CoverageTracker) := do
  let mut t := tr
  let actualHome ← LeanSwe.EnvVars.homeDir
  let modelHome := Model.homeDirModel st
  if !exceptEq actualHome modelHome then
    return .error s!"HOMEDIR_MISMATCH:{exceptValClass envErrTag modelHome}:{exceptValClass envErrTag actualHome}: model={formatExcept modelHome} actual={formatExcept actualHome}"
  match actualHome with
  | .ok _ => t := t.record "homeDir" "ok"
  | .error e =>
    if e.kind == .invalidEncoding then
      t := t.record "homeDir" "err.invalidEncoding"
    else if posixGetEnvBytesModel st "HOME" == some ByteArray.empty then
      t := t.record "homeDir" "err.notFound_empty"
    else
      t := t.record "homeDir" "err.notFound_unset"
  return .ok t

private def checkQueriesOnState (s : EnvironState) (useNullPtr : Bool)
    (extraQueries : Array String) (tracker : CoverageTracker) :
    IO (Except String CoverageTracker) := do
  let mut tr ← match ← execQueryListStep s useNullPtr tracker with
    | .error e => return .error e
    | .ok t => pure t
  tr ← match ← execQueryHomeStep s tr with
    | .error e => return .error e
    | .ok t => pure t
  let mut queryKeys : Array String := extraQueries
  for slice in s.entries do
    match splitFirstEqBytesModel slice with
    | some (kb, _) =>
      if let some kStr := String.fromUTF8? kb then
        if !queryKeys.contains kStr then
          queryKeys := queryKeys.push kStr
    | none => pure ()
  for qk in queryKeys do
    match ← execQueryGetStep none s tr qk with
    | .error e => return .error e
    | .ok t => tr := t
  return .ok tr

private def execTraceWithOracle
    (customSetEnv? : Option (EnvironState → ByteArray → ByteArray → Bool → IO (UInt32 × EnvironState)) := none)
    (customQueryGet? : Option (EnvironState → String → IO (Except EnvVarsError (Option String))) := none)
    (trace : Array EnvFuzzOp) : IO (Except String CoverageTracker) := do
  rawFuzzClearEnv
  let mut st : EnvironState := posixClearEnvModel
  let mut curIsNull : Bool := true
  let mut tr := CoverageTracker.empty
  for op in trace do
    match op with
    | .setEnv k v ovw =>
      match ← execSetEnvStep customSetEnv? st curIsNull tr k v ovw with
      | .error e => return .error e
      | .ok (s', n', tr') => st := s'; curIsNull := n'; tr := tr'
    | .unsetEnv k =>
      match ← execUnsetEnvStep st curIsNull tr k with
      | .error e => return .error e
      | .ok (s', n', tr') => st := s'; curIsNull := n'; tr := tr'
    | .clearEnv =>
      rawFuzzClearEnv
      st := posixClearEnvModel
      curIsNull := true
      tr := tr.record "clearenv" "ok.null"
    | .queryGet key =>
      match ← execQueryGetStep customQueryGet? st tr key with
      | .error e => return .error e
      | .ok tr' => tr := tr'
    | .queryList =>
      match ← execQueryListStep st curIsNull tr with
      | .error e => return .error e
      | .ok tr' => tr := tr'
    | .queryHome =>
      match ← execQueryHomeStep st tr with
      | .error e => return .error e
      | .ok tr' => tr := tr'
    | .querySplitPath path =>
      let actualSplit := LeanSwe.EnvVars.splitSearchPath path
      let modelSplit := Model.splitSearchPathModel path
      if actualSplit != modelSplit then
        return .error s!"SPLIT_PATH_MISMATCH:diff:diff: len={path.length} model={repr modelSplit} actual={repr actualSplit}"
      let b := if path.length >= 250000 then "large_stack_safe"
               else if actualSplit.isEmpty then "empty"
               else "nonempty"
      tr := tr.record "splitSearchPath" b
    | .queryMapRawErr rawErr =>
      let a1 := LeanSwe.EnvVars.mapRawError rawErr
      let a2 := LeanSwe.EnvVars.Raw.mapRawError rawErr
      let m := mapRawErrorModel rawErr
      if a1 != m || a2 != m then
        return .error s!"MAP_RAW_ERR_MISMATCH:{rawErrTag rawErr}:diff: raw={repr rawErr} m={repr m} a1={repr a1} a2={repr a2}"
      let mb := match rawErr with
        | .invalidEncoding _ _ => "invalidEncoding"
        | .invalidArgument _ _ _ => "invalidArgument"
        | .otherError _ _ => "otherError"
        | .userError _ => "userError"
      tr := tr.record "mapRawError" mb
    | .rawTable entries useNullPtr extraQueries postOps =>
      let effectiveEntries := if useNullPtr then #[] else entries
      let some sRaw := posixInstallRawTableModel effectiveEntries
        | return .error "RAW_TABLE_CONTAINED_NUL_BYTE"
      rawFuzzBegin effectiveEntries.size.toUInt32
      let res : Except String CoverageTracker ← try
        for h : i in [0 : effectiveEntries.size] do
          let setRc ← rawFuzzSet i.toUInt32 effectiveEntries[i]
          if setRc != 0 then
            throw (IO.userError s!"RAW_FUZZ_SET_FAILED idx={i} rc={setRc}")
        rawFuzzInstall (if useNullPtr then 1 else 0)
        match ← checkQueriesOnState sRaw useNullPtr extraQueries tr with
        | .error msg => pure (.error msg)
        | .ok tr0 => do
          let mut rawSt := sRaw
          let mut rawIsNull := useNullPtr
          let mut rawTr := tr0
          let mut postErr? : Option String := none
          for pOp in postOps do
            if postErr?.isSome then
              break
            match pOp with
            | .setEnv k v ovw =>
              match ← execSetEnvStep customSetEnv? rawSt rawIsNull rawTr k v ovw with
              | .error e => postErr? := some e
              | .ok (s', n', t') => rawSt := s'; rawIsNull := n'; rawTr := t'
            | .unsetEnv k =>
              match ← execUnsetEnvStep rawSt rawIsNull rawTr k with
              | .error e => postErr? := some e
              | .ok (s', n', t') => rawSt := s'; rawIsNull := n'; rawTr := t'
            | .clearEnv =>
              rawFuzzClearEnv
              rawSt := posixClearEnvModel
              rawIsNull := true
              rawTr := rawTr.record "clearenv" "ok.null"
            | .queryGet key =>
              match ← execQueryGetStep customQueryGet? rawSt rawTr key with
              | .error e => postErr? := some e
              | .ok t' => rawTr := t'
            | .queryList =>
              match ← execQueryListStep rawSt rawIsNull rawTr with
              | .error e => postErr? := some e
              | .ok t' => rawTr := t'
            | .queryHome =>
              match ← execQueryHomeStep rawSt rawTr with
              | .error e => postErr? := some e
              | .ok t' => rawTr := t'
          match postErr? with
          | some e => pure (.error e)
          | none => pure (.ok rawTr)
      finally
        rawFuzzEnd
      match res with
      | .error msg => return .error msg
      | .ok tr' => tr := tr'
      st := posixClearEnvModel
      curIsNull := true
  return .ok tr

private def requiredBuckets : Array CoverageBucket := #[
  bucket "setenv" "ok.insert",
  bucket "setenv" "ok.overwrite",
  bucket "setenv" "ok.keep_existing",
  bucket "setenv" "err.EINVAL_empty",
  bucket "setenv" "err.EINVAL_eq",
  bucket "setenv" "err.EINVAL_nul_key",
  bucket "setenv" "err.EINVAL_nul_val",
  bucket "unsetenv" "ok.present",
  bucket "unsetenv" "ok.absent",
  bucket "unsetenv" "err.EINVAL_empty",
  bucket "unsetenv" "err.EINVAL_eq",
  bucket "unsetenv" "err.EINVAL_nul",
  bucket "clearenv" "ok.null",
  bucket "raw_getEnv" "ok.some",
  bucket "raw_getEnv" "ok.none_unset",
  bucket "raw_getEnv" "ok.none_invalid_key",
  bucket "raw_getEnv" "err.invalidEncoding",
  bucket "getEnv" "ok.some",
  bucket "getEnv" "ok.none",
  bucket "getEnv" "err.invalidKey_empty",
  bucket "getEnv" "err.invalidKey_eq",
  bucket "getEnv" "err.invalidKey_nul",
  bucket "getEnv" "err.invalidEncoding",
  bucket "raw_listEnv" "ok.empty_null_ptr",
  bucket "raw_listEnv" "ok.empty_nonnull",
  bucket "raw_listEnv" "ok.entries",
  bucket "raw_listEnv" "ok.skipped_malformed",
  bucket "raw_listEnv" "ok.duplicate_keys",
  bucket "raw_listEnv" "err.invalidEncoding_key",
  bucket "raw_listEnv" "err.invalidEncoding_val",
  bucket "listEnv" "ok",
  bucket "listEnv" "err.invalidEncoding_key",
  bucket "listEnv" "err.invalidEncoding_val",
  bucket "homeDir" "ok",
  bucket "homeDir" "err.notFound_unset",
  bucket "homeDir" "err.notFound_empty",
  bucket "homeDir" "err.invalidEncoding",
  bucket "splitSearchPath" "empty",
  bucket "splitSearchPath" "nonempty",
  bucket "splitSearchPath" "large_stack_safe",
  bucket "mapRawError" "invalidEncoding",
  bucket "mapRawError" "invalidArgument",
  bucket "mapRawError" "otherError",
  bucket "mapRawError" "userError"
]

private def largeSearchPath : String :=
  String.intercalate ":" (List.replicate 100000 "ab")

private def adversarialKeyBytes : Array ByteArray := #[
  ByteArray.empty,
  ByteArray.empty,
  "=".toUTF8,
  "A=B".toUTF8,
  "A=B=C".toUTF8,
  ByteArray.mk #[0x41, 0x00, 0x42],
  ByteArray.mk #[0x41, 0x00, 0x42],
  "A".toUTF8,
  "HOME".toUTF8,
  "HOME".toUTF8,
  "DUP".toUTF8,
  "EMPTY".toUTF8,
  "α".toUTF8,
  "🔑".toUTF8,
  ByteArray.mk #[0x80],
  ByteArray.mk #[0xff],
  ByteArray.mk #[0xc0, 0xaf],
  ByteArray.mk #[0xed, 0xa0, 0x80],
  ByteArray.mk #[0xe2, 0x82]
]

private def adversarialValBytes : Array ByteArray := #[
  ByteArray.empty,
  "=".toUTF8,
  "B=secret".toUTF8,
  "a=b=c".toUTF8,
  "/tmp/home".toUTF8,
  ByteArray.mk #[0x41, 0x00, 0x42],
  "α=🔑".toUTF8,
  ByteArray.mk #[0xff],
  ByteArray.mk #[0xff, 0xfe],
  ByteArray.mk #[0x80, 0xfe],
  ByteArray.mk #[0xed, 0xa0, 0x80]
]

private def adversarialQueryStrings : Array String := #[
  "",
  "=",
  "A=B",
  "A=B=C",
  String.ofList ['A', Char.ofNat 0, 'B'],
  "A",
  "HOME",
  "DUP",
  "EMPTY",
  "ABSENT",
  "α",
  "🔑"
]

private def warmupTrace : Array EnvFuzzOp := #[
  .clearEnv,
  .queryList,
  .queryHome,
  .queryGet "ABSENT",
  .queryGet "",
  .queryGet "A=B",
  .queryGet (String.ofList ['A', Char.ofNat 0, 'B']),
  .setEnv "A".toUTF8 "B=secret".toUTF8 true,
  .queryGet "A=B",
  .queryGet (String.ofList ['A', Char.ofNat 0, 'B']),
  .setEnv "A".toUTF8 "first".toUTF8 false,
  .setEnv "A".toUTF8 "second".toUTF8 true,
  .setEnv "".toUTF8 "x".toUTF8 true,
  .setEnv "K=1".toUTF8 "x".toUTF8 true,
  .setEnv (ByteArray.mk #[0x41, 0x00, 0x42]) "x".toUTF8 true,
  .setEnv "K".toUTF8 (ByteArray.mk #[0x41, 0x00, 0x42]) true,
  .setEnv "HOME".toUTF8 ByteArray.empty true,
  .queryHome,
  .setEnv "HOME".toUTF8 "/tmp/lean-home".toUTF8 true,
  .queryHome,
  .setEnv "HOME".toUTF8 (ByteArray.mk #[0xff, 0xfe]) true,
  .queryHome,
  .queryGet "HOME",
  .queryList,
  .unsetEnv "HOME".toUTF8,
  .unsetEnv "ABSENT_KEY".toUTF8,
  .unsetEnv "".toUTF8,
  .unsetEnv "BAD=KEY".toUTF8,
  .unsetEnv (ByteArray.mk #[0x41, 0x00, 0x42]),
  .rawTable #[] true #["HOME", "A=B"] #[],
  .rawTable #[] false #["HOME"] #[],
  .rawTable #[
    "NO_EQ".toUTF8,
    "=LEADING_EQ".toUTF8,
    ByteArray.mk #[0xff, 0xfe],
    ByteArray.mk #[0x3d, 0xff],
    "DUP=1".toUTF8,
    "DUP=2".toUTF8,
    "A=B=secret".toUTF8
  ] false #["DUP", "A=B", "A", "ABSENT"] #[
    .setEnv "DUP".toUTF8 "overwritten".toUTF8 true,
    .queryGet "DUP",
    .unsetEnv "DUP".toUTF8,
    .clearEnv,
    .queryList
  ],
  .rawTable #[ByteArray.mk #[0x80, 0x3d, 0x31]] false #["A"] #[],
  .rawTable #["BAD_VAL=".toUTF8 ++ ByteArray.mk #[0xff]] false #["BAD_VAL"] #[],
  .querySplitPath "",
  .querySplitPath ":::",
  .querySplitPath ":/a::/b:",
  .querySplitPath largeSearchPath,
  .queryMapRawErr (.invalidEncoding (some "K") ""),
  .queryMapRawErr (.invalidArgument (some "K") 22 ""),
  .queryMapRawErr (.otherError 12 ""),
  .queryMapRawErr (.userError "")
]

private def replaceNulBytes (bs : ByteArray) : ByteArray :=
  ByteArray.mk (bs.data.map fun b => if b == 0 then 0x41 else b)

private def sanitizeValidKeyBytes (bs : ByteArray) : ByteArray :=
  ByteArray.mk (bs.data.map fun b =>
    if b == 0 || b == 0x3D then UInt8.ofNat ('K'.toNat) else b)

private def largeValidKey4096 : String :=
  "BIG4096_" ++ String.ofList (List.replicate 4088 'K')

private def commonCollidingKeys : Array String := #[
  "HOME", "HOME", "DUP", "A", "K", "FOO", "BAR", "X", "Y", largeValidKey4096
]

private def genFastUtf8Bytes (r : Rng) (targetLen : Nat) : ByteArray × Rng :=
  let (hdr, r1) := r.nextRange 0 25
  let (mode, r2) := r1.nextNat 3
  let prefixBytes :=
    if mode == 0 then
      ("U" ++ String.singleton (Char.ofNat (65 + hdr)) ++ "_α🔑_").toUTF8
    else if mode == 1 then
      ("V" ++ String.singleton (Char.ofNat (65 + hdr)) ++ "_β_").toUTF8
    else
      ("W" ++ String.singleton (Char.ofNat (65 + hdr)) ++ "_").toUTF8
  if targetLen ≤ prefixBytes.size then
    (ByteArray.mk (Array.replicate targetLen (UInt8.ofNat (65 + hdr))), r2)
  else
    let rem := targetLen - prefixBytes.size
    (prefixBytes ++ ByteArray.mk (Array.replicate rem (UInt8.ofNat (65 + hdr))), r2)

private def genKeyBytes (r : Rng) : ByteArray × Rng :=
  let (pick, r1) := r.nextNat 100
  if pick < 35 then
    r1.choose adversarialKeyBytes "A".toUTF8
  else if pick < 70 then
    let (k, r2) := r1.choose commonCollidingKeys "DUP"
    (k.toUTF8, r2)
  else if pick < 80 then
    let (len, r2) := r1.nextRange 25 128
    genFastUtf8Bytes r2 len
  else if pick < 88 then
    let (isUtf8, r2) := r1.nextBool
    if isUtf8 then
      genFastUtf8Bytes r2 4096
    else
      let (rawBig, r3) := r2.nextBytes 4096
      (sanitizeValidKeyBytes rawBig, r3)
  else
    let (makeValid, r2) := r1.chance 3 4
    let (bs, r3) := r2.nextBytesRange 1 24
    (if makeValid then sanitizeValidKeyBytes bs else bs, r3)

private def genValBytes (r : Rng) : ByteArray × Rng :=
  let (pick, r1) := r.nextNat 100
  if pick < 28 then
    r1.choose adversarialValBytes ByteArray.empty
  else if pick < 50 then
    (ByteArray.empty, r1)
  else if pick < 58 then
    let (len, r2) := r1.nextRange 4 64
    let (bs, r3) := r2.nextBytes len
    let (pos, r4) := r3.nextNat len
    (bs.set! pos 0, r4)
  else if pick < 74 then
    let (len, r2) := r1.nextRange 1 64
    genFastUtf8Bytes r2 len
  else if pick < 90 then
    let (len, r2) := r1.nextRange 65 2048
    let (isUtf8, r3) := r2.chance 3 5
    if isUtf8 then
      genFastUtf8Bytes r3 len
    else
      let (bs, r4) := r3.nextBytes len
      (replaceNulBytes bs, r4)
  else
    let (isUtf8, r2) := r1.nextBool
    if isUtf8 then
      genFastUtf8Bytes r2 4096
    else
      let (bs, r3) := r2.nextBytes 4096
      (replaceNulBytes bs, r3)

private def genAsciiString (r : Rng) (minLen maxLen : Nat) : String × Rng := Id.run do
  let (len, r1) := r.nextRange minLen maxLen
  let mut cur := r1
  let mut cs := Array.mkEmpty len
  for _ in List.range len do
    let (chNat, nxt) := cur.nextRange 65 90
    cur := nxt
    cs := cs.push (Char.ofNat chNat)
  return (String.ofList cs.toList, cur)

private def utf8QueryTokens : Array String := #[
  "α", "β", "λ", "日本語", "🔑", "env", "PATH", "_", "0", "=", "\x00"
]

private def genValidUtf8String (r : Rng) (minToks maxToks : Nat) : String × Rng := Id.run do
  let (tokCount, r1) := r.nextRange minToks maxToks
  let mut cur := r1
  let mut s := ""
  for _ in List.range tokCount do
    let (tok, nxt) := cur.choose utf8QueryTokens "α"
    cur := nxt
    s := s ++ tok
  return (s, cur)

private def utf8ValueTokens : Array String := #[
  "α", "β", "λ", "日本語", "🔑", "env", "PATH", "_", "0", "="
]

private def genValidUtf8Bytes (r : Rng) (minLen maxLen : Nat) : ByteArray × Rng :=
  let (useAscii, r1) := r.chance 3 4
  if useAscii then
    let (s, r2) := genAsciiString r1 minLen maxLen
    (s.toUTF8, r2)
  else
    let (tokCount, r2) := r1.nextRange 1 6
    Id.run do
      let mut cur := r2
      let mut s := ""
      for _ in List.range tokCount do
        let (tok, nxt) := cur.choose utf8ValueTokens "α"
        cur := nxt
        s := s ++ tok
      return (s.toUTF8, cur)

private def genRawSlice (r : Rng) : ByteArray × Rng :=
  let (kind, r1) := r.nextNat 100
  if kind < 12 then
    r1.choose #[
      ByteArray.empty,
      "NO_EQ".toUTF8,
      "=".toUTF8,
      "=val".toUTF8,
      ByteArray.mk #[0xff, 0xfe],
      ByteArray.mk #[0x3d, 0xff]
    ] "NO_EQ".toUTF8
  else if kind < 28 then
    let (hPick, r2) := r1.nextNat 100
    if hPick < 40 then
      ("HOME=".toUTF8, r2)
    else if hPick < 70 then
      ("HOME=/tmp/home".toUTF8, r2)
    else
      ("HOME=".toUTF8 ++ ByteArray.mk #[0xff, 0xfe], r2)
  else if kind < 40 then
    let (kb0, r2) := genKeyBytes r1
    let kb := replaceNulBytes kb0
    let (vb0, r3) := genValBytes r2
    let vb := replaceNulBytes vb0
    (kb ++ ByteArray.mk #[0x3D] ++ vb, r3)
  else
    let (usePool, r2) := r1.chance 3 5
    let (kStr, r3) := if usePool then r2.choose commonCollidingKeys "DUP" else genAsciiString r2 1 16
    let (vBytes, r4) := genValidUtf8Bytes r3 0 48
    (kStr.toUTF8 ++ ByteArray.mk #[0x3D] ++ vBytes, r4)

private def genQueryString (r : Rng) : String × Rng :=
  let (pick, r1) := r.nextNat 100
  if pick < 45 then
    r1.choose adversarialQueryStrings "A"
  else if pick < 50 then
    (largeValidKey4096, r1)
  else if pick < 60 then
    let (len, r2) := r1.nextRange 25 128
    genAsciiString r2 len len
  else if pick < 80 then
    genValidUtf8String r1 1 8
  else if pick < 90 then
    let (len, r2) := r1.nextRange 0 128
    let (bs, r3) := r2.nextBytes len
    match String.fromUTF8? bs with
    | some s => (s, r3)
    | none => genValidUtf8String r3 1 5
  else
    genAsciiString r1 1 64

private def genSplitPathString (r : Rng) : String × Rng := Id.run do
  let (pick, r1) := r.nextNat 1000
  if pick ≥ 820 then
    return (largeSearchPath, r1)
  if pick < 150 then
    return r1.choose #["", ":::", ":/a::/b:", "/usr/bin:/bin", "a:b:c"] ""
  let (segCount, r2) := r1.nextRange 0 18
  let mut cur := r2
  let mut segs : List String := []
  for _ in List.range segCount do
    let (emptySeg, nxt1) := cur.chance 1 4
    if emptySeg then
      cur := nxt1
      segs := "" :: segs
    else
      let (seg, nxt2) := genAsciiString nxt1 1 16
      cur := nxt2
      segs := seg :: segs
  return (":".intercalate segs.reverse, cur)

private def genMapRawErr (r : Rng) : LeanSwe.EnvVars.Raw.EnvVarsRawError × Rng :=
  let (kind, r1) := r.nextNat 4
  let (hasKey, r2) := r1.nextBool
  let (keyStr, r3) := genAsciiString r2 0 16
  let key? := if hasKey then some keyStr else none
  let (useEmptyDetail, r4) := r3.nextBool
  let (detail, r5) := if useEmptyDetail then ("", r4) else genAsciiString r4 1 32
  let (errnoNat, r6) := r5.nextRange 1 130
  if kind == 0 then
    (.invalidEncoding key? detail, r6)
  else if kind == 1 then
    (.invalidArgument key? (UInt32.ofNat errnoNat) detail, r6)
  else if kind == 2 then
    (.otherError (UInt32.ofNat errnoNat) detail, r6)
  else
    (.userError detail, r6)

private def genRawPostOp (r : Rng) : RawPostOp × Rng :=
  let (pick, r1) := r.nextNat 100
  if pick < 32 then
    let (k, r2) := genKeyBytes r1
    let (v, r3) := genValBytes r2
    let (ovw, r4) := r3.nextBool
    (.setEnv k v ovw, r4)
  else if pick < 55 then
    let (k, r2) := genKeyBytes r1
    (.unsetEnv k, r2)
  else if pick < 65 then
    (.clearEnv, r1)
  else if pick < 80 then
    let (qk, r2) := genQueryString r1
    (.queryGet qk, r2)
  else if pick < 90 then
    (.queryList, r1)
  else
    (.queryHome, r1)

private def genEnvOp (r : Rng) : EnvFuzzOp × Rng :=
  let (pick, r1) := r.nextNat 100
  if pick < 26 then
    let (k, r2) := genKeyBytes r1
    let (v, r3) := genValBytes r2
    let (ovw, r4) := r3.nextBool
    (.setEnv k v ovw, r4)
  else if pick < 42 then
    let (k, r2) := genKeyBytes r1
    (.unsetEnv k, r2)
  else if pick < 44 then
    (.clearEnv, r1)
  else if pick < 60 then
    let (qk, r2) := genQueryString r1
    (.queryGet qk, r2)
  else if pick < 72 then
    (.queryList, r1)
  else if pick < 83 then
    (.queryHome, r1)
  else if pick < 90 then
    let (p, r2) := genSplitPathString r1
    (.querySplitPath p, r2)
  else if pick < 94 then
    let (raw, r2) := genMapRawErr r1
    (.queryMapRawErr raw, r2)
  else Id.run do
    let (emptyPick, r2) := r1.nextNat 100
    let (n, r3) := if emptyPick < 30 then (0, r2) else r2.nextRange 1 24
    let (useNull, r4) := if n == 0 then r3.nextBool else (false, r3)
    let mut cur := r4
    let mut slices := Array.mkEmpty n
    for _ in List.range n do
      let (sl, nxt) := genRawSlice cur
      cur := nxt
      slices := slices.push sl
    let (qCount, r5) := cur.nextRange 0 6
    let mut qs := Array.mkEmpty qCount
    let mut curQ := r5
    for _ in List.range qCount do
      let (q, nxtQ) := genQueryString curQ
      curQ := nxtQ
      qs := qs.push q
    let (pCount, r6) := curQ.nextRange 0 4
    let mut posts := Array.mkEmpty pCount
    let mut curP := r6
    for _ in List.range pCount do
      let (pOp, nxtP) := genRawPostOp curP
      curP := nxtP
      posts := posts.push pOp
    return (.rawTable slices useNull qs posts, curP)

private def mismatchKindTag (s : String) : String :=
  let head := (s.splitOn " ").headD s
  let parts := head.splitOn ":"
  if parts.length >= 3 then
    s!"{parts[0]!}:{parts[1]!}:{parts[2]!}"
  else
    head

private def collectTraceKeys (trace : Array EnvFuzzOp) (minBytes : Nat := 2) : List ByteArray := Id.run do
  let mut keys : Array ByteArray := #[]
  let pushKey (k : ByteArray) (arr : Array ByteArray) : Array ByteArray :=
    if k.size ≥ minBytes && !arr.contains k then arr.push k else arr
  for op in trace do
    match op with
    | .setEnv k _ _ => keys := pushKey k keys
    | .unsetEnv k => keys := pushKey k keys
    | .queryGet k => keys := pushKey k.toUTF8 keys
    | .rawTable es _ qs post =>
      for sl in es do
        if let some (k, _) := splitFirstEqBytesModel sl then
          keys := pushKey k keys
      for q in qs do
        keys := pushKey q.toUTF8 keys
      for p in post do
        match p with
        | .setEnv k _ _ => keys := pushKey k keys
        | .unsetEnv k => keys := pushKey k keys
        | .queryGet k => keys := pushKey k.toUTF8 keys
        | _ => pure ()
    | _ => pure ()
  return keys.toList

private def replaceKeyInRawSlice (oldK newK sl : ByteArray) : ByteArray :=
  match splitFirstEqBytesModel sl with
  | some (k, v) => if k == oldK then newK ++ ByteArray.mk #[0x3D] ++ v else sl
  | none => sl

private def replaceKeyInPostOp (oldK newK : ByteArray) (oldStr? newStr? : Option String) : RawPostOp → RawPostOp
  | .setEnv k v ovw => .setEnv (if k == oldK then newK else k) v ovw
  | .unsetEnv k => .unsetEnv (if k == oldK then newK else k)
  | .queryGet k =>
    match oldStr?, newStr? with
    | some os, some ns => if k == os then .queryGet ns else .queryGet k
    | _, _ => .queryGet k
  | op => op

private def replaceKeyInOp (oldK newK : ByteArray) (oldStr? newStr? : Option String) : EnvFuzzOp → EnvFuzzOp
  | .setEnv k v ovw => .setEnv (if k == oldK then newK else k) v ovw
  | .unsetEnv k => .unsetEnv (if k == oldK then newK else k)
  | .queryGet k =>
    match oldStr?, newStr? with
    | some os, some ns => if k == os then .queryGet ns else .queryGet k
    | _, _ => .queryGet k
  | .rawTable es useNull qs post =>
    let qs' := match oldStr?, newStr? with
      | some os, some ns => qs.map fun q => if q == os then ns else q
      | _, _ => qs
    .rawTable
      (es.map (replaceKeyInRawSlice oldK newK))
      useNull
      qs'
      (post.map (replaceKeyInPostOp oldK newK oldStr? newStr?))
  | op => op

private def shrinkCoupledKeys (fails : Array EnvFuzzOp → IO Bool) (trace : Array EnvFuzzOp) : IO (Array EnvFuzzOp) := do
  let mut cur := trace
  let keys := collectTraceKeys cur 2
  let homeKey := "HOME".toUTF8
  let asciiPool := ["A", "B", "C", "D", "E", "F", "G", "H"].map String.toUTF8
  for oldK in keys do
    if oldK == homeKey then
      continue
    let mut activeK := oldK
    let mut improved := true
    while improved do
      improved := false
      let existing := collectTraceKeys cur 1
      let oldStr? := String.fromUTF8? activeK
      let strCands : List ByteArray := match oldStr? with
        | some os => asciiPool ++ (shrinkString os).map String.toUTF8
        | none => []
      let rawCands := strCands ++ shrinkBytes activeK
      let cands := rawCands.eraseDups.filter fun k' =>
        !k'.isEmpty && k'.size < activeK.size && !k'.data.any (fun b => b == 0x3D || b == 0) &&
        k' != homeKey && !existing.contains k' &&
        (oldStr?.isNone || (String.fromUTF8? k').isSome)
      for newK in cands do
        let cand := cur.map (replaceKeyInOp activeK newK oldStr? (String.fromUTF8? newK))
        if cand != cur && (← fails cand) then
          cur := cand
          activeK := newK
          improved := true
          break
  return cur

private def rawPostToEnvOp : RawPostOp → EnvFuzzOp
  | .setEnv k v ovw => .setEnv k v ovw
  | .unsetEnv k => .unsetEnv k
  | .clearEnv => .clearEnv
  | .queryGet k => .queryGet k
  | .queryList => .queryList
  | .queryHome => .queryHome

private def shrinkUnwrapRawTables (fails : Array EnvFuzzOp → IO Bool) (trace : Array EnvFuzzOp) : IO (Array EnvFuzzOp) := do
  let mut cur := trace
  let mut i := 0
  while i < cur.size do
    match cur[i]? with
    | some (.rawTable es useNull qs post) =>
      if es.isEmpty && useNull && qs.isEmpty && !post.isEmpty then
        let flat := #[.clearEnv] ++ post.map rawPostToEnvOp ++ #[.clearEnv]
        let cand := cur.extract 0 i ++ flat ++ cur.extract (i + 1) cur.size
        if ← fails cand then
          cur := cand
          i := 0
          continue
      i := i + 1
    | _ => i := i + 1
  return cur

private def shrinkEnvTraceWith (execFn : Array EnvFuzzOp → IO (Except String CoverageTracker))
    (trace : Array EnvFuzzOp) (origMsg : String) : IO (Array EnvFuzzOp × String) := do
  let targetTag := mismatchKindTag origMsg
  let lastErrRef ← IO.mkRef origMsg
  let fails (cand : Array EnvFuzzOp) : IO Bool := do
    match ← execFn cand with
    | .ok _ => return false
    | .error errMsg =>
      if mismatchKindTag errMsg == targetTag then
        lastErrRef.set errMsg
        return true
      return false
  let mut cur ← shrinkTrace fails trace
  for _ in List.range 4 do
    let s0 ← shrinkUnwrapRawTables fails cur
    let s1 ← shrinkCoupledKeys fails s0
    let s2 ← shrinkElements shrinkOp fails s1
    let s3 ← shrinkTrace fails s2
    if s3 == cur then
      break
    cur := s3
  let finalMsg ← lastErrRef.get
  return (cur, finalMsg)

private def runTraceAndShrink (trace : Array EnvFuzzOp) : IO CoverageTracker := do
  match ← execTraceWithOracle none none trace with
  | .ok tr => return tr
  | .error msg =>
    let (shrunk, finalMsg) ← shrinkEnvTraceWith (execTraceWithOracle none none) trace msg
    let labels := shrunk.toList.map reprEnvFuzzOp
    throw (IO.userError s!"ENVVARS_FUZZ_MISMATCH: {finalMsg}; shrunk({shrunk.size})=[{String.intercalate "; " labels}]")

private def runExecveSmokeCheck : IO Unit := do
  let out ← IO.Process.output {
    cmd := "/usr/bin/env"
    args := #["-i", "FOO=bar=baz", "EMPTY=", "/bin/sh", "-c", "printf '%s|%s' \"$FOO\" \"$EMPTY\""]
  }
  if out.exitCode != 0 || out.stdout != "bar=baz|" then
    throw (IO.userError s!"ENVVARS_EXECVE_SMOKE_FAILED rc={out.exitCode} out={repr out.stdout} err={repr out.stderr}")
  rawFuzzBegin 2
  let mut setErr? : Option String := none
  let _ ← try
    let r0 ← rawFuzzSet 0 "FOO=bar=baz".toUTF8
    let r1 ← rawFuzzSet 1 "EMPTY=".toUTF8
    if r0 != 0 || r1 != 0 then
      setErr? := some s!"rawFuzzSet failed r0={r0} r1={r1}"
    else
      rawFuzzInstall 0
      let rawLst ← LeanSwe.EnvVars.Raw.listEnv
      let rawFoo ← LeanSwe.EnvVars.Raw.getEnv "FOO"
      let hiEmpty ← LeanSwe.EnvVars.getEnv "EMPTY"
      if !exceptEq rawFoo (.ok (some "bar=baz")) || !exceptEq hiEmpty (.ok (some "")) then
        setErr? := some s!"execve-shim raw/high mismatch rawFoo={repr rawFoo} hiEmpty={repr hiEmpty}"
      if let .error e := rawLst then
        setErr? := some s!"execve-shim raw listEnv failed: {repr e}"
  finally
    rawFuzzEnd
  if let some errMsg := setErr? then
    throw (IO.userError s!"ENVVARS_EXECVE_SMOKE_FAILED: {errMsg}")

private def smokeRandomBuckets : Array CoverageBucket := #[
  bucket "setenv" "ok.insert",
  bucket "unsetenv" "ok.absent",
  bucket "raw_getEnv" "ok.none_unset",
  bucket "getEnv" "ok.none",
  bucket "raw_listEnv" "ok.entries",
  bucket "listEnv" "ok",
  bucket "homeDir" "err.notFound_unset",
  bucket "splitSearchPath" "nonempty"
]

private def runEnvVarsLoop (steps : Nat) (seedVal : UInt64) (isSmoke : Bool) : IO Unit := do
  withRestoredHostEnviron do
    if isSmoke then
      runExecveSmokeCheck
    let smokeTr ← runTraceAndShrink warmupTrace
    if isSmoke then
      assertCoverage "envvars-warmup" smokeTr requiredBuckets
    let mut randTr := CoverageTracker.empty
    let mut rng := Rng.seed seedVal
    let mut done := 0
    while done < steps do
      let (epLenRaw, rEp) := rng.nextRange 32 96
      rng := rEp
      let epLen := min epLenRaw (steps - done)
      let mut trace := Array.mkEmpty epLen
      for _ in List.range epLen do
        let (op, nxt) := genEnvOp rng
        rng := nxt
        trace := trace.push op
      let epTr ← runTraceAndShrink trace
      randTr := randTr.merge epTr
      done := done + epLen
    if isSmoke then
      assertCoverage "envvars-smoke-random" randTr smokeRandomBuckets
    let reportTr := if isSmoke then smokeTr.merge randTr else randTr
    if isSmoke || steps ≥ 5000 then
      assertCoverage "envvars" reportTr requiredBuckets
    IO.println (reportTr.formatReport "envvars")
    IO.println s!"FUZZ_SUMMARY suite=envvars steps={steps} seed={seedVal}"

/-- Verify trace, element, interior-chunk, O(log N) >N/2, rawTable, and pinned-class shrinking. -/
def runSelfTestShrink (seedVal : UInt64) : IO Unit := do
  withRestoredHostEnviron do
    let mut rng := Rng.seed (seedVal ^^^ 0x454e565f5348524b)
    let mut trace := Array.mkEmpty 24
    for _ in List.range 22 do
      let (op, nxt) := genEnvOp rng
      rng := nxt
      trace := trace.push op
    let (idxA, r1) := rng.nextRange 0 10
    let (idxB, _) := r1.nextRange 11 21
    let middle := (trace.extract idxA idxB).filter fun
      | .clearEnv => false
      | .rawTable _ _ _ _ => false
      | .unsetEnv k => k != "FAULT_K".toUTF8
      | .setEnv k _ _ => k != "FAULT_K".toUTF8
      | _ => true
    let bigFaultVal := ByteArray.mk (Array.replicate 80 0x41)
    let injected :=
      (trace.extract 0 idxA).push (.setEnv "FAULT_K".toUTF8 bigFaultVal true) ++
      middle.push (.queryGet "FAULT_K") ++
      trace.extract idxB trace.size
    let buggyGet (_ : EnvironState) (k : String) : IO (Except EnvVarsError (Option String)) := do
      let actual ← LeanSwe.EnvVars.getEnv k
      match actual with
      | .ok (some s) =>
        if k == "FAULT_K" && s.length ≥ 17 then
          return .ok (some "INJECTED_BUG")
        return actual
      | _ => return actual
    let fails (cand : Array EnvFuzzOp) : IO Bool := do
      match ← execTraceWithOracle none (some buggyGet) cand with
      | .ok _ => return false
      | .error _ => return true
    let shrunk0 ← match ← verifyShrinker fails injected 2 with
      | .error msg => throw (IO.userError s!"ENVVARS_SHRINK_SELFTEST_FAILED: {msg}")
      | .ok s0 => pure s0
    let shrunk ← shrinkElements shrinkOp fails shrunk0
    let shrunkValSize := match shrunk[0]? with
      | some (.setEnv _ v _) => v.size
      | _ => 999
    if shrunkValSize ≥ 80 || shrunkValSize < 17 then
      throw (IO.userError s!"ENVVARS_SHRINK_SELFTEST_FAILED: expected shrunk val size in [17, 79], got {shrunkValSize}")

    let rawFaultTrace : Array EnvFuzzOp := #[
      .rawTable #[
        "PAD0=a".toUTF8,
        "PAD1=b".toUTF8,
        "HIT=payload_long_value".toUTF8,
        "PAD2=c".toUTF8
      ] false #["Q0", "HIT", "Q2"] #[.queryGet "EXTRA"]
    ]
    let rawPred (cand : Array EnvFuzzOp) : IO Bool := do
      match cand.toList with
      | [.rawTable es _ qs _] =>
        let hasHitSlice := es.any (fun e => e == "HIT=p".toUTF8 || (e.size ≥ 5 && e.extract 0 4 == "HIT=".toUTF8))
        let hasHitQ := qs.any (· == "HIT")
        if hasHitSlice && hasHitQ then
          match ← execTraceWithOracle none none cand with
          | .ok _ => return true
          | .error _ => return false
        return false
      | _ => return false
    let rawShrunk ← shrinkElements shrinkOp rawPred rawFaultTrace
    match rawShrunk.toList with
    | [.rawTable es _ qs post] =>
      if es != #["HIT=a".toUTF8] || qs != #["HIT"] || !post.isEmpty then
        throw (IO.userError s!"ENVVARS_RAW_TABLE_SHRINK_FAILED: expected [HIT=a] [HIT] [], got es={es.map (fun b => String.fromUTF8? b |>.getD "<nonutf8>")} qs={qs} post={post.size}")
    | _ =>
      throw (IO.userError s!"ENVVARS_RAW_TABLE_SHRINK_FAILED: unexpected trace len={rawShrunk.size}")

    let bigBadKeySlice := ByteArray.mk (Array.replicate 4096 0x80) ++ "=val".toUTF8
    let keyShrinkTrace : Array EnvFuzzOp := #[
      .rawTable #["PAD=1".toUTF8, bigBadKeySlice] false #["Q0", "Q1"] #[]
    ]
    let keyPred (cand : Array EnvFuzzOp) : IO Bool := do
      match cand.toList with
      | [.rawTable es _ _ _] =>
        let hasBadKey := es.any fun sl =>
          match splitFirstEqBytesModel sl with
          | some (k, _) => !k.isEmpty && (String.fromUTF8? k).isNone
          | none => false
        if hasBadKey then
          match ← execTraceWithOracle none none cand with
          | .ok _ => return true
          | .error _ => return false
        return false
      | _ => return false
    let keyShrunk ← shrinkElements shrinkOp keyPred keyShrinkTrace
    let shrunkSliceSize := match keyShrunk.toList with
      | [.rawTable es _ qs post] =>
        if es.size == 1 && qs.isEmpty && post.isEmpty then es[0]!.size else 9999
      | _ => 9999
    if shrunkSliceSize > 2 then
      throw (IO.userError s!"ENVVARS_RAW_KEY_SHRINK_FAILED: expected slice size <= 2, got {shrunkSliceSize}")

    let nonPow2Val := ByteArray.mk (Array.replicate 4096 0x41)
    let nonPow2Trace : Array EnvFuzzOp := #[.setEnv "NP2".toUTF8 nonPow2Val true]
    let np2TrialsRef ← IO.mkRef 0
    let np2Pred (cand : Array EnvFuzzOp) : IO Bool := do
      np2TrialsRef.modify (· + 1)
      match cand.toList with
      | [.setEnv k v _] => return k == "NP2".toUTF8 && v.size ≥ 2100
      | _ => return false
    let np2Shrunk ← shrinkElements shrinkOp np2Pred nonPow2Trace
    let np2Trials ← np2TrialsRef.get
    if np2Trials ≥ 300 then
      throw (IO.userError s!"ENVVARS_NP2_SHRINK_FAILED: expected < 300 trials got {np2Trials}")
    let np2Size := match np2Shrunk.toList with
      | [.setEnv _ v _] => v.size
      | _ => 0
    if np2Size != 2100 then
      throw (IO.userError s!"ENVVARS_NP2_SHRINK_FAILED: expected 2100 got {np2Size}")

    let interiorKey := "A" ++ String.ofList (List.replicate 4094 'x') ++ "Z"
    let interiorTrace : Array EnvFuzzOp := #[.queryGet interiorKey]
    let interiorPred (cand : Array EnvFuzzOp) : IO Bool := do
      match cand.toList with
      | [.queryGet s] => return s.startsWith "A" && s.endsWith "Z" && s.length ≥ 2
      | _ => return false
    let interiorShrunk ← shrinkElements shrinkOp interiorPred interiorTrace
    let interiorLen := match interiorShrunk.toList with
      | [.queryGet s] => s.length
      | _ => 9999
    if interiorLen != 2 then
      throw (IO.userError s!"ENVVARS_INTERIOR_SHRINK_FAILED: expected \"AZ\" len=2 got len={interiorLen}")

    let pinnedSetupTrace : Array EnvFuzzOp := #[
      .setEnv "K".toUTF8 "V".toUTF8 true,
      .setEnv "H".toUTF8 ByteArray.empty true,
      .queryHome
    ]
    let pinnedHook (cand : Array EnvFuzzOp) : IO (Except String CoverageTracker) := do
      let customGet (_st : EnvironState) (k : String) : IO (Except EnvVarsError (Option String)) :=
        LeanSwe.EnvVars.getEnv k
      match ← execTraceWithOracle none (some customGet) cand with
      | .error m => return .error m
      | .ok tr =>
        let hasSetH := cand.any fun
          | .setEnv k _ _ => k == "H".toUTF8
          | _ => false
        if cand.contains .queryHome then
          if hasSetH then
            return .error "HOMEDIR_MISMATCH:err_notFound:ok: synthetic pinned setup fault"
          return .error "HOMEDIR_MISMATCH:ok:err_invalidEncoding: decoy outcome slippage"
        return .ok tr
    let (pinnedShrunk, finalPinnedErr) ← shrinkEnvTraceWith pinnedHook pinnedSetupTrace
      "HOMEDIR_MISMATCH:err_notFound:ok: synthetic pinned setup fault"
    if mismatchKindTag finalPinnedErr != "HOMEDIR_MISMATCH:err_notFound:ok" then
      throw (IO.userError s!"ENVVARS_PINNED_SHRINK_FAILED: slipped to {finalPinnedErr}")
    let pinnedOk := match pinnedShrunk.toList with
      | [.setEnv k v _, .queryHome] => k == "H".toUTF8 && v.isEmpty
      | _ => false
    if !pinnedOk then
      throw (IO.userError s!"ENVVARS_PINNED_SHRINK_FAILED: expected [setEnv H empty _, queryHome] got size={pinnedShrunk.size}")

    let coupledTrace : Array EnvFuzzOp := #[
      .setEnv largeValidKey4096.toUTF8 "V".toUTF8 true,
      .queryGet largeValidKey4096
    ]
    let coupledHook (cand : Array EnvFuzzOp) : IO (Except String CoverageTracker) := do
      let customGet (st : EnvironState) (k : String) : IO (Except EnvVarsError (Option String)) := do
        if k.length ≥ 1 then
          match st.entries.findSome? (fun e => match splitFirstEqBytesModel e with
            | some (kb, _) => if kb == k.toUTF8 then some () else none
            | none => none) with
          | some () => return .ok (some "DECOY_DIFF")
          | none => LeanSwe.EnvVars.getEnv k
        else
          LeanSwe.EnvVars.getEnv k
      execTraceWithOracle none (some customGet) cand
    let (coupledShrunk, _) ← shrinkEnvTraceWith coupledHook coupledTrace
      "GET_MISMATCH:ok_some:ok_some: coupled 4096B key mismatch"
    let coupledLens := match coupledShrunk.toList with
      | [.setEnv k v _, .queryGet qk] => (k.size, v.size, qk.length)
      | _ => (9999, 9999, 9999)
    if coupledLens.1 > 2 || coupledLens.2.1 != 0 || coupledLens.2.2 > 2 then
      throw (IO.userError s!"ENVVARS_COUPLED_KEY_SHRINK_FAILED: expected <= (2,0,2) got {coupledLens}")

    let postShrinkTrace : Array EnvFuzzOp := #[
      .rawTable #[] true #[] #[
        .setEnv "POST_K".toUTF8 (ByteArray.mk (Array.replicate 80 0x50)) true,
        .queryGet "POST_K"
      ]
    ]
    let postPred (cand : Array EnvFuzzOp) : IO Bool := do
      let okMatch := cand.any fun
        | .rawTable _ _ _ post =>
          post.any (fun | .setEnv k v _ => k == "POST_K".toUTF8 && v.size ≥ 12 | _ => false) &&
          post.any (fun | .queryGet "POST_K" => true | _ => false)
        | .setEnv k v _ => k == "POST_K".toUTF8 && v.size ≥ 12
        | _ => false
      if okMatch && cand.any (fun | .queryGet "POST_K" => true | .rawTable _ _ _ _ => true | _ => false) then
        match ← execTraceWithOracle none none cand with
        | .ok _ => return true
        | .error _ => return false
      return false
    let (postShrunk, _) ← shrinkEnvTraceWith (fun c => do
      if ← postPred c then return .error "POST_SHRINK:ok:ok:hit" else return .ok CoverageTracker.empty)
      postShrinkTrace "POST_SHRINK:ok:ok:hit"
    let postValLen := match postShrunk.toList with
      | [_, .setEnv _ v _, .queryGet _] => v.size
      | [.setEnv _ v _, .queryGet _] => v.size
      | [.rawTable _ _ _ post] =>
        post.foldl (fun acc op => match op with | .setEnv _ v _ => v.size | _ => acc) 999
      | _ => 999
    if postValLen != 12 then
      throw (IO.userError s!"ENVVARS_POST_SHRINK_FAILED: expected val len=12 got {postValLen}")

    let eqDropTrace : Array EnvFuzzOp := #[.rawTable #["KEY=val".toUTF8] false #[] #[]]
    let eqDropPred (cand : Array EnvFuzzOp) : IO Bool := do
      match cand.toList with
      | [.rawTable es false _ _] =>
        if es.size == 1 then
          match ← execTraceWithOracle none none cand with
          | .ok _ => return true
          | .error _ => return false
        return false
      | _ => return false
    let eqShrunk ← shrinkElements shrinkOp eqDropPred eqDropTrace
    let eqShrunkSize := match eqShrunk.toList with
      | [.rawTable es _ _ _] => if es.size == 1 then es[0]!.size else 999
      | _ => 999
    if eqShrunkSize != 0 then
      throw (IO.userError s!"ENVVARS_RAW_SLICE_EQ_SHRINK_FAILED: expected empty slice size 0 got {eqShrunkSize}")

    let utf8Key := "🔑🔑🔑"
    let utf8Trace : Array EnvFuzzOp := #[
      .setEnv utf8Key.toUTF8 "V".toUTF8 true,
      .queryGet utf8Key
    ]
    let utf8Hook (cand : Array EnvFuzzOp) : IO (Except String CoverageTracker) := do
      let customGet (st : EnvironState) (k : String) : IO (Except EnvVarsError (Option String)) := do
        match st.entries.findSome? (fun e => match splitFirstEqBytesModel e with
          | some (kb, _) => if kb == k.toUTF8 then some () else none
          | none => none) with
        | some () => return .error { kind := .invalidKey, key := some k, errnoCode := none, message := "decoy:utf8" }
        | none => LeanSwe.EnvVars.getEnv k
      execTraceWithOracle none (some customGet) cand
    let (utf8Shrunk, _) ← shrinkEnvTraceWith utf8Hook utf8Trace "GET_MISMATCH:ok_some:err_invalidKey:"
    let utf8Lens := match utf8Shrunk.toList with
      | [.setEnv k v _, .queryGet qk] => (k.size, v.size, qk.length)
      | _ => (9999, 9999, 9999)
    if utf8Lens != (1, 0, 1) then
      throw (IO.userError s!"ENVVARS_UTF8_COUPLED_SHRINK_FAILED: expected (1,0,1) got {utf8Lens}")

    let homeFooTrace : Array EnvFuzzOp := #[
      .setEnv "HOME_FOO".toUTF8 "X".toUTF8 true,
      .queryGet "HOME_FOO"
    ]
    let (homeFooShrunk, _) ← shrinkEnvTraceWith utf8Hook homeFooTrace "GET_MISMATCH:ok_some:err_invalidKey:"
    let homeFooOk := match homeFooShrunk.toList with
      | [.setEnv k _ _, .queryGet qk] => k != "HOME".toUTF8 && qk != "HOME" && k.size == 1 && qk.length == 1
      | _ => false
    if !homeFooOk then
      throw (IO.userError "ENVVARS_HOME_COLLISION_SHRINK_FAILED")

    let mapErrLong : EnvVarsRawError := .userError "LONG_DETAIL_A:B:C"
    let mapErrShort : EnvVarsRawError := .userError ""
    let envErrSample : EnvVarsError := { kind := .ioError, key := some "K", errnoCode := some 1, message := "m:x:y" }
    let mt1 := mismatchKindTag s!"MAP_RAW_ERR_MISMATCH:userError:diff: raw={repr mapErrLong} m={repr envErrSample}"
    let mt2 := mismatchKindTag s!"MAP_RAW_ERR_MISMATCH:userError:diff: raw={repr mapErrShort} m={repr envErrSample}"
    if mt1 != mt2 || mt1 != "MAP_RAW_ERR_MISMATCH:userError:diff" then
      throw (IO.userError s!"ENVVARS_MAP_RAW_PIN_FAILED: mt1={repr mt1} mt2={repr mt2}")
    let st1 := mismatchKindTag "SPLIT_PATH_MISMATCH:diff:diff: len=100 model=#[\"a:b:c:d\"] actual=#[]"
    let st2 := mismatchKindTag "SPLIT_PATH_MISMATCH:diff:diff: len=2 model=#[\"a\"] actual=#[]"
    if st1 != st2 || st1 != "SPLIT_PATH_MISMATCH:diff:diff" then
      throw (IO.userError s!"ENVVARS_SPLIT_PIN_FAILED: st1={repr st1} st2={repr st2}")

    let alpha31 := String.ofList (List.replicate 31 'α')
    let utf8ValTrace : Array EnvFuzzOp := #[.setEnv "HOME".toUTF8 alpha31.toUTF8 true]
    let (utf8ValShrunk, _) ← shrinkEnvTraceWith (fun cand => do
      match cand.toList with
      | [.setEnv k v true] =>
        if k == "HOME".toUTF8 && !v.isEmpty && (String.fromUTF8? v).isSome then
          return .error "HOME_VAL_TEST:a:b:hit"
        return .ok CoverageTracker.empty
      | _ => return .ok CoverageTracker.empty) utf8ValTrace "HOME_VAL_TEST:a:b:hit"
    let utf8ValSize := match utf8ValShrunk.toList with
      | [.setEnv _ v _] => v.size
      | _ => 999
    if utf8ValSize > 1 then
      throw (IO.userError s!"ENVVARS_UTF8_VAL_SHRINK_FAILED: expected <= 1 got {utf8ValSize}")

    let idx2EnvTrace : Array EnvFuzzOp := #[.queryGet "abXdefg"]
    let (idx2EnvShrunk, _) ← shrinkEnvTraceWith (fun cand => do
      match cand.toList with
      | [.queryGet k] =>
        if k.startsWith "ab" && k.endsWith "defg" then
          return .error "IDX2_TEST:a:b:hit"
        return .ok CoverageTracker.empty
      | _ => return .ok CoverageTracker.empty) idx2EnvTrace "IDX2_TEST:a:b:hit"
    match idx2EnvShrunk.toList with
    | [.queryGet "abdefg"] => pure ()
    | other => throw (IO.userError s!"ENVVARS_IDX2_SHRINK_FAILED: got len={other.length}")

    let k3Trace : Array EnvFuzzOp := #[
      .setEnv "A".toUTF8 "1".toUTF8 true,
      .setEnv "B".toUTF8 "2".toUTF8 true,
      .setEnv "🔑🔑🔑".toUTF8 "3".toUTF8 true,
      .queryGet "🔑🔑🔑"
    ]
    let k3Hook (cand : Array EnvFuzzOp) : IO (Except String CoverageTracker) := do
      let customGet (st : EnvironState) (k : String) : IO (Except EnvVarsError (Option String)) := do
        if k != "A" && k != "B" then
          match st.entries.findSome? (fun e => match splitFirstEqBytesModel e with
            | some (kb, _) => if kb == k.toUTF8 then some () else none
            | none => none) with
          | some () => return .error { kind := .invalidKey, key := some k, errnoCode := none, message := "decoy:k3" }
          | none => LeanSwe.EnvVars.getEnv k
        else LeanSwe.EnvVars.getEnv k
      execTraceWithOracle none (some customGet) cand
    let (k3Shrunk, _) ← shrinkEnvTraceWith k3Hook k3Trace "GET_MISMATCH:ok_some:err_invalidKey:"
    let k3Ok := match k3Shrunk.toList with
      | [.setEnv k _ _, .queryGet qk] => k.size == 1 && qk.length == 1
      | _ => false
    if !k3Ok then
      throw (IO.userError s!"ENVVARS_3KEY_COLLISION_SHRINK_FAILED: got size={k3Shrunk.size}")

    for oddN in [7, 15, 31, 63] do
      let oddStr := "AB" ++ String.ofList (List.replicate (oddN - 4) 'x') ++ "YZ"
      let oddShrunk ← shrinkElements shrinkOp (fun cand => do
        match cand.toList with
        | [.queryGet s] =>
          return s.startsWith "AB" && s.endsWith "YZ" && s.length ≥ 5 && s.length % 2 == 1
        | _ => return false) #[.queryGet oddStr]
      let oddLen := match oddShrunk.toList with | [.queryGet s] => s.length | _ => 999
      if oddLen != 5 then
        throw (IO.userError s!"ENVVARS_ODD_SHRINK_FAILED: n={oddN} got len={oddLen}")

    IO.println s!"ENVVARS_SHRINK_SELFTEST_OK: original={injected.size} shrunk={shrunk.size} val_size={shrunkValSize} raw_table_shrunk=1x1 bad_key_slice={shrunkSliceSize} np2_trials={np2Trials} interior_len={interiorLen} coupled={coupledLens}"

/-- Differential fuzzing suite for `LeanSwe.EnvVars` and `LeanSwe.EnvVars.Raw` over glibc `setenv`/`unsetenv`/`clearenv`/`environ`. -/
def suite : FuzzSuite := {
  name := "envvars"
  description := "Stateful POSIX setenv/unsetenv/clearenv and unrestricted raw environ differential fuzzer"
  runSmoke := fun cfg =>
    let smokeSteps := min cfg.steps 400
    runEnvVarsLoop (max 250 smokeSteps) cfg.seed true
  runFuzz := fun cfg =>
    runEnvVarsLoop cfg.steps cfg.seed false
  selfTestShrink := runSelfTestShrink
}

end Fuzz.EnvVars