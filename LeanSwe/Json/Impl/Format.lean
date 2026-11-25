import Lean.Data.Json.Basic
import LeanSwe.Json.Types

namespace LeanSwe.Json.Internal

/-- Return `msg` if non-empty, or `fallback` otherwise. -/
def ensureNonEmpty (fallback msg : String) : String :=
  if msg == "" then fallback else msg

/-- Tail-recursive helper joining path segments with `"."`. -/
def joinSegmentsAux (acc : String) : List String → String
  | [] => acc
  | k :: rest => joinSegmentsAux (acc ++ "." ++ k) rest

/-- Join path segments with `"."`. -/
def joinSegments : List String → String
  | [] => ""
  | k :: rest => joinSegmentsAux k rest

/-- Format a reversed path prefix as an optional dot-separated field path. -/
def joinPath (revPrefix : List String) : Option String :=
  if revPrefix.isEmpty then none else some (joinSegments revPrefix.reverse)

/-- Tail-recursive helper counting base-10 digits of a natural number. -/
def countDigitsAux (n digits : Nat) : Nat :=
  if h : n ≤ 9 then digits
  else
    have : n / 10 < n := Nat.div_lt_self (by omega) (by decide)
    countDigitsAux (n / 10) (digits + 1)
termination_by n

/-- Count base-10 digits of `n` (`countDigits 0 = 1`). -/
def countDigits (n : Nat) : Nat :=
  countDigitsAux n 1

/-- Strip trailing `'0'` characters from a decimal fraction character list. -/
def dropTrailingZeroChars (cs : List Char) : List Char :=
  (cs.reverse.dropWhile (· == '0')).reverse

/-- Format `k` fractional decimal digits of `rem < 10^k` with trailing `'0'`s stripped. -/
def formatFracStr (k rem : Nat) : String :=
  let raw := Nat.toDigits 10 rem
  String.ofList (dropTrailingZeroChars (List.replicate (k - raw.length) '0' ++ raw))

/-- Format a `Lean.JsonNumber` as an RFC 8259 number string using total arithmetic. -/
def jsonNumberToString : Lean.JsonNumber → String
  | ⟨0, _⟩ => "0"
  | ⟨m, 0⟩ => (if m < 0 then "-" else "") ++ m.natAbs.repr
  | ⟨m, e⟩ =>
    let sign := if m < 0 then "-" else ""
    let mAbs := m.natAbs
    let exp : Int := 9 + countDigits mAbs - (e : Int)
    let exp := if exp < 0 then exp else 0
    let k := e - exp.natAbs
    let e' := 10 ^ k
    let left := (mAbs / e').repr
    let rem := mAbs % e'
    if rem == 0 && exp == 0 then sign ++ left
    else
      let right := formatFracStr k rem
      let expStr := if exp == 0 then "" else "e-" ++ exp.natAbs.repr
      sign ++ left ++ "." ++ right ++ expStr

/-- Format a nibble `n < 16` as a lowercase hexadecimal `Char`. -/
def hexDigitLower (n : Nat) : Char :=
  if n < 10 then Char.ofNat (0x30 + n) else Char.ofNat (0x61 + (n - 10))

/-- Escape a single character into its RFC 8259 JSON string character representation. -/
def escapeCharChars (c : Char) : List Char :=
  if c == '"' then ['\\', '"']
  else if c == '\\' then ['\\', '\\']
  else if c == '\n' then ['\\', 'n']
  else if c == '\r' then ['\\', 'r']
  else if 0x0020 ≤ c.toNat then [c]
  else
    let n := c.toNat
    ['\\', 'u', hexDigitLower (n / 4096), hexDigitLower ((n % 4096) / 256),
      hexDigitLower ((n % 256) / 16), hexDigitLower (n % 16)]

/-- Render `s` as a quoted JSON string literal, appending onto `acc`. -/
def renderString (s : String) (acc : String := "") : String :=
  acc ++ "\"" ++ String.ofList (s.toList.flatMap escapeCharChars) ++ "\""

mutual
  /-- Structural weight of a `Lean.Json` value for total serialization. -/
  def jsonWeight : Lean.Json → Nat
    | .null | .bool _ | .num _ | .str _ => 2
    | .arr elems => 2 + arrWeight elems.toList
    | .obj kvs => 3 + treeWeight kvs.inner.inner
  termination_by j => sizeOf j
  decreasing_by
    · cases elems; simp; omega
    · cases kvs with | mk inner => cases inner; simp; omega

  /-- Structural weight of a JSON array element list. -/
  def arrWeight : List Lean.Json → Nat
    | [] => 0
    | x :: xs => jsonWeight x + 1 + arrWeight xs
  termination_by xs => sizeOf xs

  /-- Structural weight of a `Std.DTreeMap` internal tree of JSON values. -/
  def treeWeight : Std.DTreeMap.Internal.Impl String (fun _ => Lean.Json) → Nat
    | .leaf => 0
    | .inner _ _ v l r => treeWeight l + (jsonWeight v + 5) + treeWeight r
  termination_by t => sizeOf t
end

/-- Total Wadler pretty-printing document AST for JSON serialization and formatting. -/
inductive JsonDoc where
  /-- Single-line literal syntax or scalar token. -/
  | text (s : String)
  /-- Breakable separator (`""` in `compress`, `" "` when flattened, `"\n" ++ indent` when broken). -/
  | line
  /-- Increase indentation of `doc` by `indent` spaces. -/
  | nest (indent : Nat) (doc : JsonDoc)
  /-- Concatenate two documents. -/
  | append (left right : JsonDoc)
  /-- All-or-nothing flattening group. -/
  | group (doc : JsonDoc)

/-- Structural AST weight of a `JsonDoc`. -/
def docWeight : JsonDoc → Nat
  | .text _ | .line => 1
  | .nest _ d | .group d => docWeight d + 1
  | .append d1 d2 => docWeight d1 + docWeight d2 + 1

/-- Total termination weight of a list of `JsonDoc` nodes. -/
def docListWeight : List JsonDoc → Nat
  | [] => 0
  | d :: ds => docWeight d + docListWeight ds

/-- Tail-recursive compact single-line renderer over `JsonDoc` worklists (`line` emits `""`). -/
def compactDocLoop (acc : String) : (docs : List JsonDoc) → String
  | [] => acc
  | .text s :: rest => compactDocLoop (acc ++ s) rest
  | .line :: rest => compactDocLoop acc rest
  | .nest _ d :: rest => compactDocLoop acc (d :: rest)
  | .group d :: rest => compactDocLoop acc (d :: rest)
  | .append d1 d2 :: rest => compactDocLoop acc (d1 :: d2 :: rest)
termination_by docs => docListWeight docs
decreasing_by all_goals simp_wf; simp [docListWeight, docWeight]; try omega

/-- Worklist item for total Wadler formatting. -/
structure DocItem where
  /-- Whether enclosing group chose single-line flattening. -/
  flatten : Bool
  /-- Current indentation column for line breaks. -/
  indent : Nat
  /-- Document node to format. -/
  doc : JsonDoc

/-- Total termination weight of a `DocItem` worklist. -/
def docItemsWeight : List DocItem → Nat
  | [] => 0
  | it :: rest => docWeight it.doc + docItemsWeight rest

/-- Check whether `items` fit within `rem` remaining columns up to the next line break. -/
def docFits (rem : Int) : List DocItem → Bool
  | [] => decide (0 ≤ rem)
  | ⟨_, _, .text s⟩ :: rest => if rem < 0 then false else docFits (rem - s.length) rest
  | ⟨fl, _, .line⟩ :: rest => if rem < 0 then false else if fl then docFits (rem - 1) rest else true
  | ⟨fl, ind, .nest n d⟩ :: rest => if rem < 0 then false else docFits rem (⟨fl, ind + n, d⟩ :: rest)
  | ⟨fl, ind, .append d1 d2⟩ :: rest =>
    if rem < 0 then false else docFits rem (⟨fl, ind, d1⟩ :: ⟨fl, ind, d2⟩ :: rest)
  | ⟨_, ind, .group d⟩ :: rest => if rem < 0 then false else docFits rem (⟨true, ind, d⟩ :: rest)
termination_by items => docItemsWeight items
decreasing_by all_goals simp_wf; simp [docItemsWeight, docWeight]; try omega

/-- Format `items` targeting `width` columns starting at column `col`, appending onto `acc`. -/
def formatDocLoop (width col : Nat) (acc : String) : List DocItem → String
  | [] => acc
  | ⟨_, _, .text s⟩ :: rest => formatDocLoop width (col + s.length) (acc ++ s) rest
  | ⟨fl, ind, .line⟩ :: rest =>
    if fl then formatDocLoop width (col + 1) (acc ++ " ") rest
    else formatDocLoop width ind (acc ++ String.ofList ('\n' :: List.replicate ind ' ')) rest
  | ⟨fl, ind, .nest n d⟩ :: rest => formatDocLoop width col acc (⟨fl, ind + n, d⟩ :: rest)
  | ⟨fl, ind, .append d1 d2⟩ :: rest =>
    formatDocLoop width col acc (⟨fl, ind, d1⟩ :: ⟨fl, ind, d2⟩ :: rest)
  | ⟨fl, ind, .group d⟩ :: rest =>
    let fit := fl || docFits ((width : Int) - (col : Int)) (⟨true, ind, d⟩ :: rest)
    formatDocLoop width col acc (⟨fit, ind, d⟩ :: rest)
termination_by items => docItemsWeight items
decreasing_by all_goals simp_wf; simp [docItemsWeight, docWeight]; try omega

/-- Wrap `body` inside `openDel` and `closeDel` as a 1-space nested flattening group. -/
def docBracket (openDel : String) (body : JsonDoc) (closeDel : String) : JsonDoc :=
  .group (.nest 1 (.append (.text openDel) (.append body (.text closeDel))))

/-- Worklist item for iterative in-order traversal of JSON object trees during serialization. -/
inductive ObjWalkItem where
  /-- Traverse subtree `t` in-order. -/
  | tree (t : Std.DTreeMap.Internal.Impl String (fun _ => Lean.Json))
  /-- Format object entry `(k, v)`. -/
  | emitKv (k : String) (v : Lean.Json)

/-- Termination weight of one object walk item. -/
def objWalkWeight : ObjWalkItem → Nat
  | .tree t => treeWeight t + 1
  | .emitKv _ v => jsonWeight v + 3

/-- Total termination weight of pending object walk items. -/
def pendingWeight : List ObjWalkItem → Nat
  | [] => 0
  | w :: ws => objWalkWeight w + pendingWeight ws

/-- Continuation frame for tail-recursive total `JsonDoc` construction. -/
inductive PrettyFrame where
  /-- Waiting for the current array element, with reversed prior docs and remaining elements. -/
  | arr (accRev : List JsonDoc) (remaining : List Lean.Json)
  /-- Waiting for the value doc of key `k`, with accumulated field docs and pending walk items. -/
  | objKv (k : String) (acc : List JsonDoc) (pending : List ObjWalkItem)

/-- Termination weight of one pretty-printing frame. -/
def prettyFrameWeight : PrettyFrame → Nat
  | .arr _ rem => arrWeight rem + 1
  | .objKv _ _ pending => pendingWeight pending + 2

/-- Total termination weight of a pretty-printing continuation stack. -/
def prettyFramesWeight : List PrettyFrame → Nat
  | [] => 0
  | f :: fs => prettyFrameWeight f + prettyFramesWeight fs

/-- Tail-recursively join a non-empty reversed list of `JsonDoc` values with `"," ++ line`. -/
def joinCommaLineRev (acc : JsonDoc) : List JsonDoc → JsonDoc
  | [] => acc
  | x :: xs => joinCommaLineRev (.append x (.append (.text ",") (.append .line acc))) xs

mutual
  /-- Tail-recursively render `j` into `JsonDoc` using an explicit frame stack. -/
  def renderEval (j : Lean.Json) (frames : List PrettyFrame) : JsonDoc :=
    match j with
    | .null => renderApply (.text "null") frames
    | .bool true => renderApply (.text "true") frames
    | .bool false => renderApply (.text "false") frames
    | .num n => renderApply (.text (jsonNumberToString n)) frames
    | .str s => renderApply (.text (renderString s)) frames
    | .arr elems =>
      match heq : elems.toList with
      | [] =>
        have : 0 < jsonWeight (.arr elems) := by simp [jsonWeight]; omega
        renderApply (.text "[]") frames
      | x :: xs =>
        have hDec : jsonWeight x + prettyFramesWeight (.arr [] xs :: frames) <
            jsonWeight (.arr elems) + prettyFramesWeight frames := by
          simp only [jsonWeight, prettyFramesWeight, prettyFrameWeight]; rw [heq]; simp [arrWeight]; omega
        renderEval x (.arr [] xs :: frames)
    | .obj kvs =>
      match heq : kvs.inner.inner with
      | .leaf =>
        have : 0 < jsonWeight (.obj kvs) := by simp [jsonWeight]; omega
        renderApply (.text "{}") frames
      | t =>
        have _hDec : 1 + pendingWeight [.tree t] + prettyFramesWeight frames <
            jsonWeight (.obj kvs) + prettyFramesWeight frames := by
          simp only [jsonWeight, pendingWeight, objWalkWeight]; rw [heq]; omega
        renderObjNext [] [.tree t] frames
  termination_by jsonWeight j + prettyFramesWeight frames
  decreasing_by
    all_goals simp_wf
    · simp [jsonWeight]
    · simp [jsonWeight]
    · simp [jsonWeight]
    · simp [jsonWeight]
    · simp [jsonWeight]
    · simp [jsonWeight]; omega
    · exact hDec
    · simp [jsonWeight]; omega
    · omega

  /-- Tail-recursively advance through `pending` object tree walk items. -/
  def renderObjNext (acc : List JsonDoc) (pending : List ObjWalkItem) (frames : List PrettyFrame) : JsonDoc :=
    match pending with
    | [] =>
      let doc := match acc with
        | [] => .text "{}"
        | last :: restRev => docBracket "{" (joinCommaLineRev last restRev) "}"
      renderApply doc frames
    | .tree .leaf :: rest => renderObjNext acc rest frames
    | .tree (.inner _ k v l r) :: rest =>
      let next0 := match r with | .leaf => rest | .inner _ _ _ _ _ => .tree r :: rest
      let next1 := .emitKv k v :: next0
      let next2 := match l with | .leaf => next1 | .inner _ _ _ _ _ => .tree l :: next1
      renderObjNext acc next2 frames
    | .emitKv k v :: rest => renderEval v (.objKv k acc rest :: frames)
  termination_by 1 + pendingWeight pending + prettyFramesWeight frames
  decreasing_by
    all_goals simp_wf
    · omega
    · simp [pendingWeight, objWalkWeight]
    · cases l <;> cases r <;> simp [pendingWeight, objWalkWeight, treeWeight] <;> omega
    · simp [pendingWeight, objWalkWeight, prettyFramesWeight, prettyFrameWeight]; omega

  /-- Tail-recursively feed a completed `JsonDoc` value into the enclosing continuation frame. -/
  def renderApply (valFmt : JsonDoc) (frames : List PrettyFrame) : JsonDoc :=
    match frames with
    | [] => valFmt
    | .arr accRev [] :: rest =>
      renderApply (docBracket "[" (joinCommaLineRev valFmt accRev) "]") rest
    | .arr accRev (x :: xs) :: rest => renderEval x (.arr (valFmt :: accRev) xs :: rest)
    | .objKv k acc pending :: rest =>
      let kvFmt := JsonDoc.group (.append (.text (renderString k ++ ":")) (.append .line valFmt))
      renderObjNext (kvFmt :: acc) pending rest
  termination_by prettyFramesWeight frames
  decreasing_by
    all_goals simp_wf
    · simp [prettyFramesWeight, prettyFrameWeight]
    · simp only [prettyFramesWeight, prettyFrameWeight, arrWeight]; omega
    · simp [prettyFramesWeight, prettyFrameWeight]; omega
end

/-- Render a `Lean.Json` value into a `JsonDoc` iteratively without recursion. -/
def renderFormat (j : Lean.Json) : JsonDoc :=
  renderEval j []

end LeanSwe.Json.Internal
