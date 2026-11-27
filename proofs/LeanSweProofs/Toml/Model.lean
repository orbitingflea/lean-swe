import LeanSwe.Toml.Types
import LeanSweProofs.Toml.Model.Equiv
import LeanSweProofs.Toml.Model.Tape
import LeanSweProofs.Toml.Model.Render

namespace LeanSwe.Toml.Model

open LeanSwe.Toml

/-- Check whether `sub` occurs as a contiguous character slice within `cs`. -/
def hasCharSublist (sub : List Char) : List Char → Bool
  | [] => sub.isEmpty
  | c :: cs => sub.isPrefixOf (c :: cs) || hasCharSublist sub cs

/-- Check whether `st` is the canonical key style (`bare` if `isValidBareKey k`, else canonical `basic none`). -/
def isCleanKeyStyle (k : String) (st : KeyStyle) : Bool :=
  if isValidBareKey k then
    match st with | .bare => true | _ => false
  else
    match st with | .basic none => true | _ => false

/-- Check whether a `DottedKeyTape` uses canonical key styles and zero whitespace around dots. -/
def isCleanDottedKey (dk : DottedKeyTape) : Bool :=
  isCleanKeyStyle dk.firstKey dk.firstStyle &&
  dk.rest.all fun seg =>
    seg.wsBeforeDot.isEmpty && seg.wsAfterDot.isEmpty && isCleanKeyStyle seg.key seg.style

/-- Check whether a `LineSuffixTape` has empty trailing whitespace and no comment. -/
def isCleanLineSuffix (suf : LineSuffixTape) : Bool :=
  suf.ws.isEmpty && suf.comment.isNone

mutual
  /-- Check whether a `ValueTape` uses canonical single-line, comment-free, canonical-spacing formatting. -/
  def isCleanValueTape : ValueTape → Bool
    | .string (.basic none) => true
    | .string _ => false
    | .int _ | .float _ | .bool | .localDate | .localTime _ => true
    | .offsetDateTime .upperT .upperZ _ => true
    | .offsetDateTime _ _ _ => false
    | .localDateTime .upperT _ => true
    | .localDateTime _ _ => false
    | .array elems trailing => trailing.isNone && isCleanArrayElems true elems
    | .inlineTable assigns emptyWs => emptyWs.isEmpty && isCleanInlineAssigns true assigns
  termination_by vt => sizeOf vt
  decreasing_by all_goals simp +arith

  /-- Check canonical `", "` element spacing and clean element tapes in an inline array. -/
  def isCleanArrayElems : Bool → List (String × ValueTape × String) → Bool
    | _, [] => true
    | first, (pre, vt, post) :: rest =>
      pre == (if first then "" else " ") && post.isEmpty &&
        isCleanValueTape vt && isCleanArrayElems false rest
  termination_by _ elems => sizeOf elems
  decreasing_by all_goals simp +arith

  /-- Check canonical `", "` / `" = "` spacing and clean keys/values in an inline table. -/
  def isCleanInlineAssigns : Bool →
      List (String × DottedKeyTape × String × String × ValueTape × String) → Bool
    | _, [] => true
    | first, (wsPre, dk, wsEqL, wsEqR, vt, wsPost) :: rest =>
      wsPre == (if first then "" else " ") &&
        dk.rest.isEmpty && isCleanDottedKey dk &&
        wsEqL == " " && wsEqR == " " && wsPost.isEmpty &&
        isCleanValueTape vt && isCleanInlineAssigns false rest
  termination_by _ assigns => sizeOf assigns
  decreasing_by all_goals simp +arith
end

/-- Check whether a `StmtTape` uses canonical comment-free, trivia-free, canonical-spacing formatting. -/
def isCleanStmt : StmtTape → Bool
  | .tableHeader pre wsOpen path wsClose suf =>
    pre.isEmpty && wsOpen.isEmpty && isCleanDottedKey path && wsClose.isEmpty && isCleanLineSuffix suf
  | .aotHeader pre wsOpen path wsClose suf =>
    pre.isEmpty && wsOpen.isEmpty && isCleanDottedKey path && wsClose.isEmpty && isCleanLineSuffix suf
  | .assign pre key wsBeforeEq wsAfterEq val suf =>
    pre.isEmpty && key.rest.isEmpty && isCleanDottedKey key &&
      wsBeforeEq == " " && wsAfterEq == " " && isCleanValueTape val && isCleanLineSuffix suf

/-- Check that a `RenderTape` emits canonical comment-free, trivia-free, canonical-spacing, LF-terminated lines. -/
def isCleanFormatTape (tape : RenderTape) : Bool :=
  tape.trailingNewline &&
  tape.eofTrivia.isEmpty &&
  tape.crlfMask.isEmpty &&
  tape.stmts.all isCleanStmt

/-- Allowed outcome relation for `Toml.format` across all `TomlTable` inputs: empty tables format
to `""`; non-empty well-formed tables emit a comment-free `render` output under some `RenderTape`;
ill-formed non-empty tables still emit newline-terminated text containing every top-level rendered key. -/
def allowedFormat (doc : TomlTable) (out : String) : Prop :=
  if doc.toList.isEmpty then
    out = ""
  else if wellFormedTableBool doc then
    ∃ tape : RenderTape, isCleanFormatTape tape = true ∧ render doc tape = some out
  else
    out.toList.reverse.head? = some '\n' ∧
      ∀ k v, (k, v) ∈ doc.toList →
        ∃ rk, renderKey k (if isValidBareKey k then .bare else .basic) = some rk ∧
          hasCharSublist rk.toList out.toList = true

/-- Allowed outcome relation for `Toml.getTable`. -/
def allowedGetTable (v : TomlValue) (out : Except TomlError TomlTable) : Prop :=
  match v, out with
  | .table t, .ok res => res = t
  | .table _, .error _ => False
  | _, .ok _ => False
  | _, .error e => e.kind = .typeMismatch ∧ e.path = none ∧ !e.message.isEmpty = true

/-- Allowed outcome relation for `Toml.getArray`. -/
def allowedGetArray (v : TomlValue) (out : Except TomlError (Array TomlValue)) : Prop :=
  match v, out with
  | .array xs, .ok res => res = xs
  | .array _, .error _ => False
  | _, .ok _ => False
  | _, .error e => e.kind = .typeMismatch ∧ e.path = none ∧ !e.message.isEmpty = true

/-- Allowed outcome relation for `Toml.decode` over `[FromToml α]`. -/
def allowedDecode {α : Type} [FromToml α] (v : TomlValue) (out : Except TomlError α) : Prop :=
  match FromToml.fromToml (α := α) v, out with
  | .ok a, .ok b => b = a
  | .error _, .error e => e.kind = .decodeError ∧ !e.message.isEmpty = true
  | _, _ => False

/-- Reference model for `Toml.encode` over `[ToToml α]`. -/
def encodeModel {α : Type} [ToToml α] (x : α) : TomlValue :=
  ToToml.toToml x

/-- Allowed outcome relation for `Toml.getField` over `[FromToml α]`. -/
def allowedGetField {α : Type} [FromToml α] (t : TomlTable) (key : String)
    (out : Except TomlError α) : Prop :=
  match lookupKey key t, out with
  | none, .error e => e.kind = .missingField ∧ e.path = some key ∧ !e.message.isEmpty = true
  | some v, .ok a => FromToml.fromToml v = .ok a
  | some v, .error e =>
    (FromToml.fromToml (α := α) v).isOk = false ∧
      e.kind = .decodeError ∧ e.path = some key ∧ !e.message.isEmpty = true
  | _, _ => False

/-- Allowed outcome relation for `Toml.getOptField` over `[FromToml α]`. -/
def allowedGetOptField {α : Type} [FromToml α] (t : TomlTable) (key : String)
    (out : Except TomlError (Option α)) : Prop :=
  match lookupKey key t, out with
  | none, .ok none => True
  | some v, .ok (some a) => FromToml.fromToml v = .ok a
  | some v, .error e =>
    (FromToml.fromToml (α := α) v).isOk = false ∧
      e.kind = .decodeError ∧ e.path = some key ∧ !e.message.isEmpty = true
  | _, _ => False

/-- Recursively specify nested table path lookup and `FromToml` decoding along `keys`. -/
def allowedGetPathAux {α : Type} [FromToml α] (revPrefix : List String) (t : TomlTable) :
    List String → Except TomlError α → Prop
  | [], out =>
    match FromToml.fromToml (α := α) (.table t), out with
    | .ok a, .ok b => b = a
    | .error _, .error e => e.kind = .decodeError ∧ e.path = none ∧ !e.message.isEmpty = true
    | _, _ => False
  | [k], out =>
    let full := String.intercalate "." (revPrefix.reverse ++ [k])
    match lookupKey k t, out with
    | none, .error e => e.kind = .missingField ∧ e.path = some full ∧ !e.message.isEmpty = true
    | some v, .ok a => FromToml.fromToml v = .ok a
    | some v, .error e =>
      (FromToml.fromToml (α := α) v).isOk = false ∧
        e.kind = .decodeError ∧ e.path = some full ∧ !e.message.isEmpty = true
    | _, _ => False
  | k :: k' :: rest, out =>
    let full := String.intercalate "." (revPrefix.reverse ++ [k])
    match lookupKey k t with
    | none => ∃ e, out = .error e ∧ e.kind = .missingField ∧ e.path = some full ∧ !e.message.isEmpty = true
    | some (.table sub) => allowedGetPathAux (k :: revPrefix) sub (k' :: rest) out
    | some _ => ∃ e, out = .error e ∧ e.kind = .typeMismatch ∧ e.path = some full ∧ !e.message.isEmpty = true

/-- Allowed outcome relation for `Toml.getPath` over `[FromToml α]`. -/
def allowedGetPath {α : Type} [FromToml α] (t : TomlTable) (keys : List String)
    (out : Except TomlError α) : Prop :=
  allowedGetPathAux [] t keys out

end LeanSwe.Toml.Model
