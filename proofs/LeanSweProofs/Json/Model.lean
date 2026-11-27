import Lean.Data.Json.Basic
import Lean.Data.Json.FromToJson
import LeanSwe.Json.Types
import LeanSweProofs.Json.Model.Equiv
import LeanSweProofs.Json.Model.Syntax

namespace LeanSwe.Json.Model

open LeanSwe.Json

/-- Strict inverse-renderer specification for `LeanSwe.Json.parse`, separating pure RFC 8259 grammar (`render`) from runtime scanner limits (`withinResourceLimits`). -/
def allowedParse (raw : String) (out : Except JsonError Lean.Json) : Prop :=
  match out with
  | .ok parsed =>
    WellFormedJson parsed ∧
      (∃ tape : RenderTape, render parsed tape = some raw) ∧
      ∀ a t, render a t = some raw → JsonEquiv a parsed
  | .error e =>
    e.kind = .parseError ∧ !e.message.isEmpty = true ∧
      ∀ a t, render a t = some raw → ¬ withinResourceLimits t

/-- Allowed outcome relation for `LeanSwe.Json.compress`: single-line non-empty output witnessed by a compact `RenderTape` on all `WellFormedJson` values. -/
def allowedCompress (j : Lean.Json) (out : String) : Prop :=
  !out.isEmpty = true ∧ !out.contains '\n' = true ∧ !out.contains '\r' = true ∧
    if wellFormedJsonBool j then
      ∃ tape : RenderTape, isCompactTape tape = true ∧ render j tape = some out
    else
      out.startsWith "{" = (match j with | .obj _ => true | _ => false)

/-- Allowed outcome relation for `LeanSwe.Json.pretty`: non-empty RFC 8259 rendering witnessed by
    `render` on `WellFormedJson` values, flattening to `flatPretty j` when `(flatPretty j).length ≤ lineWidth`. -/
def allowedPretty (j : Lean.Json) (lineWidth : Nat) (out : String) : Prop :=
  !out.isEmpty = true ∧
    ((flatPretty j).length ≤ lineWidth → out = flatPretty j) ∧
    if wellFormedJsonBool j then
      ∃ tape : RenderTape, render j tape = some out
    else
      out.startsWith "{" = (match j with | .obj _ => true | _ => false)

/-- Allowed outcome relation for `LeanSwe.Json.decode` over `[Lean.FromJson α]`. -/
def allowedDecode {α : Type} [Lean.FromJson α] (j : Lean.Json) (out : Except JsonError α) : Prop :=
  match Lean.fromJson? (α := α) j, out with
  | .ok a, .ok b => b = a
  | .error _, .error e => e.kind = .decodeError ∧ e.path = none ∧ !e.message.isEmpty = true
  | _, _ => False

/-- Reference model for `LeanSwe.Json.encode` over `[Lean.ToJson α]`. -/
def encodeModel {α : Type} [Lean.ToJson α] (a : α) : Lean.Json :=
  Lean.toJson a

/-- Allowed outcome relation for `LeanSwe.Json.getObject`. -/
def allowedGetObject (j : Lean.Json)
    (out : Except JsonError (Std.TreeMap.Raw String Lean.Json compare)) : Prop :=
  match j, out with
  | .obj kvs, .ok res => res = kvs
  | .obj _, .error _ => False
  | _, .ok _ => False
  | _, .error e => e.kind = .typeMismatch ∧ e.path = none ∧ !e.message.isEmpty = true

/-- Allowed outcome relation for `LeanSwe.Json.getArray`. -/
def allowedGetArray (j : Lean.Json) (out : Except JsonError (Array Lean.Json)) : Prop :=
  match j, out with
  | .arr xs, .ok res => res = xs
  | .arr _, .error _ => False
  | _, .ok _ => False
  | _, .error e => e.kind = .typeMismatch ∧ e.path = none ∧ !e.message.isEmpty = true

/-- Allowed outcome relation for `LeanSwe.Json.getField` over `[Lean.FromJson α]`. -/
def allowedGetField {α : Type} [Lean.FromJson α] (j : Lean.Json) (key : String)
    (out : Except JsonError α) : Prop :=
  match j, out with
  | .obj kvs, _ =>
    match kvs.get? key, out with
    | none, .error e => e.kind = .missingField ∧ e.path = some key ∧ !e.message.isEmpty = true
    | some v, .ok a => Lean.fromJson? (α := α) v = .ok a
    | some v, .error e =>
      (Lean.fromJson? (α := α) v).isOk = false ∧
        e.kind = .decodeError ∧ e.path = some key ∧ !e.message.isEmpty = true
    | _, _ => False
  | _, .error e => e.kind = .typeMismatch ∧ e.path = none ∧ !e.message.isEmpty = true
  | _, .ok _ => False

/-- Allowed outcome relation for `LeanSwe.Json.getOptField` over `[Lean.FromJson α]`. -/
def allowedGetOptField {α : Type} [Lean.FromJson α] (j : Lean.Json) (key : String)
    (out : Except JsonError (Option α)) : Prop :=
  match j, out with
  | .obj kvs, _ =>
    match kvs.get? key, out with
    | none, .ok none => True
    | some .null, .ok none => True
    | some v, .ok (some a) => v ≠ .null ∧ Lean.fromJson? (α := α) v = .ok a
    | some v, .error e =>
      v ≠ .null ∧ (Lean.fromJson? (α := α) v).isOk = false ∧
        e.kind = .decodeError ∧ e.path = some key ∧ !e.message.isEmpty = true
    | _, _ => False
  | _, .error e => e.kind = .typeMismatch ∧ e.path = none ∧ !e.message.isEmpty = true
  | _, .ok _ => False

/-- Format a reversed path prefix as an optional dot-separated field path. -/
def modelJoinPath (revPrefix : List String) : Option String :=
  if revPrefix.isEmpty then none else some (String.intercalate "." revPrefix.reverse)

/-- Recursively specify nested JSON object lookup and `Lean.FromJson` decoding along `keys`. -/
def allowedGetPathAux {α : Type} [Lean.FromJson α] (revPrefix : List String) (j : Lean.Json) :
    List String → Except JsonError α → Prop
  | [], out =>
    match Lean.fromJson? (α := α) j, out with
    | .ok a, .ok b => b = a
    | .error _, .error e =>
      e.kind = .decodeError ∧ e.path = modelJoinPath revPrefix ∧ !e.message.isEmpty = true
    | _, _ => False
  | key :: rest, out =>
    match j with
    | .obj kvs =>
      let nextPrefix := key :: revPrefix
      match kvs.get? key with
      | some v => allowedGetPathAux nextPrefix v rest out
      | none =>
        ∃ e, out = .error e ∧ e.kind = .missingField ∧
          e.path = modelJoinPath nextPrefix ∧ !e.message.isEmpty = true
    | _ =>
      ∃ e, out = .error e ∧ e.kind = .typeMismatch ∧
        e.path = modelJoinPath revPrefix ∧ !e.message.isEmpty = true

/-- Allowed outcome relation for `LeanSwe.Json.getPath` over `[Lean.FromJson α]`. -/
def allowedGetPath {α : Type} [Lean.FromJson α] (j : Lean.Json) (keys : List String)
    (out : Except JsonError α) : Prop :=
  allowedGetPathAux [] j keys out

end LeanSwe.Json.Model
