namespace LeanSwe.LinuxSyscall

/-!
Shared kernel-reducible byte-equality and association-list helpers for `LeanSwe.LinuxSyscall`
world models (`Files`, `Net`, `Poll`, `Process`, `Sandbox`).
-/

/-- Unboxed `O(1)` byte lookup returning `0` when `i ≥ b.size`. -/
@[inline] def byteGetD (b : ByteArray) (i : Nat) : UInt8 :=
  if h : i < b.size then b[i] else 0

/-- Unboxed index loop comparing `rem` bytes of `a` and `b` starting at `i`. -/
def bytesEqLoop (a b : ByteArray) (i rem : Nat) : Bool :=
  match rem with
  | 0 => true
  | rem' + 1 =>
    if byteGetD a i == byteGetD b i then bytesEqLoop a b (i + 1) rem' else false

/-- Kernel-reducible unboxed `ByteArray` equality. -/
def bytesEq (a b : ByteArray) : Bool :=
  a.size == b.size && bytesEqLoop a b 0 a.size

/-- Look up a key in an association list, returning the first matching value (kernel-reducible). -/
@[specialize] def assocGet {α β : Type} [BEq α] (xs : List (α × β)) (k : α) : Option β :=
  match xs with
  | [] => none
  | (k', v) :: rest => if k' == k then some v else assocGet rest k

/-- Tail-recursive helper for `assocSet`, preserving existing key position. -/
@[specialize] def assocSetAux {α β : Type} [BEq α] :
    List (α × β) → α → β → List (α × β) → List (α × β)
  | [], k, v, acc => acc.reverseAux [(k, v)]
  | (k', v') :: rest, k, v, acc =>
    if k' == k then acc.reverseAux ((k, v) :: rest)
    else assocSetAux rest k v ((k', v') :: acc)

/-- Insert or replace the first matching key in an association list (tail-recursive, kernel-reducible). -/
@[inline] def assocSet {α β : Type} [BEq α] (xs : List (α × β)) (k : α) (v : β) : List (α × β) :=
  assocSetAux xs k v []

/-- Tail-recursive helper for `assocErase`, removing the first matching key. -/
@[specialize] def assocEraseAux {α β : Type} [BEq α] :
    List (α × β) → α → List (α × β) → List (α × β)
  | [], _, acc => acc.reverse
  | (k', v') :: rest, k, acc =>
    if k' == k then acc.reverseAux rest
    else assocEraseAux rest k ((k', v') :: acc)

/-- Remove the first entry matching key `k` from an association list (tail-recursive, kernel-reducible). -/
@[inline] def assocErase {α β : Type} [BEq α] (xs : List (α × β)) (k : α) : List (α × β) :=
  assocEraseAux xs k []

/-- Tail-recursive helper for `assocEraseAll`, removing every matching key. -/
@[specialize] def assocEraseAllAux {α β : Type} [BEq α] :
    List (α × β) → α → List (α × β) → List (α × β)
  | [], _, acc => acc.reverse
  | (k', v) :: rest, k, acc =>
    if k' == k then assocEraseAllAux rest k acc
    else assocEraseAllAux rest k ((k', v) :: acc)

/-- Remove all entries matching key `k` from an association list (tail-recursive, kernel-reducible). -/
@[inline] def assocEraseAll {α β : Type} [BEq α] (xs : List (α × β)) (k : α) : List (α × β) :=
  assocEraseAllAux xs k []

/-- Look up a `ByteArray` key in an association list using `bytesEq`. -/
def bytesAssocGet {β : Type} (xs : List (ByteArray × β)) (k : ByteArray) : Option β :=
  @assocGet ByteArray β ⟨bytesEq⟩ xs k

/-- Insert or replace the first matching `ByteArray` key in an association list (tail-recursive). -/
def bytesAssocSet {β : Type} (xs : List (ByteArray × β)) (k : ByteArray) (v : β) : List (ByteArray × β) :=
  @assocSet ByteArray β ⟨bytesEq⟩ xs k v

/-- Remove the first entry matching `ByteArray` key `k` from an association list (tail-recursive). -/
def bytesAssocErase {β : Type} (xs : List (ByteArray × β)) (k : ByteArray) : List (ByteArray × β) :=
  @assocErase ByteArray β ⟨bytesEq⟩ xs k

end LeanSwe.LinuxSyscall
