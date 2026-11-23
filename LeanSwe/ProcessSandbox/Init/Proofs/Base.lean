import LeanSwe.ProcessSandbox.Init.Aeneas.TypesExternal
import LeanSwe.ProcessSandbox.Init.Aeneas.Types
import LeanSwe.ProcessSandbox.Init.Aeneas.FunsExternal
import LeanSwe.ProcessSandbox.Init.Aeneas.Funs

/-!
# ProcessSandbox Init Aeneas Foundation Lemmas

Monadic `OkPost` combinators, `Aeneas.Std.loop` variant rules, scalar arithmetic/shift
characterizations, and `ByteArray` ↔ `List Std.U8` bridging helpers for `psandbox_init`.
-/

namespace LeanSwe.ProcessSandbox.Init.Proofs

open _root_.Aeneas _root_.Aeneas.Std Result ControlFlow
open LeanSwe.ProcessSandbox.Init.World

/-- Total Hoare postcondition predicate asserting `r = Result.ok v` with `P v`. -/
def OkPost {α : Type} (r : Result α) (P : α → Prop) : Prop :=
  ∃ v, r = Result.ok v ∧ P v

/-- Equivalence between `OkPost` and `Aeneas.Std.WP.spec`. -/
theorem okPost_iff_wp_spec {α : Type} (r : Result α) (P : α → Prop) :
    OkPost r P ↔ WP.spec r P := by
  cases r <;> simp [OkPost, WP.spec_ok, WP.spec_div, WP.spec_vis]

/-- Constructor rule for `OkPost` on `Result.ok`. -/
theorem okPost_ok {α : Type} (v : α) (P : α → Prop) (h : P v) :
    OkPost (Result.ok v) P :=
  ⟨v, rfl, h⟩

/-- Monotonicity rule for `OkPost`. -/
theorem okPost_mono {α : Type} {r : Result α} {P Q : α → Prop}
    (hr : OkPost r P) (himp : ∀ x, P x → Q x) :
    OkPost r Q := by
  rcases hr with ⟨v, hv, hp⟩
  exact ⟨v, hv, himp v hp⟩

/-- Sequential composition rule for `OkPost` over `Result.bind`. -/
theorem okPost_bind {α β : Type} {m : Result α} {k : α → Result β}
    {P : α → Prop} {Q : β → Prop}
    (hm : OkPost m P) (hk : ∀ x, P x → OkPost (k x) Q) :
    OkPost (m >>= k) Q := by
  rcases hm with ⟨v, hv, hp⟩
  subst hv
  simpa using hk v hp

/-- Natural-number decreasing variant rule for `Aeneas.Std.loop` under `OkPost`. -/
theorem okPost_loop_decr_nat {α β : Type} (measure : α → Nat) (inv : α → Prop)
    (post : β → Prop) (body : α → Result (ControlFlow α β)) (x : α)
    (hBody : ∀ a, inv a → OkPost (body a) fun r =>
      match r with
      | ControlFlow.done y => post y
      | ControlFlow.cont a' => inv a' ∧ measure a' < measure a)
    (hInv : inv x) :
    OkPost (loop body x) post := by
  rw [okPost_iff_wp_spec]
  refine loop.spec_decr_nat measure inv post body x ?_ hInv
  intro a ha
  rw [← okPost_iff_wp_spec]
  exact hBody a ha

/-- Convert a Lean `UInt8` to an Aeneas `Std.U8`. -/
def u8OfUInt8 (b : UInt8) : Std.U8 := ⟨b.toBitVec⟩

/-- Convert an Aeneas `Std.U8` to a Lean `UInt8`. -/
def uint8OfU8 (b : Std.U8) : UInt8 := UInt8.ofBitVec b.bv

/-- Convert a Lean `ByteArray` into `Bytes` (`List Std.U8`). -/
def byteArrayToBytes (ba : ByteArray) : Bytes :=
  ba.data.toList.map u8OfUInt8

/-- Convert `Bytes` (`List Std.U8`) into a Lean `ByteArray`. -/
def bytesToByteArray (bs : Bytes) : ByteArray :=
  ByteArray.mk (bs.map uint8OfU8).toArray

/-- Left inverse `uint8OfU8 (u8OfUInt8 b) = b`. -/
@[simp]
theorem uint8OfU8_u8OfUInt8 (b : UInt8) : uint8OfU8 (u8OfUInt8 b) = b := by
  cases b
  rfl

/-- Right inverse `u8OfUInt8 (uint8OfU8 b) = b`. -/
@[simp]
theorem u8OfUInt8_uint8OfU8 (b : Std.U8) : u8OfUInt8 (uint8OfU8 b) = b := by
  cases b
  rfl

/-- Value preservation of `u8OfUInt8`. -/
@[simp]
theorem u8OfUInt8_val (b : UInt8) : (u8OfUInt8 b).val = b.toNat := rfl

/-- Value preservation of `uint8OfU8`. -/
@[simp]
theorem uint8OfU8_toNat (b : Std.U8) : (uint8OfU8 b).toNat = b.val := rfl

/-- Length of `byteArrayToBytes ba` equals `ba.size`. -/
@[simp]
theorem length_byteArrayToBytes (ba : ByteArray) :
    (byteArrayToBytes ba).length = ba.size := by
  unfold byteArrayToBytes
  rw [List.length_map, Array.length_toList]
  rfl

/-- Round-trip `bytesToByteArray (byteArrayToBytes ba) = ba`. -/
@[simp]
theorem bytesToByteArray_byteArrayToBytes (ba : ByteArray) :
    bytesToByteArray (byteArrayToBytes ba) = ba := by
  cases ba with
  | mk arr =>
    simp [byteArrayToBytes, bytesToByteArray, List.map_map, Function.comp_def]

/-- Round-trip `byteArrayToBytes (bytesToByteArray bs) = bs`. -/
@[simp]
theorem byteArrayToBytes_bytesToByteArray (bs : Bytes) :
    byteArrayToBytes (bytesToByteArray bs) = bs := by
  simp [byteArrayToBytes, bytesToByteArray, List.map_map, Function.comp_def]

/-- Distribute `byteArrayToBytes` across `ByteArray.append`. -/
theorem byteArrayToBytes_append (a b : ByteArray) :
    byteArrayToBytes (a ++ b) = byteArrayToBytes a ++ byteArrayToBytes b := by
  cases a with
  | mk da =>
    cases b with
    | mk db =>
      change (ByteArray.append ⟨da⟩ ⟨db⟩).data.toList.map u8OfUInt8 = _
      simp [ByteArray.append, byteArrayToBytes, List.map_append]

/-- Lower bound `4294967295 ≤ Usize.max` on all 32-bit and 64-bit targets. -/
theorem usize_max_ge_u32_max : 4294967295 ≤ Usize.max := by
  have h1 := Usize.cMax_bound.1
  have h2 : UScalar.cMax UScalarTy.Usize = 4294967295 := by decide
  omega

/-- Exact `U64.max` constant value. -/
theorem u64_max_eq : U64.max = 18446744073709551615 := by
  rw [U64.max_def, U64.numBits_def, UScalarTy.U64_numBits_eq]
  decide

/-- Equality of `UScalar` values from equality of underlying `BitVec`s. -/
theorem uscalar_eq_of_bv {ty : UScalarTy} {x y : UScalar ty} (h : x.bv = y.bv) : x = y := by
  apply UScalar.eq_of_val_eq
  change x.bv.toNat = y.bv.toNat
  rw [h]

/-- Equality of `IScalar` values from equality of underlying `BitVec`s. -/
theorem iscalar_eq_of_bv {ty : IScalarTy} {x y : IScalar ty} (h : x.bv = y.bv) : x = y := by
  cases x
  cases y
  simp at h
  subst h
  rfl

/-- Safe indexing into a `Slice` when `i.val < s.val.length`. -/
theorem slice_index_usize_ok {α : Type} (s : Slice α) (i : Usize) (hi : i.val < s.val.length) :
    Slice.index_usize s i = Result.ok (s.val[i.val]'hi) := by
  unfold Slice.index_usize
  have hElem : s[i]? = some (s.val[i.val]'hi) := by
    change s.val[i.val]? = some (s.val[i.val]'hi)
    exact List.getElem?_eq_some_iff.mpr ⟨hi, rfl⟩
  rw [hElem]

/-- Safe indexing into a fixed-length `Array` when `i.val < n.val`. -/
theorem array_index_usize_ok {α : Type} {n : Usize} (arr : Array α n) (i : Usize)
    (hi : i.val < n.val) :
    Array.index_usize arr i = Result.ok (arr.val[i.val]'(by rw [arr.property]; exact hi)) := by
  have hLen : i.val < arr.length := by
    change i.val < arr.val.length
    rw [arr.property]
    exact hi
  obtain ⟨x, hx, hEq⟩ := (okPost_iff_wp_spec _ _).mpr (Array.index_usize_spec arr i hLen)
  rw [hx, hEq]

/-- Right-shifting an unsigned scalar by a valid `I32` shift strictly below `numBits`. -/
theorem uscalar_shr_i32_ok {ty : UScalarTy} (x : UScalar ty) (sh : I32) (n : Nat)
    (h0 : 0 ≤ sh.val) (hn : sh.toNat = n) (hLt : n < ty.numBits) :
    x >>> sh = Result.ok ⟨BitVec.ushiftRight x.bv n⟩ := by
  change UScalar.shiftRight_IScalar x sh = _
  unfold UScalar.shiftRight_IScalar UScalar.shiftRight
  have hge : (↑sh : Int) ≥ 0 := h0
  simp only [hge, hn, hLt, ↓reduceIte]

/-- Left-shifting an unsigned scalar by a valid `I32` shift strictly below `numBits`. -/
theorem uscalar_shl_i32_ok {ty : UScalarTy} (x : UScalar ty) (sh : I32) (n : Nat)
    (h0 : 0 ≤ sh.val) (hn : sh.toNat = n) (hLt : n < ty.numBits) :
    x <<< sh = Result.ok ⟨BitVec.shiftLeft x.bv n⟩ := by
  change UScalar.shiftLeft_IScalar x sh = _
  unfold UScalar.shiftLeft_IScalar UScalar.shiftLeft
  have hge : (↑sh : Int) ≥ 0 := h0
  simp only [hge, hn, hLt, ↓reduceIte]

/-- Arithmetic right-shifting an `I32` by a valid `I32` shift in `0..31`. -/
theorem i32_shr_i32_ok (x : I32) (sh : I32) (n : Nat)
    (h0 : 0 ≤ sh.val) (hn : sh.toNat = n) (hLt : n < 32) :
    x >>> sh = Result.ok ⟨BitVec.sshiftRight x.bv n⟩ := by
  change IScalar.shiftRight_IScalar x sh = _
  unfold IScalar.shiftRight_IScalar IScalar.shiftRight
  have hge : (↑sh : Int) ≥ 0 := h0
  have hBits : n < IScalarTy.I32.numBits := by
    rw [IScalarTy.I32_numBits_eq]
    exact hLt
  simp only [hge, hn, hBits, ↓reduceIte]

/-- Bitvector identity for `IScalar.hcast .U32` on `I32`. -/
theorem hcast_u32_eq (v : I32) : (IScalar.hcast .U32 v : U32) = ⟨v.bv⟩ := by
  apply uscalar_eq_of_bv
  have h : (IScalar.hcast .U32 v : U32).bv = BitVec.signExtend 32 v.bv := rfl
  rw [h]
  ext i hi
  simp

/-- Bitvector identity for `UScalar.hcast .I32` on `U32`. -/
theorem hcast_i32_eq (u : U32) : (UScalar.hcast .I32 u : I32) = ⟨u.bv⟩ := by
  apply iscalar_eq_of_bv
  have h : (UScalar.hcast .I32 u : I32).bv = BitVec.setWidth 32 u.bv := rfl
  rw [h]
  ext i hi
  simp

/-- Checked `Usize` addition helper. -/
theorem usize_add_ok (a b : Usize) (h : a.val + b.val ≤ Usize.max) :
    ∃ c : Usize, a + b = Result.ok c ∧ c.val = a.val + b.val := by
  obtain ⟨c, hc, hcVal⟩ := (okPost_iff_wp_spec _ _).mpr (Usize.add_spec h)
  exact ⟨c, hc, by simpa using hcVal⟩

/-- Checked `Usize` subtraction helper. -/
theorem usize_sub_ok (a b : Usize) (h : b.val ≤ a.val) :
    ∃ c : Usize, a - b = Result.ok c ∧ c.val = a.val - b.val := by
  obtain ⟨c, hc, hcVal⟩ := (okPost_iff_wp_spec _ _).mpr (Usize.sub_spec h)
  exact ⟨c, hc, hcVal.1⟩

/-- Checked `Usize` multiplication helper. -/
theorem usize_mul_ok (a b : Usize) (h : a.val * b.val ≤ Usize.max) :
    ∃ c : Usize, a * b = Result.ok c ∧ c.val = a.val * b.val := by
  obtain ⟨c, hc, hcVal⟩ := (okPost_iff_wp_spec _ _).mpr (Usize.mul_spec h)
  exact ⟨c, hc, by simpa using hcVal⟩

/-- Checked `U32` addition helper. -/
theorem u32_add_ok (a b : U32) (h : a.val + b.val ≤ U32.max) :
    ∃ c : U32, a + b = Result.ok c ∧ c.val = a.val + b.val := by
  obtain ⟨c, hc, hcVal⟩ := (okPost_iff_wp_spec _ _).mpr (U32.add_spec h)
  exact ⟨c, hc, by simpa using hcVal⟩

/-- Exact value preservation when widening `U32` to `Usize` (`32 ≤ System.Platform.numBits`). -/
@[simp]
theorem u32_cast_usize_val (u : U32) :
    (UScalar.cast .Usize u : Usize).val = u.val := by
  scalar_tac

/-- Step through an Aeneas `?` (`CoreOpsTry.branch`) block on `Result.ok (.Ok v)`. -/
theorem try_step_ok {α γ : Type} {m : Result (core.result.Result α I32)} {v : α}
    {k : α → Result γ}
    {ek : _ → Result γ}
    (hm : m = Result.ok (.Ok v)) :
    (do
      let r ← m
      let cf ← core.result.Result.Insts.CoreOpsTry.branch r
      match cf with
      | core.ops.control_flow.ControlFlow.Continue val => k val
      | core.ops.control_flow.ControlFlow.Break residual => ek residual) =
    k v := by
  rw [hm]
  simp [core.result.Result.Insts.CoreOpsTry.branch]

/-- Step through an Aeneas `?` (`CoreOpsTry.branch`) block returning a pair `(v₁, v₂)`. -/
theorem try_step_pair_ok {α₁ α₂ γ : Type} {m : Result (core.result.Result (α₁ × α₂) I32)}
    {v₁ : α₁} {v₂ : α₂}
    {k : α₁ → α₂ → Result γ}
    {ek : _ → Result γ}
    (hm : m = Result.ok (.Ok (v₁, v₂))) :
    (do
      let r ← m
      let cf ← core.result.Result.Insts.CoreOpsTry.branch r
      match cf with
      | core.ops.control_flow.ControlFlow.Continue val =>
        let (x₁, x₂) := val
        k x₁ x₂
      | core.ops.control_flow.ControlFlow.Break residual => ek residual) =
    k v₁ v₂ := by
  rw [hm]
  simp [core.result.Result.Insts.CoreOpsTry.branch]

/-- Step through an Aeneas `?` (`CoreOpsTry.branch`) block returning `((v₁, v₂), v₃)`. -/
theorem try_step_nested_pair_ok {α₁ α₂ α₃ γ : Type}
    {m : Result (core.result.Result ((α₁ × α₂) × α₃) I32)}
    {v₁ : α₁} {v₂ : α₂} {v₃ : α₃}
    {k : α₁ → α₂ → α₃ → Result γ}
    {ek : _ → Result γ}
    (hm : m = Result.ok (.Ok ((v₁, v₂), v₃))) :
    (do
      let r ← m
      let cf ← core.result.Result.Insts.CoreOpsTry.branch r
      match cf with
      | core.ops.control_flow.ControlFlow.Continue val =>
        let ((x₁, x₂), x₃) := val
        k x₁ x₂ x₃
      | core.ops.control_flow.ControlFlow.Break residual => ek residual) =
    k v₁ v₂ v₃ := by
  rw [hm]
  simp [core.result.Result.Insts.CoreOpsTry.branch]

/-- Short-circuit an Aeneas `?` (`CoreOpsTry.branch`) block on `Result.ok (.Err e)`. -/
theorem try_step_err {α β : Type} {m : Result (core.result.Result α I32)} {e : I32}
    {k : α → Result (core.result.Result β I32)}
    (hm : m = Result.ok (.Err e)) :
    (do
      let r ← m
      let cf ← core.result.Result.Insts.CoreOpsTry.branch r
      match cf with
      | core.ops.control_flow.ControlFlow.Continue val => k val
      | core.ops.control_flow.ControlFlow.Break residual =>
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
          β (core.convert.FromSame I32) residual) =
    Result.ok (.Err e) := by
  rw [hm]
  simp [core.result.Result.Insts.CoreOpsTry.branch,
    core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]

/-- Rewrite `if c then t else e` to `t` given `hc : c` without invoking `simp`. -/
theorem if_true_eq {α : Type} {c : Prop} [Decidable c] {t e : α} (hc : c) :
    (if c then t else e) = t := by
  split
  · rfl
  · contradiction

/-- Rewrite `if c then t else e` to `e` given `hc : ¬ c` without invoking `simp`. -/
theorem if_false_eq {α : Type} {c : Prop} [Decidable c] {t e : α} (hc : ¬ c) :
    (if c then t else e) = e := by
  split
  · contradiction
  · rfl

/-- Eliminate a `have x := v; f x` binding by pure rewriting without invoking `simp`. -/
theorem have_elim {α β : Type} (v : α) (f : α → β) :
    (have x := v; f x) = f v := rfl

/-- Step through `let x ← m; k x` on `m = Result.ok v` without invoking `simp`. -/
theorem bind_val_ok {α γ : Type} {m : Result α} {v : α} {k : α → Result γ}
    (hm : m = Result.ok v) :
    (do let x ← m; k x) = k v := by
  rw [hm]
  simp

/-- Step through `let (x₁, x₂, x₃) ← m; k x₁ x₂ x₃` on `m = Result.ok (v₁, v₂, v₃)`. -/
theorem bind_triple_ok {α₁ α₂ α₃ γ : Type} {m : Result (α₁ × α₂ × α₃)}
    {v₁ : α₁} {v₂ : α₂} {v₃ : α₃} {k : α₁ → α₂ → α₃ → Result γ}
    (hm : m = Result.ok (v₁, v₂, v₃)) :
    (do let (x₁, x₂, x₃) ← m; k x₁ x₂ x₃) = k v₁ v₂ v₃ := by
  rw [hm]
  simp

/-- Step through `m >>= k = Result.ok res` via definitional unification. -/
theorem eq_ok_of_bind {α γ : Type} {m : Result α} {v : α} {k : α → Result γ} {res : γ}
    (hm : m = Result.ok v) (hk : k v = Result.ok res) :
    (m >>= k) = Result.ok res := by
  rw [hm]
  simpa using hk

/-- Step through an Aeneas `?` (`CoreOpsTry.branch`) block on `.Ok v` via definitional unification. -/
theorem eq_ok_of_try_ok {α γ : Type} {m : Result (core.result.Result α I32)} {v : α}
    {k : core.ops.control_flow.ControlFlow (core.result.Result Never I32) α → Result γ}
    {res : γ}
    (hm : m = Result.ok (.Ok v))
    (hk : k (.Continue v) = Result.ok res) :
    (m >>= fun r => core.result.Result.Insts.CoreOpsTry.branch r >>= k) = Result.ok res := by
  rw [hm]
  simpa [core.result.Result.Insts.CoreOpsTry.branch] using hk

/-- Short-circuit an Aeneas `?` (`CoreOpsTry.branch`) block on `.Err e` via definitional unification. -/
theorem eq_ok_of_try_err {α γ : Type} {m : Result (core.result.Result α I32)} {e : I32}
    {k : core.ops.control_flow.ControlFlow (core.result.Result Never I32) α → Result γ}
    {res : γ}
    (hm : m = Result.ok (.Err e))
    (hk : k (.Break (.Err e)) = Result.ok res) :
    (m >>= fun r => core.result.Result.Insts.CoreOpsTry.branch r >>= k) = Result.ok res := by
  rw [hm]
  simpa [core.result.Result.Insts.CoreOpsTry.branch] using hk

end LeanSwe.ProcessSandbox.Init.Proofs
