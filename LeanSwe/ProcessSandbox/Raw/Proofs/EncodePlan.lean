import LeanSwe.ProcessSandbox.Raw.Types
import LeanSwe.ProcessSandbox.Raw.Interface
import LeanSwe.ProcessSandbox.Raw.Impl
import LeanSwe.ProcessSandbox.Raw.SpecTests

namespace LeanSwe.ProcessSandbox.Raw.Proofs

open Core
open Core.NondetTest

private theorem ifEmpty_ne_empty_enc (fallback msg : String) (hf : fallback ≠ "") :
    (if msg.isEmpty then fallback else msg) ≠ "" := by
  split
  · exact hf
  · next h =>
    intro hem
    subst hem
    simp [String.isEmpty] at h

private def LswpHeader : ByteArray := "LSWP0002".toUTF8

private theorem lswpHeader_size : LswpHeader.size = 8 := by decide

private def HeaderPreserved (ba : ByteArray) : Prop :=
  8 ≤ ba.size ∧ ba.extract 0 8 = LswpHeader

private theorem byteArray_ext {a b : ByteArray} (h : a.data = b.data) : a = b := by
  cases a; cases b; congr

private theorem extract_eq_of_data {a : ByteArray} {b e : Nat} (hle : b ≤ e) :
    (a.extract b e).data = a.data.extract b e := by
  have hbe : b + (e - b) = e := by omega
  simp [ByteArray.extract, ByteArray.copySlice, hbe]

private theorem headerPreserved_push {ba : ByteArray} (hp : HeaderPreserved ba) (b : UInt8) :
    HeaderPreserved (ba.push b) := by
  rcases hp with ⟨hsz, hex⟩
  refine ⟨by simp [ByteArray.size_push]; omega, ?_⟩
  apply byteArray_ext
  have hba : (ba.extract 0 8).data = LswpHeader.data := congrArg ByteArray.data hex
  rw [extract_eq_of_data (by omega)] at hba ⊢
  have hpush : (ba.push b).data = ba.data ++ #[b] := by
    change ba.data.push b = ba.data ++ #[b]
    exact Array.push_eq_append
  rw [hpush, Array.extract_append]
  have hszd : 8 ≤ ba.data.size := hsz
  have hzero : 0 - ba.data.size = 0 := by omega
  have heigh : 8 - ba.data.size = 0 := by omega
  rw [hzero, heigh]
  simp [hba]

private theorem headerPreserved_append {a b : ByteArray} (hp : HeaderPreserved a) :
    HeaderPreserved (a ++ b) := by
  rcases hp with ⟨hsz, hex⟩
  refine ⟨by rw [ByteArray.size_append]; omega, ?_⟩
  apply byteArray_ext
  have ha : (a.extract 0 8).data = LswpHeader.data := congrArg ByteArray.data hex
  rw [extract_eq_of_data (by omega)] at ha ⊢
  rw [ByteArray.data_append, Array.extract_append]
  have hszd : 8 ≤ a.data.size := hsz
  have hzero : 0 - a.data.size = 0 := by omega
  have heigh : 8 - a.data.size = 0 := by omega
  rw [hzero, heigh]
  simp [ha]

private theorem headerPreserved_pushU8 {ba : ByteArray} (hp : HeaderPreserved ba) (v : UInt8) :
    HeaderPreserved (Internal.pushU8 ba v) :=
  headerPreserved_push hp v

private theorem headerPreserved_pushU16LE {ba : ByteArray} (hp : HeaderPreserved ba) (v : UInt16) :
    HeaderPreserved (Internal.pushU16LE ba v) :=
  headerPreserved_push (headerPreserved_push hp _) _

private theorem headerPreserved_pushU32LE {ba : ByteArray} (hp : HeaderPreserved ba) (v : UInt32) :
    HeaderPreserved (Internal.pushU32LE ba v) :=
  headerPreserved_push (headerPreserved_push (headerPreserved_push (headerPreserved_push hp _) _) _) _

private theorem headerPreserved_pushU64LE_go :
    ∀ (idx : Nat) (cur : UInt64) (acc : ByteArray),
      HeaderPreserved acc → HeaderPreserved (Internal.pushU64LE.go idx cur acc)
  | 0, _, _, hp => hp
  | k + 1, cur, _acc, hp => headerPreserved_pushU64LE_go k (cur >>> 8) _ (headerPreserved_push hp _)

private theorem headerPreserved_pushU64LE {ba : ByteArray} (hp : HeaderPreserved ba) (v : UInt64) :
    HeaderPreserved (Internal.pushU64LE ba v) :=
  headerPreserved_pushU64LE_go 8 v ba hp

private theorem pushStr_spec (ba : ByteArray) (s : String) (hp : HeaderPreserved ba) :
    match Internal.pushStr ba s with
    | .ok out => HeaderPreserved out
    | .error err => err.kind = .invalidInput ∧ err.message ≠ "" := by
  unfold Internal.pushStr
  simp only [bind, Except.bind, pure, Except.pure]
  by_cases hnul : Internal.hasNulByte s = true
  · simp [hnul, Internal.mapRawError, Model.Internal.mapRawError]
  · simp only [hnul, Bool.false_eq_true, ↓reduceIte]
    by_cases hsz : s.toUTF8.size ≥ UInt32.size
    · simp only [hsz, ↓reduceIte, Internal.mapRawError, Model.Internal.mapRawError]
      exact ⟨trivial, ifEmpty_ne_empty_enc _ _ (by decide)⟩
    · simp only [hsz, ↓reduceIte]
      exact headerPreserved_append (headerPreserved_pushU32LE hp _)

private theorem headerPreserved_init : HeaderPreserved "LSWP0002".toUTF8 := by
  refine ⟨by decide, ?_⟩
  apply byteArray_ext
  decide

private theorem extract_append_right_exact (a b : ByteArray) :
    (a ++ b).extract a.size (a.size + b.size) = b := by
  apply byteArray_ext
  rw [extract_eq_of_data (Nat.le_add_right _ _), ByteArray.data_append]
  change (a.data ++ b.data).extract a.data.size (a.data.size + b.data.size) = b.data
  rw [Array.extract_append_right]
  exact Array.extract_size (xs := b.data)

private def ExceptHeaderInv (r : Except SandboxError ByteArray) : Prop :=
  match r with
  | .error err => err.kind = .invalidInput ∧ err.message ≠ ""
  | .ok ba => HeaderPreserved ba

private theorem pushStr_headerInv {ba : ByteArray} (s : String) (hp : HeaderPreserved ba) :
    ExceptHeaderInv (Internal.pushStr ba s) := by
  have h := pushStr_spec ba s hp
  cases hr : Internal.pushStr ba s <;> simpa [ExceptHeaderInv, hr] using h

private theorem exceptHeaderInv_yield_bind
    {r : Except SandboxError ByteArray} (hr : ExceptHeaderInv r) :
    match (r >>= fun ba' => pure (ForInStep.yield ba')) with
    | .error err => err.kind = .invalidInput ∧ err.message ≠ ""
    | .ok (.yield ba') => HeaderPreserved ba'
    | .ok (.done ba') => HeaderPreserved ba' := by
  cases r <;> simpa [ExceptHeaderInv, bind, Except.bind, pure, Except.pure] using hr

private theorem exceptHeaderInv_yield_bind2
    {r : Except SandboxError ByteArray} (hr : ExceptHeaderInv r)
    {f : ByteArray → Except SandboxError ByteArray}
    (hf : ∀ ba, HeaderPreserved ba → ExceptHeaderInv (f ba)) :
    match (r >>= fun ba => f ba >>= fun ba' => pure (ForInStep.yield ba')) with
    | .error err => err.kind = .invalidInput ∧ err.message ≠ ""
    | .ok (.yield ba') => HeaderPreserved ba'
    | .ok (.done ba') => HeaderPreserved ba' := by
  cases r with
  | error e => simpa [ExceptHeaderInv, bind, Except.bind] using hr
  | ok ba => exact exceptHeaderInv_yield_bind (hf ba hr)

private theorem exceptHeaderInv_bind
    {r : Except SandboxError ByteArray} (hr : ExceptHeaderInv r)
    {k : ByteArray → Except SandboxError ByteArray}
    (hk : ∀ ba, HeaderPreserved ba → ExceptHeaderInv (k ba)) :
    ExceptHeaderInv (r >>= k) := by
  cases r with
  | error err => exact hr
  | ok ba => exact hk ba hr

private theorem exceptHeaderInv_forIn_list {α : Type}
    (xs : List α) (init : ByteArray) (hi : HeaderPreserved init)
    (f : α → ByteArray → Except SandboxError (ForInStep ByteArray))
    (hf : ∀ x ba, HeaderPreserved ba →
      match f x ba with
      | .error err => err.kind = .invalidInput ∧ err.message ≠ ""
      | .ok (.yield ba') => HeaderPreserved ba'
      | .ok (.done ba') => HeaderPreserved ba') :
    ExceptHeaderInv (forIn xs init f) := by
  induction xs generalizing init with
  | nil => exact hi
  | cons x rest ih =>
    rw [List.forIn_cons]
    have hfx := hf x init hi
    dsimp only [bind, Except.bind, pure, Except.pure]
    cases hres : f x init with
    | error err =>
      simp only [hres] at hfx
      exact hfx
    | ok step =>
      simp only [hres] at hfx
      cases step with
      | done b => exact hfx
      | yield b => exact ih b hfx

private theorem exceptHeaderInv_forIn_array {α : Type}
    (arr : Array α) (init : ByteArray) (hi : HeaderPreserved init)
    (f : α → ByteArray → Except SandboxError (ForInStep ByteArray))
    (hf : ∀ x ba, HeaderPreserved ba →
      match f x ba with
      | .error err => err.kind = .invalidInput ∧ err.message ≠ ""
      | .ok (.yield ba') => HeaderPreserved ba'
      | .ok (.done ba') => HeaderPreserved ba') :
    ExceptHeaderInv (forIn arr init f) := by
  rw [← Array.forIn_toList]
  exact exceptHeaderInv_forIn_list arr.toList init hi f hf

private theorem push_getElem_lt {ba : ByteArray} {b : UInt8} {i : Nat}
    (hi : i < ba.size) (hpb : i < (ba.push b).size) :
    (ba.push b)[i]'hpb = ba[i]'hi := by
  change (ba.data.push b)[i]'(by rw [Array.size_push]; exact Nat.lt_succ_of_lt hi) = ba.data[i]'hi
  exact Array.getElem_push_lt hi

private theorem push_getElem_eq {ba : ByteArray} {b : UInt8}
    (hpb : ba.size < (ba.push b).size) :
    (ba.push b)[ba.size]'hpb = b := by
  change (ba.data.push b)[ba.data.size]'(by rw [Array.size_push]; exact Nat.lt_succ_self _) = b
  exact Array.getElem_push_eq

private theorem pushU32LE_size (ba : ByteArray) (v : UInt32) :
    (Internal.pushU32LE ba v).size = ba.size + 4 := by
  simp [Internal.pushU32LE, ByteArray.size_push]

private theorem push4_getElem (ba : ByteArray) (b0 b1 b2 b3 : UInt8) :
    let out := (((ba.push b0).push b1).push b2).push b3
    out[ba.size]'(by dsimp [out]; rw [ByteArray.size_push, ByteArray.size_push, ByteArray.size_push, ByteArray.size_push]; omega) = b0 ∧
    out[ba.size + 1]'(by dsimp [out]; rw [ByteArray.size_push, ByteArray.size_push, ByteArray.size_push, ByteArray.size_push]; omega) = b1 ∧
    out[ba.size + 2]'(by dsimp [out]; rw [ByteArray.size_push, ByteArray.size_push, ByteArray.size_push, ByteArray.size_push]; omega) = b2 ∧
    out[ba.size + 3]'(by dsimp [out]; rw [ByteArray.size_push, ByteArray.size_push, ByteArray.size_push, ByteArray.size_push]; omega) = b3 := by
  have hs1 : (ba.push b0).size = ba.size + 1 := ByteArray.size_push
  have hs2 : ((ba.push b0).push b1).size = ba.size + 2 := by rw [ByteArray.size_push, hs1]
  have hs3 : (((ba.push b0).push b1).push b2).size = ba.size + 3 := by rw [ByteArray.size_push, hs2]
  have hs4 : ((((ba.push b0).push b1).push b2).push b3).size = ba.size + 4 := by rw [ByteArray.size_push, hs3]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [push_getElem_lt (by omega) (by rw [hs4]; omega)]
    rw [push_getElem_lt (by omega) (by rw [hs3]; omega)]
    rw [push_getElem_lt (by omega) (by rw [hs2]; omega)]
    exact push_getElem_eq _
  · rw [push_getElem_lt (by omega) (by rw [hs4]; omega)]
    rw [push_getElem_lt (by omega) (by rw [hs3]; omega)]
    have heq := push_getElem_eq (ba := ba.push b0) (b := b1) (by rw [hs2]; omega)
    simpa [hs1] using heq
  · rw [push_getElem_lt (by omega) (by rw [hs4]; omega)]
    have heq := push_getElem_eq (ba := (ba.push b0).push b1) (b := b2) (by rw [hs3]; omega)
    simpa [hs2] using heq
  · have heq := push_getElem_eq (ba := ((ba.push b0).push b1).push b2) (b := b3) (by rw [hs4]; omega)
    simpa [hs3] using heq

private theorem pushU32LE_getElem (ba : ByteArray) (v : UInt32) :
    let out := Internal.pushU32LE ba v
    out[ba.size]'(by rw [pushU32LE_size]; omega) = UInt8.ofNat (v.toNat % 256) ∧
    out[ba.size + 1]'(by rw [pushU32LE_size]; omega) = UInt8.ofNat ((v.toNat / 256) % 256) ∧
    out[ba.size + 2]'(by rw [pushU32LE_size]; omega) = UInt8.ofNat ((v.toNat / 65536) % 256) ∧
    out[ba.size + 3]'(by rw [pushU32LE_size]; omega) = UInt8.ofNat ((v.toNat / 16777216) % 256) :=
  push4_getElem ba _ _ _ _

private theorem getElemBang_append_pushU32LE (ba seccompBytes : ByteArray) (v : UInt32) :
    let wire := Internal.pushU32LE ba v ++ seccompBytes
    wire[ba.size]! = UInt8.ofNat (v.toNat % 256) ∧
    wire[ba.size + 1]! = UInt8.ofNat ((v.toNat / 256) % 256) ∧
    wire[ba.size + 2]! = UInt8.ofNat ((v.toNat / 65536) % 256) ∧
    wire[ba.size + 3]! = UInt8.ofNat ((v.toNat / 16777216) % 256) := by
  intro wire
  have hsz : (Internal.pushU32LE ba v).size = ba.size + 4 := pushU32LE_size ba v
  have hlt0 : ba.size < wire.size := by dsimp [wire]; rw [ByteArray.size_append, hsz]; omega
  have hlt1 : ba.size + 1 < wire.size := by dsimp [wire]; rw [ByteArray.size_append, hsz]; omega
  have hlt2 : ba.size + 2 < wire.size := by dsimp [wire]; rw [ByteArray.size_append, hsz]; omega
  have hlt3 : ba.size + 3 < wire.size := by dsimp [wire]; rw [ByteArray.size_append, hsz]; omega
  have h0 : wire[ba.size]! = (Internal.pushU32LE ba v)[ba.size]'(by rw [hsz]; omega) := by
    rw [getElem!_pos wire ba.size hlt0]
    exact ByteArray.getElem_append_left (by rw [hsz]; omega)
  have h1 : wire[ba.size + 1]! = (Internal.pushU32LE ba v)[ba.size + 1]'(by rw [hsz]; omega) := by
    rw [getElem!_pos wire (ba.size + 1) hlt1]
    exact ByteArray.getElem_append_left (by rw [hsz]; omega)
  have h2 : wire[ba.size + 2]! = (Internal.pushU32LE ba v)[ba.size + 2]'(by rw [hsz]; omega) := by
    rw [getElem!_pos wire (ba.size + 2) hlt2]
    exact ByteArray.getElem_append_left (by rw [hsz]; omega)
  have h3 : wire[ba.size + 3]! = (Internal.pushU32LE ba v)[ba.size + 3]'(by rw [hsz]; omega) := by
    rw [getElem!_pos wire (ba.size + 3) hlt3]
    exact ByteArray.getElem_append_left (by rw [hsz]; omega)
  rw [h0, h1, h2, h3]
  exact pushU32LE_getElem ba v

private theorem encodePlan_body_inv (plan : CompiledSandboxPlan) :
    ExceptHeaderInv (Internal.encodePlanPrefix plan) := by
  dsimp +zeta only [Internal.encodePlanPrefix, bind, Except.bind, pure, Except.pure]
  have h0 : HeaderPreserved
      (Internal.pushU64LE
        (Internal.pushU8
          (Internal.pushU64LE
            (Internal.pushU8
              (Internal.pushU64LE
                (Internal.pushU8
                  (Internal.pushU64LE
                    (Internal.pushU8
                      (Internal.pushU64LE
                        (Internal.pushU8
                          (Internal.pushU8
                            (Internal.pushU8
                              (Internal.pushU8
                                (Internal.pushU8
                                  (Internal.pushU8
                                    (Internal.pushU8
                                      (Internal.pushU8
                                        (Internal.pushU8
                                          (Internal.pushU32LE
                                            (Internal.pushU8
                                              (Internal.pushU8
                                                (Internal.pushU8
                                                  (Internal.pushU8
                                                    (Internal.pushU8 "LSWP0002".toUTF8
                                                      (Internal.boolU8 plan.emptyRoot))
                                                    (Internal.boolU8 plan.unshareAllNamespaces))
                                                  (Internal.boolU8 plan.mountFreshProc))
                                                (Internal.boolU8 plan.mountSafeDev))
                                              (Internal.boolU8 plan.directCgroupV2Fs))
                                            (UInt32.ofNat (Nat.min plan.landlockMinAbi (UInt32.size - 1))))
                                          (Internal.boolU8 plan.allowBoxLocalhost))
                                        (Internal.boolU8 plan.blockUnixSocketAndSmc))
                                      (Internal.boolU8 plan.allowAnonUnixSocketpair))
                                    (Internal.boolU8 plan.clone3EnosysFallback))
                                  (Internal.boolU8 plan.seccompStrictDenylist))
                                (Internal.boolU8 plan.noNewPrivs))
                              (Internal.boolU8 plan.rlimitCoreZero))
                            (Internal.boolU8 plan.subreaperAndPdeathsig))
                          (Internal.boolU8 plan.cleanEnv))
                        (Internal.natToUInt64Sat plan.limits.timeoutMs))
                      (Internal.boolU8 plan.limits.memoryMaxBytes.isSome))
                    (Internal.natToUInt64Sat (plan.limits.memoryMaxBytes.getD 0)))
                  (Internal.boolU8 plan.limits.pidsMax.isSome))
                (Internal.natToUInt64Sat (plan.limits.pidsMax.getD 0)))
              (Internal.boolU8 plan.limits.fileSizeMaxBytes.isSome))
            (Internal.natToUInt64Sat (plan.limits.fileSizeMaxBytes.getD 0)))
          (Internal.boolU8 plan.limits.maxOutputBytes.isSome))
        (Internal.natToUInt64Sat (plan.limits.maxOutputBytes.getD 0))) := by
    apply headerPreserved_pushU64LE
    apply headerPreserved_pushU8
    apply headerPreserved_pushU64LE
    apply headerPreserved_pushU8
    apply headerPreserved_pushU64LE
    apply headerPreserved_pushU8
    apply headerPreserved_pushU64LE
    apply headerPreserved_pushU8
    apply headerPreserved_pushU64LE
    apply headerPreserved_pushU8
    apply headerPreserved_pushU8
    apply headerPreserved_pushU8
    apply headerPreserved_pushU8
    apply headerPreserved_pushU8
    apply headerPreserved_pushU8
    apply headerPreserved_pushU8
    apply headerPreserved_pushU8
    apply headerPreserved_pushU8
    apply headerPreserved_pushU32LE
    apply headerPreserved_pushU8
    apply headerPreserved_pushU8
    apply headerPreserved_pushU8
    apply headerPreserved_pushU8
    apply headerPreserved_pushU8
    exact headerPreserved_init
  refine exceptHeaderInv_bind (pushStr_headerInv plan.program h0) fun ba hba => ?_
  refine exceptHeaderInv_bind (pushStr_headerInv plan.cwd hba) fun ba hba => ?_
  refine exceptHeaderInv_bind (exceptHeaderInv_forIn_array plan.args _ (headerPreserved_pushU32LE hba _) _ ?_) fun ba hba => ?_
  · intro a ba h
    exact exceptHeaderInv_yield_bind (pushStr_headerInv a h)
  refine exceptHeaderInv_bind (exceptHeaderInv_forIn_array plan.env _ (headerPreserved_pushU32LE hba _) _ ?_) fun ba hba => ?_
  · intro kv ba h
    exact exceptHeaderInv_yield_bind2 (pushStr_headerInv kv.1 h) fun ba1 h1 => pushStr_headerInv kv.2 h1
  refine exceptHeaderInv_bind (exceptHeaderInv_forIn_array plan.presetSystemEntries _ (headerPreserved_pushU32LE hba _) _ ?_) fun ba hba => ?_
  · intro e ba h
    cases e with
    | readOnlyDir p =>
      exact exceptHeaderInv_yield_bind (pushStr_headerInv p (headerPreserved_pushU8 h 0))
    | topSymlink lp tgt =>
      exact exceptHeaderInv_yield_bind2 (pushStr_headerInv lp (headerPreserved_pushU8 h 1))
        fun ba1 h1 => pushStr_headerInv tgt h1
  refine exceptHeaderInv_bind (exceptHeaderInv_forIn_array plan.presetEtcPaths _ (headerPreserved_pushU32LE hba _) _ ?_) fun ba hba => ?_
  · intro p ba h
    exact exceptHeaderInv_yield_bind (pushStr_headerInv p h)
  refine exceptHeaderInv_bind (exceptHeaderInv_forIn_array plan.maskedPresetPaths _ (headerPreserved_pushU32LE hba _) _ ?_) fun ba hba => ?_
  · intro m ba h
    exact exceptHeaderInv_yield_bind (pushStr_headerInv m h)
  refine exceptHeaderInv_bind (exceptHeaderInv_forIn_array plan.userMounts _ (headerPreserved_pushU32LE hba _) _ ?_) fun ba hba => ?_
  · intro m ba h
    cases m with
    | readOnly hp bp =>
      exact exceptHeaderInv_yield_bind2 (pushStr_headerInv hp (headerPreserved_pushU8 h 0))
        fun ba1 h1 => pushStr_headerInv bp h1
    | readWrite hp bp =>
      exact exceptHeaderInv_yield_bind2 (pushStr_headerInv hp (headerPreserved_pushU8 h 1))
        fun ba1 h1 => pushStr_headerInv bp h1
    | scratch bp =>
      exact exceptHeaderInv_yield_bind (pushStr_headerInv bp (headerPreserved_pushU8 h 2))
  refine exceptHeaderInv_forIn_array plan.portForwards _ (headerPreserved_pushU32LE hba _) _ ?_
  intro pf ba h
  exact headerPreserved_pushU16LE (headerPreserved_pushU16LE h _) _

private theorem encodePlan_inv (plan : CompiledSandboxPlan) (seccompBytes : ByteArray) :
    match Internal.encodePlan plan seccompBytes with
    | .error err => err.kind = .invalidInput ∧ err.message ≠ ""
    | .ok wire =>
      0 < seccompBytes.size ∧
      seccompBytes.size % 8 = 0 ∧
      seccompBytes.size ≤ 8 * SECCOMP_MAX_INSNS ∧
      wire.size ≥ 12 + seccompBytes.size ∧
      wire.extract 0 8 = "LSWP0002".toUTF8 ∧
      wire[wire.size - (4 + seccompBytes.size)]! = UInt8.ofNat ((seccompBytes.size / 8) % 256) ∧
      wire[wire.size - (4 + seccompBytes.size) + 1]! = UInt8.ofNat (((seccompBytes.size / 8) / 256) % 256) ∧
      wire[wire.size - (4 + seccompBytes.size) + 2]! = UInt8.ofNat (((seccompBytes.size / 8) / 65536) % 256) ∧
      wire[wire.size - (4 + seccompBytes.size) + 3]! = UInt8.ofNat (((seccompBytes.size / 8) / 16777216) % 256) ∧
      wire.extract (wire.size - seccompBytes.size) wire.size = seccompBytes := by
  unfold Internal.encodePlan
  by_cases h1 : (!plan.emptyRoot || !plan.unshareAllNamespaces || !plan.mountFreshProc || !plan.mountSafeDev ||
      !plan.directCgroupV2Fs || decide (plan.landlockMinAbi < 4) || !plan.blockUnixSocketAndSmc ||
      !plan.allowAnonUnixSocketpair || !plan.clone3EnosysFallback || !plan.seccompStrictDenylist ||
      !plan.noNewPrivs || !plan.rlimitCoreZero || !plan.subreaperAndPdeathsig || !plan.cleanEnv) = true
  · simp only [h1, ↓reduceIte, Internal.mapRawError, Model.Internal.mapRawError]
    exact ⟨trivial, ifEmpty_ne_empty_enc _ _ (by decide)⟩
  · simp only [h1, Bool.false_eq_true, ↓reduceIte]
    by_cases h2 : (plan.program.isEmpty || plan.cwd.isEmpty) = true
    · simp only [h2, ↓reduceIte, Internal.mapRawError, Model.Internal.mapRawError]
      exact ⟨trivial, ifEmpty_ne_empty_enc _ _ (by decide)⟩
    · simp only [h2, Bool.false_eq_true, ↓reduceIte]
      by_cases h3 : (plan.limits.timeoutMs == 0 || plan.limits.memoryMaxBytes == some 0 || plan.limits.pidsMax == some 0) = true
      · simp only [h3, ↓reduceIte, Internal.mapRawError, Model.Internal.mapRawError]
        exact ⟨trivial, ifEmpty_ne_empty_enc _ _ (by decide)⟩
      · simp only [h3, Bool.false_eq_true, ↓reduceIte]
        by_cases h4 : (plan.portForwards.any fun pf => pf.boxPort == 0 || pf.hostPort == 0) = true
        · simp only [h4, ↓reduceIte, Internal.mapRawError, Model.Internal.mapRawError]
          exact ⟨trivial, ifEmpty_ne_empty_enc _ _ (by decide)⟩
        · simp only [h4, Bool.false_eq_true, ↓reduceIte]
          by_cases hsec : (seccompBytes.size == 0 || seccompBytes.size % 8 != 0 || decide (seccompBytes.size > 8 * SECCOMP_MAX_INSNS)) = true
          · simp only [hsec, ↓reduceIte, Internal.mapRawError, Model.Internal.mapRawError]
            exact ⟨trivial, ifEmpty_ne_empty_enc _ _ (by decide)⟩
          · simp only [hsec, Bool.false_eq_true, ↓reduceIte]
            have hpos : 0 < seccompBytes.size := by
              by_cases h0 : seccompBytes.size = 0
              · simp [h0] at hsec
              · omega
            have hmod : seccompBytes.size % 8 = 0 := by
              by_cases hm : seccompBytes.size % 8 = 0
              · exact hm
              · have hne : (seccompBytes.size % 8 != 0) = true := by simp [hm]
                simp [hne] at hsec
            have hmax : seccompBytes.size ≤ 8 * SECCOMP_MAX_INSNS := by
              by_cases hl : seccompBytes.size ≤ 8 * SECCOMP_MAX_INSNS
              · exact hl
              · have hgt : seccompBytes.size > 8 * SECCOMP_MAX_INSNS := by omega
                simp [hgt] at hsec
            have hbody := encodePlan_body_inv plan
            have hu32 : (UInt32.ofNat (seccompBytes.size / 8)).toNat = seccompBytes.size / 8 := by
              have hdiv : seccompBytes.size / 8 < UInt32.size := by
                have hmax' : seccompBytes.size ≤ 8 * 160 := hmax
                have hs : UInt32.size = 4294967296 := rfl
                omega
              simp [Nat.mod_eq_of_lt hdiv]
            cases hres : Internal.encodePlanPrefix plan with
            | error err =>
              rw [hres] at hbody
              simpa [bind, Except.bind, hres, ExceptHeaderInv] using hbody
            | ok ba =>
              rw [hres] at hbody
              change HeaderPreserved ba at hbody
              have hwire := headerPreserved_append
                (headerPreserved_pushU32LE hbody (UInt32.ofNat (seccompBytes.size / 8))) (b := seccompBytes)
              have hpushSz : (Internal.pushU32LE ba (UInt32.ofNat (seccompBytes.size / 8))).size = ba.size + 4 :=
                pushU32LE_size ba _
              have hwireSz : (Internal.pushU32LE ba (UInt32.ofNat (seccompBytes.size / 8)) ++ seccompBytes).size =
                  ba.size + 4 + seccompBytes.size := by
                rw [ByteArray.size_append, hpushSz]
              have hba8 : 8 ≤ ba.size := hbody.1
              have hge : (Internal.pushU32LE ba (UInt32.ofNat (seccompBytes.size / 8)) ++ seccompBytes).size ≥
                  12 + seccompBytes.size := by omega
              have hoff : (Internal.pushU32LE ba (UInt32.ofNat (seccompBytes.size / 8)) ++ seccompBytes).size -
                  (4 + seccompBytes.size) = ba.size := by omega
              have hsecOff : (Internal.pushU32LE ba (UInt32.ofNat (seccompBytes.size / 8)) ++ seccompBytes).size -
                  seccompBytes.size = (Internal.pushU32LE ba (UInt32.ofNat (seccompBytes.size / 8))).size := by
                rw [hwireSz, hpushSz]; omega
              have hbytes := getElemBang_append_pushU32LE ba seccompBytes (UInt32.ofNat (seccompBytes.size / 8))
              rw [hu32] at hbytes
              have hext := extract_append_right_exact
                (Internal.pushU32LE ba (UInt32.ofNat (seccompBytes.size / 8))) seccompBytes
              rw [← ByteArray.size_append] at hext
              simp only [bind, Except.bind, pure, Except.pure] at hwire hext ⊢
              refine ⟨hpos, hmod, hmax, hge, hwire.2, ?_, ?_, ?_, ?_, ?_⟩
              · rw [hoff]; exact hbytes.1
              · rw [hoff]; exact hbytes.2.1
              · rw [hoff]; exact hbytes.2.2.1
              · rw [hoff]; exact hbytes.2.2.2
              · rw [hsecOff]; exact hext

private theorem pushStr_literal_ok (ba : ByteArray) (s : String)
    (hnul : Internal.hasNulByte s = false) (hsz : decide (s.utf8ByteSize ≥ UInt32.size) = false) :
    Internal.pushStr ba s = .ok (Internal.pushU32LE ba (UInt32.ofNat s.utf8ByteSize) ++ s.toUTF8) := by
  have hnot : ¬ (UInt32.size ≤ s.utf8ByteSize) := of_decide_eq_false hsz
  simp [Internal.pushStr, hnul, hnot, pure, Except.pure]

private theorem encodePlan_defaultPlan_ok (seccompBytes : ByteArray)
    (hp : 0 < seccompBytes.size) (hm : seccompBytes.size % 8 = 0)
    (hx : seccompBytes.size ≤ 8 * SECCOMP_MAX_INSNS) :
    ∃ wire, defaultOps.encodePlan { program := "/bin/true" } seccompBytes = .ok wire := by
  have h5 : (seccompBytes.size == 0 || seccompBytes.size % 8 != 0 || decide (seccompBytes.size > 8 * SECCOMP_MAX_INSNS)) = false := by
    have ha : (seccompBytes.size == 0) = false := by simp [Nat.ne_of_gt hp]
    have hb : (seccompBytes.size % 8 != 0) = false := by simp [hm]
    have hc : decide (seccompBytes.size > 8 * SECCOMP_MAX_INSNS) = false :=
      decide_eq_false (Nat.not_lt.mpr hx)
    simp [ha, hb, hc]
  have hp1 := fun ba => pushStr_literal_ok ba "/bin/true" (by decide) (by decide)
  have hp3 := fun ba => pushStr_literal_ok ba "PATH" (by decide) (by decide)
  have hp4 := fun ba => pushStr_literal_ok ba "/usr/bin:/bin" (by decide) (by decide)
  have hp5 := fun ba => pushStr_literal_ok ba "/tmp" (by decide) (by decide)
  simp [defaultOps, Internal.encodePlan, Internal.encodePlanPrefix, h5,
    hp1, hp3, hp4, hp5, ← Array.forIn_toList, List.forIn_cons, List.forIn_nil,
    bind, Except.bind, pure, Except.pure]

/-- Proof of `test_psandboxRaw_encodePlan_validatesSeccompFilterAndFramesLswp0002` for `defaultOps`. -/
theorem proof_psandboxRaw_encodePlan_validatesSeccompFilterAndFramesLswp0002 :
    AllPass (test_psandboxRaw_encodePlan_validatesSeccompFilterAndFramesLswp0002 defaultOps) := by
  dsimp only [test_psandboxRaw_encodePlan_validatesSeccompFilterAndFramesLswp0002, Bind.bind]
  intro planBad badSeccomp hbad
  have hinv1 := encodePlan_inv planBad badSeccomp
  cases hres1 : defaultOps.encodePlan planBad badSeccomp with
  | ok wire =>
    have hres1' : Internal.encodePlan planBad badSeccomp = .ok wire := hres1
    rw [hres1'] at hinv1
    omega
  | error err =>
    have hres1' : Internal.encodePlan planBad badSeccomp = .error err := hres1
    rw [hres1'] at hinv1
    dsimp only [assert]
    refine ⟨hinv1, ?_⟩
    intro goodSeccomp hgood
    rcases hgood with ⟨hp, hm, hx⟩
    rcases encodePlan_defaultPlan_ok goodSeccomp hp hm hx with ⟨wireOk, hres2⟩
    rw [hres2]
    dsimp only
    intro planAny seccompAny
    have hinv3 := encodePlan_inv planAny seccompAny
    cases hres3 : defaultOps.encodePlan planAny seccompAny with
    | error err3 =>
      have hres3' : Internal.encodePlan planAny seccompAny = .error err3 := hres3
      rw [hres3'] at hinv3
      simpa [assert, hres3] using hinv3
    | ok wire3 =>
      have hres3' : Internal.encodePlan planAny seccompAny = .ok wire3 := hres3
      rw [hres3'] at hinv3
      simpa [assert, hres3] using hinv3

/-- Non-vacuity `CanReach` witness for `test_psandboxRaw_encodePlan_validatesSeccompFilterAndFramesLswp0002`. -/
theorem reach_psandboxRaw_encodePlan_validatesSeccompFilterAndFramesLswp0002 :
    CanReach (test_psandboxRaw_encodePlan_validatesSeccompFilterAndFramesLswp0002 defaultOps) := by
  let zeroSeccomp : ByteArray := ByteArray.mk #[0, 0, 0, 0, 0, 0, 0, 0]
  dsimp only [test_psandboxRaw_encodePlan_validatesSeccompFilterAndFramesLswp0002, Bind.bind]
  refine ⟨{ program := "/bin/true" }, ByteArray.empty, Or.inl rfl, ?_⟩
  have hinv1 := encodePlan_inv { program := "/bin/true" } ByteArray.empty
  cases hres1 : defaultOps.encodePlan { program := "/bin/true" } ByteArray.empty with
  | ok wire =>
    have hres1' : Internal.encodePlan { program := "/bin/true" } ByteArray.empty = .ok wire := hres1
    rw [hres1'] at hinv1
    have hgt : 0 < ByteArray.empty.size := hinv1.1
    have hzero : ByteArray.empty.size = 0 := rfl
    omega
  | error err =>
    have hres1' : Internal.encodePlan { program := "/bin/true" } ByteArray.empty = .error err := hres1
    rw [hres1'] at hinv1
    refine ⟨hinv1, zeroSeccomp, ⟨by decide, by decide, by decide⟩, ?_⟩
    rcases encodePlan_defaultPlan_ok zeroSeccomp (by decide) (by decide) (by decide) with ⟨wireOk, hres2⟩
    rw [hres2]
    dsimp only
    refine ⟨{ program := "/bin/true" }, zeroSeccomp, ?_⟩
    have hinv3 := encodePlan_inv { program := "/bin/true" } zeroSeccomp
    cases hres3 : defaultOps.encodePlan { program := "/bin/true" } zeroSeccomp with
    | error err3 =>
      have hres3' : Internal.encodePlan { program := "/bin/true" } zeroSeccomp = .error err3 := hres3
      rw [hres3'] at hinv3
      dsimp only at hinv3
      simp [assert, hres3]
      exact hinv3
    | ok wire3 =>
      have hres3' : Internal.encodePlan { program := "/bin/true" } zeroSeccomp = .ok wire3 := hres3
      rw [hres3'] at hinv3
      dsimp only at hinv3
      simp [assert, hres3]
      exact hinv3

end LeanSwe.ProcessSandbox.Raw.Proofs
