import Core.Obeys
import LeanSwe.Uuid.Types
import LeanSweProofs.Uuid.Model

/-!
# Targeted Dummy Mutants and Satisfiability Witness for `LeanSwe.Uuid.Model`

Proves that broken `UuidApiM` implementations (`constZeroUuidApi`,
`alwaysErrUuidApi`) fail `LeanSwe.Uuid.Model.allowedPkgStep` under
`Core.ObeysStep`, and proves `LeanSwe.Uuid.Model.allowedPkgStep` is
satisfiable via an explicit reference implementation `refUuidApi`.
-/

namespace ModelMutants.Uuid

open LeanSwe.Uuid
open LeanSwe.Uuid.Model

private theorem stateM_map_run {W α β : Type} (f : α → β) (x : StateM W α) (w : W) :
    (f <$> x).run w = (f (x.run w).1, (x.run w).2) := rfl

private theorem stateM_bind_run {W α β : Type} (x : StateM W α) (f : α → StateM W β) (w : W) :
    (x >>= f).run w = (f (x.run w).1).run (x.run w).2 := rfl

private theorem stateM_pure_run {W α : Type} (a : α) (w : W) :
    (pure a : StateM W α).run w = (a, w) := rfl

/-- Constant RFC 4122 v4 UUID `00000000-0000-4000-8000-000000000000`. -/
def zeroV4Uuid : Uuid :=
  { bytes := ByteArray.mk #[0, 0, 0, 0, 0, 0, 0x40, 0, 0x80, 0, 0, 0, 0, 0, 0, 0] }

/-- `zeroV4Uuid` is a valid RFC 4122 version 4 UUID. -/
theorem zeroV4Uuid_isValidV4 : isValidV4Uuid zeroV4Uuid = true := by
  decide

/-- Broken dummy `UuidApiM` whose `getUuid` always returns `.ok zeroV4Uuid`. -/
def constZeroUuidApi {m : Type → Type} [Monad m] : UuidApiM m :=
  { mapRawError := mapRawError
    fromRandomBytes := fromRandomBytes
    toString := toString
    toHex := toHex
    parse := parse
    parseHex := parseHex
    isValid := isValid
    getUuid := pure (.ok zeroV4Uuid) }

/-- Broken dummy `UuidApiM` whose `getUuid` always returns `.error`. -/
def alwaysErrUuidApi {m : Type → Type} [Monad m] : UuidApiM m :=
  { mapRawError := mapRawError
    fromRandomBytes := fromRandomBytes
    toString := toString
    toHex := toHex
    parse := parse
    parseHex := parseHex
    isValid := isValid
    getUuid := pure (.error { kind := .entropyFailed, message := "uuid generator unavailable" }) }

/-- No `UuidApiM (StateM W)` whose `getUuid` always returns `.ok zeroV4Uuid` can satisfy
    `allowedPkgStep` from any state `w0` with room for two consecutive draws. -/
theorem any_constZeroUuid_fails_model {W : Type} (proj : W → UuidModelState)
    (api : UuidApiM (StateM W))
    (hConst : ∀ w : W, (api.getUuid.run w).1 = .ok zeroV4Uuid)
    (w0 : W) (hRoom : (proj w0).seen.length + 1 < maxValidV4Uuids) :
    ¬ Core.ObeysStep proj pkgWf (execPkgStep api) allowedPkgStep := by
  intro hObeys
  have hwf0 : pkgWf (proj w0) = true := by
    unfold pkgWf
    exact decide_eq_true (by omega)
  have hStep1 := hObeys w0 .getUuid hwf0
  dsimp only [execPkgStep] at hStep1
  rw [stateM_map_run] at hStep1
  cases h1 : api.getUuid.run w0 with
  | mk res1 w1 =>
    have hr1 : res1 = .ok zeroV4Uuid := by
      have hc := hConst w0
      rw [h1] at hc
      exact hc
    subst hr1
    rw [h1] at hStep1
    dsimp only [allowedPkgStep] at hStep1
    rcases hStep1 with ⟨_, _, hSeen1⟩
    have hwf1 : pkgWf (proj w1) = true := by
      unfold pkgWf
      rw [hSeen1, List.length_cons]
      exact decide_eq_true hRoom
    have hStep2 := hObeys w1 .getUuid hwf1
    dsimp only [execPkgStep] at hStep2
    rw [stateM_map_run] at hStep2
    cases h2 : api.getUuid.run w1 with
    | mk res2 w2 =>
      have hr2 : res2 = .ok zeroV4Uuid := by
        have hc := hConst w1
        rw [h2] at hc
        exact hc
      subst hr2
      rw [h2] at hStep2
      dsimp only [allowedPkgStep] at hStep2
      rcases hStep2 with ⟨_, hNotMem, _⟩
      rw [hSeen1] at hNotMem
      exact hNotMem List.mem_cons_self

/-- `constZeroUuidApi` fails `allowedPkgStep` under `Core.ObeysStepId`. -/
theorem constZeroUuidApi_fails_model_id :
    ¬ Core.ObeysStepId pkgWf (execPkgStep (constZeroUuidApi (m := StateM UuidModelState)))
      allowedPkgStep :=
  any_constZeroUuid_fails_model id constZeroUuidApi (fun _ => rfl) {} (by decide)

/-- `constZeroUuidApi` fails `allowedPkgStep` under any projection with an empty initial state. -/
theorem constZeroUuidApi_fails_model_from_initial {W : Type} (proj : W → UuidModelState)
    (w0 : W) (hInit : proj w0 = {}) :
    ¬ Core.ObeysStep proj pkgWf (execPkgStep (constZeroUuidApi (m := StateM W))) allowedPkgStep :=
  any_constZeroUuid_fails_model proj constZeroUuidApi (fun _ => rfl) w0
    (by rw [hInit]; decide)

/-- No `UuidApiM (StateM W)` whose `getUuid` returns `.error` on a well-formed state can satisfy
    `allowedPkgStep`. -/
theorem any_alwaysErrUuid_fails_model {W : Type} (proj : W → UuidModelState)
    (api : UuidApiM (StateM W))
    (w0 : W) (hw0 : pkgWf (proj w0) = true)
    (err : UuidError) (hErr : (api.getUuid.run w0).1 = .error err) :
    ¬ Core.ObeysStep proj pkgWf (execPkgStep api) allowedPkgStep := by
  intro hObeys
  have hStep := hObeys w0 .getUuid hw0
  dsimp only [execPkgStep] at hStep
  rw [stateM_map_run] at hStep
  cases h1 : api.getUuid.run w0 with
  | mk res1 w1 =>
    have hr1 : res1 = .error err := by
      rw [h1] at hErr
      exact hErr
    subst hr1
    rw [h1] at hStep
    exact hStep

/-- `alwaysErrUuidApi` fails `allowedPkgStep` under `Core.ObeysStepId`. -/
theorem alwaysErrUuidApi_fails_model_id :
    ¬ Core.ObeysStepId pkgWf (execPkgStep (alwaysErrUuidApi (m := StateM UuidModelState)))
      allowedPkgStep :=
  any_alwaysErrUuid_fails_model id alwaysErrUuidApi {} (by decide)
    { kind := .entropyFailed, message := "uuid generator unavailable" } rfl

/-- `alwaysErrUuidApi` fails `allowedPkgStep` under any projection with a well-formed state. -/
theorem alwaysErrUuidApi_fails_model_any {W : Type} (proj : W → UuidModelState)
    (w0 : W) (hw0 : pkgWf (proj w0) = true) :
    ¬ Core.ObeysStep proj pkgWf (execPkgStep (alwaysErrUuidApi (m := StateM W))) allowedPkgStep :=
  any_alwaysErrUuid_fails_model proj alwaysErrUuidApi w0 hw0
    { kind := .entropyFailed, message := "uuid generator unavailable" } rfl

/-- Encode `n` (bijectively for `n < 2 ^ 122`) into a valid RFC 4122 v4 `Uuid`. -/
def uuidOfNat (n : Nat) : Uuid :=
  let b0 := n % 256; let n1 := n / 256
  let b1 := n1 % 256; let n2 := n1 / 256
  let b2 := n2 % 256; let n3 := n2 / 256
  let b3 := n3 % 256; let n4 := n3 / 256
  let b4 := n4 % 256; let n5 := n4 / 256
  let b5 := n5 % 256; let n6 := n5 / 256
  let b6 := 64 + n6 % 16; let n7 := n6 / 16
  let b7 := n7 % 256; let n8 := n7 / 256
  let b8 := 128 + n8 % 64; let n9 := n8 / 64
  let b9 := n9 % 256; let n10 := n9 / 256
  let b10 := n10 % 256; let n11 := n10 / 256
  let b11 := n11 % 256; let n12 := n11 / 256
  let b12 := n12 % 256; let n13 := n12 / 256
  let b13 := n13 % 256; let n14 := n13 / 256
  let b14 := n14 % 256; let n15 := n14 / 256
  let b15 := n15 % 256
  { bytes := ByteArray.mk #[
      UInt8.ofNat b0, UInt8.ofNat b1, UInt8.ofNat b2, UInt8.ofNat b3,
      UInt8.ofNat b4, UInt8.ofNat b5, UInt8.ofNat b6, UInt8.ofNat b7,
      UInt8.ofNat b8, UInt8.ofNat b9, UInt8.ofNat b10, UInt8.ofNat b11,
      UInt8.ofNat b12, UInt8.ofNat b13, UInt8.ofNat b14, UInt8.ofNat b15] }

/-- Decode the 122 payload bits of a `Uuid` back into `Nat` (left inverse of `uuidOfNat` on `< 2 ^ 122`). -/
def natOfUuid (u : Uuid) : Nat :=
  let g (i : Nat) : Nat := (u.bytes[i]!).toNat
  g 0 + 256 * (g 1 + 256 * (g 2 + 256 * (g 3 + 256 * (g 4 + 256 * (g 5 + 256 *
    (g 6 % 16 + 16 * (g 7 + 256 * (g 8 % 64 + 64 * (g 9 + 256 * (g 10 + 256 *
      (g 11 + 256 * (g 12 + 256 * (g 13 + 256 * (g 14 + 256 * g 15))))))))))))))

private theorem v4_byte6_mask : ∀ r : Fin 16,
    (UInt8.ofNat (64 + r.val) &&& (0xF0 : UInt8)) = (0x40 : UInt8) := by
  decide

private theorem v4_byte8_mask : ∀ r : Fin 64,
    (UInt8.ofNat (128 + r.val) &&& (0xC0 : UInt8)) = (0x80 : UInt8) := by
  decide

private theorem uuidOfNat_isValidV4 (n : Nat) : isValidV4Uuid (uuidOfNat n) = true := by
  unfold isValidV4Uuid uuidOfNat
  have h6 : (UInt8.ofNat (64 + n / 256 / 256 / 256 / 256 / 256 / 256 % 16) &&& (0xF0 : UInt8)) = (0x40 : UInt8) :=
    v4_byte6_mask ⟨_, Nat.mod_lt _ (by decide)⟩
  have h8 : (UInt8.ofNat (128 + n / 256 / 256 / 256 / 256 / 256 / 256 / 16 / 256 % 64) &&& (0xC0 : UInt8)) = (0x80 : UInt8) :=
    v4_byte8_mask ⟨_, Nat.mod_lt _ (by decide)⟩
  change (16 == 16 &&
    ((UInt8.ofNat (64 + n / 256 / 256 / 256 / 256 / 256 / 256 % 16) &&& (0xF0 : UInt8)) == (0x40 : UInt8)) &&
    ((UInt8.ofNat (128 + n / 256 / 256 / 256 / 256 / 256 / 256 / 16 / 256 % 64) &&& (0xC0 : UInt8)) == (0x80 : UInt8))) = true
  rw [h6, h8]
  rfl

private theorem natOfUuid_mk16 (b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 : UInt8) :
    natOfUuid { bytes := ByteArray.mk #[b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15] } =
      b0.toNat + 256 * (b1.toNat + 256 * (b2.toNat + 256 * (b3.toNat + 256 * (b4.toNat + 256 * (b5.toNat + 256 *
        (b6.toNat % 16 + 16 * (b7.toNat + 256 * (b8.toNat % 64 + 64 * (b9.toNat + 256 * (b10.toNat + 256 *
          (b11.toNat + 256 * (b12.toNat + 256 * (b13.toNat + 256 * (b14.toNat + 256 * b15.toNat)))))))))))))) :=
  rfl

private theorem natOfUuid_uuidOfNat (n : Nat) (hn : n < maxValidV4Uuids) :
    natOfUuid (uuidOfNat n) = n := by
  unfold uuidOfNat
  rw [natOfUuid_mk16]
  simp only [UInt8.toNat_ofNat']
  unfold maxValidV4Uuids at hn
  omega

/-- Return `true` iff `u` occurs in `seen` using propositional equality (`DecidableEq Uuid`). -/
def hasUuid (u : Uuid) : List Uuid → Bool
  | [] => false
  | x :: xs => if x = u then true else hasUuid u xs

private theorem hasUuid_iff_mem (u : Uuid) : ∀ seen : List Uuid, hasUuid u seen = true ↔ u ∈ seen
  | [] => by simp [hasUuid]
  | x :: xs => by
    unfold hasUuid
    split
    · rename_i h; subst h; simp
    · rename_i h; simp [hasUuid_iff_mem u xs, Ne.symm h]

/-- Bounded linear search for an unseen RFC 4122 v4 UUID starting at index `k`. -/
def findFreshAux (seen : List Uuid) (k : Nat) : Nat → Uuid
  | 0 => uuidOfNat k
  | fuel' + 1 =>
    let cand := uuidOfNat k
    if hasUuid cand seen then findFreshAux seen (k + 1) fuel' else cand

/-- Constructive fresh RFC 4122 v4 UUID selector guaranteed to avoid `seen` whenever `seen.length < 2 ^ 122`. -/
def pickFreshUuid (seen : List Uuid) : Uuid :=
  findFreshAux seen 0 seen.length

private theorem findFreshAux_isValidV4 (seen : List Uuid) :
    ∀ (fuel k : Nat), isValidV4Uuid (findFreshAux seen k fuel) = true
  | 0, k => uuidOfNat_isValidV4 k
  | fuel' + 1, k => by
    dsimp only [findFreshAux]
    cases hc : hasUuid (uuidOfNat k) seen with
    | true => exact findFreshAux_isValidV4 seen fuel' (k + 1)
    | false => exact uuidOfNat_isValidV4 k

private theorem findFreshAux_mem_imp (seen : List Uuid) :
    ∀ (fuel k : Nat), findFreshAux seen k fuel ∈ seen →
      ∀ j, k ≤ j → j ≤ k + fuel → uuidOfNat j ∈ seen
  | 0, k, hmem, j, hlo, hhi => by
    have hj : j = k := by omega
    subst hj
    exact hmem
  | fuel' + 1, k, hmem, j, hlo, hhi => by
    dsimp only [findFreshAux] at hmem
    cases hc : hasUuid (uuidOfNat k) seen with
    | true =>
      simp only [hc, ↓reduceIte] at hmem
      by_cases hjk : j = k
      · subst hjk
        exact (hasUuid_iff_mem _ seen).mp hc
      · exact findFreshAux_mem_imp seen fuel' (k + 1) hmem j (by omega) (by omega)
    | false =>
      simp only [hc, Bool.false_eq_true, ↓reduceIte] at hmem
      have hct : hasUuid (uuidOfNat k) seen = true := (hasUuid_iff_mem _ seen).mpr hmem
      rw [hc] at hct
      cases hct

private theorem list_length_ge_of_forall_lt_mem :
    ∀ (n : Nat) (l : List Nat), (∀ k, k < n → k ∈ l) → n ≤ l.length
  | 0, _, _ => Nat.zero_le _
  | n + 1, l, h => by
    have hmem : n ∈ l := h n (Nat.lt_succ_self n)
    have hlen : (l.erase n).length + 1 = l.length := by
      rw [List.length_erase_of_mem hmem]
      have hpos : 0 < l.length := List.length_pos_of_mem hmem
      omega
    have hsub : ∀ k, k < n → k ∈ l.erase n := by
      intro k hk
      exact (List.mem_erase_of_ne (Nat.ne_of_lt hk)).mpr (h k (Nat.lt_trans hk (Nat.lt_succ_self n)))
    have ih := list_length_ge_of_forall_lt_mem n (l.erase n) hsub
    omega

private theorem pickFreshUuid_not_mem (seen : List Uuid) (hLen : seen.length < maxValidV4Uuids) :
    pickFreshUuid seen ∉ seen := by
  intro hMem
  have hall := findFreshAux_mem_imp seen seen.length 0 hMem
  have hMap : ∀ k, k < seen.length + 1 → k ∈ seen.map natOfUuid := by
    intro k hk
    have hu : uuidOfNat k ∈ seen := hall k (Nat.zero_le k) (by omega)
    have hdec : natOfUuid (uuidOfNat k) = k := natOfUuid_uuidOfNat k (by omega)
    rw [← hdec]
    exact List.mem_map_of_mem hu
  have hge := list_length_ge_of_forall_lt_mem (seen.length + 1) (seen.map natOfUuid) hMap
  rw [List.length_map] at hge
  omega

/-- Reference model-level `UuidApiM (StateM UuidModelState)` demonstrating model satisfiability. -/
def refUuidApi : UuidApiM (StateM UuidModelState) :=
  { mapRawError := mapRawError
    fromRandomBytes := fromRandomBytes
    toString := toString
    toHex := toHex
    parse := parse
    parseHex := parseHex
    isValid := isValid
    getUuid := do
      let s ← get
      let u := pickFreshUuid s.seen
      set ({ seen := u :: s.seen } : UuidModelState)
      pure (.ok u) }

/-- `refUuidApi` satisfies `LeanSwe.Uuid.Model.allowedPkgStep` under `Core.ObeysStepId`. -/
theorem refUuidApi_obeys_model :
    Core.ObeysStepId pkgWf (execPkgStep refUuidApi) allowedPkgStep := by
  intro s req hwf
  cases req
  have hLen : s.seen.length < maxValidV4Uuids := of_decide_eq_true hwf
  have hRun : (execPkgStep refUuidApi .getUuid).run s =
      (.getUuid (.ok (pickFreshUuid s.seen)), { seen := pickFreshUuid s.seen :: s.seen }) := rfl
  rw [hRun]
  exact ⟨findFreshAux_isValidV4 s.seen s.seen.length 0, pickFreshUuid_not_mem s.seen hLen, rfl⟩

/-- Satisfiability witness confirming `LeanSwe.Uuid.Model.allowedPkgStep` is inhabited. -/
theorem uuid_model_satisfiable :
    ∃ api : UuidApiM (StateM UuidModelState),
      Core.ObeysStepId pkgWf (execPkgStep api) allowedPkgStep :=
  ⟨refUuidApi, refUuidApi_obeys_model⟩

end ModelMutants.Uuid
