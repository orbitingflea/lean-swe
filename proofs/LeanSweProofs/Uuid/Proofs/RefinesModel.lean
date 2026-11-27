import Core.Obeys
import LeanSweProofs.Uuid.Model
import LeanSweProofs.Uuid.Model.Refines
import LeanSwe.Uuid.Interface
import LeanSweProofs.Uuid.Proofs.Codec
import LeanSweProofs.Uuid.Proofs.Entropy

/-!
# Model Refinement Proofs for `LeanSwe.Uuid`

Proves `LeanSwe.Uuid.Proofs.RefinesModel.refines_model_impl` relating every pure
operation in `LeanSwe.Uuid.Interface` to `LeanSwe.Uuid.Model` and lifting
`Model.allowedRawStep` through `Internal.mkApi` to `Model.allowedPkgStep` via
`Core.ObeysStepFrom`, plus a constructive non-vacuity witness for `allowedRawStep`.
-/

namespace LeanSwe.Uuid.Proofs.RefinesModel

open Core
open LeanSwe.LinuxSyscall.TimeRand (TimeRandOpsM execTimeRandReq)
open LeanSwe.Uuid
open LeanSwe.Uuid.Proofs.Codec
open LeanSwe.Uuid.Proofs.Entropy

private theorem hexCharsToByte_eq (hi lo : Char) :
    Internal.hexCharsToByte hi lo = Model.hexCharsToByte hi lo := rfl

private theorem decodeHexPairs_eq : ∀ cs : List Char,
    Internal.decodeHexPairs cs = Model.decodeHexPairs cs
  | [] => rfl
  | [_] => rfl
  | hi :: lo :: rest => by
    change (match Internal.hexCharsToByte hi lo, Internal.decodeHexPairs rest with
      | some b, some bs => some (b :: bs)
      | _, _ => none) =
      (match Model.hexCharsToByte hi lo, Model.decodeHexPairs rest with
      | some b, some bs => some (b :: bs)
      | _, _ => none)
    rw [hexCharsToByte_eq, decodeHexPairs_eq rest]

private theorem validateV4BytesList_eq (bs : List UInt8) :
    Internal.validateV4BytesList bs = Model.validateV4BytesList bs := rfl

private theorem parseHexChars_eq (cs : List Char) :
    Internal.parseHexChars cs = Model.parseHexChars cs := by
  dsimp only [Internal.parseHexChars, Model.parseHexChars]
  rw [decodeHexPairs_eq]
  cases Model.decodeHexPairs cs <;> rfl

private theorem stripCanonicalHyphens_eq (cs : List Char) :
    Internal.stripCanonicalHyphens cs = Model.stripCanonicalHyphens cs := rfl

private theorem parseCanonicalChars_eq (cs : List Char) :
    Internal.parseCanonicalChars cs = Model.parseCanonicalChars cs := by
  dsimp only [Internal.parseCanonicalChars, Model.parseCanonicalChars]
  rw [stripCanonicalHyphens_eq]
  cases Model.stripCanonicalHyphens cs with
  | none => rfl
  | some hex =>
    by_cases hlen : (cs.length != 36) = true
    · simp [hlen]
    · simp [hlen, parseHexChars_eq]

/-- Pure refinement of `LeanSwe.Uuid.mapRawError` to `Model.mapRawError`. -/
theorem refines_mapRawError :
    Core.ObeysPureEq LeanSwe.Uuid.mapRawError Model.mapRawError := by
  intro raw
  cases raw <;> rfl

/-- Pure refinement of `LeanSwe.Uuid.fromRandomBytes` to `Model.fromRandomBytes`. -/
theorem refines_fromRandomBytes :
    Core.ObeysPureEq LeanSwe.Uuid.fromRandomBytes Model.fromRandomBytes := by
  intro _
  rfl

/-- Pure refinement of `LeanSwe.Uuid.toString` to `Model.toString`. -/
theorem refines_toString :
    Core.ObeysPureEq LeanSwe.Uuid.toString Model.toString := by
  intro _
  rfl

/-- Pure refinement of `LeanSwe.Uuid.toHex` to `Model.toHex`. -/
theorem refines_toHex :
    Core.ObeysPureEq LeanSwe.Uuid.toHex Model.toHex := by
  intro _
  rfl

/-- Pure refinement of `LeanSwe.Uuid.parse` to `Model.parse`. -/
theorem refines_parse :
    Core.ObeysPureEq LeanSwe.Uuid.parse Model.parse := by
  intro s
  exact parseCanonicalChars_eq s.toList

/-- Pure refinement of `LeanSwe.Uuid.parseHex` to `Model.parseHex`. -/
theorem refines_parseHex :
    Core.ObeysPureEq LeanSwe.Uuid.parseHex Model.parseHex := by
  intro s
  exact parseHexChars_eq s.toList

/-- Pure refinement of `LeanSwe.Uuid.isValid` to `Model.isValid`. -/
theorem refines_isValid :
    Core.ObeysPureEq LeanSwe.Uuid.isValid Model.isValid := by
  intro s
  dsimp [LeanSwe.Uuid.isValid, defaultApi, Internal.mkApi, Internal.isValid, Model.isValid]
  rw [show Internal.parse s = Model.parse s from refines_parse s]

private theorem stateM_map_run {W α β : Type} (f : α → β) (x : StateM W α) (w : W) :
    (f <$> x).run w = (f (x.run w).1, (x.run w).2) := rfl

private theorem stateM_bind_run {σ α β : Type} (a : StateM σ α) (f : α → StateM σ β) (s : σ) :
    (a >>= f).run s = (f (a.run s).1).run (a.run s).2 := rfl

private theorem fromRandomBytes_isValidV4 {bs : ByteArray} (hsz : bs.size = 16) :
    ∃ u : Uuid, Internal.fromRandomBytes bs = .ok u ∧ Model.isValidV4Uuid u = true := by
  obtain ⟨u, hfr, hv, _, _, _⟩ := fromRandomBytes_spec hsz
  refine ⟨u, hfr, ?_⟩
  rw [Model.isValidV4Uuid, hv.1, hv.2.1, hv.2.2]
  rfl

/-- Inductive verification of the full `Internal.gatherRandomBytes16` loop covering
    arbitrary `1..need`-byte partial reads, non-empty `Internal.appendBytes` accumulation,
    and up to `MAX_GETRANDOM_EINTR` interleaved `Errno.EINTR` retries. -/
theorem gatherRandomBytes16_raw {W : Type}
    (proj : W → Model.UuidRawState) (sys : TimeRandOpsM (StateM W))
    (hRaw : Core.ObeysStep proj Model.rawWf (Model.execRawStep sys) Model.allowedRawStep) :
    ∀ (fuel : Nat) (acc : ByteArray) (lastErrno? : Option LeanSwe.LinuxSyscall.Errno) (w : W),
      acc.size < 16 →
      (acc = ByteArray.empty ∨ (0 < acc.size ∧ (proj w).inFlight = acc)) →
      Model.hasFreshCompletion (proj w).seen acc →
      (16 - acc.size) + (proj w).eintrBudget.val ≤ fuel →
      Model.rawWf (proj w) = true →
      let r := (Internal.gatherRandomBytes16 sys fuel acc lastErrno?).run w
      ∃ bs : ByteArray,
        r.1 = .ok bs ∧
        bs.size = 16 ∧
        match Model.fromRandomBytes bs with
        | .ok u => u ∉ (proj w).seen ∧ (proj r.2).seen = u :: (proj w).seen
        | .error _ => False
  | 0, acc, _, w, hlt, _, _, hfuel, _ => by omega
  | fuel' + 1, acc, lastErrno?, w, hlt, hmatch, hfresh, hfuel, hw => by
    rw [gatherRandomBytes16_step_succ sys fuel' acc hlt lastErrno?, stateM_bind_run]
    let need : Nat := 16 - acc.size
    have hneedPos : 1 ≤ need := by omega
    have hneedToNat : (UInt32.ofNat need).toNat = need := by
      rw [UInt32.toNat_ofNat']
      have hbound : 16 < UInt32.size := by simp [UInt32.size]
      exact Nat.mod_eq_of_lt (by omega)
    have hbase : (if (UInt32.ofNat need).toNat == 16 then ByteArray.empty else (proj w).inFlight) = acc := by
      rw [hneedToNat]
      rcases hmatch with rfl | ⟨hpos, hinf⟩
      · rfl
      · have hne : (need == 16) = false := beq_false_of_ne (by omega)
        rw [hne]
        exact hinf
    have hStep := hRaw w (.getrandom (UInt32.ofNat need) {}) hw
    dsimp only [Model.execRawStep, execTimeRandReq, Model.allowedRawStep] at hStep
    rw [stateM_bind_run] at hStep
    cases hgr : (sys.getrandom (UInt32.ofNat need) {}).run w with
    | mk res w1 =>
      rw [hgr] at hStep
      dsimp only [Pure.pure, StateT.pure, StateT.run, Bind.bind, StateT.bind] at hStep ⊢
      cases res with
      | error e =>
        dsimp only [LeanSwe.LinuxSyscall.TimeRand.outcomeOfBytes] at hStep
        rw [hbase] at hStep
        rcases hStep with ⟨_, _, _, _, he, hbudLt, hseenEq, hinfEq⟩
        subst he
        dsimp only [Internal.stepRandomBytes16]
        simp only [beq_self_eq_true, ↓reduceIte]
        have hmatch1 : acc = ByteArray.empty ∨ (0 < acc.size ∧ (proj w1).inFlight = acc) := by
          rcases hmatch with rfl | ⟨hpos, _⟩
          · exact Or.inl rfl
          · exact Or.inr ⟨hpos, hinfEq⟩
        have hwf1 : Model.rawWf (proj w1) = true := by
          simpa only [Model.rawWf, Model.toModelState, hseenEq] using hw
        have hfresh1 : Model.hasFreshCompletion (proj w1).seen acc := by
          simpa only [hseenEq] using hfresh
        have hih := gatherRandomBytes16_raw proj sys hRaw fuel' acc
          (some LeanSwe.LinuxSyscall.Errno.EINTR) w1 hlt hmatch1 hfresh1 (by omega) hwf1
        dsimp only [StateT.run] at hih
        simpa only [hseenEq] using hih
      | ok got =>
        dsimp only [LeanSwe.LinuxSyscall.TimeRand.outcomeOfBytes] at hStep
        rw [hbase, hneedToNat] at hStep
        have hguard : (({} : LeanSwe.LinuxSyscall.TimeRand.GrndFlags) == {} &&
            decide (1 ≤ need) && decide (acc.size + need = 16)) = true := by
          simp only [Bool.and_eq_true, decide_eq_true_eq]
          exact ⟨⟨by decide, hneedPos⟩, by omega⟩
        rw [hguard] at hStep
        simp only [↓reduceIte] at hStep
        rcases hStep.1 hfresh with ⟨hgotPos, hgotLe, hrest⟩
        have hbad : (got.size == 0 || decide (got.size > need)) = false := by
          simp only [Bool.or_eq_false_iff, beq_eq_false_iff_ne, decide_eq_false_iff_not]
          exact ⟨by omega, by omega⟩
        dsimp only [Internal.stepRandomBytes16]
        rw [hbad]
        simp only [Bool.false_eq_true, ↓reduceIte]
        have happEq : Model.concatBytes acc got = Internal.appendBytes acc got := rfl
        rw [happEq] at hrest
        have happSz : (Internal.appendBytes acc got).size = acc.size + got.size :=
          appendBytes_size acc got
        by_cases hltNext : (Internal.appendBytes acc got).size < 16
        · simp only [hltNext, ↓reduceIte] at hrest
          rcases hrest with ⟨hseenEq, hinfEq, hbudLe, hfreshNext⟩
          have hne16 : ((Internal.appendBytes acc got).size == 16) = false :=
            beq_false_of_ne (by omega)
          rw [hne16]
          simp only [Bool.false_eq_true, ↓reduceIte]
          have hmatch1 : Internal.appendBytes acc got = ByteArray.empty ∨
              (0 < (Internal.appendBytes acc got).size ∧
                (proj w1).inFlight = Internal.appendBytes acc got) :=
            Or.inr ⟨by omega, hinfEq⟩
          have hwf1 : Model.rawWf (proj w1) = true := by
            simpa only [Model.rawWf, Model.toModelState, hseenEq] using hw
          have hfresh1 : Model.hasFreshCompletion (proj w1).seen (Internal.appendBytes acc got) := by
            simpa only [hseenEq] using hfreshNext
          have hih := gatherRandomBytes16_raw proj sys hRaw fuel'
            (Internal.appendBytes acc got) none w1 hltNext hmatch1 hfresh1 (by omega) hwf1
          dsimp only [StateT.run] at hih
          simpa only [hseenEq] using hih
        · simp only [hltNext, ↓reduceIte] at hrest
          have heq16 : (Internal.appendBytes acc got).size = 16 := by omega
          have hbeq16 : ((Internal.appendBytes acc got).size == 16) = true := by simp [heq16]
          rw [hbeq16]
          simp only [↓reduceIte]
          dsimp only [Pure.pure, StateT.pure, StateT.run]
          exact ⟨Internal.appendBytes acc got, rfl, heq16, hrest.2⟩

private def uuidOfNat (n : Nat) : Uuid :=
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

private def natOfUuid (u : Uuid) : Nat :=
  let g (i : Nat) : Nat := (u.bytes[i]!).toNat
  g 0 + 256 * (g 1 + 256 * (g 2 + 256 * (g 3 + 256 * (g 4 + 256 * (g 5 + 256 *
    (g 6 % 16 + 16 * (g 7 + 256 * (g 8 % 64 + 64 * (g 9 + 256 * (g 10 + 256 *
      (g 11 + 256 * (g 12 + 256 * (g 13 + 256 * (g 14 + 256 * g 15))))))))))))))

private theorem v4_byte6_stamp : ∀ r : Fin 16,
    ((UInt8.ofNat (64 + r.val) &&& (0x0F : UInt8)) ||| (0x40 : UInt8)) = UInt8.ofNat (64 + r.val) := by
  decide

private theorem v4_byte8_stamp : ∀ r : Fin 64,
    ((UInt8.ofNat (128 + r.val) &&& (0x3F : UInt8)) ||| (0x80 : UInt8)) = UInt8.ofNat (128 + r.val) := by
  decide

private theorem byteArray_set!_self {bs : ByteArray} {i : Nat} (hi : i < bs.size) :
    bs.set! i bs[i]! = bs := by
  apply ByteArray.ext
  apply Array.ext
  · rw [ByteArray.size_data, ByteArray.size_set!, ByteArray.size_data]
  · intro j hj1 hj2
    have hjb : j < bs.size := by simpa [ByteArray.size_data] using hj2
    change (bs.set! i bs[i]!)[j]'(by rw [ByteArray.size_set!]; exact hjb) = bs[j]'hjb
    rw [ByteArray.getElem_set! bs i j bs[i]! hi hjb]
    split
    · rename_i hij; subst hij; rw [getElem!_pos bs i hi]
    · rfl

private theorem fromRandomBytes_uuidOfNat (n : Nat) :
    (uuidOfNat n).bytes.size = 16 ∧ Model.fromRandomBytes (uuidOfNat n).bytes = .ok (uuidOfNat n) := by
  refine ⟨rfl, ?_⟩
  unfold Model.fromRandomBytes
  simp only [show (uuidOfNat n).bytes.size = 16 from rfl, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
  have hsz : (uuidOfNat n).bytes.size = 16 := rfl
  have h6 : (((uuidOfNat n).bytes[6]! &&& (0x0F : UInt8)) ||| (0x40 : UInt8)) = (uuidOfNat n).bytes[6]! :=
    v4_byte6_stamp ⟨_, Nat.mod_lt _ (by decide)⟩
  have h8 : (((uuidOfNat n).bytes[8]! &&& (0x3F : UInt8)) ||| (0x80 : UInt8)) = (uuidOfNat n).bytes[8]! :=
    v4_byte8_stamp ⟨_, Nat.mod_lt _ (by decide)⟩
  rw [h6, byteArray_set!_self (by omega), h8, byteArray_set!_self (by omega)]

private theorem natOfUuid_uuidOfNat (n : Nat) (hn : n < Model.maxValidV4Uuids) :
    natOfUuid (uuidOfNat n) = n := by
  unfold uuidOfNat
  change (UInt8.ofNat _).toNat + 256 * ((UInt8.ofNat _).toNat + 256 * ((UInt8.ofNat _).toNat +
    256 * ((UInt8.ofNat _).toNat + 256 * ((UInt8.ofNat _).toNat + 256 * ((UInt8.ofNat _).toNat +
    256 * ((UInt8.ofNat _).toNat % 16 + 16 * ((UInt8.ofNat _).toNat + 256 * ((UInt8.ofNat _).toNat % 64 +
    64 * ((UInt8.ofNat _).toNat + 256 * ((UInt8.ofNat _).toNat + 256 * ((UInt8.ofNat _).toNat +
    256 * ((UInt8.ofNat _).toNat + 256 * ((UInt8.ofNat _).toNat + 256 * ((UInt8.ofNat _).toNat +
    256 * (UInt8.ofNat _).toNat)))))))))))))) = n
  simp only [UInt8.toNat_ofNat']
  unfold Model.maxValidV4Uuids at hn
  omega

private def hasUuid (u : Uuid) : List Uuid → Bool
  | [] => false
  | x :: xs => if x = u then true else hasUuid u xs

private theorem hasUuid_iff_mem (u : Uuid) : ∀ seen : List Uuid, hasUuid u seen = true ↔ u ∈ seen
  | [] => by simp [hasUuid]
  | x :: xs => by
    unfold hasUuid
    split
    · rename_i h; subst h; simp
    · rename_i h; simp [hasUuid_iff_mem u xs, Ne.symm h]

private def findFreshAux (seen : List Uuid) (k : Nat) : Nat → Uuid
  | 0 => uuidOfNat k
  | fuel' + 1 =>
    let cand := uuidOfNat k
    if hasUuid cand seen then findFreshAux seen (k + 1) fuel' else cand

private def pickFreshUuid (seen : List Uuid) : Uuid :=
  findFreshAux seen 0 seen.length

private theorem findFreshAux_is_uuidOfNat (seen : List Uuid) :
    ∀ (fuel k : Nat), ∃ j, findFreshAux seen k fuel = uuidOfNat j
  | 0, k => ⟨k, rfl⟩
  | fuel' + 1, k => by
    dsimp only [findFreshAux]
    cases hasUuid (uuidOfNat k) seen with
    | true => exact findFreshAux_is_uuidOfNat seen fuel' (k + 1)
    | false => exact ⟨k, rfl⟩

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
      · subst hjk; exact (hasUuid_iff_mem _ seen).mp hc
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
    have hsub : ∀ k, k < n → k ∈ l.erase n := fun k hk =>
      (List.mem_erase_of_ne (Nat.ne_of_lt hk)).mpr (h k (Nat.lt_trans hk (Nat.lt_succ_self n)))
    have ih := list_length_ge_of_forall_lt_mem n (l.erase n) hsub
    omega

private theorem pickFreshUuid_not_mem (seen : List Uuid) (hLen : seen.length < Model.maxValidV4Uuids) :
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

private theorem hasFreshCompletion_empty (seen : List Uuid)
    (hLen : seen.length < Model.maxValidV4Uuids) :
    Model.hasFreshCompletion seen ByteArray.empty := by
  obtain ⟨j, hj⟩ := findFreshAux_is_uuidOfNat seen seen.length 0
  obtain ⟨hsz, hfr⟩ := fromRandomBytes_uuidOfNat j
  refine ⟨(pickFreshUuid seen).bytes, ?_, ?_⟩
  · change 0 + (pickFreshUuid seen).bytes.size = 16
    simpa [pickFreshUuid, hj] using hsz
  · have hcat : Model.concatBytes ByteArray.empty (pickFreshUuid seen).bytes =
        (pickFreshUuid seen).bytes := rfl
    rw [hcat]
    have hfr' : Model.fromRandomBytes (pickFreshUuid seen).bytes = .ok (pickFreshUuid seen) := by
      simpa [pickFreshUuid, hj] using hfr
    rw [hfr']
    exact pickFreshUuid_not_mem seen hLen

/-- Compositional single-step refinement of `Internal.mkApi` over `Model.allowedRawStep`. -/
theorem refinesStepFrom_mkApi :
    Core.ObeysStepFrom Model.toModelState Model.rawWf Model.execRawStep Model.allowedRawStep
      Model.pkgWf Internal.mkApi Model.execPkgStep Model.allowedPkgStep := by
  intro W proj sys hRaw w req hw
  cases req
  dsimp only [Model.execPkgStep, Internal.mkApi, Function.comp, Model.toModelState]
  rw [stateM_map_run, stateM_bind_run]
  have hbud : (proj w).eintrBudget.val ≤ 16 := Nat.le_of_lt_succ (proj w).eintrBudget.isLt
  have hfresh0 : Model.hasFreshCompletion (proj w).seen ByteArray.empty :=
    hasFreshCompletion_empty (proj w).seen (of_decide_eq_true hw)
  have hgather := gatherRandomBytes16_raw proj sys hRaw Internal.MAX_GETRANDOM_ATTEMPTS
    ByteArray.empty none w (by decide) (Or.inl rfl) hfresh0
    (by change 16 - 0 + _ ≤ 32; omega) hw
  cases hrun : (Internal.gatherRandomBytes16 sys Internal.MAX_GETRANDOM_ATTEMPTS ByteArray.empty none).run w with
  | mk res w' =>
    rw [hrun] at hgather
    rcases hgather with ⟨bs, hok, hsz, hMatch⟩
    subst hok
    dsimp only [Pure.pure, StateT.pure, StateT.run, Model.allowedPkgStep]
    obtain ⟨u, hfr, hv⟩ := fromRandomBytes_isValidV4 hsz
    have hfrM : Model.fromRandomBytes bs = .ok u := hfr
    rw [hfrM] at hMatch
    rw [hfr]
    exact ⟨hv, hMatch.1, hMatch.2⟩

/-- Full public `Interface` refinement of `LeanSwe.Uuid` against `LeanSwe.Uuid.Model`. -/
theorem refines_model_impl :
    Core.ObeysPureEq LeanSwe.Uuid.mapRawError Model.mapRawError ∧
    Core.ObeysPureEq LeanSwe.Uuid.fromRandomBytes Model.fromRandomBytes ∧
    Core.ObeysPureEq LeanSwe.Uuid.toString Model.toString ∧
    Core.ObeysPureEq LeanSwe.Uuid.toHex Model.toHex ∧
    Core.ObeysPureEq LeanSwe.Uuid.parse Model.parse ∧
    Core.ObeysPureEq LeanSwe.Uuid.parseHex Model.parseHex ∧
    Core.ObeysPureEq LeanSwe.Uuid.isValid Model.isValid ∧
    Core.ObeysStepFrom Model.toModelState Model.rawWf Model.execRawStep Model.allowedRawStep
      Model.pkgWf Internal.mkApi Model.execPkgStep Model.allowedPkgStep :=
  ⟨refines_mapRawError,
   refines_fromRandomBytes,
   refines_toString,
   refines_toHex,
   refines_parse,
   refines_parseHex,
   refines_isValid,
   refinesStepFrom_mkApi⟩

open Classical in
private noncomputable def refGetrandom (len : UInt32) (flags : LeanSwe.LinuxSyscall.TimeRand.GrndFlags)
    (s : Model.UuidRawState) : Except LeanSwe.LinuxSyscall.Errno ByteArray × Model.UuidRawState :=
  let base := if len.toNat == 16 then ByteArray.empty else s.inFlight
  if flags == {} && decide (1 ≤ len.toNat) && decide (base.size + len.toNat = 16) then
    if h : Model.hasFreshCompletion s.seen base then
      let suf := Classical.choose h
      match Model.fromRandomBytes (Model.concatBytes base suf) with
      | .ok u =>
        (.ok suf, { seen := u :: s.seen, inFlight := ByteArray.empty, eintrBudget := ⟨0, by decide⟩ })
      | .error _ => (.ok ByteArray.empty, s)
    else
      (.ok ByteArray.empty, s)
  else
    (.ok ByteArray.empty, s)

/-- `TimeRandOpsM (StateM UuidRawState)` witnessing satisfiability of `Model.allowedRawStep`. -/
noncomputable def refRawOps : TimeRandOpsM (StateM Model.UuidRawState) :=
  { clock_gettime := fun _ => pure (.ok { sec := 0, nsec := 0 })
    clock_nanosleep := fun _ _ _ => pure (.ok ())
    getrandom := fun len flags s => refGetrandom len flags s }

/-- `refRawOps` satisfies `Model.allowedRawStep` under `Core.ObeysStepId`. -/
theorem refRawOps_obeys_model :
    Core.ObeysStepId Model.rawWf (Model.execRawStep refRawOps) Model.allowedRawStep := by
  classical
  intro s req _hwf
  cases req with
  | clock_gettime _ => rfl
  | clock_nanosleep _ _ _ => rfl
  | getrandom len flags =>
    let base := if len.toNat == 16 then ByteArray.empty else s.inFlight
    by_cases hguard : (flags == {} && decide (1 ≤ len.toNat) && decide (base.size + len.toNat = 16)) = true
    · have hparts := Bool.and_eq_true_iff.mp hguard
      have hlen1 : 1 ≤ len.toNat := of_decide_eq_true (Bool.and_eq_true_iff.mp hparts.1).2
      have hsum : base.size + len.toNat = 16 := of_decide_eq_true hparts.2
      by_cases hfresh : Model.hasFreshCompletion s.seen base
      · let suf := Classical.choose hfresh
        have hsufSpec := Classical.choose_spec hfresh
        have hsufSz : base.size + suf.size = 16 := hsufSpec.1
        have hcatSz : (Model.concatBytes base suf).size = base.size + suf.size :=
          appendBytes_size base suf
        have hcat16 : (Model.concatBytes base suf).size = 16 := by omega
        obtain ⟨u, hfr, _⟩ := fromRandomBytes_isValidV4 hcat16
        have hfrM : Model.fromRandomBytes (Model.concatBytes base suf) = .ok u := hfr
        have huNotMem : u ∉ s.seen := by
          have hm := hsufSpec.2
          rw [hfrM] at hm
          exact hm
        have hrg : refGetrandom len flags s =
            (.ok suf, { seen := u :: s.seen, inFlight := ByteArray.empty, eintrBudget := ⟨0, by decide⟩ }) := by
          unfold refGetrandom
          change (if (flags == {} && decide (1 ≤ len.toNat) && decide (base.size + len.toNat = 16)) = true then _ else _) = _
          rw [hguard]
          simp only [↓reduceIte]
          have hfresh' : Model.hasFreshCompletion s.seen
              (if (len.toNat == 16) = true then ByteArray.empty else s.inFlight) := hfresh
          rw [dite_eq_left_of_eq_true (eq_true hfresh')]
          dsimp only [base] at hfrM
          rw [show Classical.choose hfresh' = suf from rfl, hfrM]
        have hrun : (Model.execRawStep refRawOps (.getrandom len flags)).run s =
            (.bytes suf, { seen := u :: s.seen, inFlight := ByteArray.empty, eintrBudget := ⟨0, by decide⟩ }) := by
          change (LeanSwe.LinuxSyscall.TimeRand.outcomeOfBytes (refGetrandom len flags s).1,
            (refGetrandom len flags s).2) = _
          rw [hrg]
          rfl
        rw [hrun]
        dsimp only [Model.allowedRawStep, id]
        change (if (flags == {} && decide (1 ≤ len.toNat) && decide (base.size + len.toNat = 16)) = true then _ else _)
        rw [hguard]
        simp only [↓reduceIte]
        refine ⟨fun _ => ?_, fun hn => False.elim (hn hfresh)⟩
        refine ⟨by omega, by omega, ?_⟩
        dsimp only [base] at hcat16 hfrM
        simp only [show ¬ ((Model.concatBytes (if (len.toNat == 16) = true then ByteArray.empty else s.inFlight) suf).size < 16) by omega,
          ↓reduceIte, hfrM]
        exact ⟨trivial, huNotMem, trivial⟩
      · have hrg : refGetrandom len flags s = (.ok ByteArray.empty, s) := by
          unfold refGetrandom
          change (if (flags == {} && decide (1 ≤ len.toNat) && decide (base.size + len.toNat = 16)) = true then _ else _) = _
          rw [hguard]
          simp only [↓reduceIte]
          have hfresh' : ¬ Model.hasFreshCompletion s.seen
              (if (len.toNat == 16) = true then ByteArray.empty else s.inFlight) := hfresh
          rw [dite_eq_right_of_eq_false (eq_false hfresh')]
        have hrun : (Model.execRawStep refRawOps (.getrandom len flags)).run s =
            (.bytes ByteArray.empty, s) := by
          change (LeanSwe.LinuxSyscall.TimeRand.outcomeOfBytes (refGetrandom len flags s).1,
            (refGetrandom len flags s).2) = _
          rw [hrg]
          rfl
        rw [hrun]
        dsimp only [Model.allowedRawStep, id]
        change (if (flags == {} && decide (1 ≤ len.toNat) && decide (base.size + len.toNat = 16)) = true then _ else _)
        rw [hguard]
        exact ⟨fun hf => False.elim (hfresh hf), fun _ => rfl⟩
    · have hguardF : (flags == {} && decide (1 ≤ len.toNat) && decide (base.size + len.toNat = 16)) = false :=
        Bool.eq_false_iff.mpr hguard
      have hrg : refGetrandom len flags s = (.ok ByteArray.empty, s) := by
        unfold refGetrandom
        change (if (flags == {} && decide (1 ≤ len.toNat) && decide (base.size + len.toNat = 16)) = true then _ else _) = _
        rw [hguardF]
        simp only [Bool.false_eq_true, ↓reduceIte]
      have hrun : (Model.execRawStep refRawOps (.getrandom len flags)).run s =
          (.bytes ByteArray.empty, s) := by
        change (LeanSwe.LinuxSyscall.TimeRand.outcomeOfBytes (refGetrandom len flags s).1,
          (refGetrandom len flags s).2) = _
        rw [hrg]
        rfl
      rw [hrun]
      dsimp only [Model.allowedRawStep, id]
      change (if (flags == {} && decide (1 ≤ len.toNat) && decide (base.size + len.toNat = 16)) = true then _ else _)
      rw [hguardF]
      simp only [Bool.false_eq_true, ↓reduceIte]

end LeanSwe.Uuid.Proofs.RefinesModel
