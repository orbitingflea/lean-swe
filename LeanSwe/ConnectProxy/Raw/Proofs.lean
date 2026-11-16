import LeanSwe.ConnectProxy.Raw.Types
import LeanSwe.ConnectProxy.Raw.Interface
import LeanSwe.ConnectProxy.Raw.Impl
import LeanSwe.ConnectProxy.Raw.SpecTests

namespace LeanSwe.ConnectProxy.Raw.Proofs

open Core
open Core.NondetTest

private theorem nonEmptyMsg_ne_empty (fallback msg : String) (hf : fallback ≠ "") :
    Internal.nonEmptyMsg fallback msg ≠ "" := by
  unfold Internal.nonEmptyMsg
  split
  · exact hf
  · next h =>
    intro hem
    subst hem
    simp [String.isEmpty] at h

private theorem append_tail_ne_empty (pre tail : String) (ht : tail ≠ "") :
    pre ++ tail ≠ "" := by
  simp [String.append_eq_empty_iff, ht]

/-- Proof of `test_cproxyRaw_mapRawError_returnsNonEmptyMessage` for `defaultOps`. -/
theorem proof_cproxyRaw_mapRawError_returnsNonEmptyMessage :
    AllPass (test_cproxyRaw_mapRawError_returnsNonEmptyMessage defaultOps) := by
  intro raw
  simp only [defaultOps, Internal.mkRawOps, Internal.mapRawError, assert]
  refine ⟨?_, trivial⟩
  cases raw with
  | invalidArgument _ _ => exact nonEmptyMsg_ne_empty _ _ (by decide)
  | addressInUse port _ _ =>
    exact nonEmptyMsg_ne_empty _ _
      (append_tail_ne_empty ("127.0.0.1:" ++ toString port) " is already in use" (by decide))
  | permissionDenied _ _ => exact nonEmptyMsg_ne_empty _ _ (by decide)
  | resourceExhausted _ _ => exact nonEmptyMsg_ne_empty _ _ (by decide)
  | otherError errno _ =>
    exact nonEmptyMsg_ne_empty _ _
      (append_tail_ne_empty ("connect-proxy OS error (errno " ++ toString errno) ")" (by decide))
  | userError _ => exact nonEmptyMsg_ne_empty _ _ (by decide)

/-- Non-vacuity `CanReach` witness for `test_cproxyRaw_mapRawError_returnsNonEmptyMessage`. -/
theorem reach_cproxyRaw_mapRawError_returnsNonEmptyMessage :
    CanReach (test_cproxyRaw_mapRawError_returnsNonEmptyMessage defaultOps) :=
  ⟨.userError "", proof_cproxyRaw_mapRawError_returnsNonEmptyMessage (.userError "")⟩

/-- Proof of `test_cproxyRaw_mapRawError_preservesKindAndFields` for `defaultOps`. -/
theorem proof_cproxyRaw_mapRawError_preservesKindAndFields :
    AllPass (test_cproxyRaw_mapRawError_preservesKindAndFields defaultOps) := by
  intro raw
  cases raw <;> simp [defaultOps, Internal.mkRawOps, Internal.mapRawError, assert]

/-- Non-vacuity `CanReach` witness for `test_cproxyRaw_mapRawError_preservesKindAndFields`. -/
theorem reach_cproxyRaw_mapRawError_preservesKindAndFields :
    CanReach (test_cproxyRaw_mapRawError_preservesKindAndFields defaultOps) :=
  ⟨.userError "err", by simp [defaultOps, Internal.mkRawOps, Internal.mapRawError, assert]⟩

/-- Pure state model for verifying `RawConnectProxyOpsM` proxy lifecycle contracts. -/
structure RawProxyState where
  /-- Active proxy handle identifiers. -/
  active : List Nat := []
  deriving DecidableEq, Repr

private def freshHandleId (active : List Nat) : Nat :=
  (active.foldl Nat.max 0) + 1

private theorem freshHandleId_gt_all (active : List Nat) :
    ∀ h ∈ active, h < freshHandleId active := by
  have hle : ∀ (xs : List Nat) (init : Nat),
      init ≤ xs.foldl Nat.max init ∧ ∀ h ∈ xs, h ≤ xs.foldl Nat.max init := by
    intro xs
    induction xs with
    | nil =>
      intro init
      exact ⟨Nat.le_refl _, fun _ h => by contradiction⟩
    | cons x rest ih =>
      intro init
      obtain ⟨h1, h2⟩ := ih (Nat.max init x)
      constructor
      · exact Nat.le_trans (Nat.le_max_left _ _) h1
      · intro h hh
        rcases List.mem_cons.mp hh with rfl | hh'
        · exact Nat.le_trans (Nat.le_max_right _ _) h1
        · exact h2 h hh'
  intro h hh
  have := (hle active 0).2 h hh
  unfold freshHandleId
  omega

private theorem contains_fresh_false (k : Nat) (xs : List Nat)
    (hfresh : ∀ h ∈ xs, h < k) :
    xs.contains k = false := by
  rw [Bool.eq_false_iff]
  intro hmem
  have hlt := hfresh k (List.contains_iff_mem.mp hmem)
  omega

private theorem contains_fresh_cons (k : Nat) (xs : List Nat) :
    (k :: xs).contains k = true :=
  List.contains_iff_mem.mpr List.mem_cons_self

private theorem filter_ne_fresh (k : Nat) (xs : List Nat)
    (hfresh : ∀ h ∈ xs, h < k) :
    (k :: xs).filter (· != k) = xs := by
  simp only [List.filter_cons, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
  induction xs with
  | nil => rfl
  | cons x rest ih =>
    have hlt : x < k := hfresh x (by simp)
    have hbne : (x != k) = true := bne_iff_ne.mpr (Nat.ne_of_lt hlt)
    simp only [List.filter_cons, hbne, ↓reduceIte]
    congr 1
    exact ih (fun h hh => hfresh h (by simp [hh]))

private theorem validateStartLimits_eq_error_of_zero (vcfg : ValidProxyConfig)
    (hzero : vcfg.config.limits.maxHeaderBytes = 0 ∨ vcfg.config.limits.headerTimeoutMs = 0 ∨
      vcfg.config.limits.connectTimeoutMs = 0 ∨ vcfg.config.limits.maxConcurrentTunnels = 0) :
    Internal.validateStartLimits vcfg =
      .error (Internal.mapRawError (.invalidArgument none "proxy limits must be positive")) := by
  unfold Internal.validateStartLimits
  rcases hzero with h | h | h | h <;> simp [h]

/-- Pure `StateM RawProxyState` implementation of `RawConnectProxyOpsM` used in `Raw.Proofs`. -/
def mockRawOps : RawConnectProxyOpsM (StateM RawProxyState) :=
  { mapRawError := Internal.mapRawError
    startProxy := fun vcfg _ _ s =>
      match Internal.validateStartLimits vcfg with
      | .error err => (.error err, s)
      | .ok _ =>
        let hid := freshHandleId s.active
        let boundPort : UInt16 :=
          if vcfg.config.listenPort == 0 then 49152 else vcfg.config.listenPort
        (.ok { handleId := hid, port := boundPort }, { active := hid :: s.active })
    stopProxy := fun proxy s =>
      match s.active.contains proxy.handleId with
      | true =>
        (.ok #[], { active := s.active.filter (· != proxy.handleId) })
      | false =>
        (.error (Internal.mapRawError (.invalidArgument none "proxy handle is not active")), s)
    activeProxyCount := fun s => (s.active.length, s) }

/-- Proof of `test_cproxyRaw_startProxy_zeroLimits_failsInvalidInput` for `mockRawOps`. -/
theorem proof_cproxyRaw_startProxy_zeroLimits_failsInvalidInput :
    AllPass (test_cproxyRaw_startProxy_zeroLimits_failsInvalidInput mockRawOps) := by
  intro s₀ vcfg hzero
  have hval := validateStartLimits_eq_error_of_zero vcfg hzero
  simp only [mockRawOps, hval, Internal.mapRawError, StateT.run, assert]
  refine ⟨⟨⟨_, rfl, rfl, ?_⟩, trivial⟩, trivial⟩
  dsimp
  exact nonEmptyMsg_ne_empty _ _ (by decide)

/-- Non-vacuity `CanReach` witness for `test_cproxyRaw_startProxy_zeroLimits_failsInvalidInput`. -/
theorem reach_cproxyRaw_startProxy_zeroLimits_failsInvalidInput :
    CanReach (test_cproxyRaw_startProxy_zeroLimits_failsInvalidInput mockRawOps) := by
  let badCfg : ValidProxyConfig := { config := { limits := { maxHeaderBytes := 0 } } }
  have hval : Internal.validateStartLimits badCfg =
      .error (Internal.mapRawError (.invalidArgument none "proxy limits must be positive")) := rfl
  refine ⟨{}, badCfg, Or.inl rfl, ?_⟩
  simp only [mockRawOps, hval, Internal.mapRawError, StateT.run, assert]
  refine ⟨⟨⟨_, rfl, rfl, ?_⟩, trivial⟩, trivial⟩
  decide

/-- Proof of `test_cproxyRaw_startAndStop_bindsPortAndConservesActiveCount` for `mockRawOps`. -/
theorem proof_cproxyRaw_startAndStop_bindsPortAndConservesActiveCount :
    AllPass (test_cproxyRaw_startAndStop_bindsPortAndConservesActiveCount mockRawOps) := by
  intro s₀ vcfg
  dsimp only [test_cproxyRaw_startAndStop_bindsPortAndConservesActiveCount,
    mockRawOps, StateT.run, Bind.bind]
  cases hval : Internal.validateStartLimits vcfg with
  | error err =>
    simp [assume]
  | ok _ =>
    dsimp only
    have hgt : ∀ h ∈ s₀.active, h < freshHandleId s₀.active := freshHandleId_gt_all s₀.active
    have hcontainsTrue := contains_fresh_cons (freshHandleId s₀.active) s₀.active
    have hflt := filter_ne_fresh (freshHandleId s₀.active) s₀.active hgt
    have hcontainsFalse := contains_fresh_false (freshHandleId s₀.active) s₀.active hgt
    have hport :
        (if vcfg.config.listenPort == 0 then (49152 : UInt16) else vcfg.config.listenPort) ≠ 0 ∧
        (vcfg.config.listenPort = 0 ∨
          (if vcfg.config.listenPort == 0 then (49152 : UInt16) else vcfg.config.listenPort) =
            vcfg.config.listenPort) := by
      by_cases hp : vcfg.config.listenPort = 0
      · simp [hp]
      · simp [hp]
    refine ⟨⟨hport.1, hport.2, by simp⟩, ?_⟩
    simp only [hcontainsTrue, hflt, assert]
    refine ⟨trivial, ?_, trivial⟩
    simp only [hcontainsFalse, Internal.mapRawError]
    refine ⟨⟨_, rfl, rfl, ?_⟩, trivial⟩
    dsimp
    exact nonEmptyMsg_ne_empty _ _ (by decide)

/-- Non-vacuity `CanReach` witness for `test_cproxyRaw_startAndStop_bindsPortAndConservesActiveCount`. -/
theorem reach_cproxyRaw_startAndStop_bindsPortAndConservesActiveCount :
    CanReach (test_cproxyRaw_startAndStop_bindsPortAndConservesActiveCount mockRawOps) := by
  let okCfg : ValidProxyConfig := { config := {} }
  have hval : Internal.validateStartLimits okCfg = .ok okCfg := rfl
  have hid : freshHandleId [] = 1 := rfl
  have hc1 : ([1] : List Nat).contains 1 = true := rfl
  have hf1 : ([1] : List Nat).filter (· != 1) = [] := rfl
  have hc0 : ([] : List Nat).contains 1 = false := rfl
  refine ⟨{}, okCfg, ?_⟩
  simp only [mockRawOps, hval, hid, hc1, hf1, hc0, Internal.mapRawError, StateT.run, assert, okCfg]
  refine ⟨⟨by decide, Or.inl trivial, rfl⟩, trivial, ⟨⟨_, rfl, rfl, by decide⟩, trivial⟩, trivial⟩

end LeanSwe.ConnectProxy.Raw.Proofs
