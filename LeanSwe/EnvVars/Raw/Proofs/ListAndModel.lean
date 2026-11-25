import LeanSwe.EnvVars.Raw.Proofs.Utf8AndSplit

namespace LeanSwe.EnvVars.Raw.Proofs

open Core
open Core.NondetTest

private theorem decodeEnvironAcc_spec (accRev : List (String × String)) (xs : List ByteArray) :
    Internal.decodeEnvironAcc accRev xs =
      (decodeEnvironList xs).map (fun tail => accRev.reverse ++ tail) := by
  induction xs generalizing accRev with
  | nil => simp [Internal.decodeEnvironAcc, decodeEnvironList, Except.map]
  | cons entry rest ih =>
    unfold Internal.decodeEnvironAcc decodeEnvironList
    cases hsp : Internal.splitFirstEqBytes entry with
    | none => exact ih accRev
    | some kv =>
      rcases kv with ⟨kBytes, vBytes⟩
      dsimp only
      cases hk : String.fromUTF8? kBytes with
      | none => rfl
      | some k =>
        cases hv : String.fromUTF8? vBytes with
        | none => rfl
        | some v =>
          simp only [ih ((k, v) :: accRev), List.reverse_cons, List.append_assoc, List.cons_append, List.nil_append]
          cases decodeEnvironList rest <;> rfl

/-- `Internal.decodeEnvironAcc []` agrees with `decodeEnvironList`. -/
theorem decodeEnvironAcc_nil (xs : List ByteArray) :
    Internal.decodeEnvironAcc [] xs = decodeEnvironList xs := by
  rw [decodeEnvironAcc_spec]
  cases decodeEnvironList xs <;> rfl

/-- Proof of `test_envvarsraw_listEnv_splitsFirstEqualsAndPreservesOrder` for `Internal.mkRawOps`. -/
theorem proof_envvarsraw_listEnv_splitsFirstEqualsAndPreservesOrder :
    AllPass (test_envvarsraw_listEnv_splitsFirstEqualsAndPreservesOrder (Internal.mkRawOps (m := Id))) := by
  intro getSnap pairs hall
  have hitems : ((pairs.map Sum.inr : List (Sum ByteArray (String × String))).all (fun
      | .inl mal => !(mal.data.toList.contains (0x3D : UInt8)) || mal.data.toList.head? == some (0x3D : UInt8)
      | .inr (k, _) => !k.isEmpty && !('=' ∈ k.toList))) = true := by
    rw [List.all_map]
    exact hall
  have hdec : decodeEnvironList (pairs.map (fun x => (x.1 ++ "=" ++ x.2).toUTF8)) = .ok pairs := by
    have h0 := decodeEnvironList_of_items (pairs.map Sum.inr) hitems
    rw [List.map_map, List.filterMap_map] at h0
    have h1 : decodeEnvironList (pairs.map (fun x => (x.1 ++ "=" ++ x.2).toUTF8)) =
        .ok (pairs.filterMap some) := h0
    rw [List.filterMap_some] at h1
    exact h1
  simp only [Internal.mkRawOps, bind, pure, assert, decodeEnvironAcc_nil]
  exact ⟨congrArg (Except.map List.toArray) hdec, trivial⟩

/-- Non-vacuity `CanReach` witness for `test_envvarsraw_listEnv_splitsFirstEqualsAndPreservesOrder`. -/
theorem reach_envvarsraw_listEnv_splitsFirstEqualsAndPreservesOrder :
    CanReach (test_envvarsraw_listEnv_splitsFirstEqualsAndPreservesOrder (Internal.mkRawOps (m := Id))) :=
  ⟨fun _ => none, [("A", "1")], by decide,
    proof_envvarsraw_listEnv_splitsFirstEqualsAndPreservesOrder (fun _ => none) [("A", "1")] (by decide)⟩

/-- Proof of `test_envvarsraw_listEnv_skipsMissingEqualsAndEmptyKey` for `Internal.mkRawOps`. -/
theorem proof_envvarsraw_listEnv_skipsMissingEqualsAndEmptyKey :
    AllPass (test_envvarsraw_listEnv_skipsMissingEqualsAndEmptyKey (Internal.mkRawOps (m := Id))) := by
  intro getSnap items hall
  simp only [Internal.mkRawOps, bind, pure, assert, decodeEnvironAcc_nil]
  exact ⟨congrArg (Except.map List.toArray) (decodeEnvironList_of_items items hall), trivial⟩

/-- Non-vacuity `CanReach` witness for `test_envvarsraw_listEnv_skipsMissingEqualsAndEmptyKey`. -/
theorem reach_envvarsraw_listEnv_skipsMissingEqualsAndEmptyKey :
    CanReach (test_envvarsraw_listEnv_skipsMissingEqualsAndEmptyKey (Internal.mkRawOps (m := Id))) :=
  ⟨fun _ => none, [], rfl,
    proof_envvarsraw_listEnv_skipsMissingEqualsAndEmptyKey (fun _ => none) [] rfl⟩

private theorem decodeEnvironList_append_error (xs ys : List ByteArray) (out : List (String × String))
    (hxs : decodeEnvironList xs = .ok out)
    (err : EnvVarsRawError) (hys : decodeEnvironList ys = .error err) :
    decodeEnvironList (xs ++ ys) = .error err := by
  induction xs generalizing out with
  | nil => exact hys
  | cons x rest ih =>
    change decodeEnvironList (x :: (rest ++ ys)) = .error err
    unfold decodeEnvironList at hxs ⊢
    cases hsx : Internal.splitFirstEqBytes x with
    | none => rw [hsx] at hxs; exact ih out hxs
    | some p =>
      rw [hsx] at hxs
      dsimp only at hxs ⊢
      cases hkx : String.fromUTF8? p.1 with
      | none => rw [hkx] at hxs; cases hxs
      | some kx =>
        rw [hkx] at hxs
        cases hvx : String.fromUTF8? p.2 with
        | none => rw [hvx] at hxs; cases hxs
        | some vx =>
          rw [hvx] at hxs
          cases htail : decodeEnvironList rest with
          | error e => rw [htail] at hxs; cases hxs
          | ok tl =>
            rw [htail] at hxs
            rw [ih tl htail]

/-- Proof of `test_envvarsraw_listEnv_invalidUtf8KeyReturnsNoneKeyError` for `Internal.mkRawOps`. -/
theorem proof_envvarsraw_listEnv_invalidUtf8KeyReturnsNoneKeyError :
    AllPass (test_envvarsraw_listEnv_invalidUtf8KeyReturnsNoneKeyError (Internal.mkRawOps (m := Id))) := by
  intro getSnap pre badKey valBytes tail hpre ⟨hsz, hno, hbad⟩
  have hno' : (0x3D : UInt8) ∉ badKey.data.toList := by
    intro hm
    have hc : badKey.data.toList.contains (0x3D : UInt8) = true := List.contains_iff_mem.mpr hm
    rw [hc] at hno
    cases hno
  have hsp : Internal.splitFirstEqBytes (badKey ++ ByteArray.mk #[0x3D] ++ valBytes) = some (badKey, valBytes) :=
    splitFirstEqBytes_rawConcat badKey valBytes hsz hno'
  have hpreDec := decodeEnvironList_of_items pre hpre
  have hbadEntry : decodeEnvironList ((badKey ++ ByteArray.mk #[0x3D] ++ valBytes) :: tail) =
      .error (.invalidEncoding none "invalid UTF-8 in environment key") := by
    unfold decodeEnvironList
    rw [hsp]
    dsimp only
    rw [hbad]
  have hfull := decodeEnvironList_append_error _ ((badKey ++ ByteArray.mk #[0x3D] ++ valBytes) :: tail) _
    hpreDec _ hbadEntry
  simp only [Internal.mkRawOps, bind, pure, assert, decodeEnvironAcc_nil]
  exact ⟨⟨"invalid UTF-8 in environment key", congrArg (Except.map List.toArray) hfull, by decide⟩, trivial⟩

/-- Non-vacuity `CanReach` witness for `test_envvarsraw_listEnv_invalidUtf8KeyReturnsNoneKeyError`. -/
theorem reach_envvarsraw_listEnv_invalidUtf8KeyReturnsNoneKeyError :
    CanReach (test_envvarsraw_listEnv_invalidUtf8KeyReturnsNoneKeyError (Internal.mkRawOps (m := Id))) :=
  ⟨fun _ => none, [], ByteArray.mk #[0xFF], ByteArray.empty, [], rfl, ⟨by decide, rfl, rfl⟩,
    proof_envvarsraw_listEnv_invalidUtf8KeyReturnsNoneKeyError
      (fun _ => none) [] (ByteArray.mk #[0xFF]) ByteArray.empty [] rfl ⟨by decide, rfl, rfl⟩⟩

/-- Proof of `test_envvarsraw_listEnv_invalidUtf8ValueReturnsSomeKeyError` for `Internal.mkRawOps`. -/
theorem proof_envvarsraw_listEnv_invalidUtf8ValueReturnsSomeKeyError :
    AllPass (test_envvarsraw_listEnv_invalidUtf8ValueReturnsSomeKeyError (Internal.mkRawOps (m := Id))) := by
  intro getSnap pre key badVal tail hpre ⟨hkne, hkno⟩ hbad
  have hsz : key.toUTF8.size > 0 := by
    have hne : key.toUTF8.data.toList ≠ [] := (toUTF8_data_ne_nil_iff key).mpr hkne
    cases hdl : key.toUTF8.data.toList with
    | nil => exact absurd hdl hne
    | cons _ _ =>
      have hlen : key.toUTF8.size = key.toUTF8.data.toList.length := by
        change key.toUTF8.data.size = key.toUTF8.data.toList.length
        exact (Array.length_toList).symm
      rw [hlen, hdl]
      simp
  have hno' : (0x3D : UInt8) ∉ key.toUTF8.data.toList := fun hm =>
    hkno ((eqByte_mem_toUTF8_iff key).mp hm)
  have hsp : Internal.splitFirstEqBytes (key.toUTF8 ++ ByteArray.mk #[0x3D] ++ badVal) = some (key.toUTF8, badVal) :=
    splitFirstEqBytes_rawConcat key.toUTF8 badVal hsz hno'
  have hpreDec := decodeEnvironList_of_items pre hpre
  have hbadEntry : decodeEnvironList ((key.toUTF8 ++ ByteArray.mk #[0x3D] ++ badVal) :: tail) =
      .error (.invalidEncoding (some key) "invalid UTF-8 in environment value") := by
    unfold decodeEnvironList
    rw [hsp]
    dsimp only
    rw [fromUTF8?_toUTF8]
    dsimp only
    rw [hbad]
  have hfull := decodeEnvironList_append_error _ ((key.toUTF8 ++ ByteArray.mk #[0x3D] ++ badVal) :: tail) _
    hpreDec _ hbadEntry
  simp only [Internal.mkRawOps, bind, pure, assert, decodeEnvironAcc_nil]
  exact ⟨⟨"invalid UTF-8 in environment value", congrArg (Except.map List.toArray) hfull, by decide⟩, trivial⟩

/-- Non-vacuity `CanReach` witness for `test_envvarsraw_listEnv_invalidUtf8ValueReturnsSomeKeyError`. -/
theorem reach_envvarsraw_listEnv_invalidUtf8ValueReturnsSomeKeyError :
    CanReach (test_envvarsraw_listEnv_invalidUtf8ValueReturnsSomeKeyError (Internal.mkRawOps (m := Id))) :=
  ⟨fun _ => none, [], "BAD_VAL", ByteArray.mk #[0xFF], [], rfl, ⟨by decide, by decide⟩, rfl,
    proof_envvarsraw_listEnv_invalidUtf8ValueReturnsSomeKeyError
      (fun _ => none) [] "BAD_VAL" (ByteArray.mk #[0xFF]) [] rfl ⟨by decide, by decide⟩ rfl⟩

private theorem decodeEnvironList_keys_wellFormed (entries : List ByteArray)
    (out : List (String × String))
    (hdec : decodeEnvironList entries = .ok out) :
    ∀ p ∈ out, !p.1.isEmpty && !('=' ∈ p.1.toList) := by
  induction entries generalizing out with
  | nil =>
    simp [decodeEnvironList] at hdec
    subst hdec
    intro p hp
    cases hp
  | cons e rest ih =>
    unfold decodeEnvironList at hdec
    cases hsp : Internal.splitFirstEqBytes e with
    | none =>
      rw [hsp] at hdec
      exact ih out hdec
    | some kv =>
      rcases kv with ⟨kBytes, vBytes⟩
      rw [hsp] at hdec
      dsimp only at hdec
      cases hk : String.fromUTF8? kBytes with
      | none => rw [hk] at hdec; cases hdec
      | some k =>
        rw [hk] at hdec
        cases hv : String.fromUTF8? vBytes with
        | none => rw [hv] at hdec; cases hdec
        | some v =>
          rw [hv] at hdec
          cases htail : decodeEnvironList rest with
          | error err => rw [htail] at hdec; cases hdec
          | ok tail =>
            rw [htail] at hdec
            injection hdec with hEq
            subst hEq
            intro p hp
            rcases List.mem_cons.mp hp with rfl | hmem
            · have hsp' : Internal.splitFirstEqList [] e.data.toList = some (kBytes, vBytes) := hsp
              rcases splitFirstEqList_spec kBytes vBytes [] e.data.toList hsp' (by simp) with
                ⟨hneBytes, hnoEqBytes, _, _⟩
              have hkUtf : kBytes = k.toUTF8 := (fromUTF8?_eq_some_iff kBytes k).mp hk
              rw [hkUtf] at hneBytes hnoEqBytes
              have hkne : k ≠ "" := (toUTF8_data_ne_nil_iff k).mp hneBytes
              have hkno : '=' ∉ k.toList := fun hm => hnoEqBytes ((eqByte_mem_toUTF8_iff k).mpr hm)
              have hkEmpty : k.isEmpty = false := by
                cases hke : k.isEmpty with
                | false => rfl
                | true => exact absurd (String.isEmpty_iff.mp hke) hkne
              simp [hkEmpty, hkno]
            · exact ih tail htail p hmem

private theorem decodeEnvironList_nulFree (entries : List ByteArray)
    (out : List (String × String))
    (hnul : ∀ e ∈ entries, (0 : UInt8) ∉ e.data.toList)
    (hdec : decodeEnvironList entries = .ok out) :
    ∀ p ∈ out, !(Char.ofNat 0 ∈ p.1.toList) && !(Char.ofNat 0 ∈ p.2.toList) := by
  induction entries generalizing out with
  | nil =>
    simp [decodeEnvironList] at hdec
    subst hdec
    intro p hp
    cases hp
  | cons e rest ih =>
    have heNul : (0 : UInt8) ∉ e.data.toList := hnul e List.mem_cons_self
    have hrestNul : ∀ x ∈ rest, (0 : UInt8) ∉ x.data.toList := fun x hx =>
      hnul x (List.mem_cons_of_mem e hx)
    unfold decodeEnvironList at hdec
    cases hsp : Internal.splitFirstEqBytes e with
    | none =>
      rw [hsp] at hdec
      exact ih out hrestNul hdec
    | some kv =>
      rcases kv with ⟨kBytes, vBytes⟩
      rw [hsp] at hdec
      dsimp only at hdec
      cases hk : String.fromUTF8? kBytes with
      | none => rw [hk] at hdec; cases hdec
      | some k =>
        rw [hk] at hdec
        cases hv : String.fromUTF8? vBytes with
        | none => rw [hv] at hdec; cases hdec
        | some v =>
          rw [hv] at hdec
          cases htail : decodeEnvironList rest with
          | error err => rw [htail] at hdec; cases hdec
          | ok tail =>
            rw [htail] at hdec
            injection hdec with hEq
            subst hEq
            intro p hp
            rcases List.mem_cons.mp hp with rfl | hmem
            · have hsp' : Internal.splitFirstEqList [] e.data.toList = some (kBytes, vBytes) := hsp
              rcases splitFirstEqList_spec kBytes vBytes [] e.data.toList hsp' (by simp) with
                ⟨_, _, hkmem, hvmem⟩
              have hkUtf : kBytes = k.toUTF8 := (fromUTF8?_eq_some_iff kBytes k).mp hk
              have hvUtf : vBytes = v.toUTF8 := (fromUTF8?_eq_some_iff vBytes v).mp hv
              have h0k : (0 : UInt8) ∉ k.toUTF8.data.toList := by
                intro hm
                rw [← hkUtf] at hm
                rcases hkmem 0 hm with hnil | hmemE
                · cases hnil
                · exact heNul hmemE
              have h0v : (0 : UInt8) ∉ v.toUTF8.data.toList := by
                intro hm
                rw [← hvUtf] at hm
                exact heNul (hvmem 0 hm)
              have hkNul : Char.ofNat 0 ∉ k.toList := fun hm => h0k ((zeroByte_mem_toUTF8_iff k).mpr hm)
              have hvNul : Char.ofNat 0 ∉ v.toList := fun hm => h0v ((zeroByte_mem_toUTF8_iff v).mpr hm)
              simp [hkNul, hvNul]
            · exact ih tail hrestNul htail p hmem

/-- Proof of `test_envvarsraw_listEnv_outputKeysWellFormed` for `Internal.mkRawOps`. -/
theorem proof_envvarsraw_listEnv_outputKeysWellFormed :
    AllPass (test_envvarsraw_listEnv_outputKeysWellFormed (Internal.mkRawOps (m := Id))) := by
  intro getSnap entries pairs hok
  simp only [Internal.mkRawOps, bind, pure, decodeEnvironAcc_nil] at hok
  change (decodeEnvironList entries.toList).map List.toArray = .ok pairs at hok
  cases hdec : decodeEnvironList entries.toList with
  | error err => rw [hdec] at hok; cases hok
  | ok out =>
    rw [hdec] at hok
    injection hok with hEq
    subst hEq
    simp only [assert]
    exact ⟨List.all_eq_true.mpr (decodeEnvironList_keys_wellFormed entries.toList out hdec), trivial⟩

/-- Non-vacuity `CanReach` witness for `test_envvarsraw_listEnv_outputKeysWellFormed`. -/
theorem reach_envvarsraw_listEnv_outputKeysWellFormed :
    CanReach (test_envvarsraw_listEnv_outputKeysWellFormed (Internal.mkRawOps (m := Id))) :=
  ⟨fun _ => none, #[], #[], rfl,
    proof_envvarsraw_listEnv_outputKeysWellFormed (fun _ => none) #[] #[] rfl⟩

/-- Proof of `test_envvarsraw_listEnv_nulFreeInputsPreserveNulFreedom` for `Internal.mkRawOps`. -/
theorem proof_envvarsraw_listEnv_nulFreeInputsPreserveNulFreedom :
    AllPass (test_envvarsraw_listEnv_nulFreeInputsPreserveNulFreedom (Internal.mkRawOps (m := Id))) := by
  intro getSnap entries pairs hnul hok
  simp only [Internal.mkRawOps, bind, pure, decodeEnvironAcc_nil] at hok
  change (decodeEnvironList entries.toList).map List.toArray = .ok pairs at hok
  cases hdec : decodeEnvironList entries.toList with
  | error err => rw [hdec] at hok; cases hok
  | ok out =>
    rw [hdec] at hok
    injection hok with hEq
    subst hEq
    have hnulList : ∀ e ∈ entries.toList, (0 : UInt8) ∉ e.data.toList := by
      intro e he hm
      have hAll := List.all_eq_true.mp hnul e he
      have hc : e.data.toList.contains (0 : UInt8) = true := List.contains_iff_mem.mpr hm
      rw [hc] at hAll
      cases hAll
    have hwf := decodeEnvironList_keys_wellFormed entries.toList out hdec
    have hnf := decodeEnvironList_nulFree entries.toList out hnulList hdec
    simp only [assert]
    refine ⟨List.all_eq_true.mpr fun p hp => ?_, trivial⟩
    have h12 := hwf p hp
    have h34 := hnf p hp
    simp only [Bool.and_eq_true] at h12 h34 ⊢
    exact ⟨⟨⟨h12.1, h12.2⟩, h34.1⟩, h34.2⟩

/-- Non-vacuity `CanReach` witness for `test_envvarsraw_listEnv_nulFreeInputsPreserveNulFreedom`. -/
theorem reach_envvarsraw_listEnv_nulFreeInputsPreserveNulFreedom :
    CanReach (test_envvarsraw_listEnv_nulFreeInputsPreserveNulFreedom (Internal.mkRawOps (m := Id))) :=
  ⟨fun _ => none, #[], #[], rfl, rfl,
    proof_envvarsraw_listEnv_nulFreeInputsPreserveNulFreedom (fun _ => none) #[] #[] rfl rfl⟩

/-- Satisfiability `CanReach` witness for `assume_envvarsraw_listEnv_consistentWithGetEnv`. -/
theorem reach_assume_envvarsraw_listEnv_consistentWithGetEnv :
    CanReach (assume_envvarsraw_listEnv_consistentWithGetEnv
      (Internal.mkRawOps { getEnvBytes := fun _ => none, listEnvironBytes := #[] })) := by
  refine ⟨#[], "PATH", rfl, ⟨by decide, by decide, by decide⟩, ?_⟩
  simp [Internal.mkRawOps, Internal.isValidPosixKey, bind, pure, assert]

/-- Any error produced by `decodeEnvironList` has kind `.invalidEncoding`. -/
theorem decodeEnvironList_only_invalidEncoding (xs : List ByteArray) {err : EnvVarsRawError}
    (herr : decodeEnvironList xs = .error err) : err.kind = .invalidEncoding := by
  induction xs with
  | nil => simp [decodeEnvironList] at herr
  | cons x rest ih =>
    unfold decodeEnvironList at herr
    cases hs : Internal.splitFirstEqBytes x with
    | none => rw [hs] at herr; exact ih herr
    | some kv =>
      rw [hs] at herr
      dsimp only at herr
      rcases kv with ⟨kBytes, vBytes⟩
      cases hkf : String.fromUTF8? kBytes with
      | none => rw [hkf] at herr; injection herr with he; subst he; rfl
      | some k =>
        rw [hkf] at herr
        dsimp only at herr
        cases hvf : String.fromUTF8? vBytes with
        | none => rw [hvf] at herr; injection herr with he; subst he; rfl
        | some v =>
          rw [hvf] at herr
          dsimp only at herr
          cases hr : decodeEnvironList rest with
          | error e => rw [hr] at herr; injection herr with he; subst he; exact ih hr
          | ok tl => rw [hr] at herr; cases herr

private theorem hasInvalidKeyCharModel_eq (cs : List Char) :
    Model.hasInvalidKeyCharModel cs = Internal.hasInvalidKeyChar cs := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    simp only [Model.hasInvalidKeyCharModel, Internal.hasInvalidKeyChar, ih]
    cases (c == '=' || c == Char.ofNat 0) <;> rfl

/-- `Model.isValidPosixKeyModel` agrees pointwise with `Internal.isValidPosixKey`. -/
theorem isValidPosixKeyModel_eq (key : String) :
    Model.isValidPosixKeyModel key = Internal.isValidPosixKey key := by
  simp [Model.isValidPosixKeyModel, Internal.isValidPosixKey, hasInvalidKeyCharModel_eq]

private theorem splitFirstEqListModel_eq (rp bl : List UInt8) :
    Model.splitFirstEqListModel rp bl = Internal.splitFirstEqList rp bl := by
  induction bl generalizing rp with
  | nil => rfl
  | cons b bs ih =>
    simp only [Model.splitFirstEqListModel, Internal.splitFirstEqList]
    split
    · rfl
    · exact ih (b :: rp)

private theorem splitFirstEqBytesModel_eq (entry : ByteArray) :
    Model.splitFirstEqBytesModel entry = Internal.splitFirstEqBytes entry :=
  splitFirstEqListModel_eq [] entry.data.toList

/-- `Model.decodeEnvironModelAcc` agrees pointwise with `Internal.decodeEnvironAcc`. -/
theorem decodeEnvironModelAcc_eq (accRev : List (String × String)) (xs : List ByteArray) :
    Model.decodeEnvironModelAcc accRev xs = Internal.decodeEnvironAcc accRev xs := by
  induction xs generalizing accRev with
  | nil => rfl
  | cons entry rest ih =>
    simp only [Model.decodeEnvironModelAcc, Internal.decodeEnvironAcc, splitFirstEqBytesModel_eq]
    cases Internal.splitFirstEqBytes entry with
    | none => exact ih accRev
    | some kv =>
      rcases kv with ⟨kBytes, vBytes⟩
      dsimp only
      cases String.fromUTF8? kBytes with
      | none => rfl
      | some k =>
        cases String.fromUTF8? vBytes with
        | none => rfl
        | some v => exact ih ((k, v) :: accRev)

/-- `Model.mapRawErrorModel` equals `Internal.mapRawError`. -/
theorem mapRawErrorModel_eq : Model.mapRawErrorModel = Internal.mapRawError := by
  funext r
  cases r <;> rfl

/-- Proof of `test_envvarsraw_mkRaw_matchesModel` for `Internal.mkRawOps`. -/
theorem proof_envvarsraw_mkRaw_matchesModel :
    AllPass (test_envvarsraw_mkRaw_matchesModel (Internal.mkRawOps (m := Id))) := by
  intro s key rawErr
  dsimp [test_envvarsraw_mkRaw_matchesModel]
  simp only [Internal.mkRawOps, Model.modelPosixRawOps,
    Model.rawGetEnvModel, Model.rawListEnvModel, Model.posixGetEnvBytesModel,
    isValidPosixKeyModel_eq, decodeEnvironModelAcc_eq, mapRawErrorModel_eq, Bind.bind, bind, pure, assert]
  refine ⟨?_, trivial, trivial, trivial⟩
  · by_cases hk : Internal.isValidPosixKey key
    · simp only [hk, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
      cases Model.findFirstKeyValue s.entries.toList key.toUTF8 with
      | none => rfl
      | some bs => cases String.fromUTF8? bs <;> rfl
    · simp [hk]

private theorem findFirstKeyValue_eq_decodeEnvironList_find? (xs : List ByteArray)
    (out : List (String × String)) (k : String)
    (hdec : decodeEnvironList xs = .ok out) :
    Model.findFirstKeyValue xs k.toUTF8 =
      (out.find? (fun p => p.1 == k)).map (fun p => p.2.toUTF8) := by
  induction xs generalizing out with
  | nil =>
    simp [decodeEnvironList] at hdec
    subst hdec
    rfl
  | cons entry rest ih =>
    unfold decodeEnvironList at hdec
    unfold Model.findFirstKeyValue
    rw [splitFirstEqBytesModel_eq]
    cases hsp : Internal.splitFirstEqBytes entry with
    | none =>
      rw [hsp] at hdec
      exact ih out hdec
    | some kv =>
      rcases kv with ⟨kBytes, vBytes⟩
      rw [hsp] at hdec
      dsimp only at hdec
      cases hk : String.fromUTF8? kBytes with
      | none => rw [hk] at hdec; cases hdec
      | some k' =>
        rw [hk] at hdec
        cases hv : String.fromUTF8? vBytes with
        | none => rw [hv] at hdec; cases hdec
        | some v' =>
          rw [hv] at hdec
          cases htail : decodeEnvironList rest with
          | error e => rw [htail] at hdec; cases hdec
          | ok tail =>
            rw [htail] at hdec
            injection hdec with hEq
            subst hEq
            have hkUtf : kBytes = k'.toUTF8 := (fromUTF8?_eq_some_iff kBytes k').mp hk
            have hvUtf : vBytes = v'.toUTF8 := (fromUTF8?_eq_some_iff vBytes v').mp hv
            have heqIff : (kBytes == k.toUTF8) = (k' == k) := by
              rw [hkUtf]
              cases h1 : k'.toUTF8 == k.toUTF8
              · cases h2 : k' == k
                · rfl
                · have hs : k' = k := eq_of_beq h2; subst hs; simp at h1
              · have hb : k'.toUTF8 = k.toUTF8 := eq_of_beq h1
                have hs : some k' = some k := by
                  rw [← fromUTF8?_toUTF8 k', hb, fromUTF8?_toUTF8 k]
                injection hs with hs'
                subst hs'
                simp
            simp only [heqIff, List.find?_cons]
            cases hkk : k' == k with
            | true =>
              simp [hvUtf]
            | false =>
              simp only [Bool.false_eq_true, ↓reduceIte]
              exact ih tail htail

private theorem findFirstKeyValue_valid_rawGetEnv (s : Model.EnvironState)
    (out : List (String × String)) (k : String)
    (hvalid : k ≠ "" ∧ '=' ∉ k.toList ∧ Char.ofNat 0 ∉ k.toList)
    (hdec : decodeEnvironList s.entries.toList = .ok out) :
    Model.rawGetEnvModel s k = .ok ((out.find? (fun p => p.1 == k)).map Prod.snd) := by
  have hkPos : Model.isValidPosixKeyModel k = true := by
    rw [isValidPosixKeyModel_eq]
    exact (isValidPosixKey_true_iff k).mpr hvalid
  have hfind := findFirstKeyValue_eq_decodeEnvironList_find? s.entries.toList out k hdec
  unfold Model.rawGetEnvModel Model.posixGetEnvBytesModel
  simp only [hkPos, Bool.not_true, Bool.false_eq_true, ↓reduceIte, hfind]
  cases out.find? (fun p => p.1 == k) with
  | none => rfl
  | some p =>
    dsimp only [Option.map]
    change (match String.fromUTF8? p.2.toUTF8 with
      | some v => Except.ok (some v)
      | none => Except.error (EnvVarsRawError.invalidEncoding (some k) "invalid UTF-8 in environment value")) =
      Except.ok (some p.2)
    rw [fromUTF8?_toUTF8]

/-- Proof of `test_envvarsraw_modelSatisfiesConsistentWithGetEnv` for `Model.modelRawOps`. -/
theorem proof_envvarsraw_modelSatisfiesConsistentWithGetEnv :
    AllPass (test_envvarsraw_modelSatisfiesConsistentWithGetEnv Model.modelRawOps) := by
  intro s pairs k hwf hlist hvalid
  simp only [Model.modelRawOps, Model.rawListEnvModel, decodeEnvironModelAcc_eq,
    decodeEnvironAcc_nil] at hlist ⊢
  cases hdec : decodeEnvironList s.entries.toList with
  | error e => rw [hdec] at hlist; cases hlist
  | ok out =>
    rw [hdec] at hlist
    injection hlist with hEq
    subst hEq
    have hnulList : ∀ e ∈ s.entries.toList, (0 : UInt8) ∉ e.data.toList := by
      intro e he hm
      have hAll := List.all_eq_true.mp hwf e he
      simp only [Model.isNulFreeBytes, Bool.not_eq_true'] at hAll
      have hc : e.data.toList.contains (0 : UInt8) = true := List.contains_iff_mem.mpr hm
      rw [hc] at hAll
      cases hAll
    have hkeys := decodeEnvironList_keys_wellFormed s.entries.toList out hdec
    have hnf := decodeEnvironList_nulFree s.entries.toList out hnulList hdec
    have hall : (List.toArray out).toList.all
        (fun p => !p.1.isEmpty && !('=' ∈ p.1.toList) && !(Char.ofNat 0 ∈ p.1.toList)) = true := by
      apply List.all_eq_true.mpr
      intro p hp
      have hp' : p ∈ out := by simpa using hp
      have h12 := hkeys p hp'
      have h34 := hnf p hp'
      simp only [Bool.and_eq_true] at h12 h34 ⊢
      exact ⟨⟨h12.1, h12.2⟩, h34.1⟩
    have hget := findFirstKeyValue_valid_rawGetEnv s out k hvalid hdec
    simp only [assert]
    exact ⟨⟨hall, by simpa using hget⟩, trivial⟩

/-- Non-vacuity `CanReach` witness for `test_envvarsraw_modelSatisfiesConsistentWithGetEnv`. -/
theorem reach_envvarsraw_modelSatisfiesConsistentWithGetEnv :
    CanReach (test_envvarsraw_modelSatisfiesConsistentWithGetEnv Model.modelRawOps) :=
  ⟨{}, #[], "PATH", rfl, rfl, ⟨by decide, by decide, by decide⟩,
    proof_envvarsraw_modelSatisfiesConsistentWithGetEnv {} #[] "PATH" rfl rfl ⟨by decide, by decide, by decide⟩⟩

end LeanSwe.EnvVars.Raw.Proofs
