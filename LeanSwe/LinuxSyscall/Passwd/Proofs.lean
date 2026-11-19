import LeanSwe.LinuxSyscall.Passwd.Types
import LeanSwe.LinuxSyscall.Passwd.Impl
import LeanSwe.LinuxSyscall.Passwd.Interface
import LeanSwe.LinuxSyscall.Passwd.Model
import LeanSwe.LinuxSyscall.Passwd.SpecTests
import Std.Data.DTreeMap.Internal.Lemmas

namespace LeanSwe.LinuxSyscall.Passwd.Proofs

open Core (NondetTest AllPass CanReach)
open Core.NondetTest
open LeanSwe.LinuxSyscall
open LeanSwe.LinuxSyscall.Passwd
open Std.DTreeMap.Internal

private theorem list_foldl_and_eq_true {K V : Type} (p : K → V → Bool)
    (l : List ((_ : K) × V)) (init : Bool) :
    l.foldl (fun acc e => acc && p e.1 e.2) init = true ↔
      init = true ∧ ∀ e ∈ l, p e.1 e.2 = true := by
  induction l generalizing init with
  | nil => simp
  | cons hd tl ih =>
    simp only [List.foldl_cons, List.mem_cons, forall_eq_or_imp]
    rw [ih]
    simp [Bool.and_eq_true, and_assoc]

private theorem treemap_get?_insert_self {K V : Type} [Ord K] [Std.TransOrd K]
    (t : Std.TreeMap K V) (k : K) (v : V) :
    (t.insert k v).get? k = some v := by
  change Impl.Const.get? (Impl.insert k v t.inner.inner t.inner.wf.balanced).impl k = some v
  rw [Impl.Const.get?_insert t.inner.wf]
  simp [Std.ReflCmp.compare_self]

private theorem treemap_foldl_lookup {K V : Type} [Ord K] [Std.TransOrd K] [Std.LawfulEqOrd K]
    {t : Std.TreeMap K V} {p : K → V → Bool}
    (hwf : t.foldl (fun acc k v => acc && p k v) true = true)
    {k : K} {v : V} (hget : t.get? k = some v) : p k v = true := by
  have hfold : Impl.foldl (fun acc k v => acc && p k v) true t.inner.inner = true := hwf
  rw [Impl.foldl_eq_foldl_toList, list_foldl_and_eq_true] at hfold
  have hget' : t.inner.inner.get? k = some v := by
    change Impl.Const.get? t.inner.inner k = some v at hget
    rw [Impl.Const.get?_eq_get? t.inner.wf] at hget
    exact hget
  have hmem := (Impl.mem_toList_iff_get?_eq_some t.inner.wf).2 hget'
  exact hfold.2 ⟨k, v⟩ hmem

private theorem treemap_foldl_insert {K V : Type} [Ord K] [Std.TransOrd K] [Std.LawfulEqOrd K]
    {t : Std.TreeMap K V} {p : K → V → Bool}
    (hwf : t.foldl (fun acc k v => acc && p k v) true = true)
    (k : K) (v : V) (hp : p k v = true) :
    (t.insert k v).foldl (fun acc k v => acc && p k v) true = true := by
  have hfold : Impl.foldl (fun acc k v => acc && p k v) true t.inner.inner = true := hwf
  rw [Impl.foldl_eq_foldl_toList, list_foldl_and_eq_true] at hfold
  change Impl.foldl (fun acc k v => acc && p k v) true (t.insert k v).inner.inner = true
  rw [Impl.foldl_eq_foldl_toList, list_foldl_and_eq_true]
  refine ⟨rfl, fun ⟨k', v'⟩ hmem => ?_⟩
  have hwf' : (t.insert k v).inner.inner.WF := (t.insert k v).inner.wf
  have hget' := (Impl.mem_toList_iff_get?_eq_some hwf').1 hmem
  rw [← Impl.Const.get?_eq_get? hwf'] at hget'
  change Impl.Const.get? (Impl.insert k v t.inner.inner t.inner.wf.balanced).impl k' = some v' at hget'
  rw [Impl.Const.get?_insert t.inner.wf] at hget'
  by_cases hcmp : compare k k' = .eq
  · simp only [hcmp, ↓reduceIte, Option.some.injEq] at hget'
    have hkeq : k = k' := Std.LawfulEqCmp.eq_of_compare hcmp
    subst hkeq hget'
    exact hp
  · simp only [hcmp, ↓reduceIte] at hget'
    rw [Impl.Const.get?_eq_get? t.inner.wf] at hget'
    have hmem0 := (Impl.mem_toList_iff_get?_eq_some t.inner.wf).2 hget'
    exact hfold.2 ⟨k', v'⟩ hmem0

private def overCapWitness : ByteArray :=
  ByteArray.mk (Array.replicate (MAX_PASSWD_NAME_BYTES + 1) 97)

private theorem validPasswdName_overCapWitness :
    validPasswdName overCapWitness = true :=
  validPasswdName_replicate (MAX_PASSWD_NAME_BYTES + 1) 97 (by decide)

private theorem overCapWitness_size_gt :
    overCapWitness.size > MAX_PASSWD_NAME_BYTES := by
  change (Array.replicate (MAX_PASSWD_NAME_BYTES + 1) (97 : UInt8)).size > MAX_PASSWD_NAME_BYTES
  rw [Array.size_replicate]
  omega

private theorem lookupPasswdByUid_set_self (db : Std.TreeMap UInt32 (Option PasswdEntry))
    (uid : UInt32) (v : Option PasswdEntry) :
    lookupPasswdByUid (setPasswdByUid db uid v) uid = some v :=
  treemap_get?_insert_self db uid v

private theorem lookupPasswdByName_set_self (db : Std.TreeMap ByteArray (Option PasswdEntry))
    (name : ByteArray) (v : Option PasswdEntry) :
    lookupPasswdByName (setPasswdByName db name v) name = some v :=
  treemap_get?_insert_self db name v

private theorem lookupPasswdByUid_wellFormed {db : Std.TreeMap UInt32 (Option PasswdEntry)}
    {uid : UInt32} {v : Option PasswdEntry}
    (hwf : db.foldl (fun acc k v => acc && isValidUidEntry k v) true = true)
    (hlookup : lookupPasswdByUid db uid = some v) :
    isValidUidEntry uid v = true :=
  treemap_foldl_lookup hwf hlookup

private theorem lookupPasswdByName_wellFormed {db : Std.TreeMap ByteArray (Option PasswdEntry)}
    {name : ByteArray} {v : Option PasswdEntry}
    (hwf : db.foldl (fun acc k v => acc && isValidNameEntry k v) true = true)
    (hlookup : lookupPasswdByName db name = some v) :
    isValidNameEntry name v = true :=
  treemap_foldl_lookup hwf hlookup

private theorem setPasswdByUid_wellFormed (db : Std.TreeMap UInt32 (Option PasswdEntry))
    (uid : UInt32) (v : Option PasswdEntry)
    (hwf : db.foldl (fun acc k v => acc && isValidUidEntry k v) true = true)
    (hv : isValidUidEntry uid v = true) :
    (setPasswdByUid db uid v).foldl (fun acc k v => acc && isValidUidEntry k v) true = true :=
  treemap_foldl_insert hwf uid v hv

private theorem setPasswdByName_wellFormed (db : Std.TreeMap ByteArray (Option PasswdEntry))
    (name : ByteArray) (v : Option PasswdEntry)
    (hwf : db.foldl (fun acc k v => acc && isValidNameEntry k v) true = true)
    (hv : isValidNameEntry name v = true) :
    (setPasswdByName db name v).foldl (fun acc k v => acc && isValidNameEntry k v) true = true :=
  treemap_foldl_insert hwf name v hv

private theorem modelOps_getpwuid_eval (uid : UInt32) (s : PasswdState) :
    modelOps.getpwuid uid s =
      match lookupPasswdByUid s.byUid uid with
      | none => (.ok none, { s with byUid := setPasswdByUid s.byUid uid none })
      | some none => (.ok none, s)
      | some (some entry) =>
        if entry.hasNoEmbeddedNul && entry.uid == uid then (.ok (some entry), s)
        else (.error Errno.EIO, s) := by
  dsimp [modelOps, Bind.bind, Pure.pure, get, getThe, MonadStateOf.get, set,
    StateT.bind, StateT.pure, StateT.get, StateT.set, MonadState.set]
  cases lookupPasswdByUid s.byUid uid with
  | none => rfl
  | some opt =>
    cases opt with
    | none => rfl
    | some entry =>
      by_cases h : (entry.hasNoEmbeddedNul && entry.uid == uid) = true
      · simp [h]; rfl
      · simp [h]; rfl

private theorem modelOps_getpwnam_eval (name : ByteArray) (s : PasswdState) :
    modelOps.getpwnam name s =
      if !validPasswdName name then
        (.error Errno.EINVAL, s)
      else if name.size > MAX_PASSWD_NAME_BYTES then
        (.error Errno.ENAMETOOLONG, s)
      else
        match lookupPasswdByName s.byName name with
        | none => (.ok none, { s with byName := setPasswdByName s.byName name none })
        | some none => (.ok none, s)
        | some (some entry) =>
          if entry.hasNoEmbeddedNul && entry.name == name then (.ok (some entry), s)
          else (.error Errno.EIO, s) := by
  dsimp only [modelOps]
  by_cases hv : validPasswdName name = true
  · simp only [hv, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    by_cases hlen : name.size > MAX_PASSWD_NAME_BYTES
    · simp only [hlen, ↓reduceIte]
      rfl
    · simp only [hlen, ↓reduceIte]
      dsimp [Bind.bind, Pure.pure, get, getThe, MonadStateOf.get, set,
        StateT.bind, StateT.pure, StateT.get, StateT.set, MonadState.set]
      cases lookupPasswdByName s.byName name with
      | none => rfl
      | some opt =>
        cases opt with
        | none => rfl
        | some entry =>
          by_cases h : (entry.hasNoEmbeddedNul && entry.name == name) = true
          · simp [h]; rfl
          · simp [h]; rfl
  · have hvF : validPasswdName name = false := by
      cases hb : validPasswdName name <;> simp_all
    simp only [hvF, Bool.not_false, ↓reduceIte]
    rfl

/-- Proof of `test_passwd_errno_classificationAndTransient`. -/
theorem proof_passwd_errno_classificationAndTransient :
    AllPass test_passwd_errno_classificationAndTransient := by
  intro e
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, trivial⟩

/-- Proof of `test_passwd_entry_utf8Accessors`. -/
theorem proof_passwd_entry_utf8Accessors :
    AllPass test_passwd_entry_utf8Accessors := by
  intro entry
  exact ⟨rfl, rfl, rfl, rfl, rfl, by decide, by decide, rfl, trivial⟩

/-- Non-vacuity `CanReach` witness for `test_passwd_entry_utf8Accessors`. -/
theorem reach_passwd_entry_utf8Accessors :
    CanReach test_passwd_entry_utf8Accessors :=
  ⟨default, proof_passwd_entry_utf8Accessors default⟩

/-- Proof of `test_passwd_ops_exactContracts` for `modelOps`. -/
theorem proof_passwd_ops_exactContracts :
    AllPass (test_passwd_ops_exactContracts modelOps) := by
  intro s₀ uid name badName overCapName entry _ hbad hOverValid hOverSize hNamValid hNamSize
    hNul hUid hName
  dsimp only [test_passwd_ops_exactContracts, NondetTest.assert, Bind.bind, Pure.pure, StateT.run]
  have hBad : modelOps.getpwnam badName s₀ = (.error Errno.EINVAL, s₀) := by
    rw [modelOps_getpwnam_eval]
    simp [hbad]
  have hOver : modelOps.getpwnam overCapName s₀ = (.error Errno.ENAMETOOLONG, s₀) := by
    rw [modelOps_getpwnam_eval]
    simp [hOverValid, hOverSize]
  have hNamNotGt : ¬ (name.size > MAX_PASSWD_NAME_BYTES) := by omega
  let sAbs : PasswdState :=
    { s₀ with
      byUid := setPasswdByUid s₀.byUid uid none
      byName := setPasswdByName s₀.byName name none }
  have hAbsUid : modelOps.getpwuid uid sAbs = (.ok none, sAbs) := by
    rw [modelOps_getpwuid_eval]
    simp [sAbs, lookupPasswdByUid_set_self]
  have hAbsNam : modelOps.getpwnam name sAbs = (.ok none, sAbs) := by
    rw [modelOps_getpwnam_eval]
    have hLookup : lookupPasswdByName sAbs.byName name = some none :=
      lookupPasswdByName_set_self _ _ _
    simp [sAbs, hLookup, hNamValid, hNamNotGt]
  let sPres : PasswdState :=
    { s₀ with
      byUid := setPasswdByUid s₀.byUid uid (some entry)
      byName := setPasswdByName s₀.byName name (some entry) }
  have hPresUid : modelOps.getpwuid uid sPres = (.ok (some entry), sPres) := by
    rw [modelOps_getpwuid_eval]
    have hLookup : lookupPasswdByUid sPres.byUid uid = some (some entry) :=
      lookupPasswdByUid_set_self _ _ _
    simp [sPres, hLookup, hNul, hUid]
  have hPresNam : modelOps.getpwnam name sPres = (.ok (some entry), sPres) := by
    rw [modelOps_getpwnam_eval]
    have hLookup : lookupPasswdByName sPres.byName name = some (some entry) :=
      lookupPasswdByName_set_self _ _ _
    simp [sPres, hLookup, hNul, hName, hNamValid, hNamNotGt]
  refine ⟨hBad, hOver, hAbsUid, hAbsNam, hPresUid, hPresNam, trivial⟩

/-- Non-vacuity `CanReach` witness for `test_passwd_ops_exactContracts`. -/
theorem reach_passwd_ops_exactContracts :
    CanReach (test_passwd_ops_exactContracts modelOps) := by
  let e : PasswdEntry :=
    { name := ByteArray.empty, uid := 0, gid := 0,
      gecos := ByteArray.empty, homeDir := ByteArray.empty, shell := ByteArray.empty }
  refine ⟨PasswdState.initial, 0, ByteArray.empty, ByteArray.mk #[0], overCapWitness, e,
    by decide, by decide, validPasswdName_overCapWitness, overCapWitness_size_gt,
    by decide, by decide, by decide, rfl, rfl, ?_⟩
  exact proof_passwd_ops_exactContracts PasswdState.initial 0 ByteArray.empty (ByteArray.mk #[0])
    overCapWitness e (by decide) (by decide) validPasswdName_overCapWitness overCapWitness_size_gt
    (by decide) (by decide) (by decide) rfl rfl

/-- Proof of `test_passwd_allowedStep_nssSemantics` for `allowedStep`. -/
theorem proof_passwd_allowedStep_nssSemantics :
    AllPass test_passwd_allowedStep_nssSemantics := by
  intro sRaw uid overCapName _ hOverValid hOverSize
  dsimp only [test_passwd_allowedStep_nssSemantics, NondetTest.assert, Bind.bind]
  let rootName := asciiBytes ['r', 'o', 'o', 't']
  let otherName := asciiBytes ['o', 't', 'h', 'e', 'r']
  let badName := ByteArray.mk #[114, 0, 111]
  let entryOk : PasswdEntry :=
    { name := rootName, uid := uid, gid := 0, gecos := rootName,
      homeDir := asciiBytes ['/', 'r', 'o', 'o', 't'],
      shell := asciiBytes ['/', 'b', 'i', 'n', '/', 's', 'h'] }
  let entryOther : PasswdEntry := { entryOk with homeDir := asciiBytes ['/', 't', 'm', 'p'] }
  let entryWrongUid : PasswdEntry := { entryOk with uid := uid + 1 }
  let entryWrongName : PasswdEntry := { entryOk with name := otherName }
  let entryWithNul : PasswdEntry := { entryOk with homeDir := ByteArray.mk #[47, 0, 120] }
  have hBadValid : validPasswdName badName = false := by decide
  have hRootValid : validPasswdName rootName = true := by decide
  have hRootSize : ¬ (rootName.size > MAX_PASSWD_NAME_BYTES) := by decide
  have hEntryOkNul : entryOk.hasNoEmbeddedNul = true := by
    simp only [entryOk, rootName, PasswdEntry.hasNoEmbeddedNul, asciiBytes]
    decide
  have hWithNulF : entryWithNul.hasNoEmbeddedNul = false := by
    simp only [entryWithNul, entryOk, rootName, PasswdEntry.hasNoEmbeddedNul, asciiBytes]
    decide
  have hWrongUidF : (entryWrongUid.uid == uid) = false := by
    have hLt : uid.toNat < 2 ^ 32 := uid.toNat_lt
    have hNe : uid + 1 ≠ uid := by
      intro h
      have h2 := congrArg UInt32.toNat h
      rw [UInt32.toNat_add] at h2
      have hOne : (1 : UInt32).toNat = 1 := rfl
      rw [hOne] at h2
      omega
    simp [entryWrongUid, hNe]
  have hWrongNameF : (entryWrongName.name == rootName) = false := by
    simp [entryWrongName, rootName, otherName, asciiBytes]
  let s : PasswdState :=
    { sRaw with ambientSeccomp := false, transientNssUnavail := false, byUid := ∅, byName := ∅ }
  have hEmptyUid : lookupPasswdByUid (∅ : Std.TreeMap UInt32 (Option PasswdEntry)) uid = none := by
    rfl
  have hEmptyNam : lookupPasswdByName (∅ : Std.TreeMap ByteArray (Option PasswdEntry)) rootName = none := by
    rfl
  have h1 :
      allowedStep s (.getpwnam badName) .notFound = none ∧
      allowedStep s (.getpwnam badName) (.found entryOk) = none ∧
      allowedStep s (.getpwnam badName) (.err Errno.ERANGE) = none ∧
      allowedStep s (.getpwnam badName) (.err Errno.EINVAL) = some s ∧
      allowedStep s (.getpwnam overCapName) .notFound = none ∧
      allowedStep s (.getpwnam overCapName) (.err Errno.EIO) = none ∧
      allowedStep s (.getpwnam overCapName) (.err Errno.ENAMETOOLONG) = some s ∧
      allowedStep s (.getpwuid uid) (.found entryWithNul) = none ∧
      allowedStep s (.getpwuid uid) (.found entryWrongUid) = none ∧
      allowedStep s (.getpwnam rootName) (.found entryWrongName) = none ∧
      allowedStep s (.getpwuid uid) (.err Errno.EINVAL) = none ∧
      allowedStep s (.getpwuid uid) (.err Errno.EFAULT) = none ∧
      allowedStep s (.getpwuid uid) (.err Errno.EPIPE) = none ∧
      allowedStep s (.getpwnam rootName) (.err Errno.EPIPE) = none ∧
      allowedStep s (.getpwuid uid) (.err Errno.ERANGE) = some s ∧
      allowedStep s (.getpwuid uid) (.err Errno.EINTR) = some s ∧
      allowedStep s (.getpwnam rootName) (.err Errno.EIO) = some s ∧
      allowedStep s (.getpwuid uid) (.err Errno.ENOENT) = some s ∧
      allowedStep s (.getpwuid uid) (.err Errno.ENXIO) = some s ∧
      allowedStep s (.getpwnam rootName) (.err Errno.ENXIO) = some s ∧
      allowedStep s (.getpwnam rootName) (.err Errno.EAGAIN) = some s ∧
      allowedStep s (.getpwnam rootName) (.err Errno.ENODEV) = some s ∧
      allowedStep s (.getpwnam rootName) (.err Errno.ENOTDIR) = some s ∧
      allowedStep s (.getpwnam rootName) (.err Errno.EISDIR) = some s ∧
      allowedStep s (.getpwuid uid) (.err Errno.ESPIPE) = some s ∧
      allowedStep s (.getpwnam rootName) (.err Errno.ESPIPE) = some s ∧
      allowedStep s (.getpwnam rootName) (.err Errno.ENAMETOOLONG) = some s ∧
      allowedStep s (.getpwnam rootName) (.err Errno.ELOOP) = some s ∧
      allowedStep s (.getpwuid uid) (.err Errno.EMFILE) = some s ∧
      allowedStep s (.getpwuid uid) (.err Errno.ENFILE) = some s ∧
      allowedStep s (.getpwuid uid) (.err Errno.ENOMEM) = some s ∧
      allowedStep s (.getpwuid uid) (.err Errno.EPERM) = some s ∧
      allowedStep s (.getpwuid uid) (.err Errno.EACCES) = some s := by
    simp [s, allowedStep, allowedStepCore, isUserspaceInvalidReq, hBadValid, hOverValid, hOverSize,
      hRootValid, hRootSize, hWithNulF, hWrongUidF, hWrongNameF, hEmptyUid, hEmptyNam,
      isAllowedPasswdOsErrno, Errno.EINVAL, Errno.ERANGE, Errno.EFAULT, Errno.EPIPE, Errno.ENOENT,
      Errno.ENXIO, Errno.EINTR, Errno.EIO, Errno.EMFILE, Errno.ENFILE, Errno.ENOMEM, Errno.EPERM,
      Errno.EACCES, Errno.EAGAIN, Errno.ENODEV, Errno.ENOTDIR, Errno.EISDIR, Errno.ESPIPE,
      Errno.ENAMETOOLONG, Errno.ELOOP]
  have hAbsUidEq : allowedStep s (.getpwuid uid) .notFound =
      some { s with byUid := setPasswdByUid ∅ uid none } := by
    simp [s, allowedStep, allowedStepCore, hEmptyUid]
  have hAbsNamEq : allowedStep s (.getpwnam rootName) .notFound =
      some { s with byName := setPasswdByName ∅ rootName none } := by
    simp [s, allowedStep, allowedStepCore, hRootValid, hRootSize, hEmptyNam]
  have hFoundUidEq : allowedStep s (.getpwuid uid) (.found entryOk) =
      some { s with byUid := setPasswdByUid ∅ uid (some entryOk) } := by
    simp [s, allowedStep, allowedStepCore, hEmptyUid, hEntryOkNul, entryOk]
  have hFoundNamEq : allowedStep s (.getpwnam rootName) (.found entryOk) =
      some { s with byName := setPasswdByName ∅ rootName (some entryOk) } := by
    simp [s, allowedStep, allowedStepCore, hRootValid, hRootSize, hEmptyNam, hEntryOkNul, entryOk]
  rw [hAbsUidEq, hAbsNamEq, hFoundUidEq, hFoundNamEq]
  dsimp only
  rcases h1 with ⟨c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14,
    c15, c16, c17, c18, c19, c20, c21, c22, c23, c24, c25, c26, c27,
    c28, c29, c30, c31, c32⟩
  refine ⟨c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14,
    c15, c16, c17, c18, c19, c20, c21, c22, c23, c24, c25, c26, c27,
    c28, c29, c30, c31, c32,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, trivial⟩
  · simp [allowedStep, allowedStepCore, lookupPasswdByUid_set_self]
  · simp [allowedStep, allowedStepCore, lookupPasswdByUid_set_self]
  · simp [allowedStep, allowedStepCore, hRootValid, hRootSize, lookupPasswdByName_set_self, rootName]
  · simp [allowedStep, allowedStepCore, hRootValid, hRootSize, lookupPasswdByName_set_self, rootName]
  · simp [allowedStep, allowedStepCore, lookupPasswdByUid_set_self]
  · simp [allowedStep, allowedStepCore, lookupPasswdByUid_set_self, entryOk, rootName, asciiBytes]
  · simp [allowedStep, allowedStepCore, lookupPasswdByUid_set_self, entryOk, rootName, hEntryOkNul]
  · simp [allowedStep, allowedStepCore, hRootValid, hRootSize, lookupPasswdByName_set_self, rootName]
  · simp [allowedStep, allowedStepCore, lookupPasswdByName_set_self, rootName, entryOk, asciiBytes]
  · simp [allowedStep, allowedStepCore, hRootValid, hRootSize, lookupPasswdByName_set_self,
      rootName, entryOk, hEntryOkNul]

/-- Non-vacuity `CanReach` witness for `test_passwd_allowedStep_nssSemantics`. -/
theorem reach_passwd_allowedStep_nssSemantics :
    CanReach test_passwd_allowedStep_nssSemantics := by
  refine ⟨PasswdState.initial, 0, overCapWitness,
    by decide, validPasswdName_overCapWitness, overCapWitness_size_gt, ?_⟩
  exact proof_passwd_allowedStep_nssSemantics PasswdState.initial 0 overCapWitness
    (by decide) validPasswdName_overCapWitness overCapWitness_size_gt

/-- Proof of `test_passwd_allowedStep_withOuterSeccomp` for `allowedStep`. -/
theorem proof_passwd_allowedStep_withOuterSeccomp :
    AllPass test_passwd_allowedStep_withOuterSeccomp := by
  intro sRaw uid overCapName hOverValid hOverSize
  dsimp only [test_passwd_allowedStep_withOuterSeccomp, NondetTest.assert, Bind.bind]
  let sBase : PasswdState := { sRaw with byUid := ∅, byName := ∅ }
  let rootName := asciiBytes ['r', 'o', 'o', 't']
  let badName := ByteArray.mk #[114, 0, 111]
  let entryOk : PasswdEntry :=
    { name := rootName, uid := uid, gid := 0, gecos := rootName,
      homeDir := asciiBytes ['/', 'r', 'o', 'o', 't'],
      shell := asciiBytes ['/', 'b', 'i', 'n', '/', 's', 'h'] }
  let entryOther : PasswdEntry := { entryOk with homeDir := asciiBytes ['/', 't', 'm', 'p'] }
  let entryWrongUid : PasswdEntry := { entryOk with uid := uid + 1 }
  let entryWrongName : PasswdEntry := { entryOk with name := asciiBytes ['o', 't', 'h', 'e', 'r'] }
  let entryWithNul : PasswdEntry := { entryOk with homeDir := ByteArray.mk #[47, 0, 120] }
  have hRootValid : validPasswdName rootName = true := by decide
  have hRootSize : ¬ (rootName.size > MAX_PASSWD_NAME_BYTES) := by decide
  have hBadValid : validPasswdName badName = false := by decide
  have hEntryOkNul : entryOk.hasNoEmbeddedNul = true := by
    simp only [entryOk, rootName, PasswdEntry.hasNoEmbeddedNul, asciiBytes]
    decide
  have hWithNulF : entryWithNul.hasNoEmbeddedNul = false := by
    simp only [entryWithNul, entryOk, rootName, PasswdEntry.hasNoEmbeddedNul, asciiBytes]
    decide
  have hWrongUidF : (entryWrongUid.uid == uid) = false := by
    have hLt : uid.toNat < 2 ^ 32 := uid.toNat_lt
    have hNe : uid + 1 ≠ uid := by
      intro h
      have h2 := congrArg UInt32.toNat h
      rw [UInt32.toNat_add] at h2
      have hOne : (1 : UInt32).toNat = 1 := rfl
      rw [hOne] at h2
      omega
    simp [entryWrongUid, hNe]
  have hWrongNameF : (entryWrongName.name == rootName) = false := by
    simp [entryWrongName, rootName, asciiBytes]
  let sNoSec : PasswdState := { sBase with ambientSeccomp := false, transientNssUnavail := false }
  let sSec := sNoSec.withOuterSeccomp
  let sTrans := sNoSec.withTransientNssUnavail
  let sSecFound : PasswdState :=
    { sSec with
      byUid := setPasswdByUid sSec.byUid uid (some entryOther)
      byName := setPasswdByName sSec.byName rootName (some entryOther) }
  let sTransFound : PasswdState :=
    { sTrans with
      byUid := setPasswdByUid sTrans.byUid uid (some entryOther)
      byName := setPasswdByName sTrans.byName rootName (some entryOther) }
  have hU : lookupPasswdByUid sBase.byUid uid = none := rfl
  have hN : lookupPasswdByName sBase.byName rootName = none := rfl
  have hBase :
      PasswdState.initial.ambientSeccomp = false ∧
      PasswdState.initial.transientNssUnavail = false ∧
      sSec.ambientSeccomp = true ∧
      allowedStep sNoSec (.getpwuid uid) (.err Errno.ENOSYS) = none ∧
      allowedStep sSec (.getpwuid uid) (.err Errno.ENOSYS) = some sSec ∧
      allowedStep sSec (.getpwnam rootName) (.err Errno.EPERM) = some sSec ∧
      allowedStep sSec (.getpwnam badName) (.err Errno.ENOSYS) = none ∧
      allowedStep sSec (.getpwnam overCapName) (.err Errno.ENOSYS) = none ∧
      allowedStep sSec (.getpwuid uid) (.err Errno.EFAULT) = none ∧
      allowedStep sSec (.getpwnam rootName) (.err Errno.EFAULT) = none ∧
      allowedStep sSec (.getpwuid uid) (.err 0) = none ∧
      allowedStep sSec (.getpwuid uid) (.err 4096) = none := by
    simp [PasswdState.initial, PasswdState.withOuterSeccomp, sNoSec, sSec, rootName, badName,
      allowedStep, allowedStepCore, isUserspaceInvalidReq, hRootValid, hRootSize, hBadValid,
      hOverValid, hOverSize, hU, hN, isAllowedPasswdOsErrno, Errno.ENOSYS, Errno.EINVAL,
      Errno.EPERM, Errno.EFAULT, Errno.ERANGE, Errno.ENOENT, Errno.ENXIO, Errno.EINTR,
      Errno.EIO, Errno.EMFILE, Errno.ENFILE, Errno.ENOMEM, Errno.EACCES, Errno.EAGAIN,
      Errno.ENODEV, Errno.ENOTDIR, Errno.EISDIR, Errno.ESPIPE, Errno.ENAMETOOLONG, Errno.ELOOP]
  have hSecF :
      allowedStep sSecFound (.getpwuid uid) .notFound = some sSecFound ∧
      allowedStep sSecFound (.getpwuid uid) (.found entryOk) = some sSecFound ∧
      allowedStep sSecFound (.getpwnam rootName) .notFound = some sSecFound ∧
      allowedStep sSecFound (.getpwnam rootName) (.found entryOk) = some sSecFound ∧
      allowedStep sSecFound (.getpwuid uid) (.found entryWrongUid) = none ∧
      allowedStep sSecFound (.getpwnam rootName) (.found entryWrongName) = none ∧
      allowedStep sSecFound (.getpwuid uid) (.found entryWithNul) = none ∧
      allowedStep sSecFound (.getpwnam badName) .notFound = none ∧
      allowedStep sSecFound (.getpwnam overCapName) .notFound = none := by
    have hNeOther : (entryOk == entryOther) = false := by
      simp [entryOk, entryOther, asciiBytes]
    have hNeWrongName : (entryWrongName == entryOther) = false := by
      simp [entryWrongName, entryOk, entryOther, rootName, asciiBytes]
    simp [sSecFound, sSec, sNoSec, PasswdState.withOuterSeccomp, allowedStep, allowedStepCore,
      isUserspaceInvalidReq, isValidNssFallbackOutcome, lookupPasswdByUid_set_self,
      lookupPasswdByName_set_self, hRootValid, hRootSize, hBadValid, hOverValid, hOverSize,
      hEntryOkNul, hWithNulF, hWrongUidF, hWrongNameF, hNeOther, hNeWrongName, entryOk]
  have hTransF :
      allowedStep sTransFound (.getpwuid uid) .notFound = some sTransFound ∧
      allowedStep sTransFound (.getpwuid uid) (.found entryOk) = some sTransFound ∧
      allowedStep sTransFound (.getpwnam rootName) .notFound = some sTransFound ∧
      allowedStep sTransFound (.getpwnam rootName) (.found entryOk) = some sTransFound ∧
      allowedStep sTransFound (.getpwuid uid) (.found entryWrongUid) = none ∧
      allowedStep sTransFound (.getpwnam rootName) (.found entryWrongName) = none ∧
      allowedStep sTransFound (.getpwuid uid) (.err Errno.EPIPE) = none ∧
      allowedStep sTransFound (.getpwnam badName) .notFound = none ∧
      allowedStep sTransFound (.getpwnam overCapName) .notFound = none := by
    have hNeOther : (entryOk == entryOther) = false := by
      simp [entryOk, entryOther, asciiBytes]
    have hNeWrongName : (entryWrongName == entryOther) = false := by
      simp [entryWrongName, entryOk, entryOther, rootName, asciiBytes]
    simp [sTransFound, sTrans, sNoSec, PasswdState.withTransientNssUnavail, allowedStep,
      allowedStepCore, isUserspaceInvalidReq, isValidNssFallbackOutcome, lookupPasswdByUid_set_self,
      lookupPasswdByName_set_self, hRootValid, hRootSize, hBadValid, hOverValid, hOverSize,
      hEntryOkNul, hWrongUidF, hWrongNameF, hNeOther, hNeWrongName, isAllowedPasswdOsErrno,
      Errno.EPIPE, Errno.ERANGE, Errno.EINTR, Errno.EIO, Errno.EMFILE, Errno.ENFILE,
      Errno.ENOMEM, Errno.EPERM, Errno.EACCES, Errno.ENOENT, Errno.ENXIO, Errno.EAGAIN,
      Errno.ENODEV, Errno.ENOTDIR, Errno.EISDIR, Errno.ESPIPE, Errno.ENAMETOOLONG, Errno.ELOOP,
      entryOk]
  rcases hBase with ⟨b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11⟩
  rcases hSecF with ⟨sf0, sf1, sf2, sf3, sf4, sf5, sf6, sf7, sf8⟩
  rcases hTransF with ⟨tf0, tf1, tf2, tf3, tf4, tf5, tf6, tf7, tf8⟩
  exact ⟨b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11,
    sf0, sf1, sf2, sf3, sf4, sf5, sf6, sf7, sf8,
    tf0, tf1, tf2, tf3, tf4, tf5, tf6, tf7, tf8, trivial⟩

/-- Non-vacuity `CanReach` witness for `test_passwd_allowedStep_withOuterSeccomp`. -/
theorem reach_passwd_allowedStep_withOuterSeccomp :
    CanReach test_passwd_allowedStep_withOuterSeccomp := by
  refine ⟨PasswdState.initial, 0, overCapWitness,
    validPasswdName_overCapWitness, overCapWitness_size_gt, ?_⟩
  exact proof_passwd_allowedStep_withOuterSeccomp PasswdState.initial 0 overCapWitness
    validPasswdName_overCapWitness overCapWitness_size_gt

/-- Proof of `test_passwd_modelOps_soundAgainstAllowedStep` for `modelOps` and `allowedStep`. -/
theorem proof_passwd_modelOps_soundAgainstAllowedStep :
    AllPass (test_passwd_modelOps_soundAgainstAllowedStep modelOps) := by
  intro s uid name hwf
  simp only [PasswdState.isWellFormed, Bool.and_eq_true] at hwf
  have ⟨hwfUid, hwfName⟩ := hwf
  dsimp only [test_passwd_modelOps_soundAgainstAllowedStep, NondetTest.assert, Bind.bind]
  change allowedStep s (.getpwuid uid) (outcomeOfEntryOpt (modelOps.getpwuid uid s).1) =
      some (modelOps.getpwuid uid s).2 ∧
    (modelOps.getpwuid uid s).2.isWellFormed = true ∧
    allowedStep s (.getpwnam name) (outcomeOfEntryOpt (modelOps.getpwnam name s).1) =
      some (modelOps.getpwnam name s).2 ∧
    (modelOps.getpwnam name s).2.isWellFormed = true ∧ True
  refine ⟨?_, ?_, ?_, ?_, trivial⟩
  · rw [modelOps_getpwuid_eval]
    cases hdb : lookupPasswdByUid s.byUid uid with
    | none => simp [outcomeOfEntryOpt, allowedStep, allowedStepCore, hdb]
    | some opt =>
      cases opt with
      | none => simp [outcomeOfEntryOpt, allowedStep, allowedStepCore, hdb]
      | some e =>
        have hv := lookupPasswdByUid_wellFormed hwfUid hdb
        simp only [isValidUidEntry, Bool.and_eq_true] at hv
        have ⟨hNul, hUid⟩ := hv
        simp [outcomeOfEntryOpt, allowedStep, allowedStepCore, hdb, hNul, hUid]
  · rw [modelOps_getpwuid_eval]
    cases hdb : lookupPasswdByUid s.byUid uid with
    | none =>
      simp only [PasswdState.isWellFormed, Bool.and_eq_true]
      exact ⟨setPasswdByUid_wellFormed s.byUid uid none hwfUid rfl, hwfName⟩
    | some opt =>
      cases opt with
      | none =>
        simp only [PasswdState.isWellFormed, Bool.and_eq_true]
        exact ⟨hwfUid, hwfName⟩
      | some e =>
        have hv := lookupPasswdByUid_wellFormed hwfUid hdb
        simp only [isValidUidEntry, Bool.and_eq_true] at hv
        simp only [hv.1, hv.2, PasswdState.isWellFormed, Bool.and_eq_true]
        exact ⟨hwfUid, hwfName⟩
  · rw [modelOps_getpwnam_eval]
    by_cases hv : validPasswdName name = true
    · simp only [hv, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
      by_cases hlen : name.size > MAX_PASSWD_NAME_BYTES
      · simp [hlen, outcomeOfEntryOpt, allowedStep, allowedStepCore, hv, Errno.ENAMETOOLONG]
      · simp only [hlen, ↓reduceIte]
        cases hdb : lookupPasswdByName s.byName name with
        | none => simp [outcomeOfEntryOpt, allowedStep, allowedStepCore, hv, hlen, hdb]
        | some opt =>
          cases opt with
          | none => simp [outcomeOfEntryOpt, allowedStep, allowedStepCore, hv, hlen, hdb]
          | some e =>
            have hve := lookupPasswdByName_wellFormed hwfName hdb
            simp only [isValidNameEntry, Bool.and_eq_true] at hve
            rcases hve with ⟨⟨⟨_, _⟩, hNul⟩, hNam⟩
            simp [outcomeOfEntryOpt, allowedStep, allowedStepCore, hv, hlen, hdb, hNul, hNam]
    · have hvF : validPasswdName name = false := by
        cases hb : validPasswdName name <;> simp_all
      simp [hvF, outcomeOfEntryOpt, allowedStep, allowedStepCore, Errno.EINVAL]
  · rw [modelOps_getpwnam_eval]
    by_cases hv : validPasswdName name = true
    · simp only [hv, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
      by_cases hlen : name.size > MAX_PASSWD_NAME_BYTES
      · simp only [hlen, ↓reduceIte, PasswdState.isWellFormed, Bool.and_eq_true]
        exact ⟨hwfUid, hwfName⟩
      · simp only [hlen, ↓reduceIte]
        have hlenLe : name.size ≤ MAX_PASSWD_NAME_BYTES := Nat.le_of_not_lt hlen
        have hValidNone : isValidNameEntry name none = true := by
          simp [isValidNameEntry, hv, hlenLe]
        cases hdb : lookupPasswdByName s.byName name with
        | none =>
          simp only [PasswdState.isWellFormed, Bool.and_eq_true]
          exact ⟨hwfUid, setPasswdByName_wellFormed s.byName name none hwfName hValidNone⟩
        | some opt =>
          cases opt with
          | none =>
            simp only [PasswdState.isWellFormed, Bool.and_eq_true]
            exact ⟨hwfUid, hwfName⟩
          | some e =>
            have hve := lookupPasswdByName_wellFormed hwfName hdb
            simp only [isValidNameEntry, Bool.and_eq_true] at hve
            rcases hve with ⟨⟨⟨_, _⟩, hNul⟩, hNam⟩
            simp only [hNul, hNam, PasswdState.isWellFormed, Bool.and_eq_true]
            exact ⟨hwfUid, hwfName⟩
    · have hvF : validPasswdName name = false := by
        cases hb : validPasswdName name <;> simp_all
      simp only [hvF, Bool.not_false, ↓reduceIte, PasswdState.isWellFormed, Bool.and_eq_true]
      exact ⟨hwfUid, hwfName⟩

/-- Non-vacuity `CanReach` witness for `test_passwd_modelOps_soundAgainstAllowedStep`. -/
theorem reach_passwd_modelOps_soundAgainstAllowedStep :
    CanReach (test_passwd_modelOps_soundAgainstAllowedStep modelOps) := by
  refine ⟨PasswdState.initial, 0, ByteArray.empty, by decide, ?_⟩
  exact proof_passwd_modelOps_soundAgainstAllowedStep PasswdState.initial 0 ByteArray.empty (by decide)

/-- Formal verification of `Internal.mkPasswdOpsM`: invalid (`EINVAL`) and oversized (`ENAMETOOLONG`) `getpwnam` names fail before FFI, and `getpwuid`/`getpwnam` double scratch capacity across `4096 → 8192 → 16384 → 32768 → 65536` on `ERANGE`, stop immediately on non-`ERANGE` errors, and validate returned entries via `Internal.validateRawPasswdResult` (rejecting mismatched keys or embedded NULs with `Errno.EIO`). -/
theorem internal_mkPasswdOpsM_contracts
    (raw : Internal.PosixPasswdOpsM Id) (uid : UInt32) (name : ByteArray) :
    let stepOr (pred : PasswdEntry → Bool)
        (once : UInt32 → Except Errno (Option Internal.RawPasswdTuple))
        (sz : UInt32) (next : Except Errno (Option PasswdEntry)) :
        Except Errno (Option PasswdEntry) :=
      match once sz with
      | .error e => if e == Errno.ERANGE then next else .error e
      | .ok opt => Internal.validateRawPasswdResult pred (.ok opt)
    let finish (pred : PasswdEntry → Bool)
        (once : UInt32 → Except Errno (Option Internal.RawPasswdTuple))
        (sz : UInt32) : Except Errno (Option PasswdEntry) :=
      Internal.validateRawPasswdResult pred (once sz)
    let uidPred : PasswdEntry → Bool := fun entry => entry.hasNoEmbeddedNul && entry.uid == uid
    let namPred : PasswdEntry → Bool := fun entry => entry.hasNoEmbeddedNul && entry.name == name
    (Internal.mkPasswdOpsM raw).getpwuid uid =
      stepOr uidPred (raw.getpwuidOnce uid) 4096
        (stepOr uidPred (raw.getpwuidOnce uid) 8192
          (stepOr uidPred (raw.getpwuidOnce uid) 16384
            (stepOr uidPred (raw.getpwuidOnce uid) 32768
              (finish uidPred (raw.getpwuidOnce uid) 65536)))) ∧
    (Internal.mkPasswdOpsM raw).getpwnam name =
      if !validPasswdName name then
        .error Errno.EINVAL
      else if name.size > MAX_PASSWD_NAME_BYTES then
        .error Errno.ENAMETOOLONG
      else
        stepOr namPred (raw.getpwnamOnce name) 4096
          (stepOr namPred (raw.getpwnamOnce name) 8192
            (stepOr namPred (raw.getpwnamOnce name) 16384
              (stepOr namPred (raw.getpwnamOnce name) 32768
                (finish namPred (raw.getpwnamOnce name) 65536)))) := by
  refine ⟨?_, ?_⟩
  · dsimp only [Internal.mkPasswdOpsM, Internal.passwdRetryBufSizes, Internal.retryPasswdLookup,
      Bind.bind, Pure.pure]
    cases raw.getpwuidOnce uid 4096 with
    | ok _ => rfl
    | error e1 =>
      by_cases h1 : e1 == Errno.ERANGE
      · simp only [h1, ↓reduceIte]
        cases raw.getpwuidOnce uid 8192 with
        | ok _ => rfl
        | error e2 =>
          by_cases h2 : e2 == Errno.ERANGE
          · simp only [h2, ↓reduceIte]
            cases raw.getpwuidOnce uid 16384 with
            | ok _ => rfl
            | error e3 =>
              by_cases h3 : e3 == Errno.ERANGE
              · simp only [h3, ↓reduceIte]
                cases raw.getpwuidOnce uid 32768 with
                | ok _ => rfl
                | error e4 =>
                  by_cases h4 : e4 == Errno.ERANGE
                  · simp only [h4, ↓reduceIte]
                  · simp [h4]
              · simp [h3]
          · simp [h2]
      · simp [h1]
  · dsimp only [Internal.mkPasswdOpsM, Internal.passwdRetryBufSizes, Internal.retryPasswdLookup,
      Bind.bind, Pure.pure]
    by_cases hv : validPasswdName name = true
    · simp only [hv, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
      by_cases hlen : name.size > MAX_PASSWD_NAME_BYTES
      · simp [hlen]
      · simp only [hlen, ↓reduceIte]
        cases raw.getpwnamOnce name 4096 with
        | ok _ => rfl
        | error e1 =>
          by_cases h1 : e1 == Errno.ERANGE
          · simp only [h1, ↓reduceIte]
            cases raw.getpwnamOnce name 8192 with
            | ok _ => rfl
            | error e2 =>
              by_cases h2 : e2 == Errno.ERANGE
              · simp only [h2, ↓reduceIte]
                cases raw.getpwnamOnce name 16384 with
                | ok _ => rfl
                | error e3 =>
                  by_cases h3 : e3 == Errno.ERANGE
                  · simp only [h3, ↓reduceIte]
                    cases raw.getpwnamOnce name 32768 with
                    | ok _ => rfl
                    | error e4 =>
                      by_cases h4 : e4 == Errno.ERANGE
                      · simp only [h4, ↓reduceIte]
                      · simp [h4]
                  · simp [h3]
              · simp [h2]
          · simp [h1]
    · have hvF : validPasswdName name = false := by
        cases hb : validPasswdName name <;> simp_all
      simp [hvF]

private theorem allowedStep_eio (s : PasswdState) (req : PasswdReq)
    (hreq : isUserspaceInvalidReq req = false) :
    allowedStep s req (.err Errno.EIO) = some s := by
  cases req with
  | getpwuid uid =>
    cases hdb : lookupPasswdByUid s.byUid uid with
    | none => simp [allowedStep, allowedStepCore, hdb, isAllowedPasswdOsErrno, Errno.EIO]
    | some opt =>
      cases opt <;> simp [allowedStep, allowedStepCore, hdb, isAllowedPasswdOsErrno, Errno.EIO]
  | getpwnam name =>
    have hv : validPasswdName name = true := by
      simp [isUserspaceInvalidReq] at hreq
      exact hreq.1
    have hlen : ¬ (name.size > MAX_PASSWD_NAME_BYTES) := by
      simp [isUserspaceInvalidReq] at hreq
      exact Nat.not_lt.mpr hreq.2
    cases hdb : lookupPasswdByName s.byName name with
    | none => simp [allowedStep, allowedStepCore, hv, hlen, hdb, isAllowedPasswdOsErrno, Errno.EIO]
    | some opt =>
      cases opt <;> simp [allowedStep, allowedStepCore, hv, hlen, hdb, isAllowedPasswdOsErrno, Errno.EIO]

private theorem retryPasswdLookup_sound
    (s : PasswdState) (req : PasswdReq) (pred : PasswdEntry → Bool)
    (once : UInt32 → StateM PasswdState (Except Errno (Option Internal.RawPasswdTuple)))
    (sizes : List UInt32) (hNonEmpty : sizes ≠ [])
    (hInv : isUserspaceInvalidReq req = false) (hwf : s.isWellFormed = true)
    (hOnce : ∀ sz ∈ sizes,
      let (r, s') := once sz s
      match r with
      | .error e =>
        (e == Errno.ERANGE → s' = s) ∧
        allowedStep s req (.err e) = some s' ∧ s'.isWellFormed = true
      | .ok none =>
        allowedStep s req .notFound = some s' ∧ s'.isWellFormed = true
      | .ok (some t) =>
        let entry : PasswdEntry :=
          { name := t.1, uid := t.2.1, gid := t.2.2.1, gecos := t.2.2.2.1,
            homeDir := t.2.2.2.2.1, shell := t.2.2.2.2.2 }
        (pred entry → allowedStep s req (.found entry) = some s' ∧ s'.isWellFormed = true) ∧
        (!(pred entry) → s' = s)) :
    let (res, sOut) := Internal.retryPasswdLookup once pred sizes s
    allowedStep s req (outcomeOfEntryOpt res) = some sOut ∧ sOut.isWellFormed = true := by
  induction sizes with
  | nil => contradiction
  | cons sz rest ih =>
    have hSz := hOnce sz (by simp)
    cases rest with
    | nil =>
      dsimp only [Internal.retryPasswdLookup, Bind.bind, Pure.pure, StateT.bind, StateT.pure]
      cases hCall : once sz s with
      | mk r s' =>
        rw [hCall] at hSz
        dsimp only at hSz
        cases r with
        | error e =>
          simp only [Internal.validateRawPasswdResult, outcomeOfEntryOpt]
          exact ⟨hSz.2.1, hSz.2.2⟩
        | ok opt =>
          cases opt with
          | none =>
            simp only [Internal.validateRawPasswdResult, outcomeOfEntryOpt]
            exact hSz
          | some t =>
            simp only [Internal.validateRawPasswdResult]
            let entry : PasswdEntry :=
              { name := t.1, uid := t.2.1, gid := t.2.2.1, gecos := t.2.2.2.1,
                homeDir := t.2.2.2.2.1, shell := t.2.2.2.2.2 }
            change (let res := if pred entry then Except.ok (some entry) else Except.error Errno.EIO;
              allowedStep s req (outcomeOfEntryOpt res) = some s' ∧ s'.isWellFormed = true)
            dsimp only at hSz
            by_cases hp : pred entry = true
            · simp only [hp, ↓reduceIte, outcomeOfEntryOpt]
              exact hSz.1 hp
            · have hpF : pred entry = false := by
                cases hb : pred entry <;> simp_all
              simp only [hpF, Bool.false_eq_true, ↓reduceIte, outcomeOfEntryOpt]
              have hs' : s' = s := hSz.2 (by dsimp only [entry] at hpF; simp [hpF])
              rw [hs']
              exact ⟨allowedStep_eio s req hInv, hwf⟩
    | cons sz2 rest2 =>
      dsimp only [Internal.retryPasswdLookup, Bind.bind, Pure.pure, StateT.bind, StateT.pure]
      cases hCall : once sz s with
      | mk r s' =>
        rw [hCall] at hSz
        dsimp only at hSz
        cases r with
        | error e =>
          by_cases hEr : e == Errno.ERANGE
          · simp only [hEr, ↓reduceIte]
            have hs' : s' = s := hSz.1 hEr
            rw [hs']
            exact ih (by simp) (fun z hz => hOnce z (by simp [hz]))
          · simp only [hEr, Bool.false_eq_true, ↓reduceIte, outcomeOfEntryOpt]
            exact ⟨hSz.2.1, hSz.2.2⟩
        | ok opt =>
          cases opt with
          | none =>
            simp only [Internal.validateRawPasswdResult, outcomeOfEntryOpt]
            exact hSz
          | some t =>
            simp only [Internal.validateRawPasswdResult]
            let entry : PasswdEntry :=
              { name := t.1, uid := t.2.1, gid := t.2.2.1, gecos := t.2.2.2.1,
                homeDir := t.2.2.2.2.1, shell := t.2.2.2.2.2 }
            change (let res := if pred entry then Except.ok (some entry) else Except.error Errno.EIO;
              allowedStep s req (outcomeOfEntryOpt res) = some s' ∧ s'.isWellFormed = true)
            dsimp only at hSz
            by_cases hp : pred entry = true
            · simp only [hp, ↓reduceIte, outcomeOfEntryOpt]
              exact hSz.1 hp
            · have hpF : pred entry = false := by
                cases hb : pred entry <;> simp_all
              simp only [hpF, Bool.false_eq_true, ↓reduceIte, outcomeOfEntryOpt]
              have hs' : s' = s := hSz.2 (by dsimp only [entry] at hpF; simp [hpF])
              rw [hs']
              exact ⟨allowedStep_eio s req hInv, hwf⟩

private theorem passwdRetryBufSizes_range (sz : UInt32) (hMem : sz ∈ Internal.passwdRetryBufSizes) :
    4096 ≤ sz.toNat ∧ sz.toNat ≤ 65536 := by
  simp only [Internal.passwdRetryBufSizes, List.mem_cons, List.not_mem_nil, or_false] at hMem
  rcases hMem with rfl | rfl | rfl | rfl | rfl <;> decide

/-- Proof of `test_passwd_mkPasswdOps_soundAgainstAllowedStep` for `Internal.mkPasswdOpsM`. -/
theorem proof_passwd_mkPasswdOps_soundAgainstAllowedStep :
    AllPass (test_passwd_mkPasswdOps_soundAgainstAllowedStep Internal.mkPasswdOpsM) := by
  intro s uid name badName overCapName raw hwf hBad hOverValid hOverSize hRawUid hRawNam
  dsimp only [test_passwd_mkPasswdOps_soundAgainstAllowedStep, NondetTest.assert, Bind.bind]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, trivial⟩
  · simp [Internal.mkPasswdOpsM, hBad]; rfl
  · simp [Internal.mkPasswdOpsM, hOverValid, hOverSize]; rfl
  · dsimp only [Internal.mkPasswdOpsM, StateT.run]
    exact (retryPasswdLookup_sound s (.getpwuid uid)
      (fun entry => entry.hasNoEmbeddedNul && entry.uid == uid)
      (raw.getpwuidOnce uid) Internal.passwdRetryBufSizes (by decide) rfl hwf
      (fun sz hMem => hRawUid sz (passwdRetryBufSizes_range sz hMem))).1
  · dsimp only [Internal.mkPasswdOpsM, StateT.run]
    exact (retryPasswdLookup_sound s (.getpwuid uid)
      (fun entry => entry.hasNoEmbeddedNul && entry.uid == uid)
      (raw.getpwuidOnce uid) Internal.passwdRetryBufSizes (by decide) rfl hwf
      (fun sz hMem => hRawUid sz (passwdRetryBufSizes_range sz hMem))).2
  · dsimp only [Internal.mkPasswdOpsM, StateT.run]
    by_cases hv : validPasswdName name = true
    · simp only [hv, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
      by_cases hlen : name.size > MAX_PASSWD_NAME_BYTES
      · simp [hlen, pure, StateT.pure, outcomeOfEntryOpt, allowedStep, allowedStepCore, hv,
          Errno.ENAMETOOLONG]
      · simp only [hlen, ↓reduceIte]
        have hlenLe : name.size ≤ MAX_PASSWD_NAME_BYTES := Nat.le_of_not_lt hlen
        have hInv : isUserspaceInvalidReq (.getpwnam name) = false := by
          simp [isUserspaceInvalidReq, hv, hlen]
        exact (retryPasswdLookup_sound s (.getpwnam name)
          (fun entry => entry.hasNoEmbeddedNul && entry.name == name)
          (raw.getpwnamOnce name) Internal.passwdRetryBufSizes (by decide) hInv hwf
          (fun sz hMem => hRawNam sz (passwdRetryBufSizes_range sz hMem) hv hlenLe)).1
    · have hvF : validPasswdName name = false := by
        cases hb : validPasswdName name <;> simp_all
      simp [hvF, pure, StateT.pure, outcomeOfEntryOpt, allowedStep, allowedStepCore, Errno.EINVAL]
  · dsimp only [Internal.mkPasswdOpsM, StateT.run]
    by_cases hv : validPasswdName name = true
    · simp only [hv, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
      by_cases hlen : name.size > MAX_PASSWD_NAME_BYTES
      · simp [hlen, pure, StateT.pure, hwf]
      · simp only [hlen, ↓reduceIte]
        have hlenLe : name.size ≤ MAX_PASSWD_NAME_BYTES := Nat.le_of_not_lt hlen
        have hInv : isUserspaceInvalidReq (.getpwnam name) = false := by
          simp [isUserspaceInvalidReq, hv, hlen]
        exact (retryPasswdLookup_sound s (.getpwnam name)
          (fun entry => entry.hasNoEmbeddedNul && entry.name == name)
          (raw.getpwnamOnce name) Internal.passwdRetryBufSizes (by decide) hInv hwf
          (fun sz hMem => hRawNam sz (passwdRetryBufSizes_range sz hMem) hv hlenLe)).2
    · have hvF : validPasswdName name = false := by
        cases hb : validPasswdName name <;> simp_all
      simp [hvF, pure, StateT.pure, hwf]

/-- Non-vacuity `CanReach` witness for `test_passwd_mkPasswdOps_soundAgainstAllowedStep`. -/
theorem reach_passwd_mkPasswdOps_soundAgainstAllowedStep :
    CanReach (test_passwd_mkPasswdOps_soundAgainstAllowedStep Internal.mkPasswdOpsM) := by
  let rawNone : Internal.PosixPasswdOpsM (StateM PasswdState) :=
    { getpwuidOnce := fun _ _ => pure (.ok none)
      getpwnamOnce := fun _ _ => pure (.ok none) }
  let s0 : PasswdState :=
    { byUid := setPasswdByUid ∅ 0 none
      byName := setPasswdByName ∅ ByteArray.empty none }
  have hs0 : s0.isWellFormed = true := by
    simp only [s0, PasswdState.isWellFormed, Bool.and_eq_true]
    exact ⟨setPasswdByUid_wellFormed ∅ 0 none (by decide) (by decide),
      setPasswdByName_wellFormed ∅ ByteArray.empty none (by decide) (by decide)⟩
  refine ⟨s0, 0, ByteArray.empty, ByteArray.mk #[0], overCapWitness, rawNone, hs0,
    by decide, validPasswdName_overCapWitness, overCapWitness_size_gt,
    (fun _ _ => by dsimp only [rawNone, pure, StateT.pure]; simp [s0, allowedStep, allowedStepCore,
      lookupPasswdByUid_set_self, hs0]),
    (fun _ _ _ _ => by dsimp only [rawNone, pure, StateT.pure]; simp [s0, allowedStep, allowedStepCore,
      lookupPasswdByName_set_self, hs0, show validPasswdName ByteArray.empty = true by decide]),
    ?_⟩
  exact proof_passwd_mkPasswdOps_soundAgainstAllowedStep s0 0 ByteArray.empty (ByteArray.mk #[0])
    overCapWitness rawNone hs0 (by decide) validPasswdName_overCapWitness overCapWitness_size_gt
    (fun _ _ => by dsimp only [rawNone, pure, StateT.pure]; simp [s0, allowedStep, allowedStepCore,
      lookupPasswdByUid_set_self, hs0])
    (fun _ _ _ _ => by dsimp only [rawNone, pure, StateT.pure]; simp [s0, allowedStep, allowedStepCore,
      lookupPasswdByName_set_self, hs0, show validPasswdName ByteArray.empty = true by decide])

/-- Proof of `test_passwd_mkPasswdOps_exactRetryAndDelegation` for `Internal.mkPasswdOpsM` and `Internal.mkPasswdOps`. -/
theorem proof_passwd_mkPasswdOps_exactRetryAndDelegation :
    AllPass test_passwd_mkPasswdOps_exactRetryAndDelegation := by
  intro rawGetpwuid rawGetpwnam uid name
  dsimp only [test_passwd_mkPasswdOps_exactRetryAndDelegation, NondetTest.assert, Bind.bind]
  refine ⟨rfl, rfl, rfl, rfl, ?_, trivial⟩
  dsimp only [Internal.mkPasswdOpsM]
  split
  · rfl
  · split <;> rfl

/-- Soundness binding: `Passwd.getpwuid` dispatches through `Passwd.defaultOps.getpwuid`. -/
theorem proof_passwd_getpwuid_eq_defaultOps (uid : UInt32) :
    Passwd.getpwuid uid = Passwd.defaultOps.getpwuid uid := rfl

/-- Soundness binding: `Passwd.getpwnam` dispatches through `Passwd.defaultOps.getpwnam`. -/
theorem proof_passwd_getpwnam_eq_defaultOps (name : ByteArray) :
    Passwd.getpwnam name = Passwd.defaultOps.getpwnam name := rfl

/-- Pure user-space short-circuit: `Passwd.getpwnam` on any invalid name returns `pure (.error Errno.EINVAL)` without invoking the C FFI shim. -/
theorem proof_passwd_getpwnam_invalidName_eq_einval (name : ByteArray)
    (hInv : validPasswdName name = false) :
    Passwd.getpwnam name = pure (.error Errno.EINVAL) := by
  simp [Passwd.getpwnam, Passwd.defaultOps, Internal.mkPasswdOpsM, hInv]
  rfl

/-- Pure user-space short-circuit: `Passwd.getpwnam` on any NUL-free name longer than `MAX_PASSWD_NAME_BYTES` returns `pure (.error Errno.ENAMETOOLONG)` without invoking the C FFI shim. -/
theorem proof_passwd_getpwnam_overCap_eq_enametoolong (name : ByteArray)
    (hValid : validPasswdName name = true)
    (hLen : name.size > MAX_PASSWD_NAME_BYTES) :
    Passwd.getpwnam name = pure (.error Errno.ENAMETOOLONG) := by
  simp [Passwd.getpwnam, Passwd.defaultOps, Internal.mkPasswdOpsM, hValid, hLen]
  rfl

/-- Proof of `test_passwd_interface_wiringAndSoundness` for `Interface.lean` definitions. -/
theorem proof_passwd_interface_wiringAndSoundness :
    AllPass test_passwd_interface_wiringAndSoundness := by
  intro uid name
  dsimp only [test_passwd_interface_wiringAndSoundness, NondetTest.assert, Bind.bind]
  refine ⟨rfl, rfl, ?_, ?_, trivial⟩
  · intro hvF
    exact proof_passwd_getpwnam_invalidName_eq_einval name hvF
  · intro hv hlen
    exact proof_passwd_getpwnam_overCap_eq_enametoolong name hv hlen

private theorem retryPasswdLookup_baseio_sound
    (abs : Void IO.RealWorld → PasswdState)
    (w₀ : Void IO.RealWorld) (req : PasswdReq) (pred : PasswdEntry → Bool)
    (once : UInt32 → BaseIO (Except Errno (Option Internal.RawPasswdTuple)))
    (sizes : List UInt32) (hNonEmpty : sizes ≠ [])
    (hInv : isUserspaceInvalidReq req = false) (hwf : (abs w₀).isWellFormed = true)
    (hOnce : ∀ (w : Void IO.RealWorld), abs w = abs w₀ → ∀ sz ∈ sizes,
      match once sz w with
      | .mk (.error e) w' =>
        (e == Errno.ERANGE → abs w' = abs w) ∧
        allowedStep (abs w) req (.err e) = some (abs w') ∧ (abs w').isWellFormed = true
      | .mk (.ok none) w' =>
        allowedStep (abs w) req .notFound = some (abs w') ∧ (abs w').isWellFormed = true
      | .mk (.ok (some t)) w' =>
        let entry : PasswdEntry :=
          { name := t.1, uid := t.2.1, gid := t.2.2.1, gecos := t.2.2.2.1,
            homeDir := t.2.2.2.2.1, shell := t.2.2.2.2.2 }
        (pred entry → allowedStep (abs w) req (.found entry) = some (abs w') ∧ (abs w').isWellFormed = true) ∧
        (!(pred entry) → abs w' = abs w)) :
    ∀ (w : Void IO.RealWorld), abs w = abs w₀ →
      match Internal.retryPasswdLookup once pred sizes w with
      | .mk res wOut =>
        allowedStep (abs w₀) req (outcomeOfEntryOpt res) = some (abs wOut) ∧
        (abs wOut).isWellFormed = true := by
  induction sizes with
  | nil => contradiction
  | cons sz rest ih =>
    intro w hw
    have hSz := hOnce w hw sz (by simp)
    cases rest with
    | nil =>
      dsimp only [Internal.retryPasswdLookup, Bind.bind, Pure.pure,
        instMonadBaseIO, instMonadBaseIO._aux_13, instMonadBaseIO._aux_5, ST.bind, ST.pure]
      cases hCall : once sz w with
      | mk r w' =>
        rw [hCall] at hSz
        rw [hw] at hSz
        cases r with
        | error e =>
          simp only [Internal.validateRawPasswdResult, outcomeOfEntryOpt]
          exact ⟨hSz.2.1, hSz.2.2⟩
        | ok opt =>
          cases opt with
          | none =>
            simp only [Internal.validateRawPasswdResult, outcomeOfEntryOpt]
            exact hSz
          | some t =>
            dsimp only [Internal.validateRawPasswdResult]
            let entry : PasswdEntry :=
              { name := t.1, uid := t.2.1, gid := t.2.2.1, gecos := t.2.2.2.1,
                homeDir := t.2.2.2.2.1, shell := t.2.2.2.2.2 }
            change (let res := if pred entry then Except.ok (some entry) else Except.error Errno.EIO;
              allowedStep (abs w₀) req (outcomeOfEntryOpt res) = some (abs w') ∧
              (abs w').isWellFormed = true)
            dsimp only at hSz
            by_cases hp : pred entry = true
            · simp only [hp, ↓reduceIte, outcomeOfEntryOpt]
              exact hSz.1 hp
            · have hpF : pred entry = false := by
                cases hb : pred entry <;> simp_all
              simp only [hpF, Bool.false_eq_true, ↓reduceIte, outcomeOfEntryOpt]
              have hw' : abs w' = abs w₀ := hSz.2 (by dsimp only [entry] at hpF; simp [hpF])
              rw [hw']
              exact ⟨allowedStep_eio (abs w₀) req hInv, hwf⟩
    | cons sz2 rest2 =>
      dsimp only [Internal.retryPasswdLookup, Bind.bind, Pure.pure,
        instMonadBaseIO, instMonadBaseIO._aux_13, instMonadBaseIO._aux_5, ST.bind, ST.pure]
      cases hCall : once sz w with
      | mk r w' =>
        rw [hCall] at hSz
        rw [hw] at hSz
        cases r with
        | error e =>
          by_cases hEr : e == Errno.ERANGE
          · simp only [hEr, ↓reduceIte]
            have hw' : abs w' = abs w₀ := hSz.1 hEr
            exact ih (by simp) (fun w1 hw1 z hz => hOnce w1 hw1 z (by simp [hz])) w' hw'
          · simp only [hEr, Bool.false_eq_true, ↓reduceIte, outcomeOfEntryOpt]
            exact ⟨hSz.2.1, hSz.2.2⟩
        | ok opt =>
          cases opt with
          | none =>
            simp only [Internal.validateRawPasswdResult, outcomeOfEntryOpt]
            exact hSz
          | some t =>
            dsimp only [Internal.validateRawPasswdResult]
            let entry : PasswdEntry :=
              { name := t.1, uid := t.2.1, gid := t.2.2.1, gecos := t.2.2.2.1,
                homeDir := t.2.2.2.2.1, shell := t.2.2.2.2.2 }
            change (let res := if pred entry then Except.ok (some entry) else Except.error Errno.EIO;
              allowedStep (abs w₀) req (outcomeOfEntryOpt res) = some (abs w') ∧
              (abs w').isWellFormed = true)
            dsimp only at hSz
            by_cases hp : pred entry = true
            · simp only [hp, ↓reduceIte, outcomeOfEntryOpt]
              exact hSz.1 hp
            · have hpF : pred entry = false := by
                cases hb : pred entry <;> simp_all
              simp only [hpF, Bool.false_eq_true, ↓reduceIte, outcomeOfEntryOpt]
              have hw' : abs w' = abs w₀ := hSz.2 (by dsimp only [entry] at hpF; simp [hpF])
              rw [hw']
              exact ⟨allowedStep_eio (abs w₀) req hInv, hwf⟩

/-- Universal `IO` refinement soundness for `(Internal.mkPasswdOpsM raw).getpwuid`: never throws `IO.Error` and steps according to `Model.allowedStep` while preserving `PasswdState.isWellFormed`. -/
theorem proof_passwd_mkPasswdOps_getpwuid_io_soundAgainstAllowedStep
    (raw : Internal.PosixPasswdOpsM BaseIO)
    (abs : Void IO.RealWorld → PasswdState)
    (w₀ : Void IO.RealWorld) (uid : UInt32)
    (hwf : (abs w₀).isWellFormed = true)
    (hRaw : ∀ (w : Void IO.RealWorld), abs w = abs w₀ → ∀ sz : UInt32,
      4096 ≤ sz.toNat ∧ sz.toNat ≤ 65536 →
      match raw.getpwuidOnce uid sz w with
      | .mk (.error e) w' =>
        (e == Errno.ERANGE → abs w' = abs w) ∧
        allowedStep (abs w) (.getpwuid uid) (.err e) = some (abs w') ∧ (abs w').isWellFormed = true
      | .mk (.ok none) w' =>
        allowedStep (abs w) (.getpwuid uid) .notFound = some (abs w') ∧ (abs w').isWellFormed = true
      | .mk (.ok (some t)) w' =>
        let entry : PasswdEntry :=
          { name := t.1, uid := t.2.1, gid := t.2.2.1, gecos := t.2.2.2.1,
            homeDir := t.2.2.2.2.1, shell := t.2.2.2.2.2 }
        (entry.hasNoEmbeddedNul && entry.uid == uid →
          allowedStep (abs w) (.getpwuid uid) (.found entry) = some (abs w') ∧
            (abs w').isWellFormed = true) ∧
        (!(entry.hasNoEmbeddedNul && entry.uid == uid) → abs w' = abs w)) :
    ∃ res wFinal,
      ((Internal.mkPasswdOpsM raw).getpwuid uid : IO _) w₀ = .ok res wFinal ∧
      allowedStep (abs w₀) (.getpwuid uid) (outcomeOfEntryOpt res) = some (abs wFinal) ∧
      (abs wFinal).isWellFormed = true := by
  have hBase := retryPasswdLookup_baseio_sound abs w₀ (.getpwuid uid)
    (fun entry => entry.hasNoEmbeddedNul && entry.uid == uid)
    (raw.getpwuidOnce uid) Internal.passwdRetryBufSizes (by decide) rfl hwf
    (fun w hw sz hMem => hRaw w hw sz (passwdRetryBufSizes_range sz hMem)) w₀ rfl
  dsimp only [Internal.mkPasswdOpsM, liftM, monadLift, MonadLift.monadLift, BaseIO.toEIO]
  cases hCall : Internal.retryPasswdLookup (raw.getpwuidOnce uid)
      (fun entry => entry.hasNoEmbeddedNul && entry.uid == uid)
      Internal.passwdRetryBufSizes w₀ with
  | mk res wFinal =>
    rw [hCall] at hBase
    exact ⟨res, wFinal, rfl, hBase.1, hBase.2⟩

/-- Universal `IO` refinement soundness for `(Internal.mkPasswdOpsM raw).getpwnam`: never throws `IO.Error` and steps according to `Model.allowedStep` while preserving `PasswdState.isWellFormed`. -/
theorem proof_passwd_mkPasswdOps_getpwnam_io_soundAgainstAllowedStep
    (raw : Internal.PosixPasswdOpsM BaseIO)
    (abs : Void IO.RealWorld → PasswdState)
    (w₀ : Void IO.RealWorld) (name : ByteArray)
    (hwf : (abs w₀).isWellFormed = true)
    (hRaw : ∀ (w : Void IO.RealWorld), abs w = abs w₀ → ∀ sz : UInt32,
      4096 ≤ sz.toNat ∧ sz.toNat ≤ 65536 →
      validPasswdName name = true →
      name.size ≤ MAX_PASSWD_NAME_BYTES →
      match raw.getpwnamOnce name sz w with
      | .mk (.error e) w' =>
        (e == Errno.ERANGE → abs w' = abs w) ∧
        allowedStep (abs w) (.getpwnam name) (.err e) = some (abs w') ∧ (abs w').isWellFormed = true
      | .mk (.ok none) w' =>
        allowedStep (abs w) (.getpwnam name) .notFound = some (abs w') ∧ (abs w').isWellFormed = true
      | .mk (.ok (some t)) w' =>
        let entry : PasswdEntry :=
          { name := t.1, uid := t.2.1, gid := t.2.2.1, gecos := t.2.2.2.1,
            homeDir := t.2.2.2.2.1, shell := t.2.2.2.2.2 }
        (entry.hasNoEmbeddedNul && entry.name == name →
          allowedStep (abs w) (.getpwnam name) (.found entry) = some (abs w') ∧
            (abs w').isWellFormed = true) ∧
        (!(entry.hasNoEmbeddedNul && entry.name == name) → abs w' = abs w)) :
    ∃ res wFinal,
      ((Internal.mkPasswdOpsM raw).getpwnam name : IO _) w₀ = .ok res wFinal ∧
      allowedStep (abs w₀) (.getpwnam name) (outcomeOfEntryOpt res) = some (abs wFinal) ∧
      (abs wFinal).isWellFormed = true := by
  by_cases hv : validPasswdName name = true
  · by_cases hlen : name.size > MAX_PASSWD_NAME_BYTES
    · refine ⟨.error Errno.ENAMETOOLONG, w₀, ?_, ?_, hwf⟩
      · dsimp only [Internal.mkPasswdOpsM, liftM, monadLift, MonadLift.monadLift, BaseIO.toEIO]
        simp only [hv, Bool.not_true, Bool.false_eq_true, ↓reduceIte, hlen, pure,
          instMonadBaseIO._aux_5]
        rfl
      · simp [outcomeOfEntryOpt, allowedStep, allowedStepCore, hv, hlen, Errno.ENAMETOOLONG]
    · have hlenLe : name.size ≤ MAX_PASSWD_NAME_BYTES := Nat.le_of_not_lt hlen
      have hInv : isUserspaceInvalidReq (.getpwnam name) = false := by
        simp [isUserspaceInvalidReq, hv, hlen]
      have hBase := retryPasswdLookup_baseio_sound abs w₀ (.getpwnam name)
        (fun entry => entry.hasNoEmbeddedNul && entry.name == name)
        (raw.getpwnamOnce name) Internal.passwdRetryBufSizes (by decide) hInv hwf
        (fun w hw sz hMem => hRaw w hw sz (passwdRetryBufSizes_range sz hMem) hv hlenLe) w₀ rfl
      dsimp only [Internal.mkPasswdOpsM, liftM, monadLift, MonadLift.monadLift, BaseIO.toEIO]
      simp only [hv, Bool.not_true, Bool.false_eq_true, ↓reduceIte, hlen]
      cases hCall : Internal.retryPasswdLookup (raw.getpwnamOnce name)
          (fun entry => entry.hasNoEmbeddedNul && entry.name == name)
          Internal.passwdRetryBufSizes w₀ with
      | mk res wFinal =>
        rw [hCall] at hBase
        exact ⟨res, wFinal, rfl, hBase.1, hBase.2⟩
  · have hvF : validPasswdName name = false := by
      cases hb : validPasswdName name <;> simp_all
    refine ⟨.error Errno.EINVAL, w₀, ?_, ?_, hwf⟩
    · dsimp only [Internal.mkPasswdOpsM, liftM, monadLift, MonadLift.monadLift, BaseIO.toEIO]
      simp only [hvF, Bool.not_false, ↓reduceIte, pure, instMonadBaseIO._aux_5]
      rfl
    · simp [outcomeOfEntryOpt, allowedStep, allowedStepCore, hvF, Errno.EINVAL]

end LeanSwe.LinuxSyscall.Passwd.Proofs
