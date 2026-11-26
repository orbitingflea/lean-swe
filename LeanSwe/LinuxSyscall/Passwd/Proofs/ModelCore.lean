import LeanSwe.LinuxSyscall.Passwd.Types
import LeanSwe.LinuxSyscall.Passwd.Model
import LeanSwe.LinuxSyscall.Passwd.SpecTests
import Std.Data.DTreeMap.Internal.Lemmas

/-!
Core `TreeMap` invariants, `modelOps` evaluation lemmas, and foundational specification proofs
(`errno`, UTF-8 accessors, exact `modelOps` contracts, and core NSS `allowedStep` semantics) for
`LeanSwe.LinuxSyscall.Passwd`.
-/

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

private theorem hasEmbeddedNulLoop_replicate_false (n : Nat) (c : UInt8) (hc : c ≠ 0) :
    ∀ k i : Nat, hasEmbeddedNulLoop (ByteArray.mk (Array.replicate n c)) i k = false
  | 0, _ => rfl
  | k + 1, i => by
    unfold hasEmbeddedNulLoop
    split
    · rename_i hlt
      have hElem : (ByteArray.mk (Array.replicate n c))[i] = c := by
        show (Array.replicate n c)[i] = c
        exact Array.getElem_replicate ..
      have hNe : (c == (0 : UInt8)) = false := beq_eq_false_iff_ne.mpr hc
      simp only [hElem, hNe, Bool.false_eq_true, ↓reduceIte]
      exact hasEmbeddedNulLoop_replicate_false n c hc k (i + 1)
    · rfl

/-- Any repeated non-zero byte array passes `validPasswdName` in `O(1)` proof size. -/
theorem validPasswdName_replicate (n : Nat) (c : UInt8) (hc : c ≠ 0) :
    validPasswdName (ByteArray.mk (Array.replicate n c)) = true := by
  unfold validPasswdName hasEmbeddedNul
  rw [hasEmbeddedNulLoop_replicate_false n c hc]
  rfl

/-- Canonical oversized NUL-free username witness (`MAX_PASSWD_NAME_BYTES + 1` bytes). -/
def overCapWitness : ByteArray :=
  ByteArray.mk (Array.replicate (MAX_PASSWD_NAME_BYTES + 1) 97)

/-- `overCapWitness` contains no embedded NUL byte. -/
theorem validPasswdName_overCapWitness :
    validPasswdName overCapWitness = true :=
  validPasswdName_replicate (MAX_PASSWD_NAME_BYTES + 1) 97 (by decide)

/-- `overCapWitness` strictly exceeds `MAX_PASSWD_NAME_BYTES`. -/
theorem overCapWitness_size_gt :
    overCapWitness.size > MAX_PASSWD_NAME_BYTES := by
  change (Array.replicate (MAX_PASSWD_NAME_BYTES + 1) (97 : UInt8)).size > MAX_PASSWD_NAME_BYTES
  rw [Array.size_replicate]
  omega

/-- Looking up `uid` immediately after `setPasswdByUid db uid v` returns `some v`. -/
theorem lookupPasswdByUid_set_self (db : Std.TreeMap UInt32 (Option PasswdEntry))
    (uid : UInt32) (v : Option PasswdEntry) :
    lookupPasswdByUid (setPasswdByUid db uid v) uid = some v :=
  treemap_get?_insert_self db uid v

/-- Looking up `name` immediately after `setPasswdByName db name v` returns `some v`. -/
theorem lookupPasswdByName_set_self (db : Std.TreeMap ByteArray (Option PasswdEntry))
    (name : ByteArray) (v : Option PasswdEntry) :
    lookupPasswdByName (setPasswdByName db name v) name = some v :=
  treemap_get?_insert_self db name v

/-- Any entry found in a well-formed `byUid` map satisfies `isValidUidEntry`. -/
theorem lookupPasswdByUid_wellFormed {db : Std.TreeMap UInt32 (Option PasswdEntry)}
    {uid : UInt32} {v : Option PasswdEntry}
    (hwf : db.foldl (fun acc k v => acc && isValidUidEntry k v) true = true)
    (hlookup : lookupPasswdByUid db uid = some v) :
    isValidUidEntry uid v = true :=
  treemap_foldl_lookup hwf hlookup

/-- Any entry found in a well-formed `byName` map satisfies `isValidNameEntry`. -/
theorem lookupPasswdByName_wellFormed {db : Std.TreeMap ByteArray (Option PasswdEntry)}
    {name : ByteArray} {v : Option PasswdEntry}
    (hwf : db.foldl (fun acc k v => acc && isValidNameEntry k v) true = true)
    (hlookup : lookupPasswdByName db name = some v) :
    isValidNameEntry name v = true :=
  treemap_foldl_lookup hwf hlookup

/-- Inserting a valid `byUid` entry preserves the `byUid` well-formedness fold. -/
theorem setPasswdByUid_wellFormed (db : Std.TreeMap UInt32 (Option PasswdEntry))
    (uid : UInt32) (v : Option PasswdEntry)
    (hwf : db.foldl (fun acc k v => acc && isValidUidEntry k v) true = true)
    (hv : isValidUidEntry uid v = true) :
    (setPasswdByUid db uid v).foldl (fun acc k v => acc && isValidUidEntry k v) true = true :=
  treemap_foldl_insert hwf uid v hv

/-- Inserting a valid `byName` entry preserves the `byName` well-formedness fold. -/
theorem setPasswdByName_wellFormed (db : Std.TreeMap ByteArray (Option PasswdEntry))
    (name : ByteArray) (v : Option PasswdEntry)
    (hwf : db.foldl (fun acc k v => acc && isValidNameEntry k v) true = true)
    (hv : isValidNameEntry name v = true) :
    (setPasswdByName db name v).foldl (fun acc k v => acc && isValidNameEntry k v) true = true :=
  treemap_foldl_insert hwf name v hv

/-- Explicit state-transition reduction of `modelOps.getpwuid`. -/
theorem modelOps_getpwuid_eval (uid : UInt32) (s : PasswdState) :
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

/-- Explicit state-transition reduction of `modelOps.getpwnam`. -/
theorem modelOps_getpwnam_eval (name : ByteArray) (s : PasswdState) :
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

end LeanSwe.LinuxSyscall.Passwd.Proofs
