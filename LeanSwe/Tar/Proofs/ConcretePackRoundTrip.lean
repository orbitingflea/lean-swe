import LeanSwe.Tar.SpecTests
import LeanSwe.Tar.Interface
import LeanSwe.Tar.Proofs.ByteModel
import LeanSwe.Tar.Proofs.FieldCodecs
import LeanSwe.Tar.Proofs.Headers
import LeanSwe.Tar.Proofs.PackValid
import LeanSwe.Tar.Proofs.UnpackValid
import LeanSwe.Tar.Proofs.EncodeStep
import LeanSwe.Tar.Proofs.Universal
import LeanSwe.Tar.Proofs.ConcreteHelpers

namespace LeanSwe.Tar.Proofs

open Core
open Core.NondetTest
open LeanSwe.Tar
open LeanSwe.Tar.Model
open LeanSwe.Tar.Impl

private theorem list_all_replicate {α : Type} (n : Nat) (a : α) (p : α → Bool) :
    (List.replicate n a).all p = if n == 0 then true else p a := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [List.replicate_succ, List.all_cons, ih]
    cases n <;> simp

private theorem hasNulChars_replicate (n : Nat) {c : Char} (hc : c ≠ Char.ofNat 0) :
    hasNulChars (List.replicate n c) = false := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.replicate_succ]
    change (c == Char.ofNat 0 || hasNulChars (List.replicate n c)) = false
    simp [hc, ih]

private theorem splitSlashChars_go_append_noSlash (acc a rest : List Char)
    (hno : a.all (fun c => c != '/') = true) :
    splitSlashChars.go acc (a ++ rest) = splitSlashChars.go (a.reverse ++ acc) rest := by
  induction a generalizing acc with
  | nil => simp
  | cons c a ih =>
    simp only [List.all_cons, Bool.and_eq_true, bne_iff_ne] at hno
    rw [List.cons_append, splitSlashChars.go.eq_3 _ c _ hno.1,
      ih (c :: acc) hno.2, List.reverse_cons, List.append_assoc, List.singleton_append]

private theorem findUstarSplit_go_noSlash (revPfx a rest : List Char)
    (hno : a.all (fun c => c != '/') = true) :
    findUstarSplit.go revPfx (a ++ rest) = findUstarSplit.go (a.reverse ++ revPfx) rest := by
  induction a generalizing revPfx with
  | nil => simp
  | cons c a ih =>
    simp only [List.all_cons, Bool.and_eq_true, bne_iff_ne] at hno
    rw [List.cons_append, findUstarSplit.go.eq_3 _ c _ hno.1,
      ih (c :: revPfx) hno.2, List.reverse_cons, List.append_assoc, List.singleton_append]

private theorem flatMap_utf8EncodeChar_replicate (n : Nat) {c : Char} (hc : c.toNat < 128) :
    ((List.replicate n c).flatMap String.utf8EncodeChar).length = n ∧
    ((List.replicate n c).flatMap String.utf8EncodeChar).all (fun b => decide (b < 128)) = true := by
  have hcle : c.toNat ≤ 127 := by omega
  have hlt : UInt8.ofNat c.toNat < 128 := by
    change (UInt8.ofNat c.toNat).toNat < 128
    have hmod : (UInt8.ofNat c.toNat).toNat = c.toNat % 2 ^ 8 := rfl
    rw [hmod]
    omega
  have hlen1 : (String.utf8EncodeChar c).length = 1 := by
    unfold String.utf8EncodeChar
    simp [hcle]
  have hall1 : (String.utf8EncodeChar c).all (fun b => decide (b < 128)) = true := by
    unfold String.utf8EncodeChar
    simp [hcle, hlt]
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.replicate_succ, List.flatMap_cons, List.length_append, List.all_append,
      hlen1, hall1, ih.1, ih.2, Bool.and_self]
    exact ⟨Nat.add_comm 1 n, rfl⟩

private theorem toUTF8_size_ofList_replicate (n : Nat) {c : Char} (hc : c.toNat < 128) :
    (String.ofList (List.replicate n c)).toUTF8.size = n := by
  rw [toUTF8_eq_toByteArray]
  change (List.flatMap String.utf8EncodeChar (String.ofList (List.replicate n c)).toList).toByteArray.size = n
  rw [List.size_toByteArray, String.toList_ofList]
  exact (flatMap_utf8EncodeChar_replicate n hc).1

private theorem isAsciiString_append (a b : String) :
    isAsciiString (a ++ b) = (isAsciiString a && isAsciiString b) := by
  simp only [isAsciiString, toUTF8_toList, String.toList_append, List.flatMap_append, List.all_append]

private theorem isAsciiString_ofList_replicate (n : Nat) {c : Char} (hc : c.toNat < 128) :
    isAsciiString (String.ofList (List.replicate n c)) = true := by
  simp only [isAsciiString, toUTF8_toList, String.toList_ofList]
  exact (flatMap_utf8EncodeChar_replicate n hc).2

private theorem encodePaxRecord_size_of_kv (key value : String) :
    (encodePaxRecord key value).size =
      (toString (paxRecordTotalLen (1 + key.toUTF8.size + 1 + value.toUTF8.size + 1))).toUTF8.size +
        (1 + key.toUTF8.size + 1 + value.toUTF8.size + 1) := by
  unfold encodePaxRecord
  have hsuf : (" " ++ key ++ "=" ++ value ++ "\n").toUTF8.size =
      1 + key.toUTF8.size + 1 + value.toUTF8.size + 1 := by
    simp only [toUTF8_size_append]
    have hsp : (" ").toUTF8.size = 1 := by rw [toUTF8_eq_toByteArray, List.size_toByteArray]; decide
    have heq : ("=").toUTF8.size = 1 := by rw [toUTF8_eq_toByteArray, List.size_toByteArray]; decide
    have hnl : ("\n").toUTF8.size = 1 := by rw [toUTF8_eq_toByteArray, List.size_toByteArray]; decide
    rw [hsp, heq, hnl]
  dsimp only
  rw [hsuf, toUTF8_size_append, hsuf]

private theorem replicate_ne_dot1 (n : Nat) (hn : n > 0) {c : Char} (hcdot : c ≠ '.') :
    (List.replicate n c == ['.']) = false := by
  apply beq_false_of_ne
  intro h
  have hh := congrArg List.head? h
  cases n with
  | zero => omega
  | succ m =>
    rw [List.replicate_succ] at hh
    simp only [List.head?_cons, Option.some.injEq] at hh
    exact hcdot hh

private theorem replicate_ne_dot2 (n : Nat) (hn : n > 0) {c : Char} (hcdot : c ≠ '.') :
    (List.replicate n c == ['.', '.']) = false := by
  apply beq_false_of_ne
  intro h
  have hh := congrArg List.head? h
  cases n with
  | zero => omega
  | succ m =>
    rw [List.replicate_succ] at hh
    simp only [List.head?_cons, Option.some.injEq] at hh
    exact hcdot hh

private theorem splitSlashChars_replicate (n : Nat) (hn : n > 0) {c : Char} (hcsl : c ≠ '/') :
    splitSlashChars (List.replicate n c) = [List.replicate n c] := by
  have hno : (List.replicate n c).all (fun x => x != '/') = true := by
    rw [list_all_replicate]
    cases n with | zero => omega | succ _ => simp [hcsl]
  cases n with
  | zero => omega
  | succ m =>
    rw [List.replicate_succ]
    unfold splitSlashChars
    dsimp only
    rw [← List.replicate_succ, ← List.append_nil (List.replicate (m + 1) c),
      splitSlashChars_go_append_noSlash [] (List.replicate (m + 1) c) [] hno,
      List.append_nil, List.reverse_replicate, splitSlashChars.go.eq_1,
      List.reverse_replicate, List.append_nil]

private theorem checkSegments_replicate (n : Nat) (hn : n > 0) {c : Char}
    (hcsl : c ≠ '/') (hcdot : c ≠ '.') :
    checkSegments false (splitSlashChars (List.replicate n c)) = .ok () := by
  rw [splitSlashChars_replicate n hn hcsl]
  have hemp : (List.replicate n c).isEmpty = false := by
    cases n with | zero => omega | succ _ => rfl
  have hnd1 := replicate_ne_dot1 n hn hcdot
  have hnd2 := replicate_ne_dot2 n hn hcdot
  unfold checkSegments checkSegments.go
  simp only [hemp, hnd1, hnd2, Bool.false_eq_true, ↓reduceIte]
  rfl

private theorem validateEntryPath_replicate_simple (n : Nat) (hn : n > 0) {c : Char}
    (hc0 : c ≠ Char.ofNat 0) (hcsl : c ≠ '/') (hcdot : c ≠ '.') :
    validateEntryPath false false .regular (String.ofList (List.replicate n c)) =
      .ok (String.ofList (List.replicate n c)) := by
  unfold validateEntryPath
  dsimp only
  rw [String.toList_ofList, hasNulChars_replicate n hc0]
  have hemp : (List.replicate n c).isEmpty = false := by
    cases n with | zero => omega | succ _ => rfl
  have hhead : ((List.replicate n c).head? == some '/') = false := by
    cases n with
    | zero => omega
    | succ m =>
      rw [List.replicate_succ]
      simp [hcsl]
  have hlast : ((List.replicate n c).reverse.head? == some '/') = false := by
    rw [List.reverse_replicate]
    exact hhead
  have hcs := checkSegments_replicate n hn hcsl hcdot
  simp only [hemp, hhead, hlast, Bool.false_eq_true, ↓reduceIte, Bool.false_and]
  cases n with
  | zero => omega
  | succ m =>
    rw [List.replicate_succ]
    split
    · rename_i h
      split at h
      · rename_i hm
        injection hm with hhd
        exact absurd hhd hcsl
      · rw [← List.replicate_succ, hcs] at h
        cases h
    · rfl

private theorem validateEntryPath_replicate_slash_tail (n : Nat) (hn : n > 0) {c : Char}
    (hc0 : c ≠ Char.ofNat 0) (hcsl : c ≠ '/') (hcdot : c ≠ '.') (tail : String)
    (htail_ne : tail.toList ≠ [])
    (htail0 : hasNulChars tail.toList = false)
    (htail_last : (tail.toList.reverse.head? == some '/') = false)
    (htail_seg : checkSegments false (splitSlashChars tail.toList) = .ok ()) :
    validateEntryPath false false .regular (String.ofList (List.replicate n c) ++ "/" ++ tail) =
      .ok (String.ofList (List.replicate n c) ++ "/" ++ tail) := by
  unfold validateEntryPath
  dsimp only
  have hlist : (String.ofList (List.replicate n c) ++ "/" ++ tail).toList =
      List.replicate n c ++ ('/' :: tail.toList) := by
    simp [String.toList_append, String.toList_ofList]
  rw [hlist, hasNulChars_append, hasNulChars_replicate n hc0]
  have hnul_slash : hasNulChars ('/' :: tail.toList) = false := by
    change ('/' == Char.ofNat 0 || hasNulChars tail.toList) = false
    simp [htail0]
  have hemp : (List.replicate n c ++ ('/' :: tail.toList)).isEmpty = false := by
    cases n with | zero => omega | succ _ => rfl
  have hhead : ((List.replicate n c ++ ('/' :: tail.toList)).head? == some '/') = false := by
    cases n with
    | zero => omega
    | succ m =>
      rw [List.replicate_succ, List.cons_append]
      simp [hcsl]
  have hlast : ((List.replicate n c ++ ('/' :: tail.toList)).reverse.head? == some '/') = false := by
    rw [List.reverse_append, List.reverse_cons]
    cases htr : tail.toList.reverse with
    | nil => exact absurd (List.reverse_eq_nil_iff.mp htr) htail_ne
    | cons x xs =>
      rw [htr] at htail_last
      simpa using htail_last
  have hno : (List.replicate n c).all (fun x => x != '/') = true := by
    rw [list_all_replicate]
    cases n with | zero => omega | succ _ => simp [hcsl]
  have hsplit : splitSlashChars (List.replicate n c ++ ('/' :: tail.toList)) =
      List.replicate n c :: splitSlashChars tail.toList := by
    cases n with
    | zero => omega
    | succ m =>
      rw [List.replicate_succ, List.cons_append]
      unfold splitSlashChars
      dsimp only
      rw [← List.cons_append, ← List.replicate_succ,
        splitSlashChars_go_append_noSlash [] (List.replicate (m + 1) c) ('/' :: tail.toList) hno,
        List.append_nil, List.reverse_replicate, splitSlashChars.go.eq_2, List.reverse_replicate]
      cases ht : tail.toList with
      | nil => exact absurd ht htail_ne
      | cons _ _ => rfl
  have hempn : (List.replicate n c).isEmpty = false := by
    cases n with | zero => omega | succ _ => rfl
  have hnd1 := replicate_ne_dot1 n hn hcdot
  have hnd2 := replicate_ne_dot2 n hn hcdot
  simp only [hnul_slash, hemp, hhead, hlast, Bool.or_self, Bool.false_eq_true, ↓reduceIte, Bool.false_and]
  cases n with
  | zero => omega
  | succ m =>
    rw [List.replicate_succ, List.cons_append]
    split
    · rename_i h
      split at h
      · rename_i hm
        injection hm with hhd
        exact absurd hhd hcsl
      · rw [← List.cons_append, ← List.replicate_succ, hsplit] at h
        have hcs : checkSegments false (List.replicate (m + 1) c :: splitSlashChars tail.toList) = .ok () := by
          unfold checkSegments checkSegments.go
          simp only [hempn, hnd1, hnd2, Bool.false_eq_true, ↓reduceIte]
          cases hs : splitSlashChars tail.toList with
          | nil => rfl
          | cons s ss =>
            unfold checkSegments at htail_seg
            rw [hs] at htail_seg
            exact htail_seg
        rw [hcs] at h
        cases h
    · rw [← List.cons_append, ← List.replicate_succ, ← hlist, String.ofList_toList]

private theorem validateSymlinkTarget_sublink_replicate (n : Nat) (hn : n > 0) {c : Char}
    (hc0 : c ≠ Char.ofNat 0) (hcsl : c ≠ '/') (hcdot : c ≠ '.') :
    validateSymlinkTarget false false "sub/link" ("../" ++ String.ofList (List.replicate n c)) = .ok () := by
  unfold validateSymlinkTarget
  dsimp only
  have hlist : ("../" ++ String.ofList (List.replicate n c)).toList =
      ['.', '.', '/'] ++ List.replicate n c := by
    simp [String.toList_append, String.toList_ofList]
  rw [hlist, hasNulChars_append, hasNulChars_replicate n hc0]
  have hnul_pre : hasNulChars ['.', '.', '/'] = false := by decide
  have hemp : (['.', '.', '/'] ++ List.replicate n c).isEmpty = false := rfl
  have hhead : ((['.', '.', '/'] ++ List.replicate n c).head? == some '/') = false := rfl
  simp only [hnul_pre, hemp, hhead, Bool.or_self, Bool.false_eq_true, ↓reduceIte, Bool.false_and]
  have hno : (List.replicate n c).all (fun x => x != '/') = true := by
    rw [list_all_replicate]
    cases n with | zero => omega | succ _ => simp [hcsl]
  have hsp : splitSlashChars (['.', '.', '/'] ++ List.replicate n c) =
      [['.', '.'], List.replicate n c] := by
    change splitSlashChars.go [] ('.' :: '.' :: '/' :: List.replicate n c) = _
    rw [splitSlashChars.go.eq_3 _ '.' _ (by decide),
      splitSlashChars.go.eq_3 _ '.' _ (by decide),
      splitSlashChars.go.eq_2,
      ← List.append_nil (List.replicate n c),
      splitSlashChars_go_append_noSlash [] (List.replicate n c) [] hno,
      List.append_nil, List.reverse_replicate, splitSlashChars.go.eq_1, List.reverse_replicate]
    simp
  change validateSymlinkTarget.walkDepth "sub/link" 1
      (splitSlashChars (match (['.', '.', '/'] ++ List.replicate n c) with
        | '/' :: rest => rest | rest => rest)) = .ok ()
  have hcons : (match (['.', '.', '/'] ++ List.replicate n c) with
      | '/' :: rest => rest | rest => rest) = ['.', '.', '/'] ++ List.replicate n c := rfl
  rw [hcons, hsp]
  have hempn : (List.replicate n c).isEmpty = false := by
    cases n with | zero => omega | succ _ => rfl
  have hnd1 := replicate_ne_dot1 n hn hcdot
  have hnd2 := replicate_ne_dot2 n hn hcdot
  have hstep : validateSymlinkTarget.walkDepth "sub/link" (0 + 1) [] = .ok () := rfl
  have hstep1 : validateSymlinkTarget.walkDepth "sub/link" (1 - 1) [List.replicate n c] = .ok () := by
    rw [validateSymlinkTarget.walkDepth.eq_2]
    simp only [hempn, hnd1, hnd2, Bool.false_or, Bool.false_eq_true, ↓reduceIte]
    exact hstep
  rw [validateSymlinkTarget.walkDepth.eq_2]
  have h10 : (1 == 0) = false := rfl
  have hdot_eq : ((['.', '.'] : List Char) == ['.']) = false := rfl
  have hdotdot_eq : ((['.', '.'] : List Char) == ['.', '.']) = true := rfl
  simp only [List.isEmpty, Bool.false_or, hdot_eq, hdotdot_eq, h10, Bool.false_eq_true, ↓reduceIte,
    hstep1]

private theorem encodeEntryBlocks_noPax_size (e : TarEntry) (normPath : String)
    (hne : needsPax e (wirePathOf e.kind normPath) = false) :
    (encodeEntryBlocks e normPath).size = 512 + pad512 e.data.size := by
  unfold encodeEntryBlocks
  dsimp only
  rw [ite_eq_left (by simp [hne])]
  rcases hpair : (if (wirePathOf e.kind normPath).toUTF8.size ≤ 100 then ("", wirePathOf e.kind normPath)
    else match findUstarSplit (wirePathOf e.kind normPath) with
      | some pair => pair
      | none => ("", wirePathOf e.kind normPath)) with ⟨pfx, nm⟩
  rw [ByteArray.size_append, buildUstarHeader_size, padBlock512_size]

private theorem defaultApi_pack_eq (entries : List TarEntry) :
    defaultApi.pack entries = Impl.packWith {} entries := rfl

private theorem defaultApi_unpack_eq (bytes : ByteArray) :
    defaultApi.unpack bytes = Impl.unpackWith {} bytes := rfl

private theorem defaultApi_unpackWith_eq (opts : UnpackOptions) (bytes : ByteArray) :
    defaultApi.unpackWith opts bytes = Impl.unpackWith opts bytes := rfl

private theorem checkRoundTripCase_test1_empty_ex :
    ∃ emptyBytes : ByteArray,
      defaultApi.pack [] = .ok emptyBytes ∧
      emptyBytes.size = 1024 ∧
      defaultApi.unpackWith { maxEntries := 0, maxTotalBytes := 0 } emptyBytes = .ok [] := by
  have hv : ValidArchive false false [] := by
    unfold ValidArchive; decide
  have ⟨bytes, hpack_go, hbytes_eq⟩ := packWith_go_eq_encodeEntriesList {} [] [] ByteArray.empty hv
  have hpack : defaultApi.pack [] = .ok bytes := by
    rw [defaultApi_pack_eq]
    unfold Impl.packWith
    exact hpack_go
  have hbytes_form : bytes = zeroBlock ++ zeroBlock := by
    have hdet : (if ({} : PackOptions).deterministic = true then List.map zeroDeterministicMeta [] else []) = [] := rfl
    have h1 : encodeEntriesList [] = ByteArray.empty := rfl
    rw [hdet, h1, ByteArray.empty_append, ByteArray.empty_append] at hbytes_eq
    exact hbytes_eq
  have hsz : bytes.size = 1024 := by
    rw [hbytes_form, ByteArray.size_append, zeroBlock_size]
  have hnz : (bytes.size == 0 || bytes.size % 512 != 0) = false := by
    rw [hsz]; rfl
  have hunpack : defaultApi.unpackWith { maxEntries := 0, maxTotalBytes := 0 } bytes = .ok [] := by
    rw [defaultApi_unpackWith_eq]
    unfold Impl.unpackWith
    rw [hnz]
    have hloop := unpackLoop_at_twoZeroBlocks { maxEntries := 0, maxTotalBytes := 0 }
      ByteArray.empty [] [] 0
    unfold twoZeroBlocks at hloop
    rw [ByteArray.empty_append, ByteArray.size_empty, ← hbytes_form] at hloop
    exact hloop
  exact ⟨bytes, hpack, hsz, hunpack⟩

private theorem test1_split_props (splitPath : String) (splitEntry : TarEntry)
    (hsp : splitPath = String.ofList (List.replicate 60 'd') ++ "/" ++ String.ofList (List.replicate 60 'f'))
    (hse : splitEntry = { path := splitPath, kind := .regular, data := "hi".toUTF8 }) :
    ValidArchive false false [splitEntry] ∧
    normalizeTarPath splitEntry.kind splitEntry.path = splitPath ∧
    needsPax splitEntry (wirePathOf splitEntry.kind splitPath) = false ∧
    ([splitEntry].all fitsPaxLimit) = true ∧
    totalDataBytes [splitEntry] ≤ ({} : UnpackOptions).maxTotalBytes := by
  subst hsp hse
  have hval : validateEntryPath false false .regular
      (String.ofList (List.replicate 60 'd') ++ "/" ++ String.ofList (List.replicate 60 'f')) =
      .ok (String.ofList (List.replicate 60 'd') ++ "/" ++ String.ofList (List.replicate 60 'f')) := by
    apply validateEntryPath_replicate_slash_tail 60 (by decide) (by decide) (by decide) (by decide)
    · rw [String.toList_ofList]; intro h; cases h
    · rw [String.toList_ofList, hasNulChars_replicate 60 (by decide)]
    · rw [String.toList_ofList, List.reverse_replicate]
      change ((List.replicate (59 + 1) 'f').head? == some '/') = false
      rw [List.replicate_succ]
      rfl
    · rw [String.toList_ofList]
      exact checkSegments_replicate 60 (by decide) (by decide) (by decide)
  have hnp : normalizeTarPath EntryKind.regular
      (String.ofList (List.replicate 60 'd') ++ "/" ++ String.ofList (List.replicate 60 'f')) =
      String.ofList (List.replicate 60 'd') ++ "/" ++ String.ofList (List.replicate 60 'f') :=
    (validateEntryPath_normPath hval).symm
  have hv : ValidArchive false false
      [{ path := String.ofList (List.replicate 60 'd') ++ "/" ++ String.ofList (List.replicate 60 'f'),
         kind := .regular, data := "hi".toUTF8 }] := by
    unfold ValidArchive validArchiveBool
    simp only [List.all_cons, List.all_nil, Bool.and_true, validEntryBool,
      hval, noDupNormalizedPathsBool, noDupNormalizedPathsBool.go.eq_2,
      noDupNormalizedPathsBool.go.eq_1, hnp]
    have hhi : ("hi".toUTF8).size < u64Limit := by
      rw [toUTF8_eq_toByteArray, List.size_toByteArray]; decide
    have h0 : (0 : Nat) < u64Limit := by decide
    have hnu : (!hasNulString "") = true := by decide
    simp only [hhi, h0, hnu, decide_true, Bool.true_and, Bool.and_true, beq_self_eq_true,
      List.contains, List.elem]
    rfl
  have hfind : (findUstarSplit
      (String.ofList (List.replicate 60 'd') ++ "/" ++ String.ofList (List.replicate 60 'f'))).isSome = true := by
    unfold findUstarSplit
    have hlist : (String.ofList (List.replicate 60 'd') ++ "/" ++ String.ofList (List.replicate 60 'f')).toList =
        List.replicate 60 'd' ++ ('/' :: List.replicate 60 'f') := by
      simp
    have hno : (List.replicate 60 'd').all (fun c => c != '/') = true := by
      rw [list_all_replicate]; decide
    rw [hlist, findUstarSplit_go_noSlash [] (List.replicate 60 'd') ('/' :: List.replicate 60 'f') hno,
      List.append_nil, List.reverse_replicate, findUstarSplit.go.eq_2, List.reverse_replicate,
      toUTF8_size_ofList_replicate 60 (by decide), toUTF8_size_ofList_replicate 60 (by decide)]
    have he1 : (String.ofList (List.replicate 60 'd')).isEmpty = false := by decide
    have he2 : (String.ofList (List.replicate 60 'f')).isEmpty = false := by decide
    rw [he1, he2]
    decide
  have hneeds : needsPax
      { path := String.ofList (List.replicate 60 'd') ++ "/" ++ String.ofList (List.replicate 60 'f'),
        kind := .regular, data := "hi".toUTF8 }
      (wirePathOf .regular (String.ofList (List.replicate 60 'd') ++ "/" ++ String.ofList (List.replicate 60 'f'))) =
      false := by
    unfold needsPax pathFitsUstar wirePathOf
    dsimp only
    have hslash : isAsciiString "/" = true := by
      simp only [isAsciiString, toUTF8_toList]; decide
    have his : isAsciiString (String.ofList (List.replicate 60 'd') ++ "/" ++ String.ofList (List.replicate 60 'f')) = true := by
      rw [isAsciiString_append, isAsciiString_append,
        isAsciiString_ofList_replicate 60 (by decide), hslash,
        isAsciiString_ofList_replicate 60 (by decide)]
      rfl
    have hi0 : isAsciiString "" = true := by simp [isAsciiString]
    have hhi_sz : ("hi".toUTF8).size = 2 := by
      rw [toUTF8_eq_toByteArray, List.size_toByteArray]; decide
    have he_sz : ("").toUTF8.size = 0 := by
      rw [toUTF8_eq_toByteArray, List.size_toByteArray]; decide
    simp only [his, hfind, hi0, hhi_sz, he_sz,
      Bool.or_true, Bool.and_true, Bool.not_true, Bool.false_or]
    decide
  have hfit :
      ([{ path := String.ofList (List.replicate 60 'd') ++ "/" ++ String.ofList (List.replicate 60 'f'),
          kind := .regular, data := "hi".toUTF8 }].all fitsPaxLimit) = true := by
    simp only [List.all_cons, List.all_nil, Bool.and_true, fitsPaxLimit]
    rw [hnp]
    rw [ite_eq_right (fun h => absurd h (by rw [hneeds]; decide))]
  have htot :
      totalDataBytes
        [{ path := String.ofList (List.replicate 60 'd') ++ "/" ++ String.ofList (List.replicate 60 'f'),
           kind := .regular, data := "hi".toUTF8 }] ≤ ({} : UnpackOptions).maxTotalBytes := by
    have hhi : ("hi".toUTF8).size = 2 := by
      rw [toUTF8_eq_toByteArray, List.size_toByteArray]; decide
    simp only [totalDataBytes, List.foldl_cons, List.foldl_nil, Nat.zero_add, hhi]
    decide
  exact ⟨hv, hnp, hneeds, hfit, htot⟩

private theorem paxLong_buildPaxPayload_size (s : String)
    (hnot : (!pathFitsUstar s) = true) (hsz : s.toUTF8.size = 270) :
    decide ((buildPaxPayload { path := s, kind := .regular, mode := 0o644 } s).size ≤ maxPaxHeaderBytes) = true := by
  rw [decide_eq_true_eq]
  unfold buildPaxPayload
  dsimp only
  have hrUg : (!isAsciiString "" || decide (("").toUTF8.size > 32)) = false := by
    simp only [isAsciiString, toUTF8_eq_toByteArray, toByteArray_toList, List.size_toByteArray]
    decide
  rw [ite_eq_left hnot]
  rw [ite_eq_right (fun h => absurd h (by change ¬(false = true); decide))]
  rw [ite_eq_right (fun h => absurd h (by rw [hrUg]; decide))]
  rw [ite_eq_right (fun h => absurd h (by rw [hrUg]; decide))]
  rw [ite_eq_right (by decide)]
  rw [ite_eq_right (by decide)]
  rw [ite_eq_right (by decide)]
  rw [ite_eq_right (by decide)]
  simp only [ByteArray.append_empty]
  rw [encodePaxRecord_size_of_kv "path" s, hsz]
  have hpk : ("path").toUTF8.size = 4 := by rw [toUTF8_eq_toByteArray, List.size_toByteArray]; decide
  rw [hpk]
  have hpr : (1 + 4 + 1 + 270 + 1 : Nat) = 277 := rfl
  rw [hpr]
  have htl : (toString (paxRecordTotalLen 277)).toUTF8.size ≤ 10 := by
    rw [toUTF8_eq_toByteArray, List.size_toByteArray]; decide
  exact Nat.le_trans (Nat.add_le_add_right htl 277) (by decide)

private theorem test1_e14_props (paxBoundaryPath paxLongPath : String) (e1 e2 e3 e4 : TarEntry)
    (hpb : paxBoundaryPath = String.ofList (List.replicate 91 'p'))
    (hpl : paxLongPath = String.ofList (List.replicate 260 'x') ++ "/café.txt")
    (he1 : e1 =
      { path := paxBoundaryPath, kind := .regular, mode := 0o100755,
        uid := ustarOctal7Limit + 7, gid := ustarOctal7Limit + 9,
        mtime := ustarOctal11Limit + 42, uname := "üser", gname := "grøup",
        data := "payload".toUTF8 })
    (he2 : e2 = { path := "sub/", kind := .directory, mode := 0o755 })
    (he3 : e3 =
      { path := "sub/link", kind := .symlink, mode := 0o777,
        linkTarget := "../" ++ paxBoundaryPath })
    (he4 : e4 = { path := paxLongPath, kind := .regular, mode := 0o644 }) :
    ValidArchive false false [e1, e2, e3, e4] ∧
    ([e1, e2, e3, e4].all fitsPaxLimit) = true ∧
    totalDataBytes [e1, e2, e3, e4] ≤ ({} : UnpackOptions).maxTotalBytes := by
  subst hpb hpl he1 he2 he3 he4
  have hval_e1 : validateEntryPath false false .regular (String.ofList (List.replicate 91 'p')) =
      .ok (String.ofList (List.replicate 91 'p')) :=
    validateEntryPath_replicate_simple 91 (by decide) (by decide) (by decide) (by decide)
  have hval_e2 : validateEntryPath false false .directory "sub/" = .ok "sub" := rfl
  have hval_e3 : validateEntryPath false false .symlink "sub/link" = .ok "sub/link" := rfl
  have hval_e4 : validateEntryPath false false .regular (String.ofList (List.replicate 260 'x') ++ "/café.txt") =
      .ok (String.ofList (List.replicate 260 'x') ++ "/café.txt") := by
    have hcat : String.ofList (List.replicate 260 'x') ++ "/café.txt" =
        String.ofList (List.replicate 260 'x') ++ "/" ++ "café.txt" := by
      have h1 : ("/café.txt" : String) = "/" ++ "café.txt" := rfl
      rw [h1, ← String.append_assoc]
    rw [hcat]
    exact validateEntryPath_replicate_slash_tail 260 (by decide) (by decide) (by decide) (by decide)
      "café.txt" (by decide) (by decide) (by decide) rfl
  have hsym_e3 : validateSymlinkTarget false false "sub/link" ("../" ++ String.ofList (List.replicate 91 'p')) = .ok () :=
    validateSymlinkTarget_sublink_replicate 91 (by decide) (by decide) (by decide) (by decide)
  have hnp1 := (validateEntryPath_normPath hval_e1).symm
  have hnp2 := (validateEntryPath_normPath hval_e2).symm
  have hnp3 := (validateEntryPath_normPath hval_e3).symm
  have hnp4 := (validateEntryPath_normPath hval_e4).symm
  have hv_e14 : ValidArchive false false
      [{ path := String.ofList (List.replicate 91 'p'), kind := .regular, mode := 0o100755,
         uid := ustarOctal7Limit + 7, gid := ustarOctal7Limit + 9,
         mtime := ustarOctal11Limit + 42, uname := "üser", gname := "grøup",
         data := "payload".toUTF8 },
       { path := "sub/", kind := .directory, mode := 0o755 },
       { path := "sub/link", kind := .symlink, mode := 0o777,
         linkTarget := "../" ++ String.ofList (List.replicate 91 'p') },
       { path := String.ofList (List.replicate 260 'x') ++ "/café.txt", kind := .regular, mode := 0o644 }] := by
    unfold ValidArchive validArchiveBool
    simp only [List.all_cons, List.all_nil, Bool.and_true, validEntryBool,
      hval_e1, hval_e2, hval_e3, hval_e4, hsym_e3,
      noDupNormalizedPathsBool, noDupNormalizedPathsBool.go.eq_2, noDupNormalizedPathsBool.go.eq_1,
      hnp1, hnp2, hnp3, hnp4]
    have hpay : ("payload".toUTF8).size < u64Limit := by
      rw [toUTF8_eq_toByteArray, List.size_toByteArray]; decide
    have hn1 : (!hasNulString "üser") = true := by decide
    have hn2 : (!hasNulString "grøup") = true := by decide
    have hlt1 : ustarOctal7Limit + 7 < u64Limit := by decide
    have hlt2 : ustarOctal7Limit + 9 < u64Limit := by decide
    have hlt3 : ustarOctal11Limit + 42 < u64Limit := by decide
    have he_nul : (!hasNulString "") = true := by decide
    have h0_lt : (0 : Nat) < u64Limit := by decide
    have hb_sz : (ByteArray.empty).size = 0 := rfl
    simp only [hpay, hn1, hn2, hlt1, hlt2, hlt3, he_nul, h0_lt, hb_sz,
      decide_true, Bool.true_and, Bool.and_true, beq_self_eq_true]
    have hlen91 : (String.ofList (List.replicate 91 'p')).length = 91 := by
      simp only [String.length_ofList, List.length_replicate]
    have hcaf : ("/café.txt" : String).length = 9 := by decide
    have hlen269 : (String.ofList (List.replicate 260 'x') ++ "/café.txt").length = 269 := by
      simp only [String.length_append, String.length_ofList, List.length_replicate, hcaf]
    have h21 : ("sub" == String.ofList (List.replicate 91 'p')) = false := by
      apply beq_false_of_ne
      intro heq
      have hlen := congrArg String.length heq
      have hl1 : ("sub" : String).length = 3 := rfl
      omega
    have h32 : ("sub/link" == "sub") = false := rfl
    have h31 : ("sub/link" == String.ofList (List.replicate 91 'p')) = false := by
      apply beq_false_of_ne
      intro heq
      have hlen := congrArg String.length heq
      have hl1 : ("sub/link" : String).length = 8 := rfl
      omega
    have h43 : (String.ofList (List.replicate 260 'x') ++ "/café.txt" == "sub/link") = false := by
      apply beq_false_of_ne
      intro heq
      have hlen := congrArg String.length heq
      have hl1 : ("sub/link" : String).length = 8 := rfl
      omega
    have h42 : (String.ofList (List.replicate 260 'x') ++ "/café.txt" == "sub") = false := by
      apply beq_false_of_ne
      intro heq
      have hlen := congrArg String.length heq
      have hl1 : ("sub" : String).length = 3 := rfl
      omega
    have h41 : (String.ofList (List.replicate 260 'x') ++ "/café.txt" ==
        String.ofList (List.replicate 91 'p')) = false := by
      apply beq_false_of_ne
      intro heq
      have hlen := congrArg String.length heq
      omega
    simp only [List.contains, List.elem, h21, h32, h31, h43, h42, h41]
    rfl
  have his1 : isAsciiString (String.ofList (List.replicate 91 'p')) = true :=
    isAsciiString_ofList_replicate 91 (by decide)
  have hsz1 : (String.ofList (List.replicate 91 'p')).toUTF8.size = 91 :=
    toUTF8_size_ofList_replicate 91 (by decide)
  have his3_lt : isAsciiString ("../" ++ String.ofList (List.replicate 91 'p')) = true := by
    rw [isAsciiString_append, isAsciiString_ofList_replicate 91 (by decide)]
    have hdot : isAsciiString "../" = true := by simp only [isAsciiString, toUTF8_toList]; decide
    rw [hdot]; rfl
  have hsz3_lt : ("../" ++ String.ofList (List.replicate 91 'p')).toUTF8.size = 94 := by
    rw [toUTF8_size_append, toUTF8_size_ofList_replicate 91 (by decide)]
    have hdot : ("../").toUTF8.size = 3 := by rw [toUTF8_eq_toByteArray, List.size_toByteArray]; decide
    rw [hdot]
  have hsz4 : (String.ofList (List.replicate 260 'x') ++ "/café.txt").toUTF8.size = 270 := by
    have hcaf : ("/café.txt").toUTF8.size = 10 := by
      rw [toUTF8_eq_toByteArray, List.size_toByteArray]; decide
    rw [toUTF8_size_append, toUTF8_size_ofList_replicate 260 (c := 'x') (by decide), hcaf]
  have hfit1 : fitsPaxLimit
      { path := String.ofList (List.replicate 91 'p'), kind := .regular, mode := 0o100755,
        uid := ustarOctal7Limit + 7, gid := ustarOctal7Limit + 9,
        mtime := ustarOctal11Limit + 42, uname := "üser", gname := "grøup",
        data := "payload".toUTF8 } = true := by
    unfold fitsPaxLimit
    dsimp only
    rw [hnp1]
    have hne : needsPax
        { path := String.ofList (List.replicate 91 'p'), kind := .regular, mode := 0o100755,
          uid := ustarOctal7Limit + 7, gid := ustarOctal7Limit + 9,
          mtime := ustarOctal11Limit + 42, uname := "üser", gname := "grøup",
          data := "payload".toUTF8 }
        (wirePathOf .regular (String.ofList (List.replicate 91 'p'))) = true := by
      unfold needsPax pathFitsUstar wirePathOf
      dsimp only
      rw [his1, hsz1]
      simp only [isAsciiString, toUTF8_eq_toByteArray, toByteArray_toList, List.size_toByteArray]
      decide
    have hnot_path : (!pathFitsUstar (wirePathOf .regular (String.ofList (List.replicate 91 'p')))) = false := by
      unfold pathFitsUstar wirePathOf
      dsimp only
      simp only [his1, hsz1]
      decide
    rw [ite_eq_left hne]
    unfold buildPaxPayload
    simp only [hnot_path, Bool.false_eq_true, ↓reduceIte, ByteArray.size_append]
    simp only [toUTF8_eq_toByteArray, toByteArray_toList, List.size_toByteArray, isAsciiString]
    decide
  have hfit2 : fitsPaxLimit { path := "sub/", kind := .directory, mode := 0o755 } = true := by
    simp only [fitsPaxLimit, needsPax, pathFitsUstar, isAsciiString, toUTF8_eq_toByteArray,
      toByteArray_toList, List.size_toByteArray]
    decide
  have hfit3 : fitsPaxLimit
      { path := "sub/link", kind := .symlink, mode := 0o777,
        linkTarget := "../" ++ String.ofList (List.replicate 91 'p') } = true := by
    unfold fitsPaxLimit
    dsimp only
    rw [hnp3]
    have hne : needsPax
        { path := "sub/link", kind := .symlink, mode := 0o777,
          linkTarget := "../" ++ String.ofList (List.replicate 91 'p') }
        (wirePathOf .symlink "sub/link") = false := by
      unfold needsPax pathFitsUstar wirePathOf
      simp only [his3_lt, hsz3_lt]
      simp only [isAsciiString, toUTF8_eq_toByteArray, toByteArray_toList, List.size_toByteArray]
      decide
    rw [ite_eq_right (fun h => absurd h (by rw [hne]; decide))]
  have hfit4 : fitsPaxLimit
      { path := String.ofList (List.replicate 260 'x') ++ "/café.txt", kind := .regular, mode := 0o644 } = true := by
    unfold fitsPaxLimit
    dsimp only
    rw [hnp4]
    have hcaf_is : isAsciiString "/café.txt" = false := by
      simp only [isAsciiString, toUTF8_eq_toByteArray, toByteArray_toList]; decide
    have his4 : isAsciiString (String.ofList (List.replicate 260 'x') ++ "/café.txt") = false := by
      rw [isAsciiString_append, hcaf_is, Bool.and_false]
    have hnot4_w : (!pathFitsUstar (wirePathOf .regular (String.ofList (List.replicate 260 'x') ++ "/café.txt"))) = true := by
      simp only [pathFitsUstar, wirePathOf, his4, Bool.false_and, Bool.not_false]
    have hne4 : needsPax
        { path := String.ofList (List.replicate 260 'x') ++ "/café.txt", kind := .regular, mode := 0o644 }
        (wirePathOf .regular (String.ofList (List.replicate 260 'x') ++ "/café.txt")) = true := by
      unfold needsPax; simp only [hnot4_w, Bool.true_or]
    rw [ite_eq_left hne4]
    dsimp only [wirePathOf]
    have hnot4 : (!pathFitsUstar (String.ofList (List.replicate 260 'x') ++ "/café.txt")) = true := by
      simp only [pathFitsUstar, his4, Bool.false_and, Bool.not_false]
    exact paxLong_buildPaxPayload_size _ hnot4 hsz4
  have hfit_e14 :
      ([{ path := String.ofList (List.replicate 91 'p'), kind := .regular, mode := 0o100755,
          uid := ustarOctal7Limit + 7, gid := ustarOctal7Limit + 9,
          mtime := ustarOctal11Limit + 42, uname := "üser", gname := "grøup",
          data := "payload".toUTF8 },
        { path := "sub/", kind := .directory, mode := 0o755 },
        { path := "sub/link", kind := .symlink, mode := 0o777,
          linkTarget := "../" ++ String.ofList (List.replicate 91 'p') },
        { path := String.ofList (List.replicate 260 'x') ++ "/café.txt", kind := .regular, mode := 0o644 }].all
          fitsPaxLimit) = true := by
    simp only [List.all_cons, List.all_nil, hfit1, hfit2, hfit3, hfit4, Bool.and_true]
  have htot_e14 : totalDataBytes
      [{ path := String.ofList (List.replicate 91 'p'), kind := .regular, mode := 0o100755,
         uid := ustarOctal7Limit + 7, gid := ustarOctal7Limit + 9,
         mtime := ustarOctal11Limit + 42, uname := "üser", gname := "grøup",
         data := "payload".toUTF8 },
       { path := "sub/", kind := .directory, mode := 0o755 },
       { path := "sub/link", kind := .symlink, mode := 0o777,
         linkTarget := "../" ++ String.ofList (List.replicate 91 'p') },
       { path := String.ofList (List.replicate 260 'x') ++ "/café.txt", kind := .regular, mode := 0o644 }] ≤
      ({} : UnpackOptions).maxTotalBytes := by
    have h1 : ("payload".toUTF8).size = 7 := by
      rw [toUTF8_eq_toByteArray, List.size_toByteArray]; decide
    simp only [totalDataBytes, List.foldl_cons, List.foldl_nil, Nat.zero_add, h1]
    decide
  exact ⟨hv_e14, hfit_e14, htot_e14⟩

private theorem test1_e14_roundTrip (paxBoundaryPath paxLongPath : String) (e1 e2 e3 e4 : TarEntry)
    (hpb : paxBoundaryPath = String.ofList (List.replicate 91 'p'))
    (hpl : paxLongPath = String.ofList (List.replicate 260 'x') ++ "/café.txt")
    (he1 : e1 =
      { path := paxBoundaryPath, kind := .regular, mode := 0o100755,
        uid := ustarOctal7Limit + 7, gid := ustarOctal7Limit + 9,
        mtime := ustarOctal11Limit + 42, uname := "üser", gname := "grøup",
        data := "payload".toUTF8 })
    (he2 : e2 = { path := "sub/", kind := .directory, mode := 0o755 })
    (he3 : e3 =
      { path := "sub/link", kind := .symlink, mode := 0o777,
        linkTarget := "../" ++ paxBoundaryPath })
    (he4 : e4 = { path := paxLongPath, kind := .regular, mode := 0o644 }) :
    AllPass (checkRoundTripCase defaultApi {} {} [e1, e2, e3, e4]) ∧
    AllPass (checkRoundTripCase defaultApi { deterministic := true } {} [e1, e2, e3, e4]) := by
  have hprops := test1_e14_props paxBoundaryPath paxLongPath e1 e2 e3 e4 hpb hpl he1 he2 he3 he4
  have hlen_e14 : [e1, e2, e3, e4].length ≤ ({} : UnpackOptions).maxEntries := by
    simp only [List.length_cons, List.length_nil]
    decide
  exact ⟨checkRoundTripCase_of_valid (packOpts := {}) (unpackOpts := {}) hprops.1 rfl rfl
      hlen_e14 hprops.2.2 hprops.2.1,
    checkRoundTripCase_of_valid (packOpts := { deterministic := true }) (unpackOpts := {}) hprops.1 rfl rfl
      hlen_e14 hprops.2.2 hprops.2.1⟩

private theorem test1_split_ex (splitPath : String) (splitEntry : TarEntry)
    (hsp : splitPath = String.ofList (List.replicate 60 'd') ++ "/" ++ String.ofList (List.replicate 60 'f'))
    (hse : splitEntry = { path := splitPath, kind := .regular, data := "hi".toUTF8 }) :
    ∃ splitBytes decSplit,
      defaultApi.pack [splitEntry] = .ok splitBytes ∧
      splitBytes.size = 2048 ∧
      defaultApi.unpack splitBytes = .ok decSplit ∧
      TarEquiv [splitEntry] decSplit := by
  have ⟨hv_split, hnp_split, hneeds_split, hfit_split, htot_split⟩ :=
    test1_split_props splitPath splitEntry hsp hse
  have hv_split_pack : ([splitEntry].all (validEntryBool false false) &&
      noDupNormalizedPathsBool.go [] [splitEntry]) = true := hv_split
  have ⟨splitBytes, hpack_split_go, hsplit_eq⟩ :=
    packWith_go_eq_encodeEntriesList {} [splitEntry] [] ByteArray.empty hv_split_pack
  have hpack_split : defaultApi.pack [splitEntry] = .ok splitBytes := by
    rw [defaultApi_pack_eq]
    unfold Impl.packWith
    exact hpack_split_go
  have hsplit_form : splitBytes = encodeEntryBlocks splitEntry splitPath ++ (zeroBlock ++ zeroBlock) := by
    rw [hsplit_eq, ByteArray.empty_append]
    change encodeEntriesList [splitEntry] ++ (zeroBlock ++ zeroBlock) = _
    simp only [encodeEntriesList, hnp_split, ByteArray.append_empty]
  have hblk_sz : (encodeEntryBlocks splitEntry splitPath).size = 1024 := by
    rw [encodeEntryBlocks_noPax_size splitEntry splitPath hneeds_split]
    have hsuf : splitEntry.data.size = 2 := by
      rw [hse]
      rw [toUTF8_eq_toByteArray, List.size_toByteArray]; decide
    rw [hsuf]
    decide
  have hsplit_sz : splitBytes.size = 2048 := by
    rw [hsplit_form, ByteArray.size_append, ByteArray.size_append, zeroBlock_size, hblk_sz]
  have hv_split_unpack := hv_split
  unfold ValidArchive validArchiveBool at hv_split_unpack
  rw [Bool.and_eq_true, List.all_eq_true] at hv_split_unpack
  have hlen_sp : ([] : List String).length + [splitEntry].length ≤ ({} : UnpackOptions).maxEntries := by
    simp only [List.length_nil, List.length_cons]
    decide
  have ⟨decSplit, hteq_split, hloop_split⟩ := unpackLoop_encodeEntriesList {} ByteArray.empty [splitEntry] [] [] 0
    hv_split_unpack.1 hv_split_unpack.2 hfit_split hlen_sp (by rw [Nat.zero_add]; exact htot_split)
  have hsplit_nz : (splitBytes.size == 0 || splitBytes.size % 512 != 0) = false := by
    rw [hsplit_sz]; rfl
  have hunpack_split : defaultApi.unpack splitBytes = .ok decSplit := by
    rw [defaultApi_unpack_eq]
    unfold Impl.unpackWith
    rw [hsplit_nz, hsplit_form]
    have hloop' : unpackLoop {} (ByteArray.empty ++ (encodeEntriesList [splitEntry] ++ (zeroBlock ++ zeroBlock)))
        ByteArray.empty.size none [] [] 0 = .ok decSplit := by
      simpa using hloop_split
    simp only [encodeEntriesList, hnp_split, ByteArray.append_empty, ByteArray.empty_append,
      ByteArray.size_empty] at hloop'
    exact hloop'
  exact ⟨splitBytes, decSplit, hpack_split, hsplit_sz, hunpack_split, hteq_split⟩

/-- Prove `test_tar_packWith_concreteUstarAndPaxCases_roundTrip` for `defaultApi`. -/
theorem allPass_packWith_concreteUstarAndPaxCases_roundTrip :
    AllPass (test_tar_packWith_concreteUstarAndPaxCases_roundTrip defaultApi) := by
  let splitPath := String.ofList (List.replicate 60 'd') ++ "/" ++ String.ofList (List.replicate 60 'f')
  let splitEntry : TarEntry := { path := splitPath, kind := .regular, data := "hi".toUTF8 }
  have ⟨splitBytes, decSplit, hpack_split, hsplit_sz, hunpack_split, hteq_split⟩ :=
    test1_split_ex splitPath splitEntry rfl rfl
  have hiff : ∀ api po uo es (k : Unit → AllPassRun Unit),
      AllPass (Bind.bind (checkRoundTripCase api po uo es) k) ↔
      AllPass (checkRoundTripCase api po uo es) ∧ AllPass (k ()) := by
    intro api po uo es k
    unfold checkRoundTripCase
    cases api.packWith po es with
    | error _ => simp [AllPass, Bind.bind, NondetTest.assert]
    | ok bytes =>
      dsimp only
      cases api.unpackWith uo bytes with
      | error _ => simp [AllPass, Bind.bind, NondetTest.assert]
      | ok decoded => simp [AllPass, Bind.bind, NondetTest.assert]
  have allPass_have : ∀ {α : Type _} (v : α) (f : α → AllPassRun Unit),
      AllPass (have x := v; f x) ↔ ∀ x, x = v → AllPass (f x) := by
    intro _ v f
    exact ⟨fun h x hx => hx ▸ h, fun h => h v rfl⟩
  have allPass_assert_bind : ∀ (p : Prop) (k : Unit → AllPassRun Unit),
      AllPass (Bind.bind (NondetTest.assert p) k) ↔ p ∧ AllPass (k ()) := by
    intro p k
    simp [AllPass, Bind.bind, NondetTest.assert]
  have ⟨eb, hpack_eb, hsz_eb, hunpack_eb⟩ := checkRoundTripCase_test1_empty_ex
  unfold test_tar_packWith_concreteUstarAndPaxCases_roundTrip
  rw [hpack_eb]
  dsimp (config := { zeta := false }) only
  rw [allPass_have]
  intro __do_jp0 hjp0
  rw [allPass_assert_bind]
  refine ⟨hsz_eb, ?_⟩
  rw [hjp0, hunpack_eb]
  dsimp (config := { zeta := false }) only
  rw [allPass_assert_bind]
  refine ⟨rfl, ?_⟩
  rw [allPass_have]
  intro sp hsp
  rw [allPass_have]
  intro se hse
  dsimp only [splitEntry, splitPath] at hpack_split
  rw [hpack_split]
  dsimp (config := { zeta := false }) only
  rw [hse, hsp]
  dsimp (config := { zeta := false }) only
  rw [allPass_assert_bind]
  refine ⟨hsplit_sz, ?_⟩
  rw [hunpack_split]
  dsimp (config := { zeta := false }) only
  rw [allPass_assert_bind]
  refine ⟨hteq_split, ?_⟩
  rw [allPass_have]
  intro cont hcont
  rw [hiff]
  refine ⟨?_, ?_⟩
  · generalize hpb_g : String.ofList (List.replicate 91 'p') = pb_var
    generalize hpl_g : (String.ofList (List.replicate 260 'x') ++ "/café.txt") = pl_var
    exact (test1_e14_roundTrip pb_var pl_var
      { path := pb_var, kind := .regular, mode := 0o100755,
        uid := ustarOctal7Limit + 7, gid := ustarOctal7Limit + 9,
        mtime := ustarOctal11Limit + 42, uname := "üser", gname := "grøup",
        data := "payload".toUTF8 }
      { path := "sub/", kind := .directory, mode := 0o755 }
      { path := "sub/link", kind := .symlink, mode := 0o777,
        linkTarget := "../" ++ pb_var }
      { path := pl_var, kind := .regular, mode := 0o644 }
      hpb_g.symm hpl_g.symm rfl rfl rfl rfl).1
  · rw [hcont]
    dsimp (config := { zeta := false }) only
    generalize hpb_g : String.ofList (List.replicate 91 'p') = pb_var
    generalize hpl_g : (String.ofList (List.replicate 260 'x') ++ "/café.txt") = pl_var
    exact (test1_e14_roundTrip pb_var pl_var
      { path := pb_var, kind := .regular, mode := 0o100755,
        uid := ustarOctal7Limit + 7, gid := ustarOctal7Limit + 9,
        mtime := ustarOctal11Limit + 42, uname := "üser", gname := "grøup",
        data := "payload".toUTF8 }
      { path := "sub/", kind := .directory, mode := 0o755 }
      { path := "sub/link", kind := .symlink, mode := 0o777,
        linkTarget := "../" ++ pb_var }
      { path := pl_var, kind := .regular, mode := 0o644 }
      hpb_g.symm hpl_g.symm rfl rfl rfl rfl).2

end LeanSwe.Tar.Proofs
