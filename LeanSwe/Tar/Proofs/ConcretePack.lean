import LeanSwe.Tar.SpecTests
import LeanSwe.Tar.Interface
import LeanSwe.Tar.Proofs.ByteModel
import LeanSwe.Tar.Proofs.FieldCodecs
import LeanSwe.Tar.Proofs.HeaderLayout
import LeanSwe.Tar.Proofs.PackValid
import LeanSwe.Tar.Proofs.UnpackValid
import LeanSwe.Tar.Proofs.RoundTrip

/-! Concrete round-trip and negative packing tests for `LeanSwe.Tar`. -/

namespace LeanSwe.Tar.Proofs

open Core
open Core.NondetTest
open LeanSwe.Tar
open LeanSwe.Tar.Model
open LeanSwe.Tar.Impl

private theorem defaultApi_pack_eq (entries : List TarEntry) :
    defaultApi.pack entries = Impl.packWith {} entries := rfl

private theorem defaultApi_packWith_eq (opts : PackOptions) (entries : List TarEntry) :
    defaultApi.packWith opts entries = Impl.packWith opts entries := rfl

private theorem defaultApi_unpack_eq (bytes : ByteArray) :
    defaultApi.unpack bytes = Impl.unpackWith {} bytes := rfl

private theorem defaultApi_unpackWith_eq (opts : UnpackOptions) (bytes : ByteArray) :
    defaultApi.unpackWith opts bytes = Impl.unpackWith opts bytes := rfl

private theorem allPass_have {α : Type _} (v : α) (f : α → AllPassRun Unit) :
    AllPass (have x := v; f x) ↔ ∀ x, x = v → AllPass (f x) :=
  ⟨fun h _ hx => hx ▸ h, fun h => h v rfl⟩

private theorem allPass_seq_checkRoundTripCase (packOpts : PackOptions) (unpackOpts : UnpackOptions)
    (entries : List TarEntry) (next : Unit → AllPassRun Unit)
    (ha : AllPass (checkRoundTripCase defaultApi packOpts unpackOpts entries))
    (hb : AllPass (next ())) :
    AllPass (Bind.bind (checkRoundTripCase defaultApi packOpts unpackOpts entries) next) := by
  have hiff : ∀ api po uo es (n : Unit → AllPassRun Unit),
      AllPass (Bind.bind (checkRoundTripCase api po uo es) n) ↔
      AllPass (checkRoundTripCase api po uo es) ∧ AllPass (n ()) := by
    intro api po uo es n
    unfold checkRoundTripCase
    cases api.packWith po es with
    | error _ => simp [AllPass, Bind.bind, NondetTest.assert]
    | ok bytes =>
      dsimp only
      cases api.unpackWith uo bytes with
      | error _ => simp [AllPass, Bind.bind, NondetTest.assert]
      | ok decoded => simp [AllPass, Bind.bind, NondetTest.assert]
  exact (hiff _ _ _ _ _).mpr ⟨ha, hb⟩

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
    | cons _ _ =>
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

private theorem checkRoundTripCase_test1_empty_ex :
    ∃ emptyBytes : ByteArray,
      defaultApi.pack [] = .ok emptyBytes ∧
      emptyBytes.size = 1024 ∧
      defaultApi.unpackWith { maxEntries := 0, maxTotalBytes := 0 } emptyBytes = .ok [] := by
  have hv : ValidArchive false false [] := by
    unfold ValidArchive; decide
  have ⟨bytes, hpack_go⟩ := (packWith_go_spec {} [] [] ByteArray.empty).2 hv
  have hbytes_eq := ((packWith_go_spec {} [] [] ByteArray.empty).1 bytes hpack_go).2
  have hpack : defaultApi.pack [] = .ok bytes := by
    rw [defaultApi_pack_eq]
    unfold Impl.packWith
    exact hpack_go
  have hbytes_form : bytes = zeroBlock ++ zeroBlock := by
    simpa [ByteArray.empty_append] using hbytes_eq
  subst hbytes_form
  have hsz : (zeroBlock ++ zeroBlock).size = 1024 := by
    rw [ByteArray.size_append, zeroBlock_size]
  have hnz : ((zeroBlock ++ zeroBlock).size == 0 || (zeroBlock ++ zeroBlock).size % 512 != 0) = false := by
    rw [hsz]; rfl
  have hz1 : isZeroRange (zeroBlock ++ zeroBlock) 0 512 = true := by
    refine (isZeroRange_eq_true_iff (zeroBlock ++ zeroBlock) 0 512 (by decide)).mpr ⟨by rw [hsz]; omega, ?_⟩
    intro i hi _
    have hlt1 : 0 + i < zeroBlock.size := by rw [zeroBlock_size]; omega
    have hlt2 : 0 + i < (zeroBlock ++ zeroBlock).size := by rw [ByteArray.size_append, zeroBlock_size]; omega
    rw [getElem_append_left hlt1 hlt2]
    exact zeroBlock_getElem _
  have hz2 : isZeroRange (zeroBlock ++ zeroBlock) 512 512 = true := by
    refine (isZeroRange_eq_true_iff (zeroBlock ++ zeroBlock) 512 512 (by decide)).mpr ⟨by rw [hsz]; omega, ?_⟩
    intro i hi _
    have hr : zeroBlock.size ≤ 512 + i := by rw [zeroBlock_size]; omega
    rw [getElem_append_right hr]
    exact zeroBlock_getElem _
  have htr : allZeroTrailer (zeroBlock ++ zeroBlock) 1024 = true := by
    refine allZeroTrailer_of_zeros (bytes := zeroBlock ++ zeroBlock) (offset := 1024) (by rw [hsz]) ?_
    intro k hk hle
    exact False.elim (by omega)
  have hunpack : defaultApi.unpackWith { maxEntries := 0, maxTotalBytes := 0 } (zeroBlock ++ zeroBlock) = .ok [] := by
    rw [defaultApi_unpackWith_eq]
    unfold Impl.unpackWith
    simp only [hnz, Bool.false_eq_true, ↓reduceIte]
    refine unpackLoop_step_done _ _ 0 none [] [] 0 [] (by rw [hsz]; omega) ?_
    unfold unpackStep
    have hnotge : ¬0 ≥ (zeroBlock ++ zeroBlock).size := by rw [hsz]; omega
    have hnotge2 : ¬0 + 512 ≥ (zeroBlock ++ zeroBlock).size := by rw [hsz]; omega
    simp only [hnotge, hnotge2, ↓reduceIte, hz1, Option.isSome_none, Bool.false_eq_true, hz2,
      Bool.not_true, htr]
    rfl
  exact ⟨zeroBlock ++ zeroBlock, hpack, hsz, hunpack⟩

private theorem string_ofList_replicate_isEmpty_false (n : Nat) (hn : 0 < n) (c : Char) :
    (String.ofList (List.replicate n c)).isEmpty = false := by
  have h1 : (String.ofList (List.replicate n c)).length = n := by
    simp only [String.length_ofList, List.length_replicate]
  cases h : (String.ofList (List.replicate n c)).isEmpty
  · rfl
  · have he := String.isEmpty_iff.mp h
    rw [he] at h1
    have h0 : ("" : String).length = 0 := rfl
    omega

private theorem validEntryBool_reg_p (p norm : String)
    (mode : UInt32) (uid gid mtime : Nat) (uname gname : String) (data : ByteArray)
    (hval : validateEntryPath false false .regular p = .ok norm)
    (hu : (!hasNulString uname) = true) (hg : (!hasNulString gname) = true)
    (huid : uid < u64Limit) (hgid : gid < u64Limit) (hmtime : mtime < u64Limit)
    (hsz : data.size < u64Limit) :
    validEntryBool false false
      { path := p, kind := .regular, mode := mode, uid := uid, gid := gid,
        mtime := mtime, uname := uname, gname := gname, data := data } = true := by
  simp only [validEntryBool, hval, hu, hg, huid, hgid, hmtime, hsz,
    decide_true, Bool.and_true, beq_self_eq_true]

private theorem validEntryBool_sym_lnk (lnk : String)
    (hsym : validateSymlinkTarget false false "sub/link" lnk = .ok ()) :
    validEntryBool false false { path := "sub/link", kind := .symlink, mode := 0o777, linkTarget := lnk } = true := by
  have hval : validateEntryPath false false .symlink "sub/link" = .ok "sub/link" := rfl
  have h0 : (0 : Nat) < u64Limit := by decide
  have hnu : (!hasNulString "") = true := by decide
  have hsz : (ByteArray.empty).size = 0 := rfl
  simp only [validEntryBool, hval, hsym, h0, hnu, hsz, decide_true,
    Bool.and_true, beq_self_eq_true]

private theorem noDupNormalizedPathsBool_singleton (e : TarEntry) (p : String)
    (hnp : normalizeTarPath e.kind e.path = p) :
    noDupNormalizedPathsBool [e] = true := by
  simp only [noDupNormalizedPathsBool, noDupNormalizedPathsBool.go.eq_2,
    noDupNormalizedPathsBool.go.eq_1, hnp, List.contains, List.elem]
  rfl

private theorem noDupNormalizedPathsBool_four (e1 e2 e3 e4 : TarEntry) (p1 p2 p3 p4 : String)
    (h1 : normalizeTarPath e1.kind e1.path = p1)
    (h2 : normalizeTarPath e2.kind e2.path = p2)
    (h3 : normalizeTarPath e3.kind e3.path = p3)
    (h4 : normalizeTarPath e4.kind e4.path = p4)
    (h21 : (p2 == p1) = false)
    (h32 : (p3 == p2) = false) (h31 : (p3 == p1) = false)
    (h43 : (p4 == p3) = false) (h42 : (p4 == p2) = false) (h41 : (p4 == p1) = false) :
    noDupNormalizedPathsBool [e1, e2, e3, e4] = true := by
  simp only [noDupNormalizedPathsBool, noDupNormalizedPathsBool.go.eq_2,
    noDupNormalizedPathsBool.go.eq_1, h1, h2, h3, h4, List.contains, List.elem,
    h21, h32, h31, h43, h42, h41]
  rfl

private theorem validArchive_singleton_of (allowAbs allowParent : Bool) (e : TarEntry)
    (he : validEntryBool allowAbs allowParent e = true)
    (hnp : noDupNormalizedPathsBool [e] = true) :
    ValidArchive allowAbs allowParent [e] := by
  unfold ValidArchive validArchiveBool
  simp only [List.all_cons, List.all_nil, Bool.and_true, he, hnp]

private theorem validArchive_four_of (allowAbs allowParent : Bool) (e1 e2 e3 e4 : TarEntry)
    (he1 : validEntryBool allowAbs allowParent e1 = true)
    (he2 : validEntryBool allowAbs allowParent e2 = true)
    (he3 : validEntryBool allowAbs allowParent e3 = true)
    (he4 : validEntryBool allowAbs allowParent e4 = true)
    (hnd : noDupNormalizedPathsBool [e1, e2, e3, e4] = true) :
    ValidArchive allowAbs allowParent [e1, e2, e3, e4] := by
  unfold ValidArchive validArchiveBool
  simp only [List.all_cons, List.all_nil, Bool.and_true, he1, he2, he3, he4, hnd]

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
    have hhi : ("hi".toUTF8).size < u64Limit := by
      rw [toUTF8_eq_toByteArray, List.size_toByteArray]; decide
    have h0 : (0 : Nat) < u64Limit := by decide
    have hnu : (!hasNulString "") = true := by decide
    have hve := validEntryBool_reg_p _ _ 0o644 0 0 0 "" "" "hi".toUTF8 hval hnu hnu h0 h0 h0 hhi
    exact validArchive_singleton_of false false _ hve (noDupNormalizedPathsBool_singleton _ _ hnp)
  have hfind : (findUstarSplit
      (String.ofList (List.replicate 60 'd') ++ "/" ++ String.ofList (List.replicate 60 'f'))).isSome = true := by
    unfold findUstarSplit
    have hlist : (String.ofList (List.replicate 60 'd') ++ "/" ++ String.ofList (List.replicate 60 'f')).toList =
        List.replicate 60 'd' ++ ('/' :: List.replicate 60 'f') := by
      rw [String.toList_append, String.toList_append, String.toList_ofList, String.toList_ofList,
        List.append_assoc]
      rfl
    have hno : (List.replicate 60 'd').all (fun c => c != '/') = true := by
      rw [list_all_replicate]; decide
    rw [hlist, findUstarSplit_go_noSlash [] (List.replicate 60 'd') ('/' :: List.replicate 60 'f') hno,
      List.append_nil, List.reverse_replicate, findUstarSplit.go.eq_2, List.reverse_replicate,
      toUTF8_size_ofList_replicate 60 (by decide), toUTF8_size_ofList_replicate 60 (by decide)]
    have he1 := string_ofList_replicate_isEmpty_false 60 (by decide) 'd'
    have he2 := string_ofList_replicate_isEmpty_false 60 (by decide) 'f'
    rw [he1, he2, ite_eq_left (by decide)]
    rfl
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
    have hpay : ("payload".toUTF8).size < u64Limit := by
      rw [toUTF8_eq_toByteArray, List.size_toByteArray]; decide
    have hn1 : (!hasNulString "üser") = true := by decide
    have hn2 : (!hasNulString "grøup") = true := by decide
    have hlt1 : ustarOctal7Limit + 7 < u64Limit := by decide
    have hlt2 : ustarOctal7Limit + 9 < u64Limit := by decide
    have hlt3 : ustarOctal11Limit + 42 < u64Limit := by decide
    have he_nul : (!hasNulString "") = true := by decide
    have h0_lt : (0 : Nat) < u64Limit := by decide
    have hb_sz : (ByteArray.empty).size < u64Limit := h0_lt
    have hve1 := validEntryBool_reg_p _ _ 0o100755 (ustarOctal7Limit + 7) (ustarOctal7Limit + 9)
      (ustarOctal11Limit + 42) "üser" "grøup" "payload".toUTF8 hval_e1 hn1 hn2 hlt1 hlt2 hlt3 hpay
    have hve2 : validEntryBool false false { path := "sub/", kind := .directory, mode := 0o755 } = true := by
      simp only [validEntryBool, hval_e2]
      decide
    have hve3 := validEntryBool_sym_lnk _ hsym_e3
    have hve4 := validEntryBool_reg_p _ _ 0o644 0 0 0 "" "" ByteArray.empty hval_e4
      he_nul he_nul h0_lt h0_lt h0_lt hb_sz
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
    exact validArchive_four_of false false _ _ _ _ hve1 hve2 hve3 hve4
      (noDupNormalizedPathsBool_four _ _ _ _ _ _ _ _ hnp1 hnp2 hnp3 hnp4 h21 h32 h31 h43 h42 h41)
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
  have ⟨splitBytes, hpack_split_go⟩ :=
    (packWith_go_spec {} [splitEntry] [] ByteArray.empty).2 hv_split_pack
  have hsplit_eq :=
    ((packWith_go_spec {} [splitEntry] [] ByteArray.empty).1 splitBytes hpack_split_go).2
  have hpack_split : defaultApi.pack [splitEntry] = .ok splitBytes := by
    rw [defaultApi_pack_eq]
    unfold Impl.packWith
    exact hpack_split_go
  have hsplit_form : splitBytes = encodeEntryBlocks splitEntry splitPath ++ (zeroBlock ++ zeroBlock) := by
    rw [hsplit_eq, ByteArray.empty_append]
    simp only [List.foldl_cons, List.foldl_nil, ByteArray.empty_append,
      Bool.false_eq_true, ↓reduceIte, hnp_split]
  have hblk_sz : (encodeEntryBlocks splitEntry splitPath).size = 1024 := by
    rw [encodeEntryBlocks_noPax_size splitEntry splitPath hneeds_split]
    have hsuf : splitEntry.data.size = 2 := by
      rw [hse]
      rw [toUTF8_eq_toByteArray, List.size_toByteArray]; decide
    rw [hsuf]
    decide
  have hsplit_sz : splitBytes.size = 2048 := by
    rw [hsplit_form, ByteArray.size_append, ByteArray.size_append, zeroBlock_size, hblk_sz]
  have hlen_sp : ([splitEntry] : List TarEntry).length ≤ ({} : UnpackOptions).maxEntries := by
    simp only [List.length_cons, List.length_nil]
    decide
  have hfit_all : ([splitEntry] : List TarEntry).all fitsPaxLimit = true := by
    simpa using hfit_split
  have hrt := allPass_packUnpack_roundTrip [splitEntry] {} {} hv_split rfl rfl hlen_sp htot_split hfit_all
  dsimp only [test_tar_packUnpack_roundTrip, Bind.bind, Pure.pure, NondetTest.assert, AllPass] at hrt
  have hpack_split' : defaultApi.packWith {} [splitEntry] = .ok splitBytes := hpack_split
  rw [hpack_split'] at hrt
  dsimp only at hrt
  cases hu : defaultApi.unpackWith {} splitBytes with
  | error e =>
    rw [hu] at hrt
    dsimp only at hrt
    exact False.elim hrt.1
  | ok decSplit =>
    rw [hu] at hrt
    have hunpack_split : defaultApi.unpack splitBytes = .ok decSplit := by
      rw [defaultApi_unpack_eq]; exact hu
    exact ⟨splitBytes, decSplit, hpack_split, hsplit_sz, hunpack_split, hrt.1⟩

/-- Prove `test_tar_packWith_concreteUstarAndPaxCases_roundTrip` for `defaultApi`. -/
theorem allPass_packWith_concreteUstarAndPaxCases_roundTrip :
    AllPass (test_tar_packWith_concreteUstarAndPaxCases_roundTrip defaultApi) := by
  let splitPath := String.ofList (List.replicate 60 'd') ++ "/" ++ String.ofList (List.replicate 60 'f')
  let splitEntry : TarEntry := { path := splitPath, kind := .regular, data := "hi".toUTF8 }
  have ⟨splitBytes, decSplit, hpack_split, hsplit_sz, hunpack_split, hteq_split⟩ :=
    test1_split_ex splitPath splitEntry rfl rfl
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
  generalize hpb_g : String.ofList (List.replicate 91 'p') = pb_var
  generalize hpl_g : (String.ofList (List.replicate 260 'x') ++ "/café.txt") = pl_var
  refine allPass_seq_checkRoundTripCase _ _ _ _ ?_ ?_
  · exact (test1_e14_roundTrip pb_var pl_var
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
    rw [hpb_g, hpl_g]
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

private theorem allPass_checkPackError_iff (api : TarApi) (opts : PackOptions)
    (es : List TarEntry) (expectedKind : TarErrorKind) :
    AllPass (checkPackError api opts es expectedKind) ↔
    (match api.packWith opts es with
      | .ok _ => False
      | .error err => err.kind = expectedKind ∧ (!err.message.isEmpty) = true) := by
  unfold checkPackError
  cases api.packWith opts es with
  | ok _ => simp [AllPass, NondetTest.assert]
  | error err => simp [AllPass, NondetTest.assert]

private theorem tarErrorKind_eq_of_beq {a b : TarErrorKind} (h : (a == b) = true) : a = b := by
  cases a <;> cases b <;> first | rfl | cases h

private theorem checkPackError_of_eval {opts : PackOptions} {es : List TarEntry}
    {expectedKind : TarErrorKind}
    (h : (match Impl.packWith opts es with
      | .error err => err.kind == expectedKind && !err.message.isEmpty
      | .ok _ => false) = true) :
    AllPass (checkPackError defaultApi opts es expectedKind) := by
  rw [allPass_checkPackError_iff, defaultApi_packWith_eq]
  cases hp : Impl.packWith opts es with
  | ok _ => simp [hp] at h
  | error err =>
    simp only [hp, Bool.and_eq_true] at h
    exact ⟨tarErrorKind_eq_of_beq h.1, h.2⟩

private theorem checkPackError_of_pack_err {opts : PackOptions} {es : List TarEntry}
    {expectedKind : TarErrorKind} {err : TarError}
    (hp : Impl.packWith opts es = .error err)
    (hk : err.kind = expectedKind)
    (hm : (!err.message.isEmpty) = true) :
    AllPass (checkPackError defaultApi opts es expectedKind) := by
  rw [allPass_checkPackError_iff, defaultApi_packWith_eq, hp]
  exact ⟨hk, hm⟩

private theorem allPass_seq_checkPackError (opts : PackOptions) (es : List TarEntry)
    (expectedKind : TarErrorKind) (next : AllPassRun Unit)
    (ha : AllPass (checkPackError defaultApi opts es expectedKind))
    (hb : AllPass next) :
    AllPass (Bind.bind (checkPackError defaultApi opts es expectedKind) (fun _ => next)) := by
  have hiff : ∀ api opts es ek n,
      AllPass (Bind.bind (checkPackError api opts es ek) (fun _ => n)) ↔
      AllPass (checkPackError api opts es ek) ∧ AllPass n := by
    intro api opts es ek n
    unfold checkPackError
    generalize api.packWith opts es = p
    cases p with
    | ok _ => simp [AllPass, Bind.bind, NondetTest.assert]
    | error err => simp [AllPass, Bind.bind, NondetTest.assert, and_assoc]
  exact (hiff _ _ _ _ _).mpr ⟨ha, hb⟩

private theorem checkPackError_test2_dup :
    AllPass (checkPackError defaultApi {}
      [{ path := "sub/", kind := .directory }, { path := "sub", kind := .regular }]
      .duplicatePath) := by
  rw [allPass_checkPackError_iff, defaultApi_packWith_eq]
  have hp : Impl.packWith {}
      [{ path := "sub/", kind := .directory }, { path := "sub", kind := .regular }] =
      .error { kind := .duplicatePath, message := "duplicate tar entry path: sub", entryPath := some "sub" } := by
    unfold Impl.packWith
    rw [Impl.packWith.go.eq_2]
    have hv1 : validateEntryPath false false .directory "sub/" = .ok "sub" := rfl
    have hm1 : (({ path := "sub/", kind := .directory } : TarEntry).kind != .regular &&
        ({ path := "sub/", kind := .directory } : TarEntry).data.size != 0) = false := rfl
    have hl1 : (({ path := "sub/", kind := .directory } : TarEntry).kind != .symlink &&
        ({ path := "sub/", kind := .directory } : TarEntry).linkTarget != "") = false := rfl
    have hn1 : (hasNulString "" || hasNulString "") = false := by decide
    have hu1 : ((0 : Nat) ≥ u64Limit || (0 : Nat) ≥ u64Limit || (0 : Nat) ≥ u64Limit ||
        (ByteArray.empty).size ≥ u64Limit) = false := by decide
    have hval1 : validatePackEntry {} { path := "sub/", kind := .directory } = .ok "sub" := by
      unfold validatePackEntry
      simp only [hv1, hm1, hl1, hn1, hu1, Bool.false_eq_true, ↓reduceIte]
      rfl
    have hs1 : ([].contains "sub") = false := rfl
    simp only [hval1, hs1, Bool.false_eq_true, ↓reduceIte]
    rw [Impl.packWith.go.eq_2]
    have hv2 : validateEntryPath false false .regular "sub" = .ok "sub" := rfl
    have hm2 : (({ path := "sub", kind := .regular } : TarEntry).kind != .regular &&
        ({ path := "sub", kind := .regular } : TarEntry).data.size != 0) = false := rfl
    have hl2 : (({ path := "sub", kind := .regular } : TarEntry).kind != .symlink &&
        ({ path := "sub", kind := .regular } : TarEntry).linkTarget != "") = false := rfl
    have hval2 : validatePackEntry {} { path := "sub", kind := .regular } = .ok "sub" := by
      unfold validatePackEntry
      simp only [hv2, hm2, hl2, hn1, hu1, Bool.false_eq_true, ↓reduceIte]
      rfl
    have hs2 : (["sub"].contains "sub") = true := rfl
    simp only [hval2, hs2, ↓reduceIte]
    rfl
  rw [hp]
  exact ⟨rfl, rfl⟩

private theorem checkPackError_test3_dir_data :
    AllPass (checkPackError defaultApi {} [{ path := "d", kind := .directory, data := "x".toUTF8 }]
      .invalidHeader) := by
  have hx : ("x".toUTF8).size = 1 := by
    rw [toUTF8_eq_toByteArray, List.size_toByteArray]; decide
  have hp : Impl.packWith {} [{ path := "d", kind := .directory, data := "x".toUTF8 }] =
      .error { kind := .invalidHeader, message := "non-regular tar entry cannot have payload data", entryPath := some "d" } := by
    unfold Impl.packWith
    rw [Impl.packWith.go.eq_2]
    have hv : validateEntryPath false false .directory "d" = .ok "d" := rfl
    have hc : (EntryKind.directory != EntryKind.regular && 1 != 0) = true := rfl
    have hval : validatePackEntry {} { path := "d", kind := .directory, data := "x".toUTF8 } =
        .error { kind := .invalidHeader, message := "non-regular tar entry cannot have payload data", entryPath := some "d" } := by
      unfold validatePackEntry
      simp only [hv, hx, hc, ↓reduceIte]
      rfl
    rw [hval]
  exact checkPackError_of_pack_err hp rfl rfl

private theorem checkPackError_test3_sym_data :
    AllPass (checkPackError defaultApi {}
      [{ path := "s", kind := .symlink, data := "x".toUTF8, linkTarget := "t" }]
      .invalidHeader) := by
  have hx : ("x".toUTF8).size = 1 := by
    rw [toUTF8_eq_toByteArray, List.size_toByteArray]; decide
  have hp : Impl.packWith {}
      [{ path := "s", kind := .symlink, data := "x".toUTF8, linkTarget := "t" }] =
      .error { kind := .invalidHeader, message := "non-regular tar entry cannot have payload data", entryPath := some "s" } := by
    unfold Impl.packWith
    rw [Impl.packWith.go.eq_2]
    have hv : validateEntryPath false false .symlink "s" = .ok "s" := rfl
    have hs : validateSymlinkTarget false false "s" "t" = .ok () := rfl
    have hc : (EntryKind.symlink != EntryKind.regular && 1 != 0) = true := rfl
    have hval : validatePackEntry {} { path := "s", kind := .symlink, data := "x".toUTF8, linkTarget := "t" } =
        .error { kind := .invalidHeader, message := "non-regular tar entry cannot have payload data", entryPath := some "s" } := by
      unfold validatePackEntry
      simp only [hv, hx, hc, ↓reduceIte]
      dsimp only [Bind.bind, Except.bind]
      rw [hs]
      rfl
    rw [hval]
  exact checkPackError_of_pack_err hp rfl rfl

/-- Prove `test_tar_packWith_invalidAndUnsafePaths_rejected` for `defaultApi`. -/
theorem allPass_packWith_invalidAndUnsafePaths_rejected :
    AllPass (test_tar_packWith_invalidAndUnsafePaths_rejected defaultApi) := by
  have hv_rt : ValidArchive true true
      [{ path := "/../a", kind := .regular }, { path := "/sub/", kind := .directory }] := by
    unfold ValidArchive; decide
  have hfit_rt : ([{ path := "/../a", kind := .regular }, { path := "/sub/", kind := .directory }].all
      fitsPaxLimit) = true := by
    simp only [List.all_cons, List.all_nil, Bool.and_true, fitsPaxLimit, needsPax, pathFitsUstar,
      isAsciiString, toUTF8_eq_toByteArray, toByteArray_toList, List.size_toByteArray]
    decide
  have hrt := checkRoundTripCase_of_valid
    (packOpts := { allowAbsolute := true, allowParentTraversal := true })
    (unpackOpts := { allowAbsolute := true, allowParentTraversal := true })
    hv_rt rfl rfl (by decide) (by decide) hfit_rt
  unfold test_tar_packWith_invalidAndUnsafePaths_rejected
  refine allPass_seq_checkPackError _ _ _ _ (checkPackError_of_eval (by decide)) ?_
  refine allPass_seq_checkPackError _ _ _ _ (checkPackError_of_eval (by decide)) ?_
  refine allPass_seq_checkPackError _ _ _ _ (checkPackError_of_eval (by decide)) ?_
  refine allPass_seq_checkPackError _ _ _ _ (checkPackError_of_eval (by decide)) ?_
  refine allPass_seq_checkPackError _ _ _ _ (checkPackError_of_eval (by decide)) ?_
  refine allPass_seq_checkPackError _ _ _ _ (checkPackError_of_eval (by decide)) ?_
  refine allPass_seq_checkPackError _ _ _ _ (checkPackError_of_eval (by decide)) ?_
  refine allPass_seq_checkPackError _ _ _ _ (checkPackError_of_eval (by decide)) ?_
  refine allPass_seq_checkPackError _ _ _ _ (checkPackError_of_eval (by decide)) ?_
  refine allPass_seq_checkPackError _ _ _ _ (checkPackError_of_eval (by decide)) ?_
  refine allPass_seq_checkPackError _ _ _ _ (checkPackError_of_eval (by decide)) ?_
  refine allPass_seq_checkPackError _ _ _ _ (checkPackError_of_eval (by decide)) ?_
  refine allPass_seq_checkPackError _ _ _ _ (checkPackError_of_eval (by decide)) ?_
  refine allPass_seq_checkPackError _ _ _ _ (checkPackError_of_eval (by decide)) ?_
  refine allPass_seq_checkRoundTripCase _ _ _ _ hrt ?_
  refine allPass_seq_checkPackError _ _ _ _ checkPackError_test2_dup ?_
  exact checkPackError_of_eval (by decide)

/-- Prove `test_tar_packWith_symlinkAndEntryInvariants_rejected` for `defaultApi`. -/
theorem allPass_packWith_symlinkAndEntryInvariants_rejected :
    AllPass (test_tar_packWith_symlinkAndEntryInvariants_rejected defaultApi) := by
  have hv_rt : ValidArchive false false
      [{ path := "sub/ok1", kind := .symlink, linkTarget := "../target" },
       { path := "sub/ok2", kind := .symlink, linkTarget := "x/../../y" }] := by
    unfold ValidArchive; decide
  have hfit_rt : ([{ path := "sub/ok1", kind := .symlink, linkTarget := "../target" },
      { path := "sub/ok2", kind := .symlink, linkTarget := "x/../../y" }].all fitsPaxLimit) = true := by
    simp only [List.all_cons, List.all_nil, Bool.and_true, fitsPaxLimit, needsPax, pathFitsUstar,
      isAsciiString, toUTF8_eq_toByteArray, toByteArray_toList, List.size_toByteArray]
    decide
  have hrt := checkRoundTripCase_of_valid (packOpts := {}) (unpackOpts := {})
    hv_rt rfl rfl (by decide) (by decide) hfit_rt
  unfold test_tar_packWith_symlinkAndEntryInvariants_rejected
  refine allPass_seq_checkPackError _ _ _ _ (checkPackError_of_eval (by decide)) ?_
  refine allPass_seq_checkPackError _ _ _ _ (checkPackError_of_eval (by decide)) ?_
  refine allPass_seq_checkPackError _ _ _ _ (checkPackError_of_eval (by decide)) ?_
  refine allPass_seq_checkPackError _ _ _ _ (checkPackError_of_eval (by decide)) ?_
  refine allPass_seq_checkPackError _ _ _ _ (checkPackError_of_eval (by decide)) ?_
  refine allPass_seq_checkPackError _ _ _ _ (checkPackError_of_eval (by decide)) ?_
  refine allPass_seq_checkRoundTripCase _ _ _ _ hrt ?_
  refine allPass_seq_checkPackError _ _ _ _ checkPackError_test3_dir_data ?_
  refine allPass_seq_checkPackError _ _ _ _ checkPackError_test3_sym_data ?_
  refine allPass_seq_checkPackError _ _ _ _ (checkPackError_of_eval (by decide)) ?_
  refine allPass_seq_checkPackError _ _ _ _ (checkPackError_of_eval (by decide)) ?_
  refine allPass_seq_checkPackError _ _ _ _ (checkPackError_of_eval (by decide)) ?_
  refine allPass_seq_checkPackError _ _ _ _ (checkPackError_of_eval (by decide)) ?_
  refine allPass_seq_checkPackError _ _ _ _ (checkPackError_of_eval (by decide)) ?_
  refine allPass_seq_checkPackError _ _ _ _ (checkPackError_of_eval (by decide)) ?_
  exact checkPackError_of_eval (by decide)

end LeanSwe.Tar.Proofs
