import LeanSwe.Tar.SpecTests
import LeanSwe.Tar.Interface
import LeanSwe.Tar.Proofs.ByteModel
import LeanSwe.Tar.Proofs.FieldCodecs
import LeanSwe.Tar.Proofs.HeaderLayout
import LeanSwe.Tar.Proofs.PackValid
import LeanSwe.Tar.Proofs.UnpackValid
import LeanSwe.Tar.Proofs.RoundTrip

namespace LeanSwe.Tar.Proofs

open Core
open Core.NondetTest
open LeanSwe.Tar
open LeanSwe.Tar.Model
open LeanSwe.Tar.Impl

private theorem defaultApi_packWith_eq (o : PackOptions) (es : List TarEntry) : defaultApi.packWith o es = Impl.packWith o es := rfl

private theorem allPass_have {α : Type _} (v : α) (f : α → AllPassRun Unit) :
    AllPass (have x := v; f x) ↔ ∀ x, x = v → AllPass (f x) :=
  ⟨fun h _ hx => hx ▸ h, fun h => h v rfl⟩

private theorem allPass_seq_checkRoundTripCase (packOpts : PackOptions) (unpackOpts : UnpackOptions)
    (entries : List TarEntry) (next : Unit → AllPassRun Unit)
    (ha : AllPass (checkRoundTripCase defaultApi packOpts unpackOpts entries)) (hb : AllPass (next ())) :
    AllPass (Bind.bind (checkRoundTripCase defaultApi packOpts unpackOpts entries) next) := by
  unfold checkRoundTripCase at ha ⊢
  cases hp : defaultApi.packWith packOpts entries <;> rw [hp] at ha
  · exact ha.1.elim
  · dsimp only at ha ⊢
    cases hu : defaultApi.unpackWith unpackOpts _ <;> rw [hu] at ha <;> simp_all [AllPass, Bind.bind, NondetTest.assert]

private theorem allPass_checkPackError_iff (api : TarApi) (opts : PackOptions)
    (es : List TarEntry) (expectedKind : TarErrorKind) :
    AllPass (checkPackError api opts es expectedKind) ↔
    (match api.packWith opts es with
      | .ok _ => False | .error err => err.kind = expectedKind ∧ (!err.message.isEmpty) = true) := by
  unfold checkPackError; cases api.packWith opts es <;> simp [AllPass, NondetTest.assert]

private theorem tarErrorKind_eq_of_beq {a b : TarErrorKind} (h : (a == b) = true) : a = b := by
  cases a <;> cases b <;> first | rfl | cases h

private theorem checkPackError_of_eval {opts : PackOptions} {es : List TarEntry} {expectedKind : TarErrorKind}
    (h : (match Impl.packWith opts es with
      | .error err => err.kind == expectedKind && !err.message.isEmpty | .ok _ => false) = true) :
    AllPass (checkPackError defaultApi opts es expectedKind) := by
  rw [allPass_checkPackError_iff, defaultApi_packWith_eq]
  cases hp : Impl.packWith opts es with
  | ok _ => simp [hp] at h
  | error err => simp only [hp, Bool.and_eq_true] at h; exact ⟨tarErrorKind_eq_of_beq h.1, h.2⟩

private theorem allPass_seq_checkPackError (opts : PackOptions) (es : List TarEntry)
    (expectedKind : TarErrorKind) (next : AllPassRun Unit)
    (ha : AllPass (checkPackError defaultApi opts es expectedKind)) (hb : AllPass next) :
    AllPass (Bind.bind (checkPackError defaultApi opts es expectedKind) (fun _ => next)) := by
  unfold checkPackError at ha ⊢
  cases hp : defaultApi.packWith opts es <;> rw [hp] at ha <;> simp_all [AllPass, Bind.bind, NondetTest.assert]

private theorem list_all_replicate {α : Type} (n : Nat) (a : α) (p : α → Bool) :
    (List.replicate n a).all p = if n == 0 then true else p a := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [List.replicate_succ, List.all_cons, ih]; cases n <;> simp

private theorem hasNulChars_replicate (n : Nat) {c : Char} (hc : c ≠ Char.ofNat 0) :
    hasNulChars (List.replicate n c) = false := by
  induction n with
  | zero => rfl
  | succ n ih => rw [List.replicate_succ]; change (c == Char.ofNat 0 || hasNulChars _) = false; simp [hc, ih]

private theorem splitSlashChars_go_noSlash (acc a rest : List Char) (hno : a.all (fun c => c != '/') = true) :
    splitSlashChars.go acc (a ++ rest) = splitSlashChars.go (a.reverse ++ acc) rest := by
  induction a generalizing acc with
  | nil => simp
  | cons c _ ih =>
    simp only [List.all_cons, Bool.and_eq_true, bne_iff_ne] at hno
    rw [List.cons_append, splitSlashChars.go.eq_3 _ c _ hno.1, ih (c :: acc) hno.2, List.reverse_cons, List.append_assoc, List.singleton_append]

private theorem findUstarSplit_go_noSlash (revPfx a rest : List Char) (hno : a.all (fun c => c != '/') = true) :
    findUstarSplit.go revPfx (a ++ rest) = findUstarSplit.go (a.reverse ++ revPfx) rest := by
  induction a generalizing revPfx with
  | nil => simp
  | cons c _ ih =>
    simp only [List.all_cons, Bool.and_eq_true, bne_iff_ne] at hno
    rw [List.cons_append, findUstarSplit.go.eq_3 _ c _ hno.1, ih (c :: revPfx) hno.2, List.reverse_cons, List.append_assoc, List.singleton_append]

private theorem flatMap_utf8EncodeChar_replicate (n : Nat) {c : Char} (hc : c.toNat < 128) :
    ((List.replicate n c).flatMap String.utf8EncodeChar).length = n ∧
    ((List.replicate n c).flatMap String.utf8EncodeChar).all (fun b => decide (b < 128)) = true := by
  have hcle : c.toNat ≤ 127 := by omega
  have hlt : UInt8.ofNat c.toNat < 128 := by change c.toNat % 2 ^ 8 < 128; omega
  have hlen1 : (String.utf8EncodeChar c).length = 1 := by unfold String.utf8EncodeChar; simp [hcle]
  have hall1 : (String.utf8EncodeChar c).all (fun b => decide (b < 128)) = true := by unfold String.utf8EncodeChar; simp [hcle, hlt]
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.replicate_succ, List.flatMap_cons, List.length_append, List.all_append, hlen1, hall1, ih.1, ih.2, Bool.and_self]
    exact ⟨Nat.add_comm 1 n, rfl⟩

private theorem toUTF8_size_rep (n : Nat) {c : Char} (hc : c.toNat < 128) :
    (String.ofList (List.replicate n c)).toUTF8.size = n := by
  rw [toUTF8_eq_toByteArray]; change (List.flatMap String.utf8EncodeChar (String.ofList (List.replicate n c)).toList).toByteArray.size = n
  rw [List.size_toByteArray, String.toList_ofList]; exact (flatMap_utf8EncodeChar_replicate n hc).1

private theorem isAsciiString_append (a b : String) : isAsciiString (a ++ b) = (isAsciiString a && isAsciiString b) := by
  simp only [isAsciiString, toUTF8_toList, String.toList_append, List.flatMap_append, List.all_append]

private theorem isAsciiString_rep (n : Nat) {c : Char} (hc : c.toNat < 128) :
    isAsciiString (String.ofList (List.replicate n c)) = true := by
  simp only [isAsciiString, toUTF8_toList, String.toList_ofList]; exact (flatMap_utf8EncodeChar_replicate n hc).2

private theorem encodePaxRecord_size_of_kv (key value : String) :
    (encodePaxRecord key value).size =
      (toString (paxRecordTotalLen (1 + key.toUTF8.size + 1 + value.toUTF8.size + 1))).toUTF8.size +
        (1 + key.toUTF8.size + 1 + value.toUTF8.size + 1) := by
  unfold encodePaxRecord; dsimp only
  have hsuf : (" " ++ key ++ "=" ++ value ++ "\n").toUTF8.size = 1 + key.toUTF8.size + 1 + value.toUTF8.size + 1 := by
    simp only [toUTF8_size_append]
    have h1 : (" ").toUTF8.size = 1 := by rw [toUTF8_eq_toByteArray, List.size_toByteArray]; decide
    have h2 : ("=").toUTF8.size = 1 := by rw [toUTF8_eq_toByteArray, List.size_toByteArray]; decide
    have h3 : ("\n").toUTF8.size = 1 := by rw [toUTF8_eq_toByteArray, List.size_toByteArray]; decide
    rw [h1, h2, h3]
  rw [hsuf, toUTF8_size_append, hsuf]

private theorem replicate_ne_dots (n : Nat) (hn : n > 0) {c : Char} (hcdot : c ≠ '.') :
    (List.replicate n c == ['.']) = false ∧ (List.replicate n c == ['.', '.']) = false := by
  cases n with
  | zero => omega
  | succ _ =>
    rw [List.replicate_succ]
    exact ⟨beq_false_of_ne fun h => hcdot (Option.some.inj (congrArg List.head? h)),
      beq_false_of_ne fun h => hcdot (Option.some.inj (congrArg List.head? h))⟩

private theorem checkSegments_rep (n : Nat) (hn : n > 0) {c : Char} (hcsl : c ≠ '/') (hcdot : c ≠ '.') :
    checkSegments false (splitSlashChars (List.replicate n c)) = .ok () := by
  have hno : (List.replicate n c).all (fun x => x != '/') = true := by
    rw [list_all_replicate]; cases n with | zero => omega | succ _ => simp [hcsl]
  have ⟨hd1, hd2⟩ := replicate_ne_dots n hn hcdot
  cases n with
  | zero => omega
  | succ m =>
    have hsp : splitSlashChars (List.replicate (m + 1) c) = [List.replicate (m + 1) c] := by
      rw [List.replicate_succ]; unfold splitSlashChars; dsimp only
      rw [← List.replicate_succ, ← List.append_nil (List.replicate (m + 1) c),
        splitSlashChars_go_noSlash [] _ [] hno, List.append_nil, List.reverse_replicate,
        splitSlashChars.go.eq_1, List.reverse_replicate, List.append_nil]
    rw [hsp]; unfold checkSegments checkSegments.go
    have hemp : (List.replicate (m + 1) c).isEmpty = false := rfl
    simp only [hemp, hd1, hd2, Bool.false_eq_true, ↓reduceIte]; rfl

private theorem validateEntryPath_rep (n : Nat) (hn : n > 0) {c : Char}
    (hc0 : c ≠ Char.ofNat 0) (hcsl : c ≠ '/') (hcdot : c ≠ '.') :
    validateEntryPath false false .regular (String.ofList (List.replicate n c)) =
      .ok (String.ofList (List.replicate n c)) := by
  unfold validateEntryPath; dsimp only; rw [String.toList_ofList, hasNulChars_replicate n hc0]
  have hcs := checkSegments_rep n hn hcsl hcdot
  cases n with
  | zero => omega
  | succ m =>
    have hhead : ((List.replicate (m + 1) c).head? == some '/') = false := by rw [List.replicate_succ]; simp [hcsl]
    have hlast : ((List.replicate (m + 1) c).reverse.head? == some '/') = false := by rw [List.reverse_replicate]; exact hhead
    have hemp : (List.replicate (m + 1) c).isEmpty = false := rfl
    simp only [hemp, hhead, hlast, Bool.false_eq_true, ↓reduceIte, Bool.false_and]
    rw [List.replicate_succ]; split
    · rename_i h; split at h
      · rename_i hm; injection hm with hhd; exact absurd hhd hcsl
      · rw [← List.replicate_succ, hcs] at h; cases h
    · rfl

private theorem validateEntryPath_rep_slash (n : Nat) (hn : n > 0) {c : Char}
    (hc0 : c ≠ Char.ofNat 0) (hcsl : c ≠ '/') (hcdot : c ≠ '.') (tail : String)
    (htne : tail.toList ≠ []) (ht0 : hasNulChars tail.toList = false)
    (htlast : (tail.toList.reverse.head? == some '/') = false)
    (htseg : checkSegments false (splitSlashChars tail.toList) = .ok ()) :
    validateEntryPath false false .regular (String.ofList (List.replicate n c) ++ "/" ++ tail) =
      .ok (String.ofList (List.replicate n c) ++ "/" ++ tail) := by
  unfold validateEntryPath; dsimp only
  have hlist : (String.ofList (List.replicate n c) ++ "/" ++ tail).toList =
      List.replicate n c ++ ('/' :: tail.toList) := by simp [String.toList_append, String.toList_ofList]
  rw [hlist, hasNulChars_append, hasNulChars_replicate n hc0]
  have hnul_s : hasNulChars ('/' :: tail.toList) = false := by change ('/' == Char.ofNat 0 || _) = false; simp [ht0]
  have hlast : ((List.replicate n c ++ ('/' :: tail.toList)).reverse.head? == some '/') = false := by
    rw [List.reverse_append, List.reverse_cons]
    cases htr : tail.toList.reverse with
    | nil => exact absurd (List.reverse_eq_nil_iff.mp htr) htne
    | cons _ _ => rw [htr] at htlast; simpa using htlast
  have hno : (List.replicate n c).all (fun x => x != '/') = true := by
    rw [list_all_replicate]; cases n with | zero => omega | succ _ => simp [hcsl]
  have ⟨hd1, hd2⟩ := replicate_ne_dots n hn hcdot
  cases n with
  | zero => omega
  | succ m =>
    have hsp : splitSlashChars (List.replicate (m + 1) c ++ ('/' :: tail.toList)) =
        List.replicate (m + 1) c :: splitSlashChars tail.toList := by
      rw [List.replicate_succ, List.cons_append]; unfold splitSlashChars; dsimp only
      rw [← List.cons_append, ← List.replicate_succ, splitSlashChars_go_noSlash [] _ _ hno,
        List.append_nil, List.reverse_replicate, splitSlashChars.go.eq_2, List.reverse_replicate]
      cases ht : tail.toList <;> first | rfl | exact absurd ht htne
    have hhead : ((List.replicate (m + 1) c ++ ('/' :: tail.toList)).head? == some '/') = false := by
      rw [List.replicate_succ, List.cons_append]; simp [hcsl]
    have hemp : (List.replicate (m + 1) c ++ ('/' :: tail.toList)).isEmpty = false := rfl
    simp only [hnul_s, hemp, hhead, hlast, Bool.or_self, Bool.false_eq_true, ↓reduceIte, Bool.false_and]
    rw [List.replicate_succ, List.cons_append]; split
    · rename_i h; split at h
      · rename_i hm; injection hm with hhd; exact absurd hhd hcsl
      · rw [← List.cons_append, ← List.replicate_succ, hsp] at h
        have hcs : checkSegments false (List.replicate (m + 1) c :: splitSlashChars tail.toList) = .ok () := by
          unfold checkSegments checkSegments.go
          have hempn : (List.replicate (m + 1) c).isEmpty = false := rfl
          simp only [hempn, hd1, hd2, Bool.false_eq_true, ↓reduceIte]
          cases hs : splitSlashChars tail.toList with
          | nil => rfl
          | cons _ _ => unfold checkSegments at htseg; rw [hs] at htseg; exact htseg
        rw [hcs] at h; cases h
    · rw [← List.cons_append, ← List.replicate_succ, ← hlist, String.ofList_toList]

private theorem validateSymlinkTarget_sublink_rep (n : Nat) (hn : n > 0) {c : Char}
    (hc0 : c ≠ Char.ofNat 0) (hcsl : c ≠ '/') (hcdot : c ≠ '.') :
    validateSymlinkTarget false false "sub/link" ("../" ++ String.ofList (List.replicate n c)) = .ok () := by
  unfold validateSymlinkTarget; dsimp only
  have hlist : ("../" ++ String.ofList (List.replicate n c)).toList = ['.', '.', '/'] ++ List.replicate n c := by
    simp [String.toList_append, String.toList_ofList]
  rw [hlist, hasNulChars_append, hasNulChars_replicate n hc0]
  have hnul_p : hasNulChars ['.', '.', '/'] = false := by decide
  have hemp : (['.', '.', '/'] ++ List.replicate n c).isEmpty = false := rfl
  have hhead : ((['.', '.', '/'] ++ List.replicate n c).head? == some '/') = false := rfl
  simp only [hnul_p, hemp, hhead, Bool.or_self, Bool.false_eq_true, ↓reduceIte, Bool.false_and]
  have hno : (List.replicate n c).all (fun x => x != '/') = true := by
    rw [list_all_replicate]; cases n with | zero => omega | succ _ => simp [hcsl]
  have hsp : splitSlashChars (['.', '.', '/'] ++ List.replicate n c) = [['.', '.'], List.replicate n c] := by
    change splitSlashChars.go [] ('.' :: '.' :: '/' :: List.replicate n c) = _
    rw [splitSlashChars.go.eq_3 _ '.' _ (by decide), splitSlashChars.go.eq_3 _ '.' _ (by decide),
      splitSlashChars.go.eq_2, ← List.append_nil (List.replicate n c),
      splitSlashChars_go_noSlash [] _ [] hno, List.append_nil, List.reverse_replicate,
      splitSlashChars.go.eq_1, List.reverse_replicate]; simp
  change validateSymlinkTarget.walkDepth "sub/link" 1 (splitSlashChars (['.', '.', '/'] ++ List.replicate n c)) = .ok ()
  rw [hsp, validateSymlinkTarget.walkDepth.eq_2]
  have ⟨hd1, hd2⟩ := replicate_ne_dots n hn hcdot
  have hempn : (List.replicate n c).isEmpty = false := by cases n with | zero => omega | succ _ => rfl
  have hstep1 : validateSymlinkTarget.walkDepth "sub/link" (1 - 1) [List.replicate n c] = .ok () := by
    rw [validateSymlinkTarget.walkDepth.eq_2]; simp only [hempn, hd1, hd2, Bool.false_or, Bool.false_eq_true, ↓reduceIte]; rfl
  have h10 : (1 == 0) = false := rfl
  have hd_eq : ((['.', '.'] : List Char) == ['.']) = false := rfl
  have hdd_eq : ((['.', '.'] : List Char) == ['.', '.']) = true := rfl
  simp only [List.isEmpty, Bool.false_or, hd_eq, hdd_eq, h10, Bool.false_eq_true, ↓reduceIte, hstep1]

private theorem encodeEntryBlocks_noPax_size (e : TarEntry) (normPath : String)
    (hne : needsPax e (wirePathOf e.kind normPath) = false) :
    (encodeEntryBlocks e normPath).size = 512 + pad512 e.data.size := by
  unfold encodeEntryBlocks; dsimp only; simp only [hne, Bool.not_false, ↓reduceIte]
  rw [ByteArray.size_append, buildUstarHeader_size, padBlock512_size]

private theorem test1_empty_ex :
    ∃ emptyBytes : ByteArray, defaultApi.pack [] = .ok emptyBytes ∧ emptyBytes.size = 1024 ∧
      defaultApi.unpackWith { maxEntries := 0, maxTotalBytes := 0 } emptyBytes = .ok [] := by
  obtain ⟨bytes, decoded, hp, hu, hteq⟩ :=
    packUnpack_roundTrip_witness [] {} { maxEntries := 0, maxTotalBytes := 0 } rfl rfl rfl (Nat.zero_le _) (Nat.zero_le _) rfl
  have hp_eq : Impl.packWith {} [] = .ok (ByteArray.empty ++ zeroBlock ++ zeroBlock) := rfl
  have hb : bytes = ByteArray.empty ++ zeroBlock ++ zeroBlock := Except.ok.inj (hp.symm.trans hp_eq)
  cases decoded with
  | nil =>
    exact ⟨bytes, hp, by rw [hb, ByteArray.size_append, ByteArray.size_append, ByteArray.size_empty, zeroBlock_size], hu⟩
  | cons _ _ => cases hteq

private theorem string_rep_isEmpty_false (n : Nat) (hn : 0 < n) (c : Char) :
    (String.ofList (List.replicate n c)).isEmpty = false := by
  have h1 : (String.ofList (List.replicate n c)).length = n := by rw [String.length_ofList, List.length_replicate]
  cases h : (String.ofList (List.replicate n c)).isEmpty
  · rfl
  · rw [String.isEmpty_iff.mp h] at h1
    have h0 : ("" : String).length = 0 := rfl
    omega

private theorem test1_split_ex (splitPath : String) (splitEntry : TarEntry)
    (hsp : splitPath = String.ofList (List.replicate 60 'd') ++ "/" ++ String.ofList (List.replicate 60 'f'))
    (hse : splitEntry = { path := splitPath, kind := .regular, data := "hi".toUTF8 }) :
    ∃ splitBytes decSplit, defaultApi.pack [splitEntry] = .ok splitBytes ∧ splitBytes.size = 2048 ∧
      defaultApi.unpack splitBytes = .ok decSplit ∧ TarEquiv [splitEntry] decSplit := by
  have hval : validateEntryPath false false .regular splitPath = .ok splitPath := by
    rw [hsp]; refine validateEntryPath_rep_slash 60 (by decide) (by decide) (by decide) (by decide) _ ?_ ?_ ?_ ?_
    · rw [String.toList_ofList]; intro h; cases h
    · rw [String.toList_ofList, hasNulChars_replicate 60 (by decide)]
    · rw [String.toList_ofList, List.reverse_replicate]
      change ((List.replicate (59 + 1) 'f').head? == some '/') = false; rw [List.replicate_succ]; rfl
    · rw [String.toList_ofList]; exact checkSegments_rep 60 (by decide) (by decide) (by decide)
  have hnp : normalizeTarPath splitEntry.kind splitEntry.path = splitPath := by
    rw [hse]; exact (validateEntryPath_normPath hval).symm
  have hhi_sz : ("hi".toUTF8).size = 2 := by rw [toUTF8_eq_toByteArray, List.size_toByteArray]; decide
  have hv : ValidArchive false false [splitEntry] := by
    unfold ValidArchive validArchiveBool
    have hve : validEntryBool false false splitEntry = true := by
      rw [hse]; unfold validEntryBool; dsimp only; rw [hval]; dsimp only
      have h0 : (0 : Nat) < u64Limit := by decide
      have hnu : (!hasNulString "") = true := by decide
      rw [hhi_sz]; simp only [hnu, h0, decide_true, Bool.and_self, beq_self_eq_true]; decide
    have hnd : noDupNormalizedPathsBool [splitEntry] = true := by
      simp only [noDupNormalizedPathsBool, noDupNormalizedPathsBool.go.eq_2, noDupNormalizedPathsBool.go.eq_1, hnp]; rfl
    simp only [List.all_cons, List.all_nil, Bool.and_true, hve, hnd]
  have hfind : (findUstarSplit splitPath).isSome = true := by
    rw [hsp]; unfold findUstarSplit
    have hlist : (String.ofList (List.replicate 60 'd') ++ "/" ++ String.ofList (List.replicate 60 'f')).toList =
        List.replicate 60 'd' ++ ('/' :: List.replicate 60 'f') := by
      rw [String.toList_append, String.toList_append, String.toList_ofList, String.toList_ofList, List.append_assoc]; rfl
    have hno : (List.replicate 60 'd').all (fun c => c != '/') = true := by rw [list_all_replicate]; decide
    rw [hlist, findUstarSplit_go_noSlash [] _ _ hno, List.append_nil, List.reverse_replicate,
      findUstarSplit.go.eq_2, List.reverse_replicate, toUTF8_size_rep 60 (by decide),
      toUTF8_size_rep 60 (by decide), string_rep_isEmpty_false 60 (by decide) 'd',
      string_rep_isEmpty_false 60 (by decide) 'f']; decide
  have hneeds : needsPax splitEntry (wirePathOf splitEntry.kind splitPath) = false := by
    rw [hse]; unfold needsPax pathFitsUstar wirePathOf; dsimp only
    have his : isAsciiString splitPath = true := by
      rw [hsp, isAsciiString_append, isAsciiString_append, isAsciiString_rep 60 (by decide),
        isAsciiString_rep 60 (by decide)]
      have hs : isAsciiString "/" = true := by simp only [isAsciiString, toUTF8_toList]; decide
      rw [hs]; rfl
    have hi0 : isAsciiString "" = true := by simp [isAsciiString]
    have he_sz : ("").toUTF8.size = 0 := by rw [toUTF8_eq_toByteArray, List.size_toByteArray]; decide
    simp only [his, hfind, hi0, hhi_sz, he_sz, Bool.or_true, Bool.and_true, Bool.not_true, Bool.false_or]
    simp [ustarOctal7Limit, ustarOctal11Limit]
  have hfit : [splitEntry].all fitsPaxLimit = true := by
    simp only [List.all_cons, List.all_nil, Bool.and_true, fitsPaxLimit]; rw [hnp]; simp [hneeds]
  have htot : totalDataBytes [splitEntry] ≤ ({} : UnpackOptions).maxTotalBytes := by
    simp only [totalDataBytes, List.foldl_cons, List.foldl_nil, Nat.zero_add, hse, hhi_sz]; decide
  have hlen_sp : [splitEntry].length ≤ ({} : UnpackOptions).maxEntries := by simp only [List.length_cons, List.length_nil]; decide
  obtain ⟨splitBytes, decSplit, hp, hu, hteq⟩ :=
    packUnpack_roundTrip_witness [splitEntry] {} {} hv rfl rfl hlen_sp htot hfit
  have hspec := ((packWith_go_spec {} [splitEntry] [] ByteArray.empty).1 splitBytes hp).2
  have hsz : splitBytes.size = 2048 := by
    have hform : splitBytes = encodeEntryBlocks splitEntry splitPath ++ (zeroBlock ++ zeroBlock) := by
      rw [hspec, ByteArray.empty_append]
      simp only [List.foldl_cons, List.foldl_nil, ByteArray.empty_append, Bool.false_eq_true, ↓reduceIte, hnp]
    have hblk : (encodeEntryBlocks splitEntry splitPath).size = 1024 := by
      rw [encodeEntryBlocks_noPax_size splitEntry splitPath hneeds, hse]; dsimp only; rw [hhi_sz]; decide
    rw [hform, ByteArray.size_append, ByteArray.size_append, zeroBlock_size, hblk]
  exact ⟨splitBytes, decSplit, hp, hsz, hu, hteq⟩

private theorem test1_e14_roundTrip (pb pl : String) (e1 e2 e3 e4 : TarEntry)
    (hpb : pb = String.ofList (List.replicate 91 'p'))
    (hpl : pl = String.ofList (List.replicate 260 'x') ++ "/café.txt")
    (he1 : e1 =
      { path := pb, kind := .regular, mode := 0o100755
      , uid := ustarOctal7Limit + 7, gid := ustarOctal7Limit + 9, mtime := ustarOctal11Limit + 42
      , uname := "üser", gname := "grøup", data := "payload".toUTF8 })
    (he2 : e2 = { path := "sub/", kind := .directory, mode := 0o755 })
    (he3 : e3 = { path := "sub/link", kind := .symlink, mode := 0o777, linkTarget := "../" ++ pb })
    (he4 : e4 = { path := pl, kind := .regular, mode := 0o644 }) :
    AllPass (checkRoundTripCase defaultApi {} {} [e1, e2, e3, e4]) ∧
    AllPass (checkRoundTripCase defaultApi { deterministic := true } {} [e1, e2, e3, e4]) := by
  have hv1 : validateEntryPath false false .regular pb = .ok pb := by
    rw [hpb]; exact validateEntryPath_rep 91 (by decide) (by decide) (by decide) (by decide)
  have hv2 : validateEntryPath false false .directory "sub/" = .ok "sub" := rfl
  have hv3 : validateEntryPath false false .symlink "sub/link" = .ok "sub/link" := rfl
  have hv4 : validateEntryPath false false .regular pl = .ok pl := by
    rw [hpl, show ("/café.txt" : String) = "/" ++ "café.txt" from rfl, ← String.append_assoc]
    exact validateEntryPath_rep_slash 260 (by decide) (by decide) (by decide) (by decide)
      "café.txt" (by decide) (by decide) (by decide) rfl
  have hsym3 : validateSymlinkTarget false false "sub/link" ("../" ++ pb) = .ok () := by
    rw [hpb]; exact validateSymlinkTarget_sublink_rep 91 (by decide) (by decide) (by decide) (by decide)
  have hnp1 : normalizeTarPath e1.kind e1.path = pb := by rw [he1]; exact (validateEntryPath_normPath hv1).symm
  have hnp2 : normalizeTarPath e2.kind e2.path = "sub" := by rw [he2]; exact (validateEntryPath_normPath hv2).symm
  have hnp3 : normalizeTarPath e3.kind e3.path = "sub/link" := by rw [he3]; exact (validateEntryPath_normPath hv3).symm
  have hnp4 : normalizeTarPath e4.kind e4.path = pl := by rw [he4]; exact (validateEntryPath_normPath hv4).symm
  have hpay_sz : ("payload".toUTF8).size = 7 := by rw [toUTF8_eq_toByteArray, List.size_toByteArray]; decide
  have hv : ValidArchive false false [e1, e2, e3, e4] := by
    unfold ValidArchive validArchiveBool
    have hve1 : validEntryBool false false e1 = true := by
      rw [he1]; unfold validEntryBool; dsimp only; rw [hv1, hpay_sz]; dsimp only; rfl
    have hve2 : validEntryBool false false e2 = true := by rw [he2]; unfold validEntryBool; rw [hv2]; dsimp only; rfl
    have hve3 : validEntryBool false false e3 = true := by
      rw [he3]; unfold validEntryBool; dsimp only; rw [hv3]; dsimp only; rw [hsym3]; dsimp only
      have hemp_sz : ByteArray.empty.size = 0 := rfl
      rw [hemp_sz]; rfl
    have hve4 : validEntryBool false false e4 = true := by
      rw [he4]; unfold validEntryBool; dsimp only; rw [hv4]; dsimp only
      have hemp_sz : ByteArray.empty.size = 0 := rfl
      rw [hemp_sz]; rfl
    have hlen1 : pb.length = 91 := by rw [hpb, String.length_ofList, List.length_replicate]
    have hcaf_l : ("/café.txt" : String).length = 9 := by decide
    have hlen4 : pl.length = 269 := by rw [hpl, String.length_append, String.length_ofList, List.length_replicate, hcaf_l]
    have ne_of_len : ∀ {a b : String}, a.length ≠ b.length → (a == b) = false :=
      fun hne => beq_false_of_ne fun h => hne (congrArg String.length h)
    have hsub_l : ("sub" : String).length = 3 := rfl
    have hlnk_l : ("sub/link" : String).length = 8 := rfl
    have h21 : ("sub" == pb) = false := ne_of_len (by omega)
    have h32 : ("sub/link" == "sub") = false := rfl
    have h31 : ("sub/link" == pb) = false := ne_of_len (by omega)
    have h43 : (pl == "sub/link") = false := ne_of_len (by omega)
    have h42 : (pl == "sub") = false := ne_of_len (by omega)
    have h41 : (pl == pb) = false := ne_of_len (by omega)
    have hnd : noDupNormalizedPathsBool [e1, e2, e3, e4] = true := by
      simp only [noDupNormalizedPathsBool, noDupNormalizedPathsBool.go.eq_2, noDupNormalizedPathsBool.go.eq_1,
        hnp1, hnp2, hnp3, hnp4, List.contains, List.elem, h21, h32, h31, h43, h42, h41]; rfl
    simp only [List.all_cons, List.all_nil, Bool.and_true, hve1, hve2, hve3, hve4, hnd]
  have his1 : isAsciiString pb = true := by rw [hpb]; exact isAsciiString_rep 91 (by decide)
  have hsz1 : pb.toUTF8.size = 91 := by rw [hpb]; exact toUTF8_size_rep 91 (by decide)
  have his3 : isAsciiString ("../" ++ pb) = true := by
    rw [isAsciiString_append, his1]
    have hd : isAsciiString "../" = true := by simp only [isAsciiString, toUTF8_toList]; decide
    rw [hd]; rfl
  have hsz3 : ("../" ++ pb).toUTF8.size = 94 := by
    have hd : ("../").toUTF8.size = 3 := by rw [toUTF8_eq_toByteArray, List.size_toByteArray]; decide
    rw [toUTF8_size_append, hd, hsz1]
  have hsz4 : pl.toUTF8.size = 270 := by
    have hc : ("/café.txt").toUTF8.size = 10 := by rw [toUTF8_eq_toByteArray, List.size_toByteArray]; decide
    rw [hpl, toUTF8_size_append, toUTF8_size_rep 260 (by decide), hc]
  have his4 : isAsciiString pl = false := by
    have hc : isAsciiString "/café.txt" = false := by simp only [isAsciiString, toUTF8_toList]; decide
    rw [hpl, isAsciiString_append, hc, Bool.and_false]
  have hfit1 : fitsPaxLimit e1 = true := by
    unfold fitsPaxLimit; rw [hnp1]; rw [he1]; dsimp only
    have h91 : decide (91 ≤ 100) = true := rfl
    have hne : needsPax
        { path := pb, kind := .regular, mode := 0o100755, uid := ustarOctal7Limit + 7
        , gid := ustarOctal7Limit + 9, mtime := ustarOctal11Limit + 42, uname := "üser", gname := "grøup"
        , data := "payload".toUTF8 } (wirePathOf .regular pb) = true := by
      unfold needsPax pathFitsUstar wirePathOf; dsimp only; rw [his1, hsz1]
      simp only [h91, Bool.true_or, Bool.and_self, isAsciiString,
        toUTF8_eq_toByteArray, toByteArray_toList, List.size_toByteArray]; rfl
    have hnot_p : (!pathFitsUstar (wirePathOf .regular pb)) = false := by
      unfold pathFitsUstar wirePathOf; dsimp only; rw [his1, hsz1]; simp only [h91, Bool.true_or, Bool.and_self]; rfl
    simp only [hne, ↓reduceIte]; unfold buildPaxPayload
    simp only [hnot_p, Bool.false_eq_true, ↓reduceIte, ByteArray.size_append,
      toUTF8_eq_toByteArray, toByteArray_toList, List.size_toByteArray, isAsciiString]; decide
  have hfit2 : fitsPaxLimit e2 = true := by
    rw [he2]; simp only [fitsPaxLimit, needsPax, pathFitsUstar, isAsciiString,
      toUTF8_eq_toByteArray, toByteArray_toList, List.size_toByteArray]; decide
  have hfit3 : fitsPaxLimit e3 = true := by
    unfold fitsPaxLimit; rw [hnp3]; rw [he3]; dsimp only
    have hne : needsPax { path := "sub/link", kind := .symlink, mode := 0o777, linkTarget := "../" ++ pb }
        (wirePathOf .symlink "sub/link") = false := by
      unfold needsPax pathFitsUstar wirePathOf; dsimp only; rw [his3, hsz3]
      simp only [isAsciiString, toUTF8_eq_toByteArray, toByteArray_toList, List.size_toByteArray,
        show ByteArray.empty.size = 0 from rfl]; rfl
    simp [hne]
  have hfit4 : fitsPaxLimit e4 = true := by
    unfold fitsPaxLimit; rw [hnp4]; rw [he4]; dsimp only
    have hnot4 : (!pathFitsUstar pl) = true := by simp only [pathFitsUstar, his4, Bool.false_and, Bool.not_false]
    have hne4 : needsPax { path := pl, kind := .regular, mode := 0o644 } (wirePathOf .regular pl) = true := by
      unfold needsPax wirePathOf; simp only [hnot4, Bool.true_or]
    simp only [hne4, ↓reduceIte]
    rw [decide_eq_true_eq]; dsimp only [wirePathOf]; unfold buildPaxPayload; dsimp only
    have hru : (!isAsciiString "" || decide ("".toUTF8.size > 32)) = false := by
      simp only [isAsciiString, toUTF8_eq_toByteArray, toByteArray_toList, List.size_toByteArray]; decide
    have hemp_sz : ByteArray.empty.size = 0 := rfl
    simp only [hnot4, ↓reduceIte, hru, hemp_sz, Bool.false_eq_true]
    have hc5 : ¬(0 ≥ ustarOctal11Limit) := by decide
    have hc7 : ¬(0 ≥ ustarOctal7Limit) := by decide
    simp only [hc5, hc7, show (EntryKind.regular == EntryKind.symlink) = false from rfl,
      Bool.false_and, Bool.false_eq_true, ↓reduceIte, ByteArray.append_empty]
    rw [encodePaxRecord_size_of_kv "path" pl, hsz4]
    have hpk : ("path").toUTF8.size = 4 := by rw [toUTF8_eq_toByteArray, List.size_toByteArray]; decide
    rw [hpk]; change (toString (paxRecordTotalLen 277)).toUTF8.size + 277 ≤ maxPaxHeaderBytes
    have htl : (toString (paxRecordTotalLen 277)).toUTF8.size ≤ 10 := by
      rw [toUTF8_eq_toByteArray, List.size_toByteArray]; decide
    exact Nat.le_trans (Nat.add_le_add_right htl 277) (by decide)
  have hfit : [e1, e2, e3, e4].all fitsPaxLimit = true := by simp [hfit1, hfit2, hfit3, hfit4]
  have htot : totalDataBytes [e1, e2, e3, e4] ≤ ({} : UnpackOptions).maxTotalBytes := by
    simp only [totalDataBytes, List.foldl_cons, List.foldl_nil, Nat.zero_add, he1, he2, he3, he4, hpay_sz]
    have hemp_sz : ByteArray.empty.size = 0 := rfl
    rw [hemp_sz]; decide
  have hlen : [e1, e2, e3, e4].length ≤ ({} : UnpackOptions).maxEntries := by simp only [List.length_cons, List.length_nil]; decide
  exact ⟨checkRoundTripCase_of_valid (packOpts := {}) (unpackOpts := {}) hv rfl rfl hlen htot hfit,
    checkRoundTripCase_of_valid (packOpts := { deterministic := true }) (unpackOpts := {}) hv rfl rfl hlen htot hfit⟩

/-- Prove `test_tar_packWith_concreteUstarAndPaxCases_roundTrip` for `defaultApi`. -/
theorem allPass_packWith_concreteUstarAndPaxCases_roundTrip :
    AllPass (test_tar_packWith_concreteUstarAndPaxCases_roundTrip defaultApi) := by
  let splitPath := String.ofList (List.replicate 60 'd') ++ "/" ++ String.ofList (List.replicate 60 'f')
  let splitEntry : TarEntry := { path := splitPath, kind := .regular, data := "hi".toUTF8 }
  have ⟨splitBytes, decSplit, hpack_split, hsplit_sz, hunpack_split, hteq_split⟩ :=
    test1_split_ex splitPath splitEntry rfl rfl
  have ⟨eb, hpack_eb, hsz_eb, hunpack_eb⟩ := test1_empty_ex
  unfold test_tar_packWith_concreteUstarAndPaxCases_roundTrip
  rw [hpack_eb]; dsimp (config := { zeta := false }) only
  rw [allPass_have]; intro jp0 hjp0; rw [allPass_assert_bind]; refine ⟨hsz_eb, ?_⟩
  rw [hjp0, hunpack_eb]; dsimp (config := { zeta := false }) only
  rw [allPass_assert_bind]; refine ⟨rfl, ?_⟩
  rw [allPass_have]; intro sp hsp; rw [allPass_have]; intro se hse
  dsimp only [splitEntry, splitPath] at hpack_split
  rw [hpack_split]; dsimp (config := { zeta := false }) only; rw [hse, hsp]; dsimp (config := { zeta := false }) only
  rw [allPass_assert_bind]; refine ⟨hsplit_sz, ?_⟩
  rw [hunpack_split]; dsimp (config := { zeta := false }) only
  rw [allPass_assert_bind]; refine ⟨hteq_split, ?_⟩
  rw [allPass_have]; intro cont hcont
  generalize hpb_g : String.ofList (List.replicate 91 'p') = pb_var
  generalize hpl_g : (String.ofList (List.replicate 260 'x') ++ "/café.txt") = pl_var
  have h14 := test1_e14_roundTrip pb_var pl_var
    { path := pb_var, kind := .regular, mode := 0o100755
    , uid := ustarOctal7Limit + 7, gid := ustarOctal7Limit + 9, mtime := ustarOctal11Limit + 42
    , uname := "üser", gname := "grøup", data := "payload".toUTF8 }
    { path := "sub/", kind := .directory, mode := 0o755 }
    { path := "sub/link", kind := .symlink, mode := 0o777, linkTarget := "../" ++ pb_var }
    { path := pl_var, kind := .regular, mode := 0o644 } hpb_g.symm hpl_g.symm rfl rfl rfl rfl
  refine allPass_seq_checkRoundTripCase _ _ _ _ h14.1 ?_
  rw [hcont]; dsimp (config := { zeta := false }) only; rw [hpb_g, hpl_g]; exact h14.2

private theorem checkPackError_test2_dup :
    AllPass (checkPackError defaultApi {}
      [{ path := "sub/", kind := .directory }, { path := "sub", kind := .regular }] .duplicatePath) := by
  rw [allPass_checkPackError_iff, defaultApi_packWith_eq]
  obtain ⟨np1, hv1⟩ := (validatePackEntry_ok_iff {} { path := "sub/", kind := .directory }).mpr (by decide)
  rw [validatePackEntry_ok_eq _ _ hv1] at hv1
  change validatePackEntry {} _ = .ok "sub" at hv1
  obtain ⟨np2, hv2⟩ := (validatePackEntry_ok_iff {} { path := "sub", kind := .regular }).mpr (by decide)
  rw [validatePackEntry_ok_eq _ _ hv2] at hv2
  change validatePackEntry {} _ = .ok "sub" at hv2
  have hp : Impl.packWith {} [{ path := "sub/", kind := .directory }, { path := "sub", kind := .regular }] =
      .error { kind := .duplicatePath, message := "duplicate tar entry path: sub", entryPath := some "sub" } := by
    unfold Impl.packWith; rw [Impl.packWith.go.eq_2, hv1]; dsimp only
    have hs1 : ([].contains "sub") = false := rfl
    simp only [hs1, Bool.false_eq_true, ↓reduceIte]; rw [Impl.packWith.go.eq_2, hv2]; rfl
  rw [hp]; exact ⟨rfl, rfl⟩

/-- Prove `test_tar_packWith_invalidAndUnsafePaths_rejected` for `defaultApi`. -/
theorem allPass_packWith_invalidAndUnsafePaths_rejected :
    AllPass (test_tar_packWith_invalidAndUnsafePaths_rejected defaultApi) := by
  have hv_rt : ValidArchive true true
      [{ path := "/../a", kind := .regular }, { path := "/sub/", kind := .directory }] := by unfold ValidArchive; decide
  have hfit_rt : ([{ path := "/../a", kind := .regular }, { path := "/sub/", kind := .directory }].all fitsPaxLimit) = true := by
    simp only [List.all_cons, List.all_nil, Bool.and_true, fitsPaxLimit, needsPax, pathFitsUstar,
      isAsciiString, toUTF8_eq_toByteArray, toByteArray_toList, List.size_toByteArray]; decide
  have hrt := checkRoundTripCase_of_valid (packOpts := { allowAbsolute := true, allowParentTraversal := true })
    (unpackOpts := { allowAbsolute := true, allowParentTraversal := true }) hv_rt rfl rfl (by decide) (by decide) hfit_rt
  unfold test_tar_packWith_invalidAndUnsafePaths_rejected
  iterate 14 (refine allPass_seq_checkPackError _ _ _ _ (checkPackError_of_eval (by decide)) ?_)
  refine allPass_seq_checkRoundTripCase _ _ _ _ hrt ?_
  refine allPass_seq_checkPackError _ _ _ _ checkPackError_test2_dup ?_
  exact checkPackError_of_eval (by decide)

/-- Prove `test_tar_packWith_symlinkAndEntryInvariants_rejected` for `defaultApi`. -/
theorem allPass_packWith_symlinkAndEntryInvariants_rejected :
    AllPass (test_tar_packWith_symlinkAndEntryInvariants_rejected defaultApi) := by
  have hv_rt : ValidArchive false false
      [{ path := "sub/ok1", kind := .symlink, linkTarget := "../target" },
       { path := "sub/ok2", kind := .symlink, linkTarget := "x/../../y" }] := by unfold ValidArchive; decide
  have hfit_rt : ([{ path := "sub/ok1", kind := .symlink, linkTarget := "../target" },
      { path := "sub/ok2", kind := .symlink, linkTarget := "x/../../y" }].all fitsPaxLimit) = true := by
    simp only [List.all_cons, List.all_nil, Bool.and_true, fitsPaxLimit, needsPax, pathFitsUstar,
      isAsciiString, toUTF8_eq_toByteArray, toByteArray_toList, List.size_toByteArray]; decide
  have hrt := checkRoundTripCase_of_valid (packOpts := {}) (unpackOpts := {}) hv_rt rfl rfl (by decide) (by decide) hfit_rt
  have hdir_d : AllPass (checkPackError defaultApi {} [{ path := "d", kind := .directory, data := "x".toUTF8 }] .invalidHeader) := by
    rw [allPass_checkPackError_iff, defaultApi_packWith_eq]
    have hx : ("x".toUTF8).size = 1 := by rw [toUTF8_eq_toByteArray, List.size_toByteArray]; decide
    have hv : validatePackEntry {} { path := "d", kind := .directory, data := "x".toUTF8 } =
        .error { kind := .invalidHeader, message := "non-regular tar entry cannot have payload data", entryPath := some "d" } := by
      unfold validatePackEntry
      have hp0 : validateEntryPath false false .directory "d" = .ok "d" := rfl
      have hc : (EntryKind.directory != EntryKind.regular && 1 != 0) = true := rfl
      simp only [hp0, hx, hc, ↓reduceIte]; rfl
    unfold Impl.packWith; rw [Impl.packWith.go.eq_2, hv]; exact ⟨rfl, rfl⟩
  have hsym_d : AllPass (checkPackError defaultApi {} [{ path := "s", kind := .symlink, data := "x".toUTF8, linkTarget := "t" }] .invalidHeader) := by
    rw [allPass_checkPackError_iff, defaultApi_packWith_eq]
    have hx : ("x".toUTF8).size = 1 := by rw [toUTF8_eq_toByteArray, List.size_toByteArray]; decide
    have hv : validatePackEntry {} { path := "s", kind := .symlink, data := "x".toUTF8, linkTarget := "t" } =
        .error { kind := .invalidHeader, message := "non-regular tar entry cannot have payload data", entryPath := some "s" } := by
      unfold validatePackEntry
      have hp0 : validateEntryPath false false .symlink "s" = .ok "s" := rfl
      have hs0 : validateSymlinkTarget false false "s" "t" = .ok () := rfl
      have hc : (EntryKind.symlink != EntryKind.regular && 1 != 0) = true := rfl
      simp only [hp0, hx, hc, ↓reduceIte]; dsimp only [Bind.bind, Except.bind]; rw [hs0]; rfl
    unfold Impl.packWith; rw [Impl.packWith.go.eq_2, hv]; exact ⟨rfl, rfl⟩
  unfold test_tar_packWith_symlinkAndEntryInvariants_rejected
  iterate 6 (refine allPass_seq_checkPackError _ _ _ _ (checkPackError_of_eval (by decide)) ?_)
  refine allPass_seq_checkRoundTripCase _ _ _ _ hrt ?_
  refine allPass_seq_checkPackError _ _ _ _ hdir_d ?_
  refine allPass_seq_checkPackError _ _ _ _ hsym_d ?_
  iterate 6 (refine allPass_seq_checkPackError _ _ _ _ (checkPackError_of_eval (by decide)) ?_)
  exact checkPackError_of_eval (by decide)

end LeanSwe.Tar.Proofs
