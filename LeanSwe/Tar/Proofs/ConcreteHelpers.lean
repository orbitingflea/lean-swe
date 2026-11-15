import LeanSwe.Tar.SpecTests
import LeanSwe.Tar.Proofs.ByteModel
import LeanSwe.Tar.Proofs.FieldCodecs
import LeanSwe.Tar.Proofs.Headers
import LeanSwe.Tar.Proofs.Universal

namespace LeanSwe.Tar.Proofs

open Core
open Core.NondetTest
open LeanSwe.Tar
open LeanSwe.Tar.Model
open LeanSwe.Tar.Impl

/-- Size of `twoZeroBlocks` is `1024`. -/
theorem twoZeroBlocks_size : twoZeroBlocks.size = 1024 := by
  unfold twoZeroBlocks
  rw [ByteArray.size_append, zeroBlock_size]

/-- Size of `mkRegularFrame p d` is `512 + pad512 d.size`. -/
theorem mkRegularFrame_size (p : String) (d : ByteArray) :
    (mkRegularFrame p d).size = 512 + pad512 d.size := by
  unfold mkRegularFrame
  rw [ByteArray.size_append, mkUstarHeader_size, padBlock512_size]

/-- Size of `mkPaxFrame pax` is `512 + pad512 pax.size`. -/
theorem mkPaxFrame_size (pax : ByteArray) :
    (mkPaxFrame pax).size = 512 + pad512 pax.size := by
  unfold mkPaxFrame
  rw [ByteArray.size_append, mkUstarHeader_size, padBlock512_size]

/-- Structural fuel-bounded version of `Impl.findByteIn` for fast concrete evaluation. -/
def findByteInFuel : Nat → ByteArray → UInt8 → Nat → Nat → Option Nat
  | 0, _, _, _, _ => none
  | fuel + 1, bs, target, idx, stop =>
    if idx ≥ stop then none
    else if h : idx < bs.size then
      if bs[idx]'h == target then some idx else findByteInFuel fuel bs target (idx + 1) stop
    else none

/-- Equivalence between `Impl.findByteIn` and `findByteInFuel` when `stop - idx ≤ fuel`. -/
theorem findByteIn_eq_fuel (bs : ByteArray) (target : UInt8) (idx stop fuel : Nat)
    (hf : stop - idx ≤ fuel) :
    findByteIn bs target idx stop = findByteInFuel fuel bs target idx stop := by
  induction fuel generalizing idx with
  | zero =>
    have hge : idx ≥ stop := by omega
    rw [findByteIn.eq_1, findByteInFuel]
    simp [hge]
  | succ k ih =>
    rw [findByteIn.eq_1, findByteInFuel]
    by_cases hge : idx ≥ stop
    · simp [hge]
    · simp only [hge, ↓reduceIte]
      by_cases hbd : idx < bs.size
      · simp only [hbd, ↓reduceDIte]
        cases hcmp : (bs[idx]'hbd == target)
        · simp only [Bool.false_eq_true, ↓reduceIte]
          exact ih (idx + 1) (by omega)
        · simp only [↓reduceIte]
      · simp only [hbd, ↓reduceDIte]

/-- Structural fuel-bounded version of `Impl.parsePaxPayload.go` for fast concrete evaluation. -/
def parsePaxGoFuel : Nat → ByteArray → Nat → Nat → List String → PaxOverrides → Except TarError PaxOverrides
  | 0, _, offset, _, _, _ =>
    .error { kind := .invalidHeader, message := "fuel exhausted", offset := some offset }
  | fuel + 1, pax, offset, pos, seenKeys, ov =>
    if pos ≥ pax.size then
      .ok ov
    else
      match findByteInFuel (pax.size - pos) pax 0x20 pos pax.size with
      | none =>
        .error { kind := .invalidHeader, message := "missing space in PAX record", offset := some offset }
      | some spIdx =>
        match parsePaxLen pax pos spIdx with
        | none =>
          .error { kind := .invalidHeader, message := "invalid PAX record length", offset := some offset }
        | some recLen =>
          if recLen < 5 then
            .error { kind := .invalidHeader, message := "PAX record length < 5", offset := some offset }
          else
            let recEnd := pos + recLen
            if recEnd > pax.size then
              .error { kind := .invalidHeader, message := "out-of-bounds PAX record length", offset := some offset }
            else
              let hasNl : Bool :=
                if h : recEnd - 1 < pax.size then (pax[recEnd - 1]'h) == 0x0a else false
              if !hasNl then
                .error { kind := .invalidHeader, message := "PAX record missing trailing newline", offset := some offset }
              else
                match findByteInFuel (recEnd - 1 - (spIdx + 1)) pax 0x3d (spIdx + 1) (recEnd - 1) with
                | none =>
                  .error { kind := .invalidHeader, message := "PAX record missing '='", offset := some offset }
                | some eqIdx =>
                  let keyBytes := pax.extract (spIdx + 1) eqIdx
                  let valBytes := pax.extract (eqIdx + 1) (recEnd - 1)
                  match String.fromUTF8? keyBytes, String.fromUTF8? valBytes with
                  | none, _ | _, none =>
                    .error { kind := .invalidEncoding, message := "invalid UTF-8 in PAX record", offset := some offset }
                  | some key, some val =>
                    if key.isEmpty || hasNulString key || key.toList.contains '\n' then
                      .error { kind := .invalidHeader, message := "invalid PAX record key", offset := some offset }
                    else if seenKeys.contains key then
                      .error { kind := .invalidHeader, message := s!"duplicate PAX key: {key}", offset := some offset }
                    else if startsWithStr key "GNU.sparse." then
                      .error { kind := .unsupportedEntry, message := "GNU sparse PAX archives are unsupported", offset := some offset }
                    else
                      match applyPaxKey ov key val offset with
                      | .error err => .error err
                      | .ok nextOv => parsePaxGoFuel fuel pax offset recEnd (key :: seenKeys) nextOv

/-- Equivalence between `Impl.parsePaxPayload` and `parsePaxGoFuel`. -/
theorem parsePaxPayload_eq_fuel (pax : ByteArray) (offset : Nat) :
    parsePaxPayload pax offset = parsePaxGoFuel (pax.size + 1) pax offset 0 [] {} := by
  have hgo : ∀ (fuel pos : Nat) (seenKeys : List String) (ov : PaxOverrides),
      pax.size - pos < fuel →
      parsePaxPayload.go pax offset pos seenKeys ov = parsePaxGoFuel fuel pax offset pos seenKeys ov := by
    intro fuel
    induction fuel with
    | zero =>
      intro pos _ _ hf
      omega
    | succ k ih =>
      intro pos seenKeys ov hf
      rw [parsePaxPayload.go.eq_1, parsePaxGoFuel]
      by_cases hge : pos ≥ pax.size
      · simp [hge]
      · simp only [hge, ↓reduceIte]
        rw [findByteIn_eq_fuel pax 0x20 pos pax.size (pax.size - pos) (Nat.le_refl _)]
        cases hsp : findByteInFuel (pax.size - pos) pax 0x20 pos pax.size with
        | none => rfl
        | some spIdx =>
          dsimp only
          cases hlen : parsePaxLen pax pos spIdx with
          | none => rfl
          | some recLen =>
            dsimp only
            by_cases hr5 : recLen < 5
            · simp [hr5]
            · simp only [hr5, ↓reduceIte]
              by_cases hbd : pos + recLen > pax.size
              · simp [hbd]
              · simp only [hbd, ↓reduceIte]
                cases hnl : (if h : pos + recLen - 1 < pax.size then (pax[pos + recLen - 1]'h) == 0x0a else false)
                · rfl
                · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
                  rw [findByteIn_eq_fuel pax 0x3d (spIdx + 1) (pos + recLen - 1)
                    (pos + recLen - 1 - (spIdx + 1)) (Nat.le_refl _)]
                  cases heq : findByteInFuel (pos + recLen - 1 - (spIdx + 1)) pax 0x3d (spIdx + 1) (pos + recLen - 1) with
                  | none => rfl
                  | some eqIdx =>
                    dsimp only
                    cases hk : String.fromUTF8? (pax.extract (spIdx + 1) eqIdx) with
                    | none => rfl
                    | some key =>
                      cases hv : String.fromUTF8? (pax.extract (eqIdx + 1) (pos + recLen - 1)) with
                      | none => rfl
                      | some val =>
                        dsimp only
                        split
                        · rfl
                        · split
                          · rfl
                          · split
                            · rfl
                            · cases ha : applyPaxKey ov key val offset with
                              | error err => rfl
                              | ok nextOv =>
                                dsimp only
                                exact ih (pos + recLen) (key :: seenKeys) nextOv (by omega)
  exact hgo (pax.size + 1) 0 [] {} (by omega)

/-- Unpatched `mkUstarHeader` before `patchHeaderChecksum` is applied. -/
def mkUstarHeaderPre (name : String) (mode : UInt32) (uid gid size mtime : Nat)
    (typeflag : UInt8) (linkname uname gname pfx : String) : ByteArray :=
  let b0 := zeroBlock
  let b1 := blitFixed b0 0 100 name.toUTF8
  let b2 := blitFixed b1 100 8 (encodeOctalField (mode &&& 0o7777).toNat 7)
  let b3 := blitFixed b2 108 8 (encodeOctalField uid 7)
  let b4 := blitFixed b3 116 8 (encodeOctalField gid 7)
  let b5 := blitFixed b4 124 12 (encodeOctalField size 11)
  let b6 := blitFixed b5 136 12 (encodeOctalField mtime 11)
  let b7 := b6.set! 156 typeflag
  let b8 := blitFixed b7 157 100 linkname.toUTF8
  let b9 := blitFixed b8 257 6 "ustar\x00".toUTF8
  let b10 := blitFixed b9 263 2 "00".toUTF8
  let b11 := blitFixed b10 265 32 uname.toUTF8
  let b12 := blitFixed b11 297 32 gname.toUTF8
  blitFixed b12 345 155 pfx.toUTF8

private theorem byteArray_size_set!' (b : ByteArray) (k : Nat) (v : UInt8) :
    (b.set! k v).size = b.size :=
  Array.size_setIfInBounds

/-- `mkUstarHeaderPre` has size `512`. -/
theorem mkUstarHeaderPre_size (name : String) (mode : UInt32) (uid gid size mtime : Nat)
    (typeflag : UInt8) (linkname uname gname pfx : String) :
    (mkUstarHeaderPre name mode uid gid size mtime typeflag linkname uname gname pfx).size = 512 := by
  unfold mkUstarHeaderPre
  simp only [blitFixed_size, byteArray_size_set!', zeroBlock_size]

/-- `mkUstarHeader ...` is `patchHeaderChecksum (mkUstarHeaderPre ...)`. -/
theorem mkUstarHeader_eq_patch (name : String) (mode : UInt32) (uid gid size mtime : Nat)
    (typeflag : UInt8) (linkname uname gname pfx : String) :
    mkUstarHeader name mode uid gid size mtime typeflag linkname uname gname pfx =
      patchHeaderChecksum (mkUstarHeaderPre name mode uid gid size mtime typeflag linkname uname gname pfx) := by
  rfl

private theorem byteArray_set!_getElem' {b : ByteArray} {k i : Nat} {v : UInt8}
    (hk : k < b.size) (hi : i < b.size) :
    (b.set! k v)[i]'(by rw [byteArray_size_set!']; exact hi) =
      if k = i then v else b[i]'hi := by
  have hi' : i < b.data.size := hi
  change (b.data.setIfInBounds k v)[i]'(by rw [Array.size_setIfInBounds]; exact hi') = _
  by_cases h : k = i
  · subst h; simp only [↓reduceIte]
    exact Array.getElem_setIfInBounds_self (by rw [Array.size_setIfInBounds]; exact hk)
  · simp only [h, ↓reduceIte]
    exact Array.getElem_setIfInBounds_ne hi' (by omega)

private theorem ustar_magic_size : ("ustar\x00".toUTF8).size = 6 := by
  rw [toUTF8_eq_toByteArray, List.size_toByteArray]; decide

private theorem ustar_ver_size : ("00".toUTF8).size = 2 := by
  rw [toUTF8_eq_toByteArray, List.size_toByteArray]; decide

/-- Byte-level specification of `mkUstarHeaderPre` across all `512` bytes. -/
theorem mkUstarHeaderPre_getElem (name : String) (mode : UInt32) (uid gid size mtime : Nat)
    (typeflag : UInt8) (linkname uname gname pfx : String) {i : Nat} (hi : i < 512) :
    (mkUstarHeaderPre name mode uid gid size mtime typeflag linkname uname gname pfx)[i]'(by
        rw [mkUstarHeaderPre_size]; exact hi) =
      if _h0 : i < min 100 name.toUTF8.size then name.toUTF8[i]'(by omega)
      else if _h1 : 100 ≤ i ∧ i < 108 then (encodeOctalField (mode &&& 0o7777).toNat 7)[i - 100]'(by
        rw [encodeOctalField_size]; omega)
      else if _h2 : 108 ≤ i ∧ i < 116 then (encodeOctalField uid 7)[i - 108]'(by
        rw [encodeOctalField_size]; omega)
      else if _h3 : 116 ≤ i ∧ i < 124 then (encodeOctalField gid 7)[i - 116]'(by
        rw [encodeOctalField_size]; omega)
      else if _h4 : 124 ≤ i ∧ i < 136 then (encodeOctalField size 11)[i - 124]'(by
        rw [encodeOctalField_size]; omega)
      else if _h5 : 136 ≤ i ∧ i < 148 then (encodeOctalField mtime 11)[i - 136]'(by
        rw [encodeOctalField_size]; omega)
      else if _h6 : i = 156 then typeflag
      else if _h7 : 157 ≤ i ∧ i < 157 + min 100 linkname.toUTF8.size then linkname.toUTF8[i - 157]'(by omega)
      else if h8 : 257 ≤ i ∧ i < 263 then ("ustar\x00".toUTF8)[i - 257]'(by
        have := ustar_magic_size; omega)
      else if h9 : 263 ≤ i ∧ i < 265 then ("00".toUTF8)[i - 263]'(by
        have := ustar_ver_size; omega)
      else if _h10 : 265 ≤ i ∧ i < 265 + min 32 uname.toUTF8.size then uname.toUTF8[i - 265]'(by omega)
      else if _h11 : 297 ≤ i ∧ i < 297 + min 32 gname.toUTF8.size then gname.toUTF8[i - 297]'(by omega)
      else if _h12 : 345 ≤ i ∧ i < 345 + min 155 pfx.toUTF8.size then pfx.toUTF8[i - 345]'(by omega)
      else 0 := by
  unfold mkUstarHeaderPre
  have hsMode : (encodeOctalField (mode &&& 0o7777).toNat 7).size = 8 := encodeOctalField_size _ 7
  have hsUid : (encodeOctalField uid 7).size = 8 := encodeOctalField_size _ 7
  have hsGid : (encodeOctalField gid 7).size = 8 := encodeOctalField_size _ 7
  have hsSize : (encodeOctalField size 11).size = 12 := encodeOctalField_size _ 11
  have hsMtime : (encodeOctalField mtime 11).size = 12 := encodeOctalField_size _ 11
  have hsMagic : "ustar\x00".toUTF8.size = 6 := ustar_magic_size
  have hsVer : "00".toUTF8.size = 2 := ustar_ver_size
  rw [blitFixed_getElem (by simp only [blitFixed_size, byteArray_size_set!', zeroBlock_size]; omega)
    (by simp only [blitFixed_size, byteArray_size_set!', zeroBlock_size]; omega)]
  by_cases h12 : 345 ≤ i ∧ i < 345 + min 155 pfx.toUTF8.size
  · rw [dite_eq_left h12]
    rw [dite_eq_right (by omega), dite_eq_right (by omega), dite_eq_right (by omega), dite_eq_right (by omega),
      dite_eq_right (by omega), dite_eq_right (by omega), dite_eq_right (by omega), dite_eq_right (by omega),
      dite_eq_right (by omega), dite_eq_right (by omega), dite_eq_right (by omega), dite_eq_right (by omega),
      dite_eq_left h12]
  · rw [dite_eq_right h12]
    rw [blitFixed_getElem (by simp only [blitFixed_size, byteArray_size_set!', zeroBlock_size]; omega)
      (by simp only [blitFixed_size, byteArray_size_set!', zeroBlock_size]; omega)]
    by_cases h11 : 297 ≤ i ∧ i < 297 + min 32 gname.toUTF8.size
    · rw [dite_eq_left h11]
      rw [dite_eq_right (by omega), dite_eq_right (by omega), dite_eq_right (by omega), dite_eq_right (by omega),
        dite_eq_right (by omega), dite_eq_right (by omega), dite_eq_right (by omega), dite_eq_right (by omega),
        dite_eq_right (by omega), dite_eq_right (by omega), dite_eq_right (by omega), dite_eq_left h11]
    · rw [dite_eq_right h11]
      rw [blitFixed_getElem (by simp only [blitFixed_size, byteArray_size_set!', zeroBlock_size]; omega)
        (by simp only [blitFixed_size, byteArray_size_set!', zeroBlock_size]; omega)]
      by_cases h10 : 265 ≤ i ∧ i < 265 + min 32 uname.toUTF8.size
      · rw [dite_eq_left h10]
        rw [dite_eq_right (by omega), dite_eq_right (by omega), dite_eq_right (by omega), dite_eq_right (by omega),
          dite_eq_right (by omega), dite_eq_right (by omega), dite_eq_right (by omega), dite_eq_right (by omega),
          dite_eq_right (by omega), dite_eq_right (by omega), dite_eq_left h10]
      · rw [dite_eq_right h10]
        rw [blitFixed_getElem (by simp only [blitFixed_size, byteArray_size_set!', zeroBlock_size]; omega)
          (by simp only [blitFixed_size, byteArray_size_set!', zeroBlock_size]; omega)]
        by_cases h9 : 263 ≤ i ∧ i < 265
        · have h9' : 263 ≤ i ∧ i < 263 + min 2 ("00".toUTF8).size := by rw [hsVer]; omega
          rw [dite_eq_left h9']
          rw [dite_eq_right (by omega), dite_eq_right (by omega), dite_eq_right (by omega), dite_eq_right (by omega),
            dite_eq_right (by omega), dite_eq_right (by omega), dite_eq_right (by omega), dite_eq_right (by omega),
            dite_eq_right (by omega), dite_eq_left h9]
        · have h9' : ¬(263 ≤ i ∧ i < 263 + min 2 ("00".toUTF8).size) := by rw [hsVer]; omega
          rw [dite_eq_right h9']
          rw [blitFixed_getElem (by simp only [blitFixed_size, byteArray_size_set!', zeroBlock_size]; omega)
            (by simp only [blitFixed_size, byteArray_size_set!', zeroBlock_size]; omega)]
          by_cases h8 : 257 ≤ i ∧ i < 263
          · have h8' : 257 ≤ i ∧ i < 257 + min 6 ("ustar\x00".toUTF8).size := by rw [hsMagic]; omega
            rw [dite_eq_left h8']
            rw [dite_eq_right (by omega), dite_eq_right (by omega), dite_eq_right (by omega), dite_eq_right (by omega),
              dite_eq_right (by omega), dite_eq_right (by omega), dite_eq_right (by omega), dite_eq_right (by omega),
              dite_eq_left h8]
          · have h8' : ¬(257 ≤ i ∧ i < 257 + min 6 ("ustar\x00".toUTF8).size) := by rw [hsMagic]; omega
            rw [dite_eq_right h8']
            rw [blitFixed_getElem (by simp only [blitFixed_size, byteArray_size_set!', zeroBlock_size]; omega)
              (by simp only [blitFixed_size, byteArray_size_set!', zeroBlock_size]; omega)]
            by_cases h7 : 157 ≤ i ∧ i < 157 + min 100 linkname.toUTF8.size
            · rw [dite_eq_left h7]
              rw [dite_eq_right (by omega), dite_eq_right (by omega), dite_eq_right (by omega), dite_eq_right (by omega),
                dite_eq_right (by omega), dite_eq_right (by omega), dite_eq_right (by omega), dite_eq_left h7]
            · rw [dite_eq_right h7]
              rw [byteArray_set!_getElem' (by simp only [blitFixed_size, zeroBlock_size]; omega)
                (by simp only [blitFixed_size, zeroBlock_size]; omega)]
              by_cases h6 : i = 156
              · subst h6
                rw [ite_eq_left rfl]
                rw [dite_eq_right (by omega), dite_eq_right (by omega), dite_eq_right (by omega), dite_eq_right (by omega),
                  dite_eq_right (by omega), dite_eq_right (by omega), dite_eq_left rfl]
              · rw [ite_eq_right (by omega)]
                rw [blitFixed_getElem (by simp only [blitFixed_size, zeroBlock_size]; omega)
                  (by simp only [blitFixed_size, zeroBlock_size]; omega)]
                by_cases h5 : 136 ≤ i ∧ i < 148
                · have h5' : 136 ≤ i ∧ i < 136 + min 12 (encodeOctalField mtime 11).size := by rw [hsMtime]; omega
                  rw [dite_eq_left h5']
                  rw [dite_eq_right (by omega), dite_eq_right (by omega), dite_eq_right (by omega), dite_eq_right (by omega),
                    dite_eq_right (by omega), dite_eq_left h5]
                · have h5' : ¬(136 ≤ i ∧ i < 136 + min 12 (encodeOctalField mtime 11).size) := by rw [hsMtime]; omega
                  rw [dite_eq_right h5']
                  rw [blitFixed_getElem (by simp only [blitFixed_size, zeroBlock_size]; omega)
                    (by simp only [blitFixed_size, zeroBlock_size]; omega)]
                  by_cases h4 : 124 ≤ i ∧ i < 136
                  · have h4' : 124 ≤ i ∧ i < 124 + min 12 (encodeOctalField size 11).size := by rw [hsSize]; omega
                    rw [dite_eq_left h4']
                    rw [dite_eq_right (by omega), dite_eq_right (by omega), dite_eq_right (by omega), dite_eq_right (by omega),
                      dite_eq_left h4]
                  · have h4' : ¬(124 ≤ i ∧ i < 124 + min 12 (encodeOctalField size 11).size) := by rw [hsSize]; omega
                    rw [dite_eq_right h4']
                    rw [blitFixed_getElem (by simp only [blitFixed_size, zeroBlock_size]; omega)
                      (by simp only [blitFixed_size, zeroBlock_size]; omega)]
                    by_cases h3 : 116 ≤ i ∧ i < 124
                    · have h3' : 116 ≤ i ∧ i < 116 + min 8 (encodeOctalField gid 7).size := by rw [hsGid]; omega
                      rw [dite_eq_left h3']
                      rw [dite_eq_right (by omega), dite_eq_right (by omega), dite_eq_right (by omega), dite_eq_left h3]
                    · have h3' : ¬(116 ≤ i ∧ i < 116 + min 8 (encodeOctalField gid 7).size) := by rw [hsGid]; omega
                      rw [dite_eq_right h3']
                      rw [blitFixed_getElem (by simp only [blitFixed_size, zeroBlock_size]; omega)
                        (by simp only [blitFixed_size, zeroBlock_size]; omega)]
                      by_cases h2 : 108 ≤ i ∧ i < 116
                      · have h2' : 108 ≤ i ∧ i < 108 + min 8 (encodeOctalField uid 7).size := by rw [hsUid]; omega
                        rw [dite_eq_left h2']
                        rw [dite_eq_right (by omega), dite_eq_right (by omega), dite_eq_left h2]
                      · have h2' : ¬(108 ≤ i ∧ i < 108 + min 8 (encodeOctalField uid 7).size) := by rw [hsUid]; omega
                        rw [dite_eq_right h2']
                        rw [blitFixed_getElem (by simp only [blitFixed_size, zeroBlock_size]; omega)
                          (by simp only [blitFixed_size, zeroBlock_size]; omega)]
                        by_cases h1 : 100 ≤ i ∧ i < 108
                        · have h1' : 100 ≤ i ∧ i < 100 + min 8 (encodeOctalField (mode &&& 0o7777).toNat 7).size := by
                            rw [hsMode]; omega
                          rw [dite_eq_left h1']
                          rw [dite_eq_right (by omega), dite_eq_left h1]
                        · have h1' : ¬(100 ≤ i ∧ i < 100 + min 8 (encodeOctalField (mode &&& 0o7777).toNat 7).size) := by
                            rw [hsMode]; omega
                          rw [dite_eq_right h1']
                          rw [blitFixed_getElem (by rw [zeroBlock_size]; omega) (by rw [zeroBlock_size]; omega)]
                          by_cases h0 : i < min 100 name.toUTF8.size
                          · have h0' : 0 ≤ i ∧ i < 0 + min 100 name.toUTF8.size := by omega
                            rw [dite_eq_left h0', dite_eq_left h0]
                            simp
                          · have h0' : ¬(0 ≤ i ∧ i < 0 + min 100 name.toUTF8.size) := by omega
                            rw [dite_eq_right h0', zeroBlock_getElem]
                            rw [dite_eq_right h0, dite_eq_right h1, dite_eq_right h2, dite_eq_right h3,
                              dite_eq_right h4, dite_eq_right h5, dite_eq_right h6, dite_eq_right h7,
                              dite_eq_right h8, dite_eq_right h9, dite_eq_right h10, dite_eq_right h11,
                              dite_eq_right h12]

/-- Byte-level specification of `mkUstarHeader` outside the checksum range `[148..156)`. -/
theorem mkUstarHeader_getElem_outside_chk {bytes : ByteArray} {offset : Nat}
    {name : String} {mode : UInt32} {uid gid size mtime : Nat} {typeflag : UInt8}
    {linkname uname gname pfx : String}
    (hbd : offset + 512 ≤ bytes.size)
    (hext : bytes.extract offset (offset + 512) =
      mkUstarHeader name mode uid gid size mtime typeflag linkname uname gname pfx)
    {i : Nat} (hi : i < 512) (hnot : ¬(148 ≤ i ∧ i < 156)) :
    bytes[offset + i]'(by omega) =
      (mkUstarHeaderPre name mode uid gid size mtime typeflag linkname uname gname pfx)[i]'(by
        rw [mkUstarHeaderPre_size]; exact hi) := by
  have hp := parseChecksumOctal_patchHeaderChecksum
    (mkUstarHeaderPre_size name mode uid gid size mtime typeflag linkname uname gname pfx) hbd hext
  exact hp.2.2 i hi hnot

/-- Extract slice helper from `bytes[offset + a .. offset + b]` via pointwise byte equality. -/
theorem extract_eq_of_getElem {bytes target : ByteArray} {offset a b : Nat}
    (hab : a ≤ b) (hb : offset + b ≤ bytes.size) (ht : target.size = b - a)
    (hpt : ∀ (k : Nat) (hk : k < b - a),
      bytes[offset + a + k]'(by omega) = target[k]'(by rw [ht]; exact hk)) :
    bytes.extract (offset + a) (offset + b) = target := by
  apply ByteArray.ext; apply Array.ext
  · show (bytes.extract (offset + a) (offset + b)).size = target.size
    rw [ByteArray.size_extract, ht]; omega
  · intro k hk1 hk2
    have hk1' : k < (bytes.extract (offset + a) (offset + b)).size := hk1
    have hk2' : k < target.size := hk2
    have hk' : k < b - a := by omega
    rw [← ByteArray.getElem_eq_getElem_data (h := hk1'),
      ← ByteArray.getElem_eq_getElem_data (h := hk2'),
      ByteArray.getElem_extract (by rw [ByteArray.size_extract]; omega)]
    exact hpt k hk'

private theorem getElem_congr_idx {bytes : ByteArray} {i j : Nat}
    (hi : i < bytes.size) (hj : j < bytes.size) (hij : i = j) :
    bytes[i]'hi = bytes[j]'hj := by
  subst hij; rfl

private theorem ustar_magic_head_ne :
    ("ustar\x00".toUTF8)[0]'(by rw [ustar_magic_size]; decide) ≠ 0 := by
  decide

/-- A `mkUstarHeader` block at `offset` always has `isZeroRange ... 512 = false`. -/
theorem isZeroRange_mkUstarHeader_false {bytes : ByteArray} {offset : Nat}
    {name : String} {mode : UInt32} {uid gid size mtime : Nat} {typeflag : UInt8}
    {linkname uname gname pfx : String}
    (hbd : offset + 512 ≤ bytes.size)
    (hext : bytes.extract offset (offset + 512) =
      mkUstarHeader name mode uid gid size mtime typeflag linkname uname gname pfx) :
    isZeroRange bytes offset 512 = false := by
  apply isZeroRange_false_of_ne (i := 257) (by omega) (by omega)
  rw [mkUstarHeader_getElem_outside_chk hbd hext (i := 257) (by omega) (by omega)]
  rw [mkUstarHeaderPre_getElem name mode uid gid size mtime typeflag linkname uname gname pfx (by omega)]
  rw [dite_eq_right (by omega), dite_eq_right (by omega), dite_eq_right (by omega), dite_eq_right (by omega),
    dite_eq_right (by omega), dite_eq_right (by omega), dite_eq_right (by omega), dite_eq_right (by omega),
    dite_eq_left (by omega)]
  exact ustar_magic_head_ne

/-- Extraction of string fields from `mkUstarHeader` matching `padRightBytes` when fields fit. -/
theorem mkUstarHeader_extract_strings {bytes : ByteArray} {offset : Nat}
    {name : String} {mode : UInt32} {uid gid size mtime : Nat} {typeflag : UInt8}
    {linkname uname gname pfx : String}
    (hbd : offset + 512 ≤ bytes.size)
    (hext : bytes.extract offset (offset + 512) =
      mkUstarHeader name mode uid gid size mtime typeflag linkname uname gname pfx)
    (hnm : name.toUTF8.size ≤ 100) (hlk : linkname.toUTF8.size ≤ 100)
    (hun : uname.toUTF8.size ≤ 32) (hgn : gname.toUTF8.size ≤ 32)
    (hpf : pfx.toUTF8.size ≤ 155) :
    bytes.extract offset (offset + 100) = padRightBytes 100 name.toUTF8 ∧
    bytes.extract (offset + 157) (offset + 257) = padRightBytes 100 linkname.toUTF8 ∧
    bytes.extract (offset + 265) (offset + 297) = padRightBytes 32 uname.toUTF8 ∧
    bytes.extract (offset + 297) (offset + 329) = padRightBytes 32 gname.toUTF8 ∧
    bytes.extract (offset + 345) (offset + 500) = padRightBytes 155 pfx.toUTF8 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · have h0 : bytes.extract offset (offset + 100) = bytes.extract (offset + 0) (offset + 100) := by
      simp only [Nat.add_zero]
    rw [h0]
    apply extract_eq_of_getElem (by omega) (by omega) (padRightBytes_size 100 _)
    intro k hk
    rw [getElem_congr_idx (by omega) (by omega) (by omega : offset + 0 + k = offset + k),
      mkUstarHeader_getElem_outside_chk hbd hext (by omega) (by omega),
      mkUstarHeaderPre_getElem _ _ _ _ _ _ _ _ _ _ _ (by omega), padRightBytes_getElem hnm hk]
    by_cases hlt : k < name.toUTF8.size
    · rw [dite_eq_left (by omega), dite_eq_left hlt]
    · rw [dite_eq_right (by omega), dite_eq_right (by omega), dite_eq_right (by omega), dite_eq_right (by omega),
        dite_eq_right (by omega), dite_eq_right (by omega), dite_eq_right (by omega), dite_eq_right (by omega),
        dite_eq_right (by omega), dite_eq_right (by omega), dite_eq_right (by omega), dite_eq_right (by omega),
        dite_eq_right (by omega), dite_eq_right hlt]
  · apply extract_eq_of_getElem (by omega) (by omega) (padRightBytes_size 100 _)
    intro k hk
    rw [getElem_congr_idx (by omega) (by omega) (Nat.add_assoc offset 157 k),
      mkUstarHeader_getElem_outside_chk hbd hext (by omega) (by omega),
      mkUstarHeaderPre_getElem _ _ _ _ _ _ _ _ _ _ _ (by omega), padRightBytes_getElem hlk hk]
    by_cases hlt : k < linkname.toUTF8.size
    · rw [dite_eq_right (by omega), dite_eq_right (by omega), dite_eq_right (by omega), dite_eq_right (by omega),
        dite_eq_right (by omega), dite_eq_right (by omega), dite_eq_right (by omega), dite_eq_left (by omega),
        dite_eq_left hlt]
      simp
    · rw [dite_eq_right (by omega), dite_eq_right (by omega), dite_eq_right (by omega), dite_eq_right (by omega),
        dite_eq_right (by omega), dite_eq_right (by omega), dite_eq_right (by omega), dite_eq_right (by omega),
        dite_eq_right (by omega), dite_eq_right (by omega), dite_eq_right (by omega), dite_eq_right (by omega),
        dite_eq_right (by omega), dite_eq_right hlt]
  · apply extract_eq_of_getElem (by omega) (by omega) (padRightBytes_size 32 _)
    intro k hk
    rw [getElem_congr_idx (by omega) (by omega) (Nat.add_assoc offset 265 k),
      mkUstarHeader_getElem_outside_chk hbd hext (by omega) (by omega),
      mkUstarHeaderPre_getElem _ _ _ _ _ _ _ _ _ _ _ (by omega), padRightBytes_getElem hun hk]
    by_cases hlt : k < uname.toUTF8.size
    · rw [dite_eq_right (by omega), dite_eq_right (by omega), dite_eq_right (by omega), dite_eq_right (by omega),
        dite_eq_right (by omega), dite_eq_right (by omega), dite_eq_right (by omega), dite_eq_right (by omega),
        dite_eq_right (by omega), dite_eq_right (by omega), dite_eq_left (by omega), dite_eq_left hlt]
      simp
    · rw [dite_eq_right (by omega), dite_eq_right (by omega), dite_eq_right (by omega), dite_eq_right (by omega),
        dite_eq_right (by omega), dite_eq_right (by omega), dite_eq_right (by omega), dite_eq_right (by omega),
        dite_eq_right (by omega), dite_eq_right (by omega), dite_eq_right (by omega), dite_eq_right (by omega),
        dite_eq_right (by omega), dite_eq_right hlt]
  · apply extract_eq_of_getElem (by omega) (by omega) (padRightBytes_size 32 _)
    intro k hk
    rw [getElem_congr_idx (by omega) (by omega) (Nat.add_assoc offset 297 k),
      mkUstarHeader_getElem_outside_chk hbd hext (by omega) (by omega),
      mkUstarHeaderPre_getElem _ _ _ _ _ _ _ _ _ _ _ (by omega), padRightBytes_getElem hgn hk]
    by_cases hlt : k < gname.toUTF8.size
    · rw [dite_eq_right (by omega), dite_eq_right (by omega), dite_eq_right (by omega), dite_eq_right (by omega),
        dite_eq_right (by omega), dite_eq_right (by omega), dite_eq_right (by omega), dite_eq_right (by omega),
        dite_eq_right (by omega), dite_eq_right (by omega), dite_eq_right (by omega), dite_eq_left (by omega),
        dite_eq_left hlt]
      simp
    · rw [dite_eq_right (by omega), dite_eq_right (by omega), dite_eq_right (by omega), dite_eq_right (by omega),
        dite_eq_right (by omega), dite_eq_right (by omega), dite_eq_right (by omega), dite_eq_right (by omega),
        dite_eq_right (by omega), dite_eq_right (by omega), dite_eq_right (by omega), dite_eq_right (by omega),
        dite_eq_right (by omega), dite_eq_right hlt]
  · apply extract_eq_of_getElem (by omega) (by omega) (padRightBytes_size 155 _)
    intro k hk
    rw [getElem_congr_idx (by omega) (by omega) (Nat.add_assoc offset 345 k),
      mkUstarHeader_getElem_outside_chk hbd hext (by omega) (by omega),
      mkUstarHeaderPre_getElem _ _ _ _ _ _ _ _ _ _ _ (by omega), padRightBytes_getElem hpf hk]
    by_cases hlt : k < pfx.toUTF8.size
    · rw [dite_eq_right (by omega), dite_eq_right (by omega), dite_eq_right (by omega), dite_eq_right (by omega),
        dite_eq_right (by omega), dite_eq_right (by omega), dite_eq_right (by omega), dite_eq_right (by omega),
        dite_eq_right (by omega), dite_eq_right (by omega), dite_eq_right (by omega), dite_eq_right (by omega),
        dite_eq_left (by omega), dite_eq_left hlt]
      simp
    · rw [dite_eq_right (by omega), dite_eq_right (by omega), dite_eq_right (by omega), dite_eq_right (by omega),
        dite_eq_right (by omega), dite_eq_right (by omega), dite_eq_right (by omega), dite_eq_right (by omega),
        dite_eq_right (by omega), dite_eq_right (by omega), dite_eq_right (by omega), dite_eq_right (by omega),
        dite_eq_right (by omega), dite_eq_right hlt]

/-- `unpackLoop` stops cleanly with `acc.reverse` at two trailing zero blocks. -/
theorem unpackLoop_at_twoZeroBlocks (opts : UnpackOptions) (pre : ByteArray)
    (seen : List String) (acc : List TarEntry) (totalBytes : Nat) :
    unpackLoop opts (pre ++ (zeroBlock ++ zeroBlock)) pre.size none seen acc totalBytes =
      .ok acc.reverse := by
  let bytes := pre ++ (zeroBlock ++ zeroBlock)
  change unpackLoop opts bytes pre.size none seen acc totalBytes = .ok acc.reverse
  have hz2 : (zeroBlock ++ zeroBlock).size = 1024 := by rw [ByteArray.size_append, zeroBlock_size]
  have hsz : bytes.size = pre.size + 1024 := by rw [ByteArray.size_append, hz2]
  have hnotge : ¬pre.size ≥ bytes.size := by rw [hsz]; omega
  have hz1 : isZeroRange bytes pre.size 512 = true := by
    refine (isZeroRange_eq_true_iff bytes pre.size 512 (by omega)).mpr ⟨by rw [hsz]; omega, ?_⟩
    intro i hi _
    rw [getElem_append_right (Nat.le_add_right _ _)]
    have h1 : (pre.size + i) - pre.size < zeroBlock.size := by rw [zeroBlock_size]; omega
    have h2 : (pre.size + i) - pre.size < (zeroBlock ++ zeroBlock).size := by rw [hz2]; omega
    rw [getElem_append_left h1 h2]
    exact zeroBlock_getElem _
  have hz2' : isZeroRange bytes (pre.size + 512) 512 = true := by
    refine (isZeroRange_eq_true_iff bytes (pre.size + 512) 512 (by omega)).mpr ⟨by rw [hsz]; omega, ?_⟩
    intro i hi _
    rw [getElem_append_right (by omega)]
    have hr : zeroBlock.size ≤ (pre.size + 512 + i) - pre.size := by rw [zeroBlock_size]; omega
    rw [getElem_append_right hr]
    exact zeroBlock_getElem _
  have htr : allZeroTrailer bytes (pre.size + 1024) = true := by
    rw [allZeroTrailer.eq_1]; simp [hsz]
  rw [unpackLoop.eq_1]
  simp only [hnotge, ↓reduceIte]
  unfold unpackStep
  simp only [hnotge, ↓reduceIte, hz1, Option.isSome_none, Bool.false_eq_true, hz2', htr,
    Bool.not_true, (by rw [hsz]; omega : ¬pre.size + 512 ≥ bytes.size)]

private theorem extract_pre_hdr_rest (pre hdr rest : ByteArray) (hhdr : hdr.size = 512) :
    (pre ++ hdr ++ rest).extract pre.size (pre.size + 512) = hdr := by
  have h := extract_append_mid pre hdr rest
  rw [hhdr] at h
  exact h

private theorem extract_pre_hdr_pad_post (pre hdr pax post : ByteArray) (hhdr : hdr.size = 512) :
    ((pre ++ hdr) ++ (padBlock512 pax ++ post)).extract (pre.size + 512) (pre.size + 512 + pad512 pax.size) =
      padBlock512 pax := by
  have ha : (pre ++ hdr).size = pre.size + 512 := by rw [ByteArray.size_append, hhdr]
  have hsub := extract_append_mid (pre ++ hdr) (padBlock512 pax) post
  rw [ha, padBlock512_size, ByteArray.append_assoc] at hsub
  exact hsub

/-- Step `unpackLoop` over a valid `mkPaxFrame pax` at `pre.size`. -/
theorem unpackLoop_mkPaxFrame_step (opts : UnpackOptions) (pre post pax : ByteArray)
    (seen : List String) (acc : List TarEntry) (totalBytes : Nat)
    (hpax_sz : pax.size ≤ maxPaxHeaderBytes)
    (hov : PaxOverrides) (hparse_pax : parsePaxPayload pax pre.size = .ok hov)
    (hpost : post.size ≥ 512) :
    unpackLoop opts (pre ++ mkPaxFrame pax ++ post) pre.size none seen acc totalBytes =
      unpackLoop opts (pre ++ mkPaxFrame pax ++ post) (pre.size + 512 + pad512 pax.size)
        (some hov) seen acc totalBytes := by
  let frame := mkPaxFrame pax
  let hdr := mkUstarHeader "././@PaxHeader" 0o644 0 0 pax.size 0 0x78 "" "" "" ""
  let bytes := pre ++ frame ++ post
  change unpackLoop opts bytes pre.size none seen acc totalBytes =
    unpackLoop opts bytes (pre.size + 512 + pad512 pax.size) (some hov) seen acc totalBytes
  have hmax : maxPaxHeaderBytes < ustarOctal11Limit := by decide
  have hsz_frame : frame.size = 512 + pad512 pax.size := mkPaxFrame_size pax
  have hsz_bytes : bytes.size = pre.size + frame.size + post.size := by
    simp only [bytes, ByteArray.size_append]
  have hnotge : ¬pre.size ≥ bytes.size := by rw [hsz_bytes, hsz_frame]; omega
  have hassoc : bytes = pre ++ hdr ++ (padBlock512 pax ++ post) := by
    simp only [bytes, frame, mkPaxFrame, hdr, ByteArray.append_assoc]
  have hext_hdr : bytes.extract pre.size (pre.size + 512) = hdr := by
    rw [hassoc]
    exact extract_pre_hdr_rest pre hdr (padBlock512 pax ++ post) (mkUstarHeader_size _ _ _ _ _ _ _ _ _ _ _)
  have hnz : isZeroRange bytes pre.size 512 = false :=
    isZeroRange_mkUstarHeader_false (by rw [hsz_bytes, hsz_frame]; omega) hext_hdr
  have hnotgt : ¬pre.size + 512 > bytes.size := by rw [hsz_bytes, hsz_frame]; omega
  have hparse_hdr : parseUstarHeader bytes pre.size =
      .ok { mode := ((0o644 : UInt32) &&& 0o7777).toNat, uid := 0, gid := 0, size := pax.size, mtime := 0, typeflag := 0x78 } :=
    parseUstarHeader_mkUstarHeader (by decide) (by decide) (by omega) (by decide)
      (by rw [hsz_bytes, hsz_frame]; omega) hext_hdr
  have hpax_ext : bytes.extract (pre.size + 512) (pre.size + 512 + pax.size) = pax := by
    have h1 : bytes.extract (pre.size + 512) (pre.size + 512 + pad512 pax.size) = padBlock512 pax := by
      rw [hassoc]
      exact extract_pre_hdr_pad_post pre hdr pax post (mkUstarHeader_size _ _ _ _ _ _ _ _ _ _ _)
    have hle : pax.size ≤ pad512 pax.size := le_pad512 pax.size
    have h2 : bytes.extract (pre.size + 512) (pre.size + 512 + pax.size) =
        (bytes.extract (pre.size + 512) (pre.size + 512 + pad512 pax.size)).extract 0 pax.size := by
      rw [ByteArray.extract_extract]
      exact congrArg (bytes.extract (pre.size + 512)) (by omega)
    rw [h2, h1, padBlock512_extract_prefix]
  have hnot_max : ¬pax.size > maxPaxHeaderBytes := by omega
  have hnot_trunc : ¬pre.size + 512 + pad512 pax.size > bytes.size := by
    rw [hsz_bytes, hsz_frame]; omega
  have hadv : pre.size + 512 + pad512 pax.size > pre.size := by omega
  have h78 : ((0x78 : UInt8) == 0x78) = true := rfl
  rw [unpackLoop.eq_1]
  simp only [hnotge, ↓reduceIte]
  unfold unpackStep
  simp only [hnotge, ↓reduceIte, hnz, Bool.false_eq_true, hnotgt, hparse_hdr,
    Option.isSome_none, hnot_max, hnot_trunc, hpax_ext, hparse_pax, h78, hadv]

/-- Decode a regular `mkUstarHeader` block at `pre.size` when fields fit and no PAX error occurs. -/
theorem decodeTarEntry_mkUstarHeader_regular (opts : UnpackOptions) (bytes hdr : ByteArray)
    (offset : Nat) (pendingPax : Option PaxOverrides) (seen : List String)
    (accLen totalBytes : Nat)
    {name uname gname pfx : String} {mode : UInt32} {uid gid size mtime : Nat}
    (hbd : offset + 512 ≤ bytes.size)
    (hext : bytes.extract offset (offset + 512) = hdr)
    (hhdr : hdr = mkUstarHeader name mode uid gid size mtime 0x30 "" uname gname pfx)
    (hnm : name.toUTF8.size ≤ 100) (hun : uname.toUTF8.size ≤ 32) (hgn : gname.toUTF8.size ≤ 32)
    (hpf : pfx.toUTF8.size ≤ 155)
    (hnm_nul : !hasNulString name = true) (hun_nul : !hasNulString uname = true)
    (hgn_nul : !hasNulString gname = true) (hpf_nul : !hasNulString pfx = true)
    (_huid : uid < ustarOctal7Limit) (_hgid : gid < ustarOctal7Limit)
    (_hsize : size < ustarOctal11Limit) (_hmtime : mtime < ustarOctal11Limit)
    (hmaxe : accLen + 1 ≤ opts.maxEntries)
    (hmaxb : totalBytes + ((pendingPax.getD {}).size?.getD size) ≤ opts.maxTotalBytes)
    (htrunc : offset + 512 + pad512 ((pendingPax.getD {}).size?.getD size) ≤ bytes.size)
    {normPath : String}
    (hval : validateEntryPath opts.allowAbsolute opts.allowParentTraversal .regular
      ((pendingPax.getD {}).path?.getD (if pfx.isEmpty then name else pfx ++ "/" ++ name)) = .ok normPath)
    (hseen : seen.contains normPath = false) :
    decodeTarEntry opts bytes offset
        { mode := (mode &&& 0o7777).toNat, uid := uid, gid := gid, size := size, mtime := mtime, typeflag := 0x30 }
        pendingPax seen accLen totalBytes =
      .ok ({ path := normPath, kind := .regular, mode := ((mode &&& 0o7777).toNat).toUInt32,
              uid := (pendingPax.getD {}).uid?.getD uid,
              gid := (pendingPax.getD {}).gid?.getD gid,
              mtime := (pendingPax.getD {}).mtime?.getD mtime,
              uname := (pendingPax.getD {}).uname?.getD uname,
              gname := (pendingPax.getD {}).gname?.getD gname,
              data := if (pendingPax.getD {}).size?.getD size == 0 then ByteArray.empty
                else bytes.extract (offset + 512) (offset + 512 + (pendingPax.getD {}).size?.getD size),
              linkTarget := "" },
        pad512 ((pendingPax.getD {}).size?.getD size)) := by
  subst hhdr
  have hs := mkUstarHeader_extract_strings hbd hext hnm (by rw [toUTF8_eq_toByteArray, List.size_toByteArray]; decide)
    hun hgn hpf
  have hdec_nm : decodeCStringUtf8 bytes offset (offset + 100) offset "name" = .ok name :=
    decodeCStringUtf8_padRightBytes hnm_nul hnm (by omega) hs.1
  have hdec_un : decodeCStringUtf8 bytes (offset + 265) (offset + 297) offset "uname" = .ok uname := by
    have heq297 : offset + 297 = (offset + 265) + 32 := by omega
    rw [heq297]
    exact decodeCStringUtf8_padRightBytes hun_nul hun (by omega) hs.2.2.1
  have hdec_gn : decodeCStringUtf8 bytes (offset + 297) (offset + 329) offset "gname" = .ok gname := by
    have heq329 : offset + 329 = (offset + 297) + 32 := by omega
    rw [heq329]
    exact decodeCStringUtf8_padRightBytes hgn_nul hgn (by omega) hs.2.2.2.1
  have hdec_pf : decodeCStringUtf8 bytes (offset + 345) (offset + 500) offset "prefix" = .ok pfx := by
    have heq500 : offset + 500 = (offset + 345) + 155 := by omega
    rw [heq500]
    exact decodeCStringUtf8_padRightBytes hpf_nul hpf (by omega) hs.2.2.2.2
  have hnot_e : ¬accLen + 1 > opts.maxEntries := by omega
  have hnot_b : ¬totalBytes + ((pendingPax.getD {}).size?.getD size) > opts.maxTotalBytes := by omega
  have hnot_t : ¬offset + 512 + pad512 ((pendingPax.getD {}).size?.getD size) > bytes.size := by omega
  have hreg_ne : (EntryKind.regular != EntryKind.regular) = false := rfl
  have hmod : (((mode &&& 0o7777).toNat) &&& 0o7777).toUInt32 = ((mode &&& 0o7777).toNat).toUInt32 := by
    have h4095 : UInt32.toNat 0o7777 = 0o7777 := rfl
    rw [UInt32.toNat_and, h4095, Nat.and_assoc, Nat.and_self]
  unfold decodeTarEntry
  simp only [beq_self_eq_true, Bool.true_or, ↓reduceIte, hreg_ne, Bool.false_and,
    Bool.false_eq_true, hnot_e, hnot_b, hnot_t, hdec_nm, hdec_pf, hdec_un, hdec_gn, hmod]
  cases hp : (pendingPax.getD {}).path? <;>
    simp only [hp, Option.getD_none, Option.getD_some] at hval <;>
    cases (pendingPax.getD {}).uname? <;>
    cases (pendingPax.getD {}).gname? <;>
    simp only [Option.getD_none, Option.getD_some] <;>
    rw [hval] <;>
    simp only [hseen, Bool.false_eq_true, ↓reduceIte] <;>
    rfl

end LeanSwe.Tar.Proofs
