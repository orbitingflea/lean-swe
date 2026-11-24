import LeanSwe.Tar.Types
import LeanSwe.Tar.Model

namespace LeanSwe.Tar.Model

open LeanSwe.Tar

/-- Diagnostic-free error identity carrying category, optional path, and optional byte offset. -/
abbrev TarErrKey := TarErrorKind × Option String × Option Nat

/-- Project a `TarError` onto its opaque-message identity `(kind, entryPath, offset)`. -/
def tarErrKeyOf (e : TarError) : TarErrKey :=
  (e.kind, e.entryPath, e.offset)

/-- Replace non-ASCII characters with `'?'` and truncate to at most `maxChars` ASCII characters. -/
def asciiFallbackModel (s : String) (maxChars : Nat) : String :=
  String.ofList ((s.toList.take maxChars).map fun c => if c.toNat < 0x80 then c else '?')

/-- Return the USTAR `typeflag` byte for an `EntryKind`. -/
def typeflagOfKind : EntryKind → UInt8
  | .regular => 0x30
  | .directory => 0x35
  | .symlink => 0x32

/-- Encode a single validated `TarEntry` into USTAR (and optional PAX `'x'`) tar blocks using `mkUstarHeader`. -/
def encodeEntryModel (e : TarEntry) (normPath : String) : ByteArray :=
  let wp := wirePathOf e.kind normPath
  let typeByte := typeflagOfKind e.kind
  if !needsPax e wp then
    let (pfx, nm) :=
      if wp.toUTF8.size ≤ 100 then ("", wp)
      else
        match findUstarSplit wp with
        | some pair => pair
        | none => ("", wp)
    mkUstarHeader nm e.mode e.uid e.gid e.data.size e.mtime typeByte e.linkTarget e.uname e.gname pfx ++
      padBlock512 e.data
  else
    let paxPayload := buildPaxPayload e wp
    let paxHdr := mkUstarHeader "././@PaxHeader" 0o644 0 0 paxPayload.size 0 0x78 "" "" "" ""
    let (fbPrefix, fbName) :=
      if !pathFitsUstar wp then ("", asciiFallbackModel wp 100)
      else if wp.toUTF8.size ≤ 100 then ("", wp)
      else
        match findUstarSplit wp with
        | some pair => pair
        | none => ("", asciiFallbackModel wp 100)
    let fbLink := if e.kind == .symlink then asciiFallbackModel e.linkTarget 100 else ""
    let fbUname := asciiFallbackModel e.uname 32
    let fbGname := asciiFallbackModel e.gname 32
    let fbUid := if e.uid < ustarOctal7Limit then e.uid else 0
    let fbGid := if e.gid < ustarOctal7Limit then e.gid else 0
    let fbSize := if e.data.size < ustarOctal11Limit then e.data.size else 0
    let fbMtime := if e.mtime < ustarOctal11Limit then e.mtime else 0
    paxHdr ++ padBlock512 paxPayload ++
      mkUstarHeader fbName e.mode fbUid fbGid fbSize fbMtime typeByte fbLink fbUname fbGname fbPrefix ++
      padBlock512 e.data

/-- Validate a single `TarEntry` for `packWithModel`, yielding its normalized path or `TarErrKey`. -/
def validatePackEntryModel (opts : PackOptions) (e : TarEntry) : Except TarErrKey String :=
  match validateEntryPath opts.allowAbsolute opts.allowParentTraversal e.kind e.path with
  | .error err => .error (tarErrKeyOf err)
  | .ok normPath =>
    let symCheck : Except TarErrKey Unit :=
      match e.kind with
      | .symlink =>
        match validateSymlinkTarget opts.allowAbsolute opts.allowParentTraversal normPath e.linkTarget with
        | .error err => .error (tarErrKeyOf err)
        | .ok () => .ok ()
      | .regular | .directory => .ok ()
    match symCheck with
    | .error err => .error err
    | .ok () =>
      if e.kind != .regular && e.data.size != 0 then
        .error (.invalidHeader, some e.path, none)
      else if e.kind != .symlink && e.linkTarget != "" then
        .error (.invalidHeader, some e.path, none)
      else if hasNulString e.uname || hasNulString e.gname then
        .error (.invalidHeader, some e.path, none)
      else if e.uid ≥ u64Limit || e.gid ≥ u64Limit || e.mtime ≥ u64Limit || e.data.size ≥ u64Limit then
        .error (.sizeOverflow, some e.path, none)
      else
        .ok normPath

/-- Structurally recursive USTAR/PAX serializer accumulating unique normalized paths in `seen`. -/
def packWithModelAux (opts : PackOptions) (seen : List String) :
    List TarEntry → Except TarErrKey ByteArray
  | [] => .ok (zeroBlock ++ zeroBlock)
  | e :: tail =>
    match validatePackEntryModel opts e with
    | .error err => .error err
    | .ok normPath =>
      if seen.contains normPath then
        .error (.duplicatePath, some normPath, none)
      else
        let eff := if opts.deterministic then zeroDeterministicMeta e else e
        (packWithModelAux opts (normPath :: seen) tail).map fun rest =>
          encodeEntryModel eff normPath ++ rest

/-- Reference serializer model for `LeanSwe.Tar.packWith`. -/
def packWithModel (opts : PackOptions) (entries : List TarEntry) : Except TarErrKey ByteArray :=
  packWithModelAux opts [] entries

/-- Extract `[start .. stop)` of `bytes` as a `List UInt8`. -/
def sliceList (bytes : ByteArray) (start stop : Nat) : List UInt8 :=
  (bytes.extract start stop).toList

/-- Return `true` iff `bytes` holds a 512-byte all-zero block starting at `offset`. -/
def isZeroBlockAt (bytes : ByteArray) (offset : Nat) : Bool :=
  offset + 512 ≤ bytes.size && (sliceList bytes offset (offset + 512)).all (· == 0)

/-- Return `true` iff every byte from `offset` to `bytes.size` is `0x00`. -/
def isZeroSuffix (bytes : ByteArray) (offset : Nat) : Bool :=
  (sliceList bytes offset bytes.size).all (· == 0)

/-- Decode a NUL-terminated UTF-8 string from byte slice `raw`. -/
def decodeCStringList (raw : List UInt8) (offset : Nat) : Except TarErrKey String :=
  match String.fromUTF8? (ByteArray.mk (raw.takeWhile (· != 0)).toArray) with
  | some s => .ok s
  | none => .error (.invalidEncoding, none, some offset)

/-- Parse strict octal ASCII checksum bytes (no base-256, trailing spaces/NULs only). -/
def parseChecksumOctalModel (raw : List UInt8) (offset : Nat) : Except TarErrKey Nat :=
  let afterLead := raw.dropWhile (· == 0x20)
  let digits := afterLead.takeWhile (fun b => 0x30 ≤ b && b ≤ 0x37)
  let tail := afterLead.drop digits.length
  if digits.isEmpty then
    .error (.invalidHeader, none, some offset)
  else if !tail.all (fun b => b == 0x20 || b == 0x00) then
    .error (.invalidHeader, none, some offset)
  else
    .ok (digits.foldl (fun acc b => acc * 8 + (b.toNat - 0x30)) 0)

/-- Parse a USTAR numeric field (base-256 unsigned or octal ASCII) bounded by `limit`. -/
def parseUstarNumericModel (raw : List UInt8) (offset : Nat)
    (allowAllEmpty : Bool) (limit : Nat) : Except TarErrKey Nat :=
  match raw with
  | [] => .error (.invalidHeader, none, some offset)
  | b0 :: rest =>
    if (b0 &&& 0x80) != 0 then
      if (b0 &&& 0x40) != 0 then
        .error (.sizeOverflow, none, some offset)
      else
        let val := rest.foldl (fun acc b => acc * 256 + b.toNat) (b0 &&& 0x7f).toNat
        if val ≥ limit then
          .error (.sizeOverflow, none, some offset)
        else
          .ok val
    else if raw.all (fun b => b == 0x00 || b == 0x20) then
      if allowAllEmpty then .ok 0
      else .error (.invalidHeader, none, some offset)
    else
      let afterLead := raw.dropWhile (· == 0x20)
      let digits := afterLead.takeWhile (fun b => 0x30 ≤ b && b ≤ 0x37)
      let tail := afterLead.drop digits.length
      if digits.isEmpty then
        .error (.invalidHeader, none, some offset)
      else if !tail.all (fun b => b == 0x20 || b == 0x00) then
        .error (.invalidHeader, none, some offset)
      else
        let val := digits.foldl (fun acc b => acc * 8 + (b.toNat - 0x30)) 0
        if val ≥ limit then
          .error (.sizeOverflow, none, some offset)
        else
          .ok val

/-- Check POSIX USTAR (`"ustar\x00"` + `"00"`) or GNU (`"ustar "` + `" \x00"`) magic/version in a 512-byte header. -/
def hasValidMagicModel (hdr : ByteArray) : Bool :=
  let magic := sliceList hdr 257 263
  let ver := sliceList hdr 263 265
  (magic == [0x75, 0x73, 0x74, 0x61, 0x72, 0x00] && ver == [0x30, 0x30]) ||
  (magic == [0x75, 0x73, 0x74, 0x61, 0x72, 0x20] && ver == [0x20, 0x00])

/-- Parsed PAX per-entry override values from a single `'x'` extended header. -/
structure PaxModelOverrides where
  /-- Overridden entry path (`path`). -/
  path? : Option String := none
  /-- Overridden symlink target (`linkpath`). -/
  linkpath? : Option String := none
  /-- Overridden owner user name (`uname`). -/
  uname? : Option String := none
  /-- Overridden owner group name (`gname`). -/
  gname? : Option String := none
  /-- Overridden payload byte size (`size`). -/
  size? : Option Nat := none
  /-- Overridden modification timestamp (`mtime`). -/
  mtime? : Option Nat := none
  /-- Overridden numeric owner user ID (`uid`). -/
  uid? : Option Nat := none
  /-- Overridden numeric owner group ID (`gid`). -/
  gid? : Option Nat := none

/-- Parse a non-negative ASCII decimal PAX field under `u64Limit`. -/
def parsePaxNatModel (val : String) (offset : Nat) : Except TarErrKey Nat :=
  let cs := val.toList
  if cs.isEmpty then
    .error (.invalidHeader, none, some offset)
  else if cs.head? == some '-' then
    .error (.sizeOverflow, none, some offset)
  else if !cs.all (fun c => '0' ≤ c && c ≤ '9') then
    .error (.invalidHeader, none, some offset)
  else
    let n := cs.foldl (fun acc c => acc * 10 + (c.toNat - '0'.toNat)) 0
    if n ≥ u64Limit then
      .error (.sizeOverflow, none, some offset)
    else
      .ok n

/-- Parse a PAX `mtime` value `<digits>[.<digits>]`, truncating any fraction and bounding under `u64Limit`. -/
def parsePaxMtimeModel (val : String) (offset : Nat) : Except TarErrKey Nat :=
  let cs := val.toList
  if cs.isEmpty then
    .error (.invalidHeader, none, some offset)
  else if cs.head? == some '-' then
    .error (.sizeOverflow, none, some offset)
  else
    let intPart := cs.takeWhile (fun c => '0' ≤ c && c ≤ '9')
    let rest := cs.drop intPart.length
    if intPart.isEmpty then
      .error (.invalidHeader, none, some offset)
    else
      let fracOk :=
        match rest with
        | [] => true
        | '.' :: frac => !frac.isEmpty && frac.all (fun c => '0' ≤ c && c ≤ '9')
        | _ => false
      if !fracOk then
        .error (.invalidHeader, none, some offset)
      else
        let n := intPart.foldl (fun acc c => acc * 10 + (c.toNat - '0'.toNat)) 0
        if n ≥ u64Limit then
          .error (.sizeOverflow, none, some offset)
        else
          .ok n

/-- Parse a strict decimal PAX record byte length without leading `'0'`. -/
def parsePaxLenList (digits : List UInt8) : Option Nat :=
  match digits with
  | [] => none
  | d0 :: _ =>
    if d0 == 0x30 then none
    else if !digits.all (fun b => 0x30 ≤ b && b ≤ 0x39) then none
    else some (digits.foldl (fun acc b => acc * 10 + (b.toNat - 0x30)) 0)

/-- Apply a single validated PAX key-value record to `ov`. -/
def applyPaxKeyModel (ov : PaxModelOverrides) (key val : String) (offset : Nat) :
    Except TarErrKey PaxModelOverrides :=
  if key == "path" then .ok { ov with path? := some val }
  else if key == "linkpath" then .ok { ov with linkpath? := some val }
  else if key == "uname" then
    if hasNulString val then .error (.invalidHeader, none, some offset)
    else .ok { ov with uname? := some val }
  else if key == "gname" then
    if hasNulString val then .error (.invalidHeader, none, some offset)
    else .ok { ov with gname? := some val }
  else if key == "size" then
    (parsePaxNatModel val offset).map fun n => { ov with size? := some n }
  else if key == "uid" then
    (parsePaxNatModel val offset).map fun n => { ov with uid? := some n }
  else if key == "gid" then
    (parsePaxNatModel val offset).map fun n => { ov with gid? := some n }
  else if key == "mtime" then
    (parsePaxMtimeModel val offset).map fun n => { ov with mtime? := some n }
  else
    .ok ov

/-- Parse a single leading `<len> <key>=<value>\n` record from a non-empty PAX byte list, returning remaining bytes. -/
def parsePaxRecordStep (raw : List UInt8) (offset : Nat)
    (seenKeys : List String) (ov : PaxModelOverrides) :
    Except TarErrKey (Nat × String × PaxModelOverrides) :=
  let lenDigits := raw.takeWhile (· != 0x20)
  let afterSp := raw.drop lenDigits.length
  match afterSp with
  | [] => .error (.invalidHeader, none, some offset)
  | _ :: _ =>
    match parsePaxLenList lenDigits with
    | none => .error (.invalidHeader, none, some offset)
    | some recLen =>
      if recLen < 5 then
        .error (.invalidHeader, none, some offset)
      else if recLen > raw.length then
        .error (.invalidHeader, none, some offset)
      else
        let recBytes := raw.take recLen
        if recBytes.getLast? != some 0x0a then
          .error (.invalidHeader, none, some offset)
        else
          let kvBytes := (raw.drop (lenDigits.length + 1)).take (recLen - 1 - (lenDigits.length + 1))
          let keyBytes := kvBytes.takeWhile (· != 0x3d)
          let afterEq := kvBytes.drop keyBytes.length
          match afterEq with
          | [] => .error (.invalidHeader, none, some offset)
          | _ :: valBytes =>
            match String.fromUTF8? (ByteArray.mk keyBytes.toArray),
                  String.fromUTF8? (ByteArray.mk valBytes.toArray) with
            | none, _ | _, none => .error (.invalidEncoding, none, some offset)
            | some key, some val =>
              if key.isEmpty || hasNulString key || key.toList.contains '\n' then
                .error (.invalidHeader, none, some offset)
              else if seenKeys.contains key then
                .error (.invalidHeader, none, some offset)
              else if key.toList.take 11 == "GNU.sparse.".toList then
                .error (.unsupportedEntry, none, some offset)
              else
                match applyPaxKeyModel ov key val offset with
                | .error err => .error err
                | .ok nextOv => .ok (recLen, key, nextOv)

/-- Parse sequential `<len> <key>=<value>\n` records from a PAX `'x'` byte list. -/
def parsePaxRecordsModel (raw : List UInt8) (offset : Nat)
    (seenKeys : List String) (ov : PaxModelOverrides) : Except TarErrKey PaxModelOverrides :=
  match raw with
  | [] => .ok ov
  | b :: bs =>
    match parsePaxRecordStep (b :: bs) offset seenKeys ov with
    | .error err => .error err
    | .ok (recLen, key, nextOv) =>
      if 0 < recLen then
        parsePaxRecordsModel ((b :: bs).drop recLen) offset (key :: seenKeys) nextOv
      else
        .error (.invalidHeader, none, some offset)
termination_by raw.length
decreasing_by
  simp only [List.length_drop, List.length_cons]
  omega

/-- Decoded header fields from a single validated 512-byte USTAR header block. -/
structure HeaderFieldsModel where
  /-- Parsed file mode field `[100..108)`. -/
  mode : Nat
  /-- Parsed numeric user ID field `[108..116)`. -/
  uid : Nat
  /-- Parsed numeric group ID field `[116..124)`. -/
  gid : Nat
  /-- Parsed byte payload size field `[124..136)`. -/
  size : Nat
  /-- Parsed modification timestamp field `[136..148)`. -/
  mtime : Nat
  /-- Typeflag byte at `[156]`. -/
  typeflag : UInt8

/-- Validate checksum, magic/version, and numeric fields of a 512-byte USTAR header block `hdr`. -/
def parseUstarHeaderModel (hdr : ByteArray) (offset : Nat) : Except TarErrKey HeaderFieldsModel := do
  let storedChk ← parseChecksumOctalModel (sliceList hdr 148 156) offset
  if storedChk != ustarChecksum hdr then
    .error (.checksumMismatch, none, some offset)
  else if !hasValidMagicModel hdr then
    .error (.invalidHeader, none, some offset)
  else
    let uMode ← parseUstarNumericModel (sliceList hdr 100 108) offset false u32Limit
    let uUid ← parseUstarNumericModel (sliceList hdr 108 116) offset true u64Limit
    let uGid ← parseUstarNumericModel (sliceList hdr 116 124) offset true u64Limit
    let uSize ← parseUstarNumericModel (sliceList hdr 124 136) offset false u64Limit
    let uMtime ← parseUstarNumericModel (sliceList hdr 136 148) offset true u64Limit
    let typeByte : UInt8 := if h : 156 < hdr.size then hdr[156]'h else 0
    .ok { mode := uMode, uid := uUid, gid := uGid, size := uSize, mtime := uMtime, typeflag := typeByte }

/-- Construct and validate a `TarEntry` from header `hdr` at `offset` plus optional PAX overrides. -/
def decodeTarEntryModel (opts : UnpackOptions) (bytes hdrBlk : ByteArray) (offset : Nat)
    (hdr : HeaderFieldsModel) (pendingPax : Option PaxModelOverrides)
    (seen : List String) (accLen totalBytes : Nat) : Except TarErrKey (TarEntry × Nat) :=
  let kind? : Option EntryKind :=
    if hdr.typeflag == 0x30 || hdr.typeflag == 0x00 then some .regular
    else if hdr.typeflag == 0x35 then some .directory
    else if hdr.typeflag == 0x32 then some .symlink
    else none
  match kind? with
  | none => .error (.unsupportedEntry, none, some offset)
  | some kind =>
    let pax := pendingPax.getD {}
    let effSize := pax.size?.getD hdr.size
    if kind != .regular && effSize != 0 then
      .error (.invalidHeader, none, some offset)
    else if accLen + 1 > opts.maxEntries then
      .error (.resourceLimitExceeded, none, some offset)
    else if totalBytes + effSize > opts.maxTotalBytes then
      .error (.resourceLimitExceeded, none, some offset)
    else
      let padded := pad512 effSize
      if offset + 512 + padded > bytes.size then
        .error (.truncatedArchive, none, some offset)
      else
        let pathRes : Except TarErrKey String :=
          match pax.path? with
          | some p => .ok p
          | none =>
            match decodeCStringList (sliceList hdrBlk 0 100) offset,
                  decodeCStringList (sliceList hdrBlk 345 500) offset with
            | .error e, _ | _, .error e => .error e
            | .ok nm, .ok pfx => .ok (if pfx.isEmpty then nm else pfx ++ "/" ++ nm)
        let linkRes : Except TarErrKey String :=
          match kind with
          | .symlink =>
            match pax.linkpath? with
            | some l => .ok l
            | none => decodeCStringList (sliceList hdrBlk 157 257) offset
          | .regular | .directory => .ok ""
        let unameRes : Except TarErrKey String :=
          match pax.uname? with
          | some u => .ok u
          | none => decodeCStringList (sliceList hdrBlk 265 297) offset
        let gnameRes : Except TarErrKey String :=
          match pax.gname? with
          | some g => .ok g
          | none => decodeCStringList (sliceList hdrBlk 297 329) offset
        match pathRes, linkRes, unameRes, gnameRes with
        | .error e, _, _, _ | _, .error e, _, _ | _, _, .error e, _ | _, _, _, .error e => .error e
        | .ok rawPath, .ok rawLink, .ok uname, .ok gname =>
          match validateEntryPath opts.allowAbsolute opts.allowParentTraversal kind rawPath with
          | .error err => .error (err.kind, err.entryPath, some offset)
          | .ok normPath =>
            let symCheck : Except TarErrKey Unit :=
              match kind with
              | .symlink =>
                match validateSymlinkTarget opts.allowAbsolute opts.allowParentTraversal normPath rawLink with
                | .error err => .error (err.kind, err.entryPath, some offset)
                | .ok () => .ok ()
              | .regular | .directory => .ok ()
            match symCheck with
            | .error err => .error err
            | .ok () =>
              if seen.contains normPath then
                .error (.duplicatePath, some normPath, some offset)
              else
                let payload := bytes.extract (offset + 512) (offset + 512 + effSize)
                let entry : TarEntry :=
                  { path := normPath
                  , kind := kind
                  , mode := (hdr.mode &&& 0o7777).toUInt32
                  , uid := pax.uid?.getD hdr.uid
                  , gid := pax.gid?.getD hdr.gid
                  , mtime := pax.mtime?.getD hdr.mtime
                  , uname := uname
                  , gname := gname
                  , data := payload
                  , linkTarget := rawLink
                  }
                .ok (entry, padded)

/-- Result of processing one 512-byte header block in `unpackStepModel`. -/
inductive UnpackStepModel where
  /-- Valid end-of-archive zero-block trailer reached. -/
  | done
  /-- Parsed PAX `'x'` extended header advancing to `nextOffset`. -/
  | pax (nextOffset : Nat) (ov : PaxModelOverrides)
  /-- Decoded tar entry advancing to `nextOffset`. -/
  | entry (nextOffset : Nat) (e : TarEntry)

/-- Decode one 512-byte block step at `offset` against the pure tar specification. -/
def unpackStepModel (opts : UnpackOptions) (bytes : ByteArray) (offset : Nat)
    (pendingPax : Option PaxModelOverrides) (seen : List String)
    (accLen totalBytes : Nat) : Except TarErrKey UnpackStepModel :=
  if offset ≥ bytes.size then
    .error (.truncatedArchive, none, some offset)
  else if isZeroBlockAt bytes offset then
    if pendingPax.isSome then
      .error (.invalidHeader, none, some offset)
    else if offset + 512 ≥ bytes.size then
      .error (.truncatedArchive, none, some offset)
    else if !isZeroBlockAt bytes (offset + 512) then
      .error (.invalidHeader, none, some (offset + 512))
    else if !isZeroSuffix bytes (offset + 1024) then
      .error (.invalidHeader, none, some (offset + 1024))
    else
      .ok .done
  else if offset + 512 > bytes.size then
    .error (.truncatedArchive, none, some offset)
  else
    let hdrBlk := bytes.extract offset (offset + 512)
    match parseUstarHeaderModel hdrBlk offset with
    | .error err => .error err
    | .ok hdr =>
      if hdr.typeflag == 0x78 then
        if pendingPax.isSome then
          .error (.invalidHeader, none, some offset)
        else if hdr.size > maxPaxHeaderBytes then
          .error (.resourceLimitExceeded, none, some offset)
        else
          let padded := pad512 hdr.size
          let nextOffset := offset + 512 + padded
          if nextOffset > bytes.size then
            .error (.truncatedArchive, none, some offset)
          else
            match parsePaxRecordsModel (sliceList bytes (offset + 512) (offset + 512 + hdr.size)) offset [] {} with
            | .error err => .error err
            | .ok paxOv => .ok (.pax nextOffset paxOv)
      else
        match decodeTarEntryModel opts bytes hdrBlk offset hdr pendingPax seen accLen totalBytes with
        | .error err => .error err
        | .ok (entry, padded) => .ok (.entry (offset + 512 + padded) entry)

/-- Direct-style well-founded tar stream decoder advancing over 512-byte blocks. -/
def unpackStreamModel (opts : UnpackOptions) (bytes : ByteArray) (offset : Nat)
    (pendingPax : Option PaxModelOverrides) (seen : List String)
    (accLen totalBytes : Nat) : Except TarErrKey (List TarEntry) :=
  if offset ≥ bytes.size then
    .error (.truncatedArchive, none, some offset)
  else
    match unpackStepModel opts bytes offset pendingPax seen accLen totalBytes with
    | .error err => .error err
    | .ok .done => .ok []
    | .ok (.pax nextOffset paxOv) =>
      if offset < nextOffset then
        unpackStreamModel opts bytes nextOffset (some paxOv) seen accLen totalBytes
      else
        .error (.invalidHeader, none, some offset)
    | .ok (.entry nextOffset e) =>
      if offset < nextOffset then
        (unpackStreamModel opts bytes nextOffset none (e.path :: seen) (accLen + 1) (totalBytes + e.data.size)).map
          fun rest => e :: rest
      else
        .error (.invalidHeader, none, some offset)
termination_by bytes.size - offset

/-- Reference deserializer model for `LeanSwe.Tar.unpackWith`. -/
def unpackWithModel (opts : UnpackOptions) (bytes : ByteArray) : Except TarErrKey (List TarEntry) :=
  if bytes.size == 0 || bytes.size % 512 != 0 then
    .error (.truncatedArchive, none, none)
  else
    unpackStreamModel opts bytes 0 none [] 0 0

/-- Allowed outcome relation for `LeanSwe.Tar.packWith` against `packWithModel`. -/
def allowedPackWith (opts : PackOptions) (entries : List TarEntry)
    (out : Except TarError ByteArray) : Prop :=
  match out, packWithModel opts entries with
  | .ok bs, .ok mbs => bs = mbs
  | .error e, .error key => tarErrKeyOf e = key ∧ !e.message.isEmpty = true
  | _, _ => False

/-- Allowed outcome relation for `LeanSwe.Tar.pack` against `packWithModel {}`. -/
def allowedPack (entries : List TarEntry) (out : Except TarError ByteArray) : Prop :=
  allowedPackWith {} entries out

/-- Allowed outcome relation for `LeanSwe.Tar.unpackWith` against `unpackWithModel`. -/
def allowedUnpackWith (opts : UnpackOptions) (bytes : ByteArray)
    (out : Except TarError (List TarEntry)) : Prop :=
  match out, unpackWithModel opts bytes with
  | .ok decoded, .ok expected => decoded = expected
  | .error e, .error key => tarErrKeyOf e = key ∧ !e.message.isEmpty = true
  | _, _ => False

/-- Allowed outcome relation for `LeanSwe.Tar.unpack` against `unpackWithModel {}`. -/
def allowedUnpack (bytes : ByteArray) (out : Except TarError (List TarEntry)) : Prop :=
  allowedUnpackWith {} bytes out

end LeanSwe.Tar.Model
