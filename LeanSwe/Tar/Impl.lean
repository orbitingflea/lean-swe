import LeanSwe.Tar.Types
import LeanSwe.Tar.Model

namespace LeanSwe.Tar.Impl

open LeanSwe.Tar
open LeanSwe.Tar.Model

/-- Pad or truncate `bs` to exact byte width `width`, right-padding with `0x00`. -/
def padRightBytes (width : Nat) (bs : ByteArray) : ByteArray :=
  if bs.size ≥ width then bs.extract 0 width
  else bs ++ ByteArray.mk (Array.replicate (width - bs.size) 0)

/-- Sum unsigned byte values over `[start .. start + 512)` treating `[start + 148 .. start + 156)` as `0x20`. -/
def ustarChecksumAt (bytes : ByteArray) (start : Nat) : Nat :=
  go 0 0
where
  /-- Accumulate checksum bytes over `0..512`. -/
  go (idx acc : Nat) : Nat :=
    if idx ≥ 512 then acc
    else
      let b : Nat :=
        if 148 ≤ idx && idx < 156 then 0x20
        else if h : start + idx < bytes.size then (bytes[start + idx]'h).toNat
        else 0
      go (idx + 1) (acc + b)
  termination_by 512 - idx

/-- Construct a 512-byte USTAR header by concatenating exact-width fields. -/
def buildUstarHeader (name : String) (mode : UInt32) (uid gid size mtime : Nat)
    (typeflag : UInt8) (linkname uname gname pfx : String) : ByteArray :=
  let fName := padRightBytes 100 name.toUTF8
  let fMode := padRightBytes 8 (encodeOctalField (mode &&& 0o7777).toNat 7)
  let fUid := padRightBytes 8 (encodeOctalField uid 7)
  let fGid := padRightBytes 8 (encodeOctalField gid 7)
  let fSize := padRightBytes 12 (encodeOctalField size 11)
  let fMtime := padRightBytes 12 (encodeOctalField mtime 11)
  let fChkSpaces := ByteArray.mk (Array.replicate 8 0x20)
  let fType := ByteArray.mk #[typeflag]
  let fLink := padRightBytes 100 linkname.toUTF8
  let fMagic := ByteArray.mk #[0x75, 0x73, 0x74, 0x61, 0x72, 0x00]
  let fVer := ByteArray.mk #[0x30, 0x30]
  let fUname := padRightBytes 32 uname.toUTF8
  let fGname := padRightBytes 32 gname.toUTF8
  let fDev := ByteArray.mk (Array.replicate 16 0)
  let fPrefix := padRightBytes 155 pfx.toUTF8
  let fPad := ByteArray.mk (Array.replicate 12 0)
  let hdrPre := fName ++ fMode ++ fUid ++ fGid ++ fSize ++ fMtime ++ fChkSpaces ++
    fType ++ fLink ++ fMagic ++ fVer ++ fUname ++ fGname ++ fDev ++ fPrefix ++ fPad
  let chk := ustarChecksumAt hdrPre 0
  let fChk := padRightBytes 8 (encodeOctalField chk 6 ++ ByteArray.mk #[0x20])
  fName ++ fMode ++ fUid ++ fGid ++ fSize ++ fMtime ++ fChk ++
    fType ++ fLink ++ fMagic ++ fVer ++ fUname ++ fGname ++ fDev ++ fPrefix ++ fPad

/-- Replace non-ASCII characters with `'?'` and truncate to at most `maxChars` ASCII characters. -/
def asciiFallback (s : String) (maxChars : Nat) : String :=
  String.ofList ((s.toList.take maxChars).map fun c => if c.toNat < 0x80 then c else '?')

/-- Encode a single validated entry into USTAR (and optional PAX `'x'`) tar blocks. -/
def encodeEntryBlocks (e : TarEntry) (normPath : String) : ByteArray :=
  let wp := wirePathOf e.kind normPath
  let typeByte : UInt8 :=
    match e.kind with
    | .regular => 0x30
    | .directory => 0x35
    | .symlink => 0x32
  let entryBlocks :=
    if !needsPax e wp then
      let (pfx, nm) :=
        if wp.toUTF8.size ≤ 100 then ("", wp)
        else
          match findUstarSplit wp with
          | some pair => pair
          | none => ("", wp)
      let hdr := buildUstarHeader nm e.mode e.uid e.gid e.data.size e.mtime typeByte e.linkTarget e.uname e.gname pfx
      hdr ++ padBlock512 e.data
    else
      let paxPayload := buildPaxPayload e wp
      let paxHdr := buildUstarHeader "././@PaxHeader" 0o644 0 0 paxPayload.size 0 0x78 "" "" "" ""
      let (fbPrefix, fbName) :=
        if !pathFitsUstar wp then ("", asciiFallback wp 100)
        else if wp.toUTF8.size ≤ 100 then ("", wp)
        else match findUstarSplit wp with
          | some pair => pair
          | none => ("", asciiFallback wp 100)
      let fbLink := if e.kind == .symlink then asciiFallback e.linkTarget 100 else ""
      let fbUname := asciiFallback e.uname 32
      let fbGname := asciiFallback e.gname 32
      let fbUid := if e.uid < ustarOctal7Limit then e.uid else 0
      let fbGid := if e.gid < ustarOctal7Limit then e.gid else 0
      let fbSize := if e.data.size < ustarOctal11Limit then e.data.size else 0
      let fbMtime := if e.mtime < ustarOctal11Limit then e.mtime else 0
      let hdr := buildUstarHeader fbName e.mode fbUid fbGid fbSize fbMtime typeByte fbLink fbUname fbGname fbPrefix
      paxHdr ++ padBlock512 paxPayload ++ hdr ++ padBlock512 e.data
  entryBlocks

/-- Validate entries left-to-right and serialize them into a USTAR/PAX tar archive. -/
def packWith (opts : PackOptions) (entries : List TarEntry) : Except TarError ByteArray :=
  go entries [] ByteArray.empty
where
  /-- Fold entries left-to-right checking path, symlink, metadata, and duplicate invariants. -/
  go (rest : List TarEntry) (seen : List String) (acc : ByteArray) : Except TarError ByteArray :=
    match rest with
    | [] => .ok (acc ++ zeroBlock ++ zeroBlock)
    | e :: tail =>
      match validateEntryPath opts.allowAbsolute opts.allowParentTraversal e.kind e.path with
      | .error err => .error err
      | .ok normPath =>
        let symCheck : Except TarError Unit :=
          match e.kind with
          | .symlink => validateSymlinkTarget opts.allowAbsolute opts.allowParentTraversal normPath e.linkTarget
          | .regular | .directory => .ok ()
        match symCheck with
        | .error err => .error err
        | .ok () =>
          if e.kind != .regular && e.data.size != 0 then
            .error { kind := .invalidHeader, message := "non-regular tar entry cannot have payload data", entryPath := some e.path }
          else if e.kind != .symlink && e.linkTarget != "" then
            .error { kind := .invalidHeader, message := "non-symlink tar entry cannot have linkTarget", entryPath := some e.path }
          else if hasNulString e.uname || hasNulString e.gname then
            .error { kind := .invalidHeader, message := "uname/gname cannot contain NUL byte", entryPath := some e.path }
          else if e.uid ≥ u64Limit || e.gid ≥ u64Limit || e.mtime ≥ u64Limit || e.data.size ≥ u64Limit then
            .error { kind := .sizeOverflow, message := "tar entry numeric field exceeds 2^64 - 1", entryPath := some e.path }
          else if seen.contains normPath then
            .error { kind := .duplicatePath, message := s!"duplicate tar entry path: {normPath}", entryPath := some normPath }
          else
            let eff := if opts.deterministic then zeroDeterministicMeta e else e
            go tail (normPath :: seen) (acc ++ encodeEntryBlocks eff normPath)

/-- Serialize entries using default `PackOptions`. -/
def pack (entries : List TarEntry) : Except TarError ByteArray :=
  packWith {} entries

/-- Return `true` iff all `len` bytes starting at `offset` in `bytes` are `0x00`. -/
def isZeroRange (bytes : ByteArray) (offset len : Nat) : Bool :=
  go 0
where
  /-- Check byte `offset + i` for `i < len`. -/
  go (i : Nat) : Bool :=
    if i ≥ len then true
    else if h : offset + i < bytes.size then
      if (bytes[offset + i]'h) == 0 then go (i + 1) else false
    else false
  termination_by len - i

/-- Verify all remaining 512-byte blocks from `offset` to `bytes.size` are all-zero. -/
def allZeroTrailer (bytes : ByteArray) (offset : Nat) : Bool :=
  if offset ≥ bytes.size then true
  else isZeroRange bytes offset 512 && allZeroTrailer bytes (offset + 512)
  termination_by bytes.size - offset

/-- Extract bytes `[start .. stop)` up to the first `0x00` byte. -/
def extractCStringBytes (bytes : ByteArray) (start stop : Nat) : ByteArray :=
  let endPos := findNul start
  bytes.extract start endPos
where
  /-- Locate the first `0x00` byte in `[start .. stop)`. -/
  findNul (i : Nat) : Nat :=
    if i ≥ stop then stop
    else if h : i < bytes.size then
      if (bytes[i]'h) == 0 then i else findNul (i + 1)
    else stop
  termination_by stop - i

/-- Decode a NUL-terminated UTF-8 field from `[start .. stop)`. -/
def decodeCStringUtf8 (bytes : ByteArray) (start stop offset : Nat) (fieldName : String) :
    Except TarError String :=
  let slice := extractCStringBytes bytes start stop
  match String.fromUTF8? slice with
  | some s => .ok s
  | none => .error { kind := .invalidEncoding, message := s!"invalid UTF-8 in USTAR {fieldName}", offset := some offset }

/-- Parse strict octal ASCII bytes `[start .. stop)` for `chksum` (no base-256, not all-NUL/space). -/
def parseChecksumOctal (bytes : ByteArray) (start stop offset : Nat) : Except TarError Nat :=
  let raw := (bytes.extract start stop).toList
  let afterLead := raw.dropWhile (· == 0x20)
  let digits := afterLead.takeWhile (fun b => 0x30 ≤ b && b ≤ 0x37)
  let tail := afterLead.drop digits.length
  if digits.isEmpty then
    .error { kind := .invalidHeader, message := "missing octal digits in USTAR checksum", offset := some offset }
  else if !tail.all (fun b => b == 0x20 || b == 0x00) then
    .error { kind := .invalidHeader, message := "invalid trailing byte in USTAR checksum", offset := some offset }
  else
    .ok (digits.foldl (fun acc b => acc * 8 + (b.toNat - 0x30)) 0)

/-- Parse a USTAR numeric field (octal ASCII or base-256) enforcing `limit`. -/
def parseUstarNumeric (bytes : ByteArray) (start stop offset : Nat)
    (allowAllEmpty : Bool) (limit : Nat) (fieldName : String) : Except TarError Nat :=
  let raw := (bytes.extract start stop).toList
  match raw with
  | [] => .error { kind := .invalidHeader, message := s!"empty USTAR {fieldName} field", offset := some offset }
  | b0 :: rest =>
    if (b0 &&& 0x80) != 0 then
      if (b0 &&& 0x40) != 0 then
        .error { kind := .sizeOverflow, message := s!"negative base-256 USTAR {fieldName}", offset := some offset }
      else
        let val := rest.foldl (fun acc b => acc * 256 + b.toNat) (b0 &&& 0x7f).toNat
        if val ≥ limit then
          .error { kind := .sizeOverflow, message := s!"USTAR {fieldName} overflows limit", offset := some offset }
        else
          .ok val
    else if raw.all (fun b => b == 0x00 || b == 0x20) then
      if allowAllEmpty then .ok 0
      else .error { kind := .invalidHeader, message := s!"missing USTAR {fieldName}", offset := some offset }
    else
      let afterLead := raw.dropWhile (· == 0x20)
      let digits := afterLead.takeWhile (fun b => 0x30 ≤ b && b ≤ 0x37)
      let tail := afterLead.drop digits.length
      if digits.isEmpty then
        .error { kind := .invalidHeader, message := s!"malformed octal USTAR {fieldName}", offset := some offset }
      else if !tail.all (fun b => b == 0x20 || b == 0x00) then
        .error { kind := .invalidHeader, message := s!"invalid trailing byte in USTAR {fieldName}", offset := some offset }
      else
        let val := digits.foldl (fun acc b => acc * 8 + (b.toNat - 0x30)) 0
        if val ≥ limit then
          .error { kind := .sizeOverflow, message := s!"USTAR {fieldName} overflows limit", offset := some offset }
        else
          .ok val

/-- Validate USTAR POSIX or GNU magic/version bytes at `[offset + 257 .. offset + 265)`. -/
def hasValidMagic (bytes : ByteArray) (offset : Nat) : Bool :=
  let magic := (bytes.extract (offset + 257) (offset + 263)).toList
  let ver := (bytes.extract (offset + 263) (offset + 265)).toList
  (magic == [0x75, 0x73, 0x74, 0x61, 0x72, 0x00] && ver == [0x30, 0x30]) ||
  (magic == [0x75, 0x73, 0x74, 0x61, 0x72, 0x20] && ver == [0x20, 0x00])

/-- Parsed PAX per-entry overrides from a single `'x'` extended header. -/
structure PaxOverrides where
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
  /-- Overridden user ID (`uid`). -/
  uid? : Option Nat := none
  /-- Overridden group ID (`gid`). -/
  gid? : Option Nat := none

/-- Parse a non-negative ASCII decimal `Nat` (`uid`/`gid`/`size`) under `u64Limit`. -/
def parsePaxNat (val : String) (offset : Nat) (key : String) : Except TarError Nat :=
  let cs := val.toList
  if cs.isEmpty then
    .error { kind := .invalidHeader, message := s!"empty PAX {key}", offset := some offset }
  else if cs.head? == some '-' then
    .error { kind := .sizeOverflow, message := s!"negative PAX {key}", offset := some offset }
  else if !cs.all (fun c => '0' ≤ c && c ≤ '9') then
    .error { kind := .invalidHeader, message := s!"invalid PAX {key} digits", offset := some offset }
  else
    let n := cs.foldl (fun acc c => acc * 10 + (c.toNat - '0'.toNat)) 0
    if n ≥ u64Limit then
      .error { kind := .sizeOverflow, message := s!"PAX {key} overflows 2^64", offset := some offset }
    else
      .ok n

/-- Parse PAX `mtime` as `<digits>[.<digits>]`, returning integer seconds under `u64Limit`. -/
def parsePaxMtime (val : String) (offset : Nat) : Except TarError Nat :=
  let cs := val.toList
  if cs.isEmpty then
    .error { kind := .invalidHeader, message := "empty PAX mtime", offset := some offset }
  else if cs.head? == some '-' then
    .error { kind := .sizeOverflow, message := "negative PAX mtime", offset := some offset }
  else
    let intPart := cs.takeWhile (fun c => '0' ≤ c && c ≤ '9')
    let rest := cs.drop intPart.length
    if intPart.isEmpty then
      .error { kind := .invalidHeader, message := "malformed PAX mtime", offset := some offset }
    else
      let fracOk :=
        match rest with
        | [] => true
        | '.' :: frac => !frac.isEmpty && frac.all (fun c => '0' ≤ c && c ≤ '9')
        | _ => false
      if !fracOk then
        .error { kind := .invalidHeader, message := "malformed PAX mtime fraction", offset := some offset }
      else
        let n := intPart.foldl (fun acc c => acc * 10 + (c.toNat - '0'.toNat)) 0
        if n ≥ u64Limit then
          .error { kind := .sizeOverflow, message := "PAX mtime overflows 2^64", offset := some offset }
        else
          .ok n

/-- Locate index of byte `target` in `bs` starting at `idx` up to `stop`. -/
def findByteIn (bs : ByteArray) (target : UInt8) (idx stop : Nat) : Option Nat :=
  if idx ≥ stop then none
  else if h : idx < bs.size then
    if (bs[idx]'h) == target then some idx else findByteIn bs target (idx + 1) stop
  else none
  termination_by stop - idx

/-- Parse a decimal ASCII PAX record length without leading `'0'`. -/
def parsePaxLen (bs : ByteArray) (start stop : Nat) : Option Nat :=
  if start ≥ stop then none
  else
    let digits := (bs.extract start stop).toList
    match digits with
    | [] => none
    | d0 :: _ =>
      if d0 == 0x30 then none
      else if !digits.all (fun b => 0x30 ≤ b && b ≤ 0x39) then none
      else some (digits.foldl (fun acc b => acc * 10 + (b.toNat - 0x30)) 0)

/-- Return `true` iff `s` starts with prefix `pfx`. -/
def startsWithStr (s pfx : String) : Bool :=
  s.toList.take pfx.toList.length == pfx.toList

/-- Apply a single validated PAX key-value record to `ov`. -/
def applyPaxKey (ov : PaxOverrides) (key val : String) (offset : Nat) : Except TarError PaxOverrides :=
  if key == "path" then .ok { ov with path? := some val }
  else if key == "linkpath" then .ok { ov with linkpath? := some val }
  else if key == "uname" then
    if hasNulString val then
      .error { kind := .invalidHeader, message := "NUL byte in PAX uname", offset := some offset }
    else
      .ok { ov with uname? := some val }
  else if key == "gname" then
    if hasNulString val then
      .error { kind := .invalidHeader, message := "NUL byte in PAX gname", offset := some offset }
    else
      .ok { ov with gname? := some val }
  else if key == "size" then
    (parsePaxNat val offset "size").map fun n => { ov with size? := some n }
  else if key == "uid" then
    (parsePaxNat val offset "uid").map fun n => { ov with uid? := some n }
  else if key == "gid" then
    (parsePaxNat val offset "gid").map fun n => { ov with gid? := some n }
  else if key == "mtime" then
    (parsePaxMtime val offset).map fun n => { ov with mtime? := some n }
  else
    .ok ov

/-- Parse all `<len> <key>=<value>\n` records from a PAX `'x'` payload. -/
def parsePaxPayload (pax : ByteArray) (offset : Nat) : Except TarError PaxOverrides :=
  go 0 [] {}
where
  /-- Decode records sequentially from byte index `pos`. -/
  go (pos : Nat) (seenKeys : List String) (ov : PaxOverrides) : Except TarError PaxOverrides :=
    if pos ≥ pax.size then .ok ov
    else
      match findByteIn pax 0x20 pos pax.size with
      | none =>
        .error { kind := .invalidHeader, message := "missing space in PAX record", offset := some offset }
      | some spIdx =>
        match parsePaxLen pax pos spIdx with
        | none =>
          .error { kind := .invalidHeader, message := "invalid PAX record length", offset := some offset }
        | some recLen =>
          if recLen < 5 then
            .error { kind := .invalidHeader, message := "PAX record length < 5", offset := some offset }
          else if pos + recLen > pax.size then
            .error { kind := .invalidHeader, message := "out-of-bounds PAX record length", offset := some offset }
          else
            let recEnd := pos + recLen
            let hasNl :=
              if h : recEnd - 1 < pax.size then (pax[recEnd - 1]'h) == 0x0a else false
            if !hasNl then
              .error { kind := .invalidHeader, message := "PAX record missing trailing newline", offset := some offset }
            else
              match findByteIn pax 0x3d (spIdx + 1) (recEnd - 1) with
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
                    | .ok nextOv => go recEnd (key :: seenKeys) nextOv
  termination_by pax.size - pos
  decreasing_by
    simp_wf
    omega

/-- Decoded header fields from a single validated 512-byte USTAR block. -/
structure UstarHeaderFields where
  /-- Masked or raw mode parsed from `[100..108)`. -/
  mode : Nat
  /-- Numeric UID parsed from `[108..116)`. -/
  uid : Nat
  /-- Numeric GID parsed from `[116..124)`. -/
  gid : Nat
  /-- Payload size parsed from `[124..136)`. -/
  size : Nat
  /-- Modification timestamp parsed from `[136..148)`. -/
  mtime : Nat
  /-- Entry typeflag byte at `[156]`. -/
  typeflag : UInt8

/-- Validate checksum, magic/version, and numeric fields of a non-zero 512-byte header block at `offset`. -/
def parseUstarHeader (bytes : ByteArray) (offset : Nat) : Except TarError UstarHeaderFields :=
  match parseChecksumOctal bytes (offset + 148) (offset + 156) offset with
  | .error err => .error err
  | .ok storedChk =>
    if storedChk != ustarChecksumAt bytes offset then
      .error { kind := .checksumMismatch, message := "USTAR header checksum mismatch", offset := some offset }
    else if !hasValidMagic bytes offset then
      .error { kind := .invalidHeader, message := "invalid USTAR magic or version", offset := some offset }
    else
      match parseUstarNumeric bytes (offset + 100) (offset + 108) offset false u32Limit "mode" with
      | .error e => .error e
      | .ok uMode =>
        match parseUstarNumeric bytes (offset + 108) (offset + 116) offset true u64Limit "uid" with
        | .error e => .error e
        | .ok uUid =>
          match parseUstarNumeric bytes (offset + 116) (offset + 124) offset true u64Limit "gid" with
          | .error e => .error e
          | .ok uGid =>
            match parseUstarNumeric bytes (offset + 124) (offset + 136) offset false u64Limit "size" with
            | .error e => .error e
            | .ok uSize =>
              match parseUstarNumeric bytes (offset + 136) (offset + 148) offset true u64Limit "mtime" with
              | .error e => .error e
              | .ok uMtime =>
                let typeByte : UInt8 := if h : offset + 156 < bytes.size then bytes[offset + 156]'h else 0
                .ok { mode := uMode, uid := uUid, gid := uGid, size := uSize, mtime := uMtime, typeflag := typeByte }

/-- Construct and validate a `TarEntry` from a non-`'x'` USTAR header and optional PAX overrides. -/
def decodeTarEntry (opts : UnpackOptions) (bytes : ByteArray) (offset : Nat)
    (hdr : UstarHeaderFields) (pendingPax : Option PaxOverrides)
    (seen : List String) (accLen totalBytes : Nat) : Except TarError (TarEntry × Nat) :=
  let kind? : Option EntryKind :=
    if hdr.typeflag == 0x30 || hdr.typeflag == 0x00 then some .regular
    else if hdr.typeflag == 0x35 then some .directory
    else if hdr.typeflag == 0x32 then some .symlink
    else none
  match kind? with
  | none =>
    .error { kind := .unsupportedEntry, message := s!"unsupported tar entry typeflag: {hdr.typeflag.toNat}", offset := some offset }
  | some kind =>
    let pax := pendingPax.getD {}
    let effSize := pax.size?.getD hdr.size
    if kind != .regular && effSize != 0 then
      .error { kind := .invalidHeader, message := "non-regular tar entry has non-zero size", offset := some offset }
    else if accLen + 1 > opts.maxEntries then
      .error { kind := .resourceLimitExceeded, message := "tar archive exceeds maxEntries limit", offset := some offset }
    else if totalBytes + effSize > opts.maxTotalBytes then
      .error { kind := .resourceLimitExceeded, message := "tar archive exceeds maxTotalBytes limit", offset := some offset }
    else
      let padded := pad512 effSize
      if offset + 512 + padded > bytes.size then
        .error { kind := .truncatedArchive, message := "truncated tar entry payload", offset := some offset }
      else
        let pathRes : Except TarError String :=
          match pax.path? with
          | some p => .ok p
          | none =>
            match decodeCStringUtf8 bytes offset (offset + 100) offset "name",
                  decodeCStringUtf8 bytes (offset + 345) (offset + 500) offset "prefix" with
            | .error e, _ | _, .error e => .error e
            | .ok nm, .ok pfx => .ok (if pfx.isEmpty then nm else pfx ++ "/" ++ nm)
        let linkRes : Except TarError String :=
          match kind with
          | .symlink =>
            match pax.linkpath? with
            | some l => .ok l
            | none => decodeCStringUtf8 bytes (offset + 157) (offset + 257) offset "linkname"
          | .regular | .directory => .ok ""
        let unameRes : Except TarError String :=
          match pax.uname? with
          | some u => .ok u
          | none => decodeCStringUtf8 bytes (offset + 265) (offset + 297) offset "uname"
        let gnameRes : Except TarError String :=
          match pax.gname? with
          | some g => .ok g
          | none => decodeCStringUtf8 bytes (offset + 297) (offset + 329) offset "gname"
        match pathRes, linkRes, unameRes, gnameRes with
        | .error e, _, _, _ | _, .error e, _, _ | _, _, .error e, _ | _, _, _, .error e => .error e
        | .ok rawPath, .ok rawLink, .ok uname, .ok gname =>
          match validateEntryPath opts.allowAbsolute opts.allowParentTraversal kind rawPath with
          | .error err => .error { err with offset := some offset }
          | .ok normPath =>
            let symCheck : Except TarError Unit :=
              match kind with
              | .symlink => validateSymlinkTarget opts.allowAbsolute opts.allowParentTraversal normPath rawLink
              | .regular | .directory => .ok ()
            match symCheck with
            | .error err => .error { err with offset := some offset }
            | .ok () =>
              if seen.contains normPath then
                .error { kind := .duplicatePath, message := s!"duplicate tar entry path: {normPath}", entryPath := some normPath, offset := some offset }
              else
                let payload := if effSize == 0 then ByteArray.empty else bytes.extract (offset + 512) (offset + 512 + effSize)
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

/-- Result of processing one 512-byte header (plus its payload/PAX block) during `unpackWith`. -/
inductive UnpackStep where
  /-- Archive reached valid end-of-archive trailer and produced final entries. -/
  | done (entries : List TarEntry)
  /-- Continue unpacking at `nextOffset` with updated state. -/
  | cont (nextOffset : Nat) (pendingPax : Option PaxOverrides) (seen : List String)
      (acc : List TarEntry) (totalBytes : Nat)

/-- Process a single 512-byte tar block (header + payload/PAX or trailer) at `offset`. -/
def unpackStep (opts : UnpackOptions) (bytes : ByteArray) (offset : Nat)
    (pendingPax : Option PaxOverrides) (seen : List String)
    (acc : List TarEntry) (totalBytes : Nat) : Except TarError UnpackStep :=
  if offset ≥ bytes.size then
    .error { kind := .truncatedArchive, message := "tar archive missing end-of-archive zero blocks", offset := some offset }
  else if isZeroRange bytes offset 512 then
    if pendingPax.isSome then
      .error { kind := .invalidHeader, message := "dangling PAX header before zero block", offset := some offset }
    else if offset + 512 ≥ bytes.size then
      .error { kind := .truncatedArchive, message := "tar archive has only one trailing zero block", offset := some offset }
    else if !isZeroRange bytes (offset + 512) 512 then
      .error { kind := .invalidHeader, message := "non-zero block after single zero block", offset := some (offset + 512) }
    else if !allZeroTrailer bytes (offset + 1024) then
      .error { kind := .invalidHeader, message := "non-zero garbage after tar end-of-archive marker", offset := some (offset + 1024) }
    else
      .ok (.done acc.reverse)
  else if offset + 512 > bytes.size then
    .error { kind := .truncatedArchive, message := "truncated tar header block", offset := some offset }
  else
    match parseUstarHeader bytes offset with
    | .error err => .error err
    | .ok hdr =>
      if hdr.typeflag == 0x78 then
        if pendingPax.isSome then
          .error { kind := .invalidHeader, message := "consecutive PAX 'x' headers are not allowed", offset := some offset }
        else if hdr.size > maxPaxHeaderBytes then
          .error { kind := .resourceLimitExceeded, message := "PAX header exceeds maxPaxHeaderBytes", offset := some offset }
        else
          let padded := pad512 hdr.size
          let nextOffset := offset + 512 + padded
          if nextOffset > bytes.size then
            .error { kind := .truncatedArchive, message := "truncated PAX extended header payload", offset := some offset }
          else
            let paxBytes := bytes.extract (offset + 512) (offset + 512 + hdr.size)
            match parsePaxPayload paxBytes offset with
            | .error err => .error err
            | .ok paxOv => .ok (.cont nextOffset (some paxOv) seen acc totalBytes)
      else
        match decodeTarEntry opts bytes offset hdr pendingPax seen acc.length totalBytes with
        | .error err => .error err
        | .ok (entry, padded) =>
          .ok (.cont (offset + 512 + padded) none (entry.path :: seen) (entry :: acc) (totalBytes + entry.data.size))

/-- Loop `unpackStep` until `.done` or error. -/
def unpackLoop (opts : UnpackOptions) (bytes : ByteArray) (offset : Nat)
    (pendingPax : Option PaxOverrides) (seen : List String)
    (acc : List TarEntry) (totalBytes : Nat) : Except TarError (List TarEntry) :=
  if offset ≥ bytes.size then
    .error { kind := .truncatedArchive, message := "tar archive missing end-of-archive zero blocks", offset := some offset }
  else
    match unpackStep opts bytes offset pendingPax seen acc totalBytes with
    | .error err => .error err
    | .ok (.done res) => .ok res
    | .ok (.cont nextOffset nextPax nextSeen nextAcc nextTotal) =>
      if nextOffset > offset then
        unpackLoop opts bytes nextOffset nextPax nextSeen nextAcc nextTotal
      else
        .error { kind := .invalidHeader, message := "invalid tar block advance", offset := some offset }
termination_by bytes.size - offset
decreasing_by
  simp_wf
  omega

/-- Deserialize a USTAR/PAX tar byte array enforcing options and safety limits. -/
def unpackWith (opts : UnpackOptions) (bytes : ByteArray) : Except TarError (List TarEntry) :=
  if bytes.size == 0 || bytes.size % 512 != 0 then
    .error { kind := .truncatedArchive, message := "tar archive is empty or not 512-byte aligned" }
  else
    unpackLoop opts bytes 0 none [] [] 0

/-- Deserialize a tar archive using default `UnpackOptions`. -/
def unpack (bytes : ByteArray) : Except TarError (List TarEntry) :=
  unpackWith {} bytes

/-- Default `TarApi` record wired to the pure `LeanSwe.Tar.Impl` functions. -/
def makeTarApi : TarApi :=
  { pack := pack
  , packWith := packWith
  , unpack := unpack
  , unpackWith := unpackWith
  }

end LeanSwe.Tar.Impl
