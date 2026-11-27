import LeanSwe.Tar.Types

namespace LeanSwe.Tar.Model

open LeanSwe.Tar

/-- Upper exclusive bound for 64-bit unsigned metadata fields (`2^64`). -/
def u64Limit : Nat := 18446744073709551616

/-- Upper exclusive bound for 32-bit unsigned mode fields (`2^32`). -/
def u32Limit : Nat := 4294967296

/-- Upper exclusive bound for USTAR 7-digit octal fields `uid` and `gid` (`2^21`). -/
def ustarOctal7Limit : Nat := 2097152

/-- Upper exclusive bound for USTAR 11-digit octal fields `size` and `mtime` (`2^33`). -/
def ustarOctal11Limit : Nat := 8589934592

/-- Round byte count `n` up to the next 512-byte tar block boundary. -/
def pad512 (n : Nat) : Nat :=
  ((n + 511) / 512) * 512

/-- Sum of `entry.data.size` over a list of tar entries. -/
def totalDataBytes (es : List TarEntry) : Nat :=
  es.foldl (fun acc e => acc + e.data.size) 0

/-- Zero non-deterministic metadata fields (`uid`, `gid`, `mtime`, `uname`, `gname`). -/
def zeroDeterministicMeta (e : TarEntry) : TarEntry :=
  { e with uid := 0, gid := 0, mtime := 0, uname := "", gname := "" }

/-- Return `true` iff `cs` contains a NUL character (`Char.ofNat 0`). -/
def hasNulChars : List Char → Bool
  | [] => false
  | c :: cs => c == Char.ofNat 0 || hasNulChars cs

/-- Return `true` iff `s` contains a NUL character (`'\x00'`). -/
def hasNulString (s : String) : Bool :=
  hasNulChars s.toList

/-- Return `true` iff every byte in `s.toUTF8` is pure 7-bit ASCII (`< 0x80`). -/
def isAsciiString (s : String) : Bool :=
  s.toUTF8.toList.all (fun b => b < 0x80)

/-- Split `cs` on `'/'` into `'/'`-separated character segments (`""` yields `[]`). -/
def splitSlashChars : List Char → List (List Char)
  | [] => []
  | cs => go [] cs
where
  /-- Accumulate the current segment in reverse order until `'/'` or end of list. -/
  go (acc : List Char) : List Char → List (List Char)
    | [] => [acc.reverse]
    | '/' :: rest => acc.reverse :: go [] rest
    | c :: rest => go (c :: acc) rest

/-- Strip all trailing `'/'` characters from `cs`. -/
def stripTrailingSlashesChars (cs : List Char) : List Char :=
  (cs.reverse.dropWhile (· == '/')).reverse

/-- Compute canonical normalized tar path for a valid entry (preserving single leading `'/'` and stripping trailing `'/'` on directories). -/
def normalizeTarPath (kind : EntryKind) (path : String) : String :=
  match kind with
  | .directory => String.ofList (stripTrailingSlashesChars path.toList)
  | .regular => path
  | .symlink => path

/-- Return `true` iff `cs` has no empty, `"."`, or `".."` segments when split on `'/'` (after optional single leading `'/'` stripped). -/
def checkSegments (allowParentTraversal : Bool) (segs : List (List Char)) :
    Except TarError Unit :=
  match segs with
  | [] => .error { kind := .invalidPath, message := "empty tar entry path" }
  | _ => go segs
where
  /-- Inspect each segment for empty, `"."`, and `".."` violations. -/
  go : List (List Char) → Except TarError Unit
    | [] => .ok ()
    | seg :: rest =>
      if seg.isEmpty then
        .error { kind := .invalidPath, message := "empty path segment in tar entry path" }
      else if seg == ['.'] then
        .error { kind := .unsafePath, message := "'.' path segment is not allowed" }
      else if seg == ['.', '.'] && !allowParentTraversal then
        .error { kind := .unsafePath, message := "'..' path segment is not allowed" }
      else
        go rest

/-- Validate and normalize an entry path in exact 5-step precedence. -/
def validateEntryPath (allowAbsolute allowParentTraversal : Bool)
    (kind : EntryKind) (path : String) : Except TarError String :=
  let cs := path.toList
  if hasNulChars cs then
    .error { kind := .invalidPath, message := "tar path contains NUL byte", entryPath := some path }
  else if cs.isEmpty then
    .error { kind := .invalidPath, message := "tar path is empty", entryPath := some path }
  else
    let startsSlash := cs.head? == some '/'
    if startsSlash && !allowAbsolute then
      .error { kind := .unsafePath, message := "absolute tar path is not allowed", entryPath := some path }
    else
      let normChars? : Except TarError (List Char) :=
        match kind with
        | .directory =>
          let stripped := stripTrailingSlashesChars cs
          if stripped.isEmpty then
            .error { kind := .invalidPath, message := "directory tar path cannot be root-only", entryPath := some path }
          else
            .ok stripped
        | .regular | .symlink =>
          if cs.reverse.head? == some '/' then
            .error { kind := .invalidPath, message := "non-directory tar path cannot end with '/'", entryPath := some path }
          else
            .ok cs
      match normChars? with
      | .error e => .error e
      | .ok normChars =>
        let relChars := match normChars with | '/' :: rest => rest | other => other
        let segs := splitSlashChars relChars
        match checkSegments allowParentTraversal segs with
        | .error e => .error { e with entryPath := some path }
        | .ok () => .ok (String.ofList normChars)

/-- Return `true` iff `path` is a safe canonical relative path under default policy (`allowAbsolute = false`, `allowParentTraversal = false`). -/
def isSafeRelPath (kind : EntryKind) (path : String) : Bool :=
  match validateEntryPath false false kind path with
  | .ok _ => true
  | .error _ => false

/-- Validate a symbolic link target against `entryPath` and policy flags. -/
def validateSymlinkTarget (allowAbsolute allowParentTraversal : Bool)
    (entryPath linkTarget : String) : Except TarError Unit :=
  let targetCs := linkTarget.toList
  if targetCs.isEmpty then
    .error { kind := .invalidPath, message := "symlink target is empty", entryPath := some entryPath }
  else if hasNulChars targetCs then
    .error { kind := .invalidPath, message := "symlink target contains NUL byte", entryPath := some entryPath }
  else
    let startsSlash := targetCs.head? == some '/'
    if startsSlash && !allowAbsolute then
      .error { kind := .unsafePath, message := "absolute symlink target is not allowed", entryPath := some entryPath }
    else if allowParentTraversal then
      .ok ()
    else
      let normEntry := match entryPath.toList with | '/' :: rest => rest | other => other
      let entrySegs := splitSlashChars normEntry
      let parentDepth := entrySegs.length - 1
      let targetSegs := splitSlashChars (match targetCs with | '/' :: rest => rest | other => other)
      walkDepth parentDepth targetSegs
where
  /-- Walk `linkTarget` segments from `parentDepth`, failing immediately if `".."` escapes above depth `0`. -/
  walkDepth (depth : Nat) : List (List Char) → Except TarError Unit
    | [] => .ok ()
    | seg :: rest =>
      if seg.isEmpty || seg == ['.'] then
        walkDepth depth rest
      else if seg == ['.', '.'] then
        if depth == 0 then
          .error { kind := .unsafePath, message := "symlink target escapes archive root", entryPath := some entryPath }
        else
          walkDepth (depth - 1) rest
      else
        walkDepth (depth + 1) rest

/-- Computable single-entry validity check parameterized by `allowAbsolute` and `allowParentTraversal`. -/
def validEntryBool (allowAbsolute allowParentTraversal : Bool) (e : TarEntry) : Bool :=
  match validateEntryPath allowAbsolute allowParentTraversal e.kind e.path with
  | .error _ => false
  | .ok normPath =>
    let symOk :=
      match e.kind with
      | .symlink =>
        match validateSymlinkTarget allowAbsolute allowParentTraversal normPath e.linkTarget with
        | .ok () => true
        | .error _ => false
      | .regular | .directory => e.linkTarget == ""
    let dataOk :=
      match e.kind with
      | .regular => true
      | .directory | .symlink => e.data.size == 0
    let metaOk :=
      !hasNulString e.uname &&
      !hasNulString e.gname &&
      e.uid < u64Limit &&
      e.gid < u64Limit &&
      e.mtime < u64Limit &&
      e.data.size < u64Limit
    symOk && dataOk && metaOk

/-- Propositional single-entry validity predicate. -/
def ValidEntry (allowAbsolute allowParentTraversal : Bool) (e : TarEntry) : Prop :=
  validEntryBool allowAbsolute allowParentTraversal e = true

/-- Computable check that normalized paths in `es` are pairwise distinct. -/
def noDupNormalizedPathsBool (es : List TarEntry) : Bool :=
  go [] es
where
  /-- Track previously seen normalized paths in `seen`. -/
  go (seen : List String) : List TarEntry → Bool
    | [] => true
    | e :: rest =>
      let np := normalizeTarPath e.kind e.path
      !seen.contains np && go (np :: seen) rest

/-- Computable archive validity check parameterized by `allowAbsolute` and `allowParentTraversal`. -/
def validArchiveBool (allowAbsolute allowParentTraversal : Bool) (es : List TarEntry) : Bool :=
  es.all (validEntryBool allowAbsolute allowParentTraversal) && noDupNormalizedPathsBool es

/-- Propositional archive validity predicate. -/
def ValidArchive (allowAbsolute allowParentTraversal : Bool) (es : List TarEntry) : Prop :=
  validArchiveBool allowAbsolute allowParentTraversal es = true

/-- Computable canonical equivalence between two `TarEntry` values. -/
def entryEquivBool (a b : TarEntry) : Bool :=
  normalizeTarPath a.kind a.path == normalizeTarPath b.kind b.path &&
  a.kind == b.kind &&
  (a.mode &&& 0o7777) == (b.mode &&& 0o7777) &&
  a.uid == b.uid &&
  a.gid == b.gid &&
  a.mtime == b.mtime &&
  a.uname == b.uname &&
  a.gname == b.gname &&
  a.data.toList == b.data.toList &&
  (if a.kind == .symlink then a.linkTarget else "") ==
    (if b.kind == .symlink then b.linkTarget else "")

/-- Canonical archive equivalence up to normalized path, masked `0o7777` mode, and non-symlink `linkTarget` clearing. -/
def TarEquiv : List TarEntry → List TarEntry → Prop
  | [], [] => True
  | a :: xs, b :: ys => entryEquivBool a b = true ∧ TarEquiv xs ys
  | _, _ => False

/-- Wire path emitted for an entry (`normPath ++ "/"` for directories, `normPath` otherwise). -/
def wirePathOf (kind : EntryKind) (normPath : String) : String :=
  match kind with
  | .directory => normPath ++ "/"
  | .regular | .symlink => normPath

/-- Find a valid USTAR split `(prefix, name)` at `'/'` with `1 ≤ prefix.bytes ≤ 155` and `1 ≤ name.bytes ≤ 100`. -/
def findUstarSplit (wirePath : String) : Option (String × String) :=
  let cs := wirePath.toList
  go [] cs
where
  /-- Scan `'/'` boundaries left-to-right for the first valid `(prefix, name)` USTAR split. -/
  go (revPrefix : List Char) : List Char → Option (String × String)
    | [] => none
    | '/' :: rest =>
      let pfx := String.ofList revPrefix.reverse
      let nm := String.ofList rest
      if !pfx.isEmpty && !nm.isEmpty && pfx.toUTF8.size ≤ 155 && nm.toUTF8.size ≤ 100 then
        some (pfx, nm)
      else
        go ('/' :: revPrefix) rest
    | c :: rest => go (c :: revPrefix) rest

/-- Return `true` iff `wirePath` fits in pure USTAR (`name ≤ 100` or valid `prefix`/`name` split) and is ASCII. -/
def pathFitsUstar (wirePath : String) : Bool :=
  isAsciiString wirePath &&
  (wirePath.toUTF8.size ≤ 100 || (findUstarSplit wirePath).isSome)

/-- Return `true` iff an entry requires a PAX `'x'` extended header for any field. -/
def needsPax (e : TarEntry) (wirePath : String) : Bool :=
  !pathFitsUstar wirePath ||
  !isAsciiString e.linkTarget || e.linkTarget.toUTF8.size > 100 ||
  !isAsciiString e.uname || e.uname.toUTF8.size > 32 ||
  !isAsciiString e.gname || e.gname.toUTF8.size > 32 ||
  e.uid ≥ ustarOctal7Limit ||
  e.gid ≥ ustarOctal7Limit ||
  e.data.size ≥ ustarOctal11Limit ||
  e.mtime ≥ ustarOctal11Limit

/-- Compute decimal ASCII digits count for a positive `Nat`. -/
def decDigitsLen (n : Nat) : Nat :=
  (toString n).toUTF8.size

/-- Fixed-point total PAX record byte length `<len> <key>=<value>\n` given `kvBodyLen` (`(" " ++ key ++ "=" ++ val ++ "\n").toUTF8.size`). -/
def paxRecordTotalLen (kvBodyLen : Nat) : Nat :=
  go 1 20
where
  /-- Search for the fixed point `len = decDigitsLen len + kvBodyLen`. -/
  go (digits : Nat) : Nat → Nat
    | 0 => digits + kvBodyLen
    | fuel + 1 =>
      let cand := digits + kvBodyLen
      let actual := decDigitsLen cand
      if actual == digits then cand else go actual fuel

/-- Encode a single UTF-8 PAX extended header record `"<len> <key>=<value>\n"`. -/
def encodePaxRecord (key value : String) : ByteArray :=
  let suffix := " " ++ key ++ "=" ++ value ++ "\n"
  let totalLen := paxRecordTotalLen suffix.toUTF8.size
  (toString totalLen ++ suffix).toUTF8

/-- Encode all PAX `'x'` records needed for an entry whose wire path is `wirePath`. -/
def buildPaxPayload (e : TarEntry) (wirePath : String) : ByteArray :=
  let rPath := if !pathFitsUstar wirePath then encodePaxRecord "path" wirePath else ByteArray.empty
  let rLink :=
    if e.kind == .symlink && (!isAsciiString e.linkTarget || e.linkTarget.toUTF8.size > 100) then
      encodePaxRecord "linkpath" e.linkTarget
    else
      ByteArray.empty
  let rUname :=
    if !isAsciiString e.uname || e.uname.toUTF8.size > 32 then
      encodePaxRecord "uname" e.uname
    else
      ByteArray.empty
  let rGname :=
    if !isAsciiString e.gname || e.gname.toUTF8.size > 32 then
      encodePaxRecord "gname" e.gname
    else
      ByteArray.empty
  let rSize := if e.data.size ≥ ustarOctal11Limit then encodePaxRecord "size" (toString e.data.size) else ByteArray.empty
  let rMtime := if e.mtime ≥ ustarOctal11Limit then encodePaxRecord "mtime" (toString e.mtime) else ByteArray.empty
  let rUid := if e.uid ≥ ustarOctal7Limit then encodePaxRecord "uid" (toString e.uid) else ByteArray.empty
  let rGid := if e.gid ≥ ustarOctal7Limit then encodePaxRecord "gid" (toString e.gid) else ByteArray.empty
  rPath ++ rLink ++ rUname ++ rGname ++ rSize ++ rMtime ++ rUid ++ rGid

/-- Return `true` iff the entry's encoded PAX `'x'` header payload (if needed) fits `maxPaxHeaderBytes`. -/
def fitsPaxLimit (e : TarEntry) : Bool :=
  let np := normalizeTarPath e.kind e.path
  let wp := wirePathOf e.kind np
  if needsPax e wp then (buildPaxPayload e wp).size ≤ maxPaxHeaderBytes else true

/-- Compute unsigned USTAR checksum of a 512-byte header block (treating bytes `[148..156)` as `0x20`). -/
def ustarChecksum (hdr : ByteArray) : Nat :=
  go 0 0
where
  /-- Sum unsigned byte values over `[0..512)`. -/
  go (idx acc : Nat) : Nat :=
    if idx ≥ 512 then
      acc
    else
      let b : Nat :=
        if 148 ≤ idx && idx < 156 then 0x20
        else if h : idx < hdr.size then (hdr[idx]'h).toNat
        else 0
      go (idx + 1) (acc + b)
  termination_by 512 - idx

/-- Return a 512-byte all-zero block. -/
def zeroBlock : ByteArray :=
  ByteArray.mk (Array.replicate 512 0)

/-- Write a `ByteArray` slice `src` into `dst` starting at `offset` up to `width` bytes. -/
def blitFixed (dst : ByteArray) (offset width : Nat) (src : ByteArray) : ByteArray :=
  go 0 dst
where
  /-- Copy byte-by-byte up to `min width src.size`. -/
  go (i : Nat) (buf : ByteArray) : ByteArray :=
    if i ≥ width then
      buf
    else if hSrc : i < src.size then
      let idx := offset + i
      if idx < buf.size then
        go (i + 1) (buf.set! idx (src[i]'hSrc))
      else
        buf
    else
      buf
  termination_by width - i

/-- Encode `val` as `digits` zero-padded lowercase octal ASCII bytes followed by `0x00`. -/
def encodeOctalField (val digits : Nat) : ByteArray :=
  let rec loop (k v : Nat) (acc : List UInt8) : List UInt8 :=
    match k with
    | 0 => acc
    | k' + 1 =>
      let d : UInt8 := UInt8.ofNat (0x30 + (v % 8))
      loop k' (v / 8) (d :: acc)
  ByteArray.mk ((loop digits val [0]).toArray)

/-- Build a 512-byte USTAR header block with computed unsigned checksum. -/
def mkUstarHeader (name : String) (mode : UInt32) (uid gid size mtime : Nat)
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
  let b13 := blitFixed b12 345 155 pfx.toUTF8
  let chk := ustarChecksum b13
  let chkField := encodeOctalField chk 6 ++ ByteArray.mk #[0x20]
  blitFixed b13 148 8 chkField

/-- Pad a `ByteArray` with `0x00` bytes to a 512-byte boundary. -/
def padBlock512 (bs : ByteArray) : ByteArray :=
  let rem := bs.size % 512
  if rem == 0 then bs
  else bs ++ ByteArray.mk (Array.replicate (512 - rem) 0)

end LeanSwe.Tar.Model
