import LeanSwe.LinuxSyscall.Net.Model.Addr

namespace LeanSwe.LinuxSyscall.Net

open LeanSwe.LinuxSyscall

/-- Pure Lean wrapper pre-check shared by `Net/Impl.lean`, `reachesKernelSyscall`, and `stepNetCore`. -/
def preCheckNet : NetReq → Option Errno
  | .socket dom st _ proto => validateSocketArgs dom st proto
  | .socketpair dom st _ => validateSocketpairArgs dom st
  | .bind _ addr | .connect _ addr => if addr.isValidTarget then none else some Errno.EINVAL
  | .sendmsg _ fds => if isValidScmCount fds.size then none else some Errno.EINVAL
  | .recvmsg _ maxFds => if isValidScmCount maxFds.toNat then none else some Errno.EINVAL
  | .ioctl _ _ ifname => if isValidIfname ifname then none else some Errno.EINVAL
  | _ => none

/-- Returns `true` iff `req` passes pure Lean wrapper checks and reaches a kernel net syscall entry. -/
def reachesKernelSyscall (s : NetState) (req : NetReq) : Bool :=
  (preCheckNet req).isNone &&
    match req with
    | .socket .. | .socketpair .. => true
    | .sendmsg hid fds => (lookupHandleFileId s hid).isSome && fds.toList.all (isLiveHandle s)
    | .bind hid _ | .listen hid _ | .accept4 hid _ | .connect hid _
    | .getsockopt hid _ | .setsockopt hid _ _ | .getsockname hid
    | .recvfrom hid _ _ | .sendto hid _ _ | .shutdown hid _
    | .recvmsg hid _ | .ioctl hid _ _ => (lookupHandleFileId s hid).isSome

/-- Clamp a `UInt32` byte count to `MAX_READ_BYTES` (`16 MiB`). -/
def clampMaxReadU32 (n : UInt32) : Nat :=
  (if n < MAX_READ_BYTES then n else MAX_READ_BYTES).toNat

/-- Clamp a `Nat` payload length to `MAX_READ_BYTES` (`16 MiB`). -/
def clampMaxReadNat (n : Nat) : Nat :=
  if UInt64.ofNat n < MAX_READ_BYTES.toUInt64 && n < 4294967296 then n
  else MAX_READ_BYTES.toNat

/-- Returns `true` iff `e` matches `expectedErr` or a valid async TCP `connect` failure. -/
def isAsyncConnectErrno (expectedErr e : Errno) (d : SockDesc) : Bool :=
  let isConnecting :=
    match d.proto with
    | .tcp _ _ (.connecting _) _ _ => true
    | _ => false
  e == expectedErr ||
    (expectedErr == Errno.EPIPE && d.tcpLoFinPending && e == Errno.ECONNRESET) ||
    (isConnecting &&
      (e == Errno.ECONNREFUSED || e == Errno.ETIMEDOUT ||
       e == Errno.ENETUNREACH || e == Errno.EHOSTUNREACH))

/-- Check whether `d` is currently in an established/connected phase. -/
def isEstablished (d : SockDesc) : Bool :=
  match d.proto with
  | .tcp _ _ _ tcpState _ =>
    match tcpState with
    | .established .. | .finWait .. | .closeWait .. => true
    | _ => false
  | .udp _ _ peer? => peer?.isSome
  | .unixStream _ _ (.connected ..) => true
  | .unixDgram _ peer? => peer?.isSome
  | _ => false

private def isTcpSelfPeer (fid : FileId) (d : SockDesc) : Bool :=
  match d.proto with
  | .tcp _ _ _ (.established (some pf) _) _
  | .tcp _ _ _ (.finWait (some pf) _) _
  | .tcp _ _ _ (.closeWait (some pf) _ _) _ => pf == fid
  | _ => false

/-- Consume any pending non-zero `soError` on `d`, updating connecting TCP state. -/
def consumePendingSoError (d : SockDesc) : Option (Errno × SockDesc) :=
  if d.soError == 0 then none
  else
    let nextProto :=
      match d.proto with
      | .tcp fam bind (.connecting _) tcpState tainted =>
        .tcp fam bind .disconnecting tcpState tainted
      | other => other
    some (d.soError, { d with soError := 0, proto := nextProto })

/-- Consume pending `soError` for receive paths, ignoring `EPIPE` after peer TCP shutdown. -/
def consumeRecvPendingSoError (d : SockDesc) : Option (Errno × SockDesc) :=
  if d.proto.isListening then none
  else
    let tcpPeerShut :=
      match d.proto with
      | .tcp _ _ _ (.finWait ..) _ => false
      | .tcp _ _ _ (.closeWait ..) _ | .tcp _ _ _ (.closedAfterConn ..) _ => true
      | _ => false
    if tcpPeerShut && d.soError == Errno.EPIPE then none
    else consumePendingSoError d

private def releaseRxScm (s : NetState) (q : List RxUnit) : NetState :=
  releaseUnusedFiles s (q.foldl (fun acc u => acc ++ u.scm) [])

/-- Tail-recursive helper filling `n` copies of byte `b` into `acc`. -/
def replicateByteAux (b : UInt8) : Nat → ByteArray → ByteArray
  | 0, acc => acc
  | n + 1, acc => replicateByteAux b n (acc.push b)

/-- Allocate a `ByteArray` of length `n` filled with `b` without intermediate `List`/`Array` boxing. -/
def replicateByte (n : Nat) (b : UInt8) : ByteArray :=
  replicateByteAux b n (ByteArray.emptyWithCapacity n)

/-- Tail-recursive helper for `collectStreamRead`, packing stream bytes and `isScmDummy` flags (`0`/`1`) into `ByteArray`s. -/
def collectStreamReadAux : Nat → List RxUnit → ByteArray → ByteArray → ByteArray × ByteArray
  | 0, _, accB, accF => (accB, accF)
  | _, [], accB, accF => (accB, accF)
  | rem, u :: rest, accB, accF =>
    let uLen := u.bytes.size
    if uLen == 0 then collectStreamReadAux rem rest accB accF
    else
      let takeN := min rem uLen
      let part := if takeN >= uLen then u.bytes else u.bytes.extract 0 takeN
      let flags := replicateByte takeN (if u.isScmDummy then 1 else 0)
      let nextB := if accB.size == 0 then part else accB ++ part
      let nextF := if accF.size == 0 then flags else accF ++ flags
      if !u.scm.isEmpty || takeN == rem then (nextB, nextF)
      else collectStreamReadAux (rem - takeN) rest nextB nextF

/-- Collect up to `rem` bytes and their `isScmDummy` byte-mask (`0`/`1`) across stream RX chunks. -/
def collectStreamRead (rem : Nat) (q : List RxUnit) : ByteArray × ByteArray :=
  collectStreamReadAux rem q ByteArray.empty ByteArray.empty

private def consumeStreamQueue : Nat → List RxUnit → List RxUnit
  | 0, q => q
  | _, [] => []
  | n, u :: rest =>
    let uLen := u.bytes.size
    if uLen == 0 then consumeStreamQueue n rest
    else if n < uLen then
      { bytes := sliceBytes u.bytes n (uLen - n), scm := [], isScmDummy := false } :: rest
    else
      consumeStreamQueue (n - uLen) rest

private def collectConsumedStreamScmAux : Nat → List RxUnit → List FileId → List FileId
  | 0, _, acc => acc.reverse
  | _, [], acc => acc.reverse
  | n, u :: rest, acc =>
    let uLen := u.bytes.size
    let nextAcc := u.scm.reverseAux acc
    if uLen == 0 then collectConsumedStreamScmAux n rest nextAcc
    else if n < uLen then nextAcc.reverse
    else collectConsumedStreamScmAux (n - uLen) rest nextAcc

private def collectConsumedStreamScm (n : Nat) (q : List RxUnit) : List FileId :=
  collectConsumedStreamScmAux n q []

private def stripFirstStreamScmAux : List RxUnit → List RxUnit → List RxUnit × List FileId
  | [], acc => (acc.reverse, [])
  | u :: rest, acc =>
    if !u.scm.isEmpty then (acc.reverseAux ({ u with scm := [] } :: rest), u.scm)
    else if u.bytes.size == 0 then stripFirstStreamScmAux rest (u :: acc)
    else (acc.reverseAux (u :: rest), [])

private def stripFirstStreamScm (q : List RxUnit) : List RxUnit × List FileId :=
  stripFirstStreamScmAux q []

/-- Structural tail-recursive helper for `streamBytesMatches`. -/
def streamBytesMatchesAux (got avail mask : ByteArray) : Nat → Nat → Bool
  | 0, _ => true
  | rem + 1, i =>
    if mask.get! i == 0 && got.get! i != avail.get! i then false
    else streamBytesMatchesAux got avail mask rem (i + 1)

/-- Check whether an observed stream read `got` matches `avail` up to `isScmDummy` `mask`. -/
def streamBytesMatches (got avail mask : ByteArray) : Bool :=
  streamBytesMatchesAux got avail mask got.size 0

/-- Pop one unit of SCM handles and remaining queue for `recvmsg` on `sockType`. -/
def popRecvmsgUnit (sockType : SockType) : List RxUnit → Option (List FileId × List RxUnit)
  | [] => none
  | u :: rest =>
    if sockType == .stream then
      let uLen := u.bytes.size
      if uLen == 0 && u.scm.isEmpty then popRecvmsgUnit sockType rest
      else
        let nextQ :=
          if uLen > 1 then { bytes := sliceBytes u.bytes 1 (uLen - 1), scm := [], isScmDummy := false } :: rest
          else rest
        some (u.scm, nextQ)
    else some (u.scm, rest)

/-- Allocate fresh handles for up to `rem` received `SCM_RIGHTS` file IDs. -/
def cloneScmHandles (s : NetState) : Nat → HandleId → List FileId → List HandleId → NetState × Array HandleId
  | 0, _, _, acc => (s, acc.reverse.toArray)
  | _, _, [], acc => (s, acc.reverse.toArray)
  | rem + 1, nextH, srcFid :: rest, acc =>
    let s' := { s with handles := assocSet s.handles nextH (.open srcFid true), nextHid := max s.nextHid (nextH + 1) }
    cloneScmHandles s' rem (nextH + 1) rest (nextH :: acc)

/-- Bind observed received `SCM_RIGHTS` handle IDs onto `srcFids`. -/
def bindReceivedScmHandles (s : NetState) : List HandleId → List FileId → Option NetState
  | [], _ => some s
  | newHid :: restNew, srcFids =>
    if !isFreshHid s newHid then none
    else
      let entry : NetHandleEntry :=
        match srcFids with
        | srcFid :: _ => .open srcFid true
        | [] => .closed
      let s' := { s with handles := assocSet s.handles newHid entry, nextHid := max s.nextHid (newHid + 1) }
      bindReceivedScmHandles s' restNew (srcFids.drop 1)

/-- Emit or verify an error outcome (`obs? = none` produces `canon`, `some` verifies `canon`/`alts`/transient). -/
def emitErr (obs? : Option NetOutcome) (s : NetState) (canon : Errno)
    (alts : List Errno := []) (onErr : Errno → NetState := fun _ => s)
    (allowTransient : Bool := true) (allowUnit? : Option NetState := none)
    (allowU32? : Option (UInt32 → Option NetState) := none)
    (allowBytes? : Option (ByteArray → Option NetState) := none) :
    Option (NetOutcome × NetState) :=
  match obs? with
  | none => some (.err canon, onErr canon)
  | some (.err e) =>
    if e == canon || alts.contains e then some (.err e, onErr e)
    else if allowTransient && isTransientNetErrno e then some (.err e, s)
    else none
  | some .unit =>
    match allowUnit? with
    | some sOk => some (.unit, sOk)
    | none => none
  | some (.u32 n) =>
    match allowU32? with
    | some validate =>
      match validate n with
      | some sOk => some (.u32 n, sOk)
      | none => none
    | none => none
  | some (.bytes b) =>
    match allowBytes? with
    | some validate =>
      match validate b with
      | some sOk => some (.bytes b, sOk)
      | none => none
    | none => none
  | some _ => none

/-- Emit or verify a unit outcome (`obs? = none` produces `.unit`, `some` verifies `.unit` or `altErrs`/transient). -/
def emitUnit (obs? : Option NetOutcome) (s : NetState) (sOk : NetState)
    (altErrs : List Errno := []) (onAltErr : Errno → NetState := fun _ => s)
    (allowTransient : Bool := true) : Option (NetOutcome × NetState) :=
  match obs? with
  | none => some (.unit, sOk)
  | some .unit => some (.unit, sOk)
  | some (.err e) =>
    if altErrs.contains e then some (.err e, onAltErr e)
    else if allowTransient && isTransientNetErrno e then some (.err e, s)
    else none
  | some _ => none

/-- Emit or verify a `UInt32` outcome. -/
def emitU32 (obs? : Option NetOutcome) (s : NetState) (canon : UInt32) (sOk : NetState)
    (altErrs : List Errno := []) (allowZeroOk : Bool := false)
    (onAltErr : Errno → NetState := fun _ => s) (allowTransient : Bool := true) :
    Option (NetOutcome × NetState) :=
  match obs? with
  | none => some (.u32 canon, sOk)
  | some (.u32 v) =>
    if v == canon then some (.u32 v, sOk)
    else if allowZeroOk && v == 0 then some (.u32 0, s)
    else none
  | some (.err e) =>
    if altErrs.contains e then some (.err e, onAltErr e)
    else if allowTransient && isTransientNetErrno e then some (.err e, s)
    else none
  | some _ => none

/-- Emit or verify single-handle socket allocation. -/
def emitAllocFd (obs? : Option NetOutcome) (s : NetState) (desc : SockDesc)
    (cloexec : Bool) (altErrs : List Errno := []) (allowTransient : Bool := true) :
    Option (NetOutcome × NetState) :=
  let alloc (h : HandleId) : NetState :=
    let fid := s.nextFileId
    { s with
      handles := assocSet s.handles h (.open fid cloexec)
      files := assocSet s.files fid (.socket desc)
      nextHid := max s.nextHid (h + 1)
      nextFileId := fid + 1 }
  match obs? with
  | none =>
    let h := freshHidBase s
    some (.opened h, alloc h)
  | some (.opened h) =>
    if isFreshHid s h then some (.opened h, alloc h) else none
  | some (.err e) =>
    if altErrs.contains e || (allowTransient && isTransientNetErrno e) then some (.err e, s) else none
  | some _ => none

/-- Emit or verify socket-pair allocation. -/
def emitAllocPair (obs? : Option NetOutcome) (s : NetState) (d0 d1 : SockDesc)
    (cloexec : Bool) (altErrs : List Errno := []) : Option (NetOutcome × NetState) :=
  let alloc (h0 h1 : HandleId) : NetState :=
    let fid0 := s.nextFileId
    let fid1 := fid0 + 1
    let hs := assocSet (assocSet s.handles h0 (.open fid0 cloexec)) h1 (.open fid1 cloexec)
    let fs := assocSet (assocSet s.files fid0 (.socket d0)) fid1 (.socket d1)
    { s with
      handles := hs, files := fs
      nextHid := max s.nextHid (max (h0 + 1) (h1 + 1))
      nextFileId := fid0 + 2 }
  match obs? with
  | none =>
    let h0 := freshHidBase s
    let h1 := h0 + 1
    some (.pair h0 h1, alloc h0 h1)
  | some (.pair h0 h1) =>
    if h0 != h1 && isFreshHid s h0 && isFreshHid s h1 then some (.pair h0 h1, alloc h0 h1) else none
  | some (.err e) =>
    if altErrs.contains e || isTransientNetErrno e then some (.err e, s) else none
  | some _ => none

/-- Emit or verify a `SockAddr` outcome. -/
def emitAddr (obs? : Option NetOutcome) (s : NetState) (canon : SockAddr)
    (validate : SockAddr → Option NetState) : Option (NetOutcome × NetState) :=
  match obs? with
  | none =>
    match validate canon with
    | some sOk => some (.addr canon, sOk)
    | none => none
  | some (.addr gotSa) =>
    match validate gotSa with
    | some sOk => some (.addr gotSa, sOk)
    | none => none
  | some (.err e) => if isTransientNetErrno e then some (.err e, s) else none
  | some _ => none

/-- Emit or verify a `ByteArray` outcome. -/
def emitBytes (obs? : Option NetOutcome) (s : NetState) (canon : ByteArray)
    (validate : ByteArray → Option NetState) (altErrs : List Errno := []) :
    Option (NetOutcome × NetState) :=
  match obs? with
  | none =>
    match validate canon with
    | some sOk => some (.bytes canon, sOk)
    | none => none
  | some (.bytes got) =>
    match validate got with
    | some sOk => some (.bytes got, sOk)
    | none => none
  | some (.err e) =>
    if altErrs.contains e || isTransientNetErrno e then some (.err e, s) else none
  | some _ => none

/-- Emit or verify `accept4` dequeuing from a listener accept queue. -/
def emitAccept (obs? : Option NetOutcome) (s : NetState) (lFid : FileId) (ld : SockDesc)
    (aq : List AcceptEntry) (flags : SockFlags) : Option (NetOutcome × NetState) :=
  let updateListenerQueue (st : NetState) (nextQ : List AcceptEntry) : NetState :=
    match ld.proto with
    | .tcp fam bind ss (.listen bl _) t =>
      setFileSocket st lFid { ld with proto := .tcp fam bind ss (.listen bl nextQ) t }
    | .unixStream isSeq bp (.listen bl _) =>
      setFileSocket st lFid { ld with proto := .unixStream isSeq bp (.listen bl nextQ) }
    | _ => st
  match aq with
  | [] =>
    emitErr obs? s Errno.EAGAIN [Errno.EMFILE, Errno.ENFILE, Errno.ENOMEM]
      (allowTransient := true)
  | accEntry :: restQ =>
    let altErrs := [Errno.EMFILE, Errno.ENFILE, Errno.ENOMEM, Errno.ECONNABORTED]
    let installChild (st : NetState) (srvHid : HandleId) (gotPeer : SockAddr) : NetState :=
      let s1 := updateListenerQueue st restQ
      let s2 := { s1 with
        handles := assocSet s1.handles srvHid (.open accEntry.childFid flags.cloexec)
        nextHid := max s1.nextHid (srvHid + 1) }
      match (assocGet s2.files accEntry.childFid : Option OpenFileEntry) with
      | some (.socket cd) =>
        let cd' := { cd with nonblock := flags.nonblock }
        let s3 := setFileSocket s2 accEntry.childFid cd'
        if accEntry.peerPortPinned && !accEntry.peerRoutedV4 then s3
        else
          match cd'.proto with
          | .tcp _ _ _ (.established (some cliFid) _) _
          | .tcp _ _ _ (.finWait (some cliFid) _) _
          | .tcp _ _ _ (.closeWait (some cliFid) _ _) _ =>
            match lookupFileSocket s3 cliFid with
            | .ok clid =>
              match clid.proto with
              | .tcp cf (.hashed csa cep pl al) css ctcp ctaint =>
                if (cep || accEntry.peerRoutedV4) && (css == .connecting false || css == .connected) then
                  let nextSa :=
                    match csa, gotPeer with
                    | .ipv4 cip cp, .ipv4 gip gp =>
                      .ipv4 (if accEntry.peerRoutedV4 then gip else cip) (if cep then gp else cp)
                    | .ipv4 cip cp, .ipv6 0 glo gp _ _ =>
                      let nextIp := if accEntry.peerRoutedV4 then (mappedV4Addr? 0 glo).getD cip else cip
                      .ipv4 nextIp (if cep then gp else cp)
                    | .ipv6 0 clo cp fl sc, .ipv6 0 glo gp _ _ =>
                      let nextLo :=
                        if accEntry.peerRoutedV4 then
                          match mappedV4Addr? 0 glo with
                          | some gip => ipv4ToMappedV6Lo gip
                          | none => clo
                        else clo
                      .ipv6 0 nextLo (if cep then gp else cp) fl sc
                    | .ipv6 0 clo cp fl sc, .ipv4 gip gp =>
                      let nextLo := if accEntry.peerRoutedV4 then ipv4ToMappedV6Lo gip else clo
                      .ipv6 0 nextLo (if cep then gp else cp) fl sc
                    | _, _ =>
                      match gotPeer.port? with
                      | some p => if cep then csa.withPort p else csa
                      | none => csa
                  setFileSocket s3 cliFid
                    { clid with tcpMcastRoutedIp := false, proto := .tcp cf (.hashed nextSa false pl al) css ctcp ctaint }
                else s3
              | _ => s3
            | .error _ => s3
          | _ => s3
      | _ => s2
    match obs? with
    | none =>
      if ld.nonblock then
        if !matchesAcceptPeerAddr accEntry.peerAddr accEntry.peerAddr (!accEntry.peerPortPinned) accEntry.matchKind accEntry.peerRoutedV4 then
          none
        else
          let srvHid := freshHidBase s
          some (.accepted srvHid accEntry.peerAddr, installChild s srvHid accEntry.peerAddr)
      else
        if !matchesAcceptPeerAddr accEntry.peerAddr accEntry.peerAddr (!accEntry.peerPortPinned) accEntry.matchKind accEntry.peerRoutedV4 then
          none
        else
          let srvHid := freshHidBase s
          some (.accepted srvHid accEntry.peerAddr, installChild s srvHid accEntry.peerAddr)
    | some (.accepted srvHid gotPeer) =>
      if !isFreshHid s srvHid then none
      else if !matchesAcceptPeerAddr accEntry.peerAddr gotPeer (!accEntry.peerPortPinned) accEntry.matchKind accEntry.peerRoutedV4 then none
      else some (.accepted srvHid gotPeer, installChild s srvHid gotPeer)
    | some (.err e) =>
      if e == Errno.EAGAIN && ld.nonblock && aq.all (·.crossFamily) then
        let sDrop := aq.foldl (fun accS q =>
          match assocGet accS.files q.childFid with
          | some (.socket cd) =>
            match cd.proto with
            | .tcp _ _ _ (.established (some cliFid) pa) _ =>
              let accS0 := { accS with files := assocErase accS.files q.childFid }
              match lookupFileSocket accS0 cliFid with
              | .ok clid =>
                match clid.proto with
                | .tcp cf cbind _ _ ctaint =>
                  setFileSocket accS0 cliFid
                    { clid with soError := Errno.ECONNREFUSED, proto := .tcp cf cbind.unhashUnlocked .disconnecting (.closedAfterConn pa .reset) ctaint }
                | _ => accS0
              | .error _ => accS0
            | _ => accS
          | _ => accS) (updateListenerQueue s [])
        some (.err e, sDrop)
      else if altErrs.contains e || isTransientNetErrno e then
        some (.err e, s)
      else none
    | some _ => none

/-- Resolve `hid` to an open socket `(fid, desc)` or emit `EBADF`/`ENOTSOCK`. -/
def withSock (s : NetState) (hid : HandleId) (obs? : Option NetOutcome)
    (k : FileId → SockDesc → Option (NetOutcome × NetState)) : Option (NetOutcome × NetState) :=
  match lookupHandleFileId s hid with
  | none => emitErr obs? s Errno.EBADF [] (allowTransient := false)
  | some fid =>
    match lookupFileSocket s fid with
    | .error fdErr => emitErr obs? s fdErr [] (allowTransient := (fdErr == Errno.ENOTSOCK))
    | .ok d => k fid d

private def clearBindIpOnGetPortErr (s : NetState) (fid : FileId) (d : SockDesc) (e : Errno) : NetState :=
  if e != Errno.EADDRINUSE then s
  else
    match d.proto with
    | .tcp fam (.unhashed sa ep _al) ss tcpState tainted =>
      let wildSa := match sa with
        | .ipv4 _ p => .ipv4 INADDR_ANY p
        | .ipv6 _ _ p fl _ => .ipv6 0 0 p fl 0
        | other => other
      setFileSocket s fid { d with proto := .tcp fam (.unhashed wildSa ep false) ss tcpState tainted }
    | _ => s

private def setProtoBind (p : SockProtoState) (nextBind : InetBind) : SockProtoState :=
  match p with
  | .tcp fam _ ss ts taint => .tcp fam nextBind ss ts taint
  | .udp fam _ cp => .udp fam nextBind cp
  | other => other

private def bindConflictAlts (s : NetState) (addr : SockAddr) (hasScope : Bool) : List Errno :=
  let loDownV6 := match s.loState with | .up _ => false | _ => isLocalNonWildcardV6 addr
  [Errno.EACCES] ++
    (if isIpv4MappedV6Addr addr || loDownV6 then [Errno.EINVAL, Errno.EADDRNOTAVAIL] else []) ++
    (if hasScope then [Errno.ENODEV] else [])

private def resetDisconnectedTcp (d : SockDesc) : SockDesc :=
  match d.proto with
  | .tcp fam bind _ _ taint =>
    let nextBind :=
      match bind with
      | .hashed sa ep pl false =>
        let w := match sa with | .ipv4 _ p => .ipv4 INADDR_ANY p | .ipv6 _ _ p fl _ => .ipv6 0 0 p fl 0 | _ => sa
        .hashed w ep pl false
      | .unhashed sa ep false =>
        let w := match sa with | .ipv4 _ p => .ipv4 INADDR_ANY p | .ipv6 _ _ p fl _ => .ipv6 0 0 p fl 0 | _ => sa
        .unhashed w ep false
      | other => other
    { d with shut := {}, tcpSelfSynPending := false, tcpCloseWaitRst := false, tcpShutRdwrRst := false, tcpLastAck := false, proto := .tcp fam nextBind .unconnected .idle taint }
  | _ => d

private def clearTcpShutRdwrRst (s : NetState) (selfFid : FileId) (d : SockDesc) : NetState :=
  match d.proto with
  | .tcp fam bind ss (.finWait _ pa) taint
  | .tcp fam bind ss (.closedAfterConn pa _) taint =>
    setFileSocket s selfFid
      { d with tcpShutRdwrRst := false, proto := .tcp fam bind.unhashUnlocked ss (.closedAfterConn pa .reset) taint }
  | _ => s

private def clearTcpCloseWaitRst (s : NetState) (selfFid : FileId) (d : SockDesc) : NetState :=
  match d.proto with
  | .tcp fam bind ss (.closeWait _ pa _) taint =>
    setFileSocket s selfFid
      { d with tcpCloseWaitRst := false, tcpLastAck := false, proto := .tcp fam bind.unhashUnlocked ss (.closedAfterConn pa .reset) taint }
  | _ => s

/-- Consume pending `SHUT_RDWR` Nagle reset (`ECONNRESET`) on a TCP receive path, dropping any Nagle-discarded RX tail. -/
def tcpConsumeShutRdwrRecvRst? (s : NetState) (selfFid : FileId) (d : SockDesc) : Option NetState :=
  if d.tcpShutRdwrRst then
    match d.proto with
    | .tcp fam bind ss (.finWait _ pa) taint
    | .tcp fam bind ss (.closedAfterConn pa _) taint =>
      some (setFileSocket s selfFid
        { d with rxQueue := [], soError := 0, tcpShutRdwrRst := false, proto := .tcp fam bind.unhashUnlocked ss (.closedAfterConn pa .reset) taint })
    | _ => none
  else
    match d.proto with
    | .tcp fam bind ss (.closedAfterConn pa .selfShutRstPossible) taint =>
      some (setFileSocket s selfFid
        { d with rxQueue := [], soError := 0, proto := .tcp fam bind.unhashUnlocked ss (.closedAfterConn pa .reset) taint })
    | .tcp .. =>
      if d.soError == Errno.EPIPE && d.tcpLoFinPending && d.rxQueue.isEmpty then
        some (setFileSocket s selfFid { d with soError := 0 })
      else none
    | _ => none

private def applyTcpBind (s : NetState) (fid : FileId) (d : SockDesc) (nextBind : InetBind) (nextPort : UInt16) : NetState :=
  let nextProto :=
    match d.proto with
    | .tcp fam _ .disconnecting (.synSent _) taint => .tcp fam nextBind .disconnecting .idle taint
    | other => setProtoBind other nextBind
  let isUdp := match d.proto with | .udp .. => true | _ => false
  let seq := if isUdp then s.nextBindSeq else d.udpBindSeq
  let nextSeq := if isUdp then s.nextBindSeq + 1 else s.nextBindSeq
  let isFreshLoDownV4 :=
    d.domain == .inet &&
    (match nextBind.addr? with
      | some (.ipv4 ip _) => ip != INADDR_ANY
      | _ => false) &&
    match s.loState with | .down _ false => true | _ => false
  let isLoDownDirectedBcast :=
    match nextBind.addr? with
    | some (.ipv4 ip _) => !isFreshLoDownV4 && ip == 0x7fffffff && match s.loState with | .down _ _ => true | _ => false
    | some (.ipv6 hi lo _ _ _) => mappedV4Addr? hi lo == some 0x7fffffff
    | _ => false
  { (setFileSocket s fid { d with
      tcpMcastRoutedIp := false
      udpExtRoutedIp := false
      inetSaddrZero := isFreshLoDownV4
      tcpLoDownDirectedBcast := isLoDownDirectedBcast
      proto := nextProto
      udpBindSeq := seq }) with nextPort, nextBindSeq := nextSeq }

/-- Returns `true` iff socket `d` already has a bound Unix path (or is non-Unix). -/
def isAlreadyBoundUnix (d : SockDesc) : Bool :=
  match d.proto with
  | .unixStream _ bp _ => bp.isSome
  | .unixDgram bp _ => bp.isSome
  | _ => true

/-- Returns `true` iff an IPv4/IPv6 socket in state `d` can still execute `bind`. -/
def canBindInet (d : SockDesc) : Bool :=
  match d.proto with
  | .tcp _ .unbound .unconnected .idle _ => true
  | .tcp _ (.unhashed ..) ss ts _ =>
    match ss, ts with
    | .connecting _, _ | _, .listen .. | _, .established .. | _, .finWait .. | _, .closeWait .. => false
    | _, _ => true
  | .udp _ .unbound _ => true
  | _ => false

/-- Returns `true` iff `d` is a TCP socket currently in `.connecting`. -/
def isConnectingTcp (d : SockDesc) : Bool :=
  match d.proto with | .tcp _ _ (.connecting _) _ _ => true | _ => false

/-- Returns `true` iff `sa` is an IPv6 address with nonzero `scopeId`. -/
def sockAddrHasScope : SockAddr → Bool
  | .ipv6 _ _ _ _ sc => sc != 0
  | _ => false

private def refreshUnixAcceptPeerAddr (s : NetState) (childFid : FileId) (path : ByteArray) : NetState :=
  { s with
    files := s.files.map fun (fid, entry) =>
      match entry with
      | .socket sd =>
        match sd.proto with
        | .unixStream isSeq bp (.listen bl aq) =>
          let aq' := aq.map fun q => if q.childFid == childFid then { q with peerAddr := .unix path } else q
          (fid, .socket { sd with proto := .unixStream isSeq bp (.listen bl aq') })
        | _ => (fid, entry)
      | .nonSocket => (fid, entry) }

/-- Returns `true` iff `sa` is pure IPv6 wildcard `[::]:port` (`IPV6_ADDR_ANY`). -/
def isIpv6WildcardAddr : SockAddr → Bool
  | .ipv6 0 0 _ _ _ => true
  | _ => false

/-- Model transition helper for IPv4/IPv6 `Net.bind`. -/
def stepBindInet (s0 : NetState) (hid : HandleId) (selfFid : FileId) (d0 : SockDesc)
    (addr : SockAddr) (port : UInt16) (obs? : Option NetOutcome) : Option (NetOutcome × NetState) :=
  let canBind := canBindInet d0
  let hasScope0 := sockAddrHasScope addr || d0.boundDevIf != 0
  if !canBind then
    let dScoped0 := match ipv6ScopedIfindex? d0.sockType addr with
      | some sc => { d0 with boundDevIf := sc }
      | none => d0
    let normAddr0 := normalizeBindAddr addr dScoped0.boundDevIf
    let (ep0, nextP0) := allocNextPort s0
    let boundSa0 := if port == 0 then normAddr0.withPort ep0 else normAddr0
    let nextBind0 := InetBind.hashed boundSa0 (port == 0) (port != 0) (isBindAddrLockedSa boundSa0)
    let nextPortVal0 := if port == 0 then nextP0 else s0.nextPort
    let targetOpt? : Option (SockAddr × Errno) :=
      match d0.proto with
      | .tcp _ (.unhashed ..) (.connecting _) (.synSent target) _ =>
        if d0.soError != 0 then some (target, 0) else none
      | .tcp _ (.unhashed ..) (.connecting _) (.closedAfterConn target _) _ =>
        some (target, 0)
      | .tcp _ (.hashed _ _ false _) _ (.finWait _ target) _ =>
        if (d0.shut.isBoth && !d0.rxQueue.isEmpty) || d0.tcpShutRdwrRst then some (target, Errno.ECONNRESET) else none
      | .tcp _ (.hashed _ _ false _) _ (.closeWait pf? target _) _ =>
        let peerShutRd := match pf? with
          | none => true
          | some pf => match lookupFileSocket s0 pf with | .error _ => true | .ok pd => pd.shut.rd
        if peerShutRd then some (target, Errno.EPIPE) else none
      | _ => none
    let isNativeV6Lo0 := match addr with | .ipv6 0 1 _ _ _ => true | _ => false
    let devAllowsAddr0 :=
      if isIpv6WildcardAddr addr || dScoped0.boundDevIf == 0 || dScoped0.boundDevIf == 1 then
        isLocalBindableAddr addr || isIpv6LinkLocal addr
      else
        !isNativeV6Lo0 && (isLocalBindableAddr addr || isIpv6LinkLocal addr)
    let allowAsyncRstBind :=
      targetOpt?.isSome && !isInvalidV6LinkOrMulticast d0.sockType addr d0.boundDevIf &&
        devAllowsAddr0 && !(port != 0 && hasBindPortConflict s0 hid d0.sockType d0.reuseAddr normAddr0)
    let sAsyncOk? :=
      if allowAsyncRstBind then
        let s1 := applyTcpBind s0 selfFid dScoped0 nextBind0 nextPortVal0
        match lookupFileSocket s1 selfFid, targetOpt? with
        | .ok d1, some (target, rstErr) =>
          let nextSoErr := if rstErr != 0 && d1.soError == 0 then rstErr else d1.soError
          match d1.proto with
          | .tcp fam1 bind1 ss1 (.synSent _) taint1
          | .tcp fam1 bind1 ss1 .idle taint1
          | .tcp fam1 bind1 ss1 (.finWait _ _) taint1
          | .tcp fam1 bind1 ss1 (.closeWait _ _ _) taint1 =>
            some (setFileSocket s1 selfFid { d1 with soError := nextSoErr, tcpShutRdwrRst := false, tcpCloseWaitRst := false, tcpLastAck := false, proto := .tcp fam1 bind1 ss1 (.closedAfterConn target .reset) taint1 })
          | _ => some s1
        | _, _ => some s1
      else none
    let alts :=
      (if !isLocalBindableAddr addr then [Errno.EADDRNOTAVAIL] else []) ++
      (if port != 0 && port.toNat < 1024 then [Errno.EACCES] else []) ++
      (if hasScope0 then [Errno.ENODEV] else []) ++
      (if targetOpt?.isSome && port != 0 then [Errno.EADDRINUSE] else [])
    emitErr obs? s0 Errno.EINVAL alts (fun e => clearBindIpOnGetPortErr s0 selfFid d0 e) (allowUnit? := sAsyncOk?)
  else if isInvalidV6LinkOrMulticast d0.sockType addr d0.boundDevIf then
    emitErr obs? s0 Errno.EINVAL (if hasScope0 then [Errno.ENODEV] else [])
  else
    let d := match ipv6ScopedIfindex? d0.sockType addr with
      | some sc => { d0 with boundDevIf := sc }
      | none => d0
    let s := if d.boundDevIf != d0.boundDevIf then setFileSocket s0 selfFid d else s0
    let hasScope := sockAddrHasScope addr || d.boundDevIf != 0
    let normAddr := normalizeBindAddr addr d.boundDevIf
    let (ep, nextP) := allocNextPort s
    let boundSa := if port == 0 then normAddr.withPort ep else normAddr
    let nextBind := InetBind.hashed boundSa (port == 0) (port != 0) (isBindAddrLockedSa boundSa)
    let nextPortVal := if port == 0 then nextP else s.nextPort
    if !isIpv6WildcardAddr addr && d.boundDevIf != 0 && d.boundDevIf != 1 then
      let isNativeV6Lo := match addr with | .ipv6 0 1 _ _ _ => true | _ => false
      let allowExtBind :=
        !isNativeV6Lo && (isLocalBindableAddr addr || isIpv6LinkLocal addr) &&
          !(port != 0 && hasBindPortConflict s hid d.sockType d.reuseAddr normAddr)
      let sExtOk? := if allowExtBind then some (applyTcpBind s selfFid d nextBind nextPortVal) else none
      emitErr obs? s0 Errno.ENODEV [Errno.EADDRNOTAVAIL, Errno.EINVAL, Errno.EACCES, Errno.EADDRINUSE]
        (fun e => if isTransientNetErrno e then s0 else clearBindIpOnGetPortErr s selfFid d e)
        (allowUnit? := sExtOk?)
    else if !isLocalBindableAddr addr then
      let alts := [Errno.EINVAL, Errno.EACCES] ++ (if hasScope then [Errno.ENODEV] else [])
      emitErr obs? s0 Errno.EADDRNOTAVAIL alts
        (fun e => if isTransientNetErrno e then s0 else s)
    else if port != 0 && hasBindPortConflict s hid d.sockType d.reuseAddr normAddr then
      let sAsyncFreeOk? :=
        if !hasDefiniteBindPortConflict s hid d.sockType d.reuseAddr normAddr then
          some (applyTcpBind s selfFid d nextBind nextPortVal)
        else none
      emitErr obs? s0 Errno.EADDRINUSE (bindConflictAlts s normAddr hasScope)
        (fun e => if isTransientNetErrno e then s0 else clearBindIpOnGetPortErr s selfFid d e)
        (allowUnit? := sAsyncFreeOk?)
    else
      let sOk := applyTcpBind s selfFid d nextBind nextPortVal
      let loDownV6 := match s.loState with | .up _ => false | _ => isLocalNonWildcardV6 addr
      let alts :=
        (if port != 0 && port.toNat < 1024 then [Errno.EACCES] else []) ++
        (if isIpv4MappedV6Addr addr || loDownV6 || d.tcpLoFinPending then [Errno.EINVAL, Errno.EADDRNOTAVAIL] else []) ++
        (if hasScope then [Errno.ENODEV] else []) ++
        [Errno.EADDRINUSE]
      emitUnit obs? s0 sOk alts
        (fun e => if isTransientNetErrno e then s0 else clearBindIpOnGetPortErr s selfFid d e)

/-- Model transition for `Net.bind`. -/
def stepBind (s : NetState) (hid : HandleId) (addr : SockAddr) (obs? : Option NetOutcome) :
    Option (NetOutcome × NetState) :=
  withSock s hid obs? fun selfFid d =>
    if addr.domain != d.domain then
      emitErr obs? s (familyMismatchErrno d.domain addr) [Errno.EAFNOSUPPORT, Errno.EINVAL]
    else
      match addr with
      | .unix path =>
        if isAlreadyBoundUnix d then
          if isAbstractUnixPath path then
            emitErr obs? s Errno.EINVAL []
          else
            let canon := if bytesListContains s.boundUnixPaths path then Errno.EADDRINUSE else Errno.EINVAL
            let fsErrs := [Errno.EINVAL, Errno.EADDRINUSE, Errno.EACCES, Errno.EPERM, Errno.ENOENT,
              Errno.ENOTDIR, Errno.EROFS, Errno.ELOOP, Errno.ENAMETOOLONG]
            emitErr obs? s canon fsErrs
        else if hasUnixBindConflict s d.sockType path then
          emitErr obs? s Errno.EADDRINUSE
        else
          let nextProto := match d.proto with
            | .unixStream isSeq _ conn => SockProtoState.unixStream isSeq (some path) conn
            | .unixDgram _ peer? => SockProtoState.unixDgram (some path) peer?
            | other => other
          let nextPaths := if isAbstractUnixPath path then s.boundUnixPaths else path :: s.boundUnixPaths
          let s1 := { (setFileSocket s selfFid { d with proto := nextProto }) with boundUnixPaths := nextPaths }
          let sOk :=
            match d.proto with
            | .unixStream _ _ (.connected (some peerFid) ..) => refreshUnixAcceptPeerAddr s1 peerFid path
            | _ => s1
          let fsErrs := [Errno.EADDRINUSE, Errno.EACCES, Errno.EPERM, Errno.EINVAL, Errno.ENOENT,
            Errno.ENOTDIR, Errno.EROFS, Errno.ELOOP, Errno.ENAMETOOLONG]
          emitUnit obs? s sOk fsErrs
      | .ipv4 _ port | .ipv6 _ _ port _ _ =>
        stepBindInet s hid selfFid d addr port obs?

/-- Model transition for `Net.listen`. -/
def stepListen (s : NetState) (hid : HandleId) (backlog : UInt32) (obs? : Option NetOutcome) :
    Option (NetOutcome × NetState) :=
  withSock s hid obs? fun selfFid d =>
    let effBacklog : UInt32 := if backlog > 4096 then 4096 else backlog
    match d.proto with
    | .udp .. | .unixDgram .. =>
      emitErr obs? s Errno.EOPNOTSUPP []
    | .unixStream isSeq bp conn =>
      match conn with
      | .listen _ aq =>
        emitUnit obs? s (setFileSocket s selfFid { d with proto := .unixStream isSeq bp (.listen effBacklog aq) })
      | .connected .. =>
        if bp.isNone then
          emitErr obs? s Errno.EINVAL []
        else
          emitUnit obs? s s
      | .idle =>
        if bp.isNone then
          emitErr obs? s Errno.EINVAL []
        else
          emitUnit obs? s (setFileSocket s selfFid { d with proto := .unixStream isSeq bp (.listen effBacklog []) })
    | .tcp fam bind sockState tcpState tainted =>
      if sockState != .unconnected then
        emitErr obs? s Errno.EINVAL []
      else
        match tcpState with
        | .listen _ aq =>
          emitUnit obs? s (setFileSocket s selfFid { d with proto := .tcp fam bind sockState (.listen effBacklog aq) tainted })
        | .synSent _ | .established .. | .finWait .. | .closeWait .. =>
          emitErr obs? s Errno.EINVAL []
        | .idle | .closedAfterConn .. =>
          match bind with
          | .unbound =>
            let (ep, nextP) := allocNextPort s
            let autoSa := (defaultUnboundAddr d.domain).withPort ep
            let nextBind := InetBind.hashed autoSa true false false
            let sOk := { (setFileSocket s selfFid { d with proto := .tcp fam nextBind .unconnected (.listen effBacklog []) tainted }) with nextPort := nextP }
            emitUnit obs? s sOk [Errno.EADDRINUSE]
          | .hashed sa _ _ _ =>
            if hasListenConflict s hid .stream sa then
              emitErr obs? s Errno.EADDRINUSE
            else
              let sOk := setFileSocket s selfFid { d with proto := .tcp fam bind .unconnected (.listen effBacklog []) tainted }
              emitUnit obs? s sOk [Errno.EADDRINUSE]
          | .unhashed lastSa _ al =>
            let (ep0, nextP0) := allocNextPort s
            let (ep, nextP) :=
              if lastSa.port? == some ep0 then allocNextPort { s with nextPort := nextP0 }
              else (ep0, nextP0)
            let nextSa := lastSa.withPort ep
            let nextBind := InetBind.hashed nextSa true false al
            let sOk := { (setFileSocket s selfFid { d with proto := .tcp fam nextBind .unconnected (.listen effBacklog []) tainted }) with nextPort := nextP }
            emitUnit obs? s sOk [Errno.EADDRINUSE]

/-- Model transition for `Net.accept4`. -/
def stepAccept4 (s : NetState) (hid : HandleId) (flags : SockFlags) (obs? : Option NetOutcome) :
    Option (NetOutcome × NetState) :=
  withSock s hid obs? fun lFid ld =>
    match ld.proto with
    | .udp .. | .unixDgram .. =>
      emitErr obs? s Errno.EOPNOTSUPP [Errno.EMFILE, Errno.ENFILE, Errno.ENOMEM]
    | .tcp _ _ _ (.listen _ aq) _ =>
      emitAccept obs? s lFid ld aq flags
    | .unixStream _ _ (.listen _ aq) =>
      if aq.isEmpty && !ld.nonblock && ld.shut.rd then
        emitErr obs? s Errno.EINVAL [Errno.EMFILE, Errno.ENFILE, Errno.ENOMEM]
      else
        emitAccept obs? s lFid ld aq flags
    | _ => emitErr obs? s Errno.EINVAL [Errno.EMFILE, Errno.ENFILE, Errno.ENOMEM]

/-- Returns `true` when an `AF_UNIX` datagram peer socket is already connected to a different socket. -/
def isUnixDgramPeerBusy (selfFid : FileId) (peerDesc : SockDesc) : Bool :=
  match peerDesc.proto with
  | .unixDgram _ (some (pf, _)) => pf != selfFid
  | _ => false

/-- Model transition helper for `AF_UNIX` datagram `connect`. -/
def stepUnixDgramConnect (s : NetState) (selfFid : FileId) (d : SockDesc)
    (bp? : Option ByteArray) (oldPeer? : Option (FileId × SockAddr))
    (addr : SockAddr) (obs? : Option NetOutcome) : Option (NetOutcome × NetState) :=
  match addr with
  | .unix path =>
    match findBoundUnixSocket s .dgram path with
    | none =>
      let missErr :=
        if bytesListContains s.boundUnixPaths path || isAbstractUnixPath path then Errno.ECONNREFUSED
        else Errno.ENOENT
      emitErr obs? s missErr [Errno.ECONNREFUSED, Errno.EACCES, Errno.ENOTDIR, Errno.ELOOP, Errno.ENAMETOOLONG]
    | some (peerFid, peerDesc) =>
      if peerDesc.sockType != .dgram then
        emitErr obs? s Errno.EPROTOTYPE [Errno.ECONNREFUSED]
      else
        if isUnixDgramPeerBusy selfFid peerDesc then
          emitErr obs? s Errno.EPERM
        else
          let oldFid? := oldPeer?.map Prod.fst
          let purge := oldFid?.isSome && oldFid? != some peerFid
          let d' : SockDesc :=
            { d with
              proto := .unixDgram bp? (some (peerFid, addr))
              rxQueue := if purge then [] else d.rxQueue }
          let s1 := setFileSocket s selfFid d'
          let s2 := if purge then releaseRxScm s1 d.rxQueue else s1
          let sOk :=
            if purge && !d.rxQueue.isEmpty then
              match oldFid? with
              | some oldPf =>
                match lookupFileSocket s2 oldPf with
                | .ok opd =>
                  match opd.proto with
                  | .unixDgram _ (some (opf, _)) =>
                    if opf == selfFid then setFileSocket s2 oldPf { opd with soError := Errno.ECONNRESET }
                    else s2
                  | _ => s2
                | .error _ => s2
              | none => s2
            else s2
          emitUnit obs? s sOk [Errno.EACCES]
  | _ => emitErr obs? s Errno.EINVAL []

private def autobindUdp (s : NetState) (fid : FileId) (d : SockDesc) : NetState :=
  match d.proto with
  | .udp fam .unbound cp =>
    let (ep, nextP) := allocNextPort s
    let autoSa := (defaultUnboundAddr d.domain).withPort ep
    { (setFileSocket s fid { d with proto := .udp fam (.hashed autoSa true false false) cp, udpBindSeq := s.nextBindSeq }) with
      nextPort := nextP, nextBindSeq := s.nextBindSeq + 1 }
  | _ => s

private def applyUdpConnectOk (s : NetState) (selfFid : FileId) (d : SockDesc)
    (fam : InetFamily) (bind : InetBind) (addr : SockAddr) : NetState :=
  let (ep, nextP) := allocNextPort s
  let (nextBind, nextPortVal, nextSeq, descSeq) : InetBind × UInt16 × Nat × Nat :=
    match bind with
    | .unbound =>
      (.hashed (defaultAutoClientAddr d.domain addr ep) true false false, nextP, s.nextBindSeq + 1, s.nextBindSeq)
    | .hashed existing eph pl al =>
      (.hashed (concretizeClientLocalAddr existing (some addr)) eph pl al, s.nextPort, s.nextBindSeq, d.udpBindSeq)
    | .unhashed existing eph al =>
      (.unhashed (concretizeClientLocalAddr existing (some addr)) eph al, s.nextPort, s.nextBindSeq, d.udpBindSeq)
  let isExtV4Wire := !isLoopbackTargetAddr addr && (d.domain == SockDomain.inet || isIpv4MappedV6Addr addr)
  let boundLockedZero := (bind.addr?.map isAddrLockedZeroInetSaddr).getD false
  let nextMcastRouted := d.tcpMcastRoutedIp || (d.domain == SockDomain.inet6 && boundLockedZero && isExtV4Wire)
  let nextUdpExtRouted := d.udpExtRoutedIp || (boundLockedZero && isExtV4Wire)
  { (setFileSocket s selfFid { d with
      tcpMcastRoutedIp := nextMcastRouted
      udpExtRoutedIp := nextUdpExtRouted
      proto := .udp fam nextBind (some addr)
      udpBindSeq := descSeq }) with
    nextPort := nextPortVal, nextBindSeq := nextSeq }

/-- Returns `true` iff `sa` targets `127.255.255.255` or `::ffff:127.255.255.255`. -/
def isDirectedLoopBcastAddr : SockAddr → Bool
  | .ipv4 ip _ => ip == 0x7fffffff
  | .ipv6 hi lo _ _ _ => mappedV4Addr? hi lo == some 0x7fffffff
  | _ => false

/-- Map an IPv4 target (or `[::]` on an IPv4-mapped socket) onto `::ffff:a.b.c.d` when connecting an `AF_INET6` UDP socket. -/
def normalizeUdpTarget (dom : SockDomain) (rawAddr : SockAddr) (cliSa? : Option SockAddr := none) : SockAddr :=
  match dom, rawAddr with
  | .inet6, .ipv4 ip p => .ipv6 0 (ipv4ToMappedV6Lo ip) p 0 0
  | .inet6, .ipv6 0 0 tp fl sc =>
    match cliSa? with
    | some (.ipv6 chi clo _ _ _) =>
      if (mappedV4Addr? chi clo).isSome then
        .ipv6 0 (ipv4ToMappedV6Lo INADDR_LOOPBACK) tp fl sc
      else rawAddr
    | _ => rawAddr
  | _, _ => rawAddr

/-- Model transition helper for UDP `connect`. -/
def stepUdpConnect (s0 : NetState) (selfFid : FileId) (d0 : SockDesc)
    (fam : InetFamily) (bind : InetBind) (rawAddr : SockAddr) (obs? : Option NetOutcome) :
    Option (NetOutcome × NetState) :=
  let addr := normalizeUdpTarget d0.domain rawAddr bind.addr?
  let scopeAlts0 := if sockAddrHasScope rawAddr || d0.boundDevIf != 0 then [Errno.ENODEV] else []
  let scConflict := match ipv6ScopedIfindex? .dgram addr with
    | some sc => d0.boundDevIf != 0 && d0.boundDevIf != sc
    | none => false
  if addr.domain != d0.domain then
    emitErr obs? s0 (familyMismatchErrno d0.domain addr) ([Errno.EAFNOSUPPORT, Errno.EINVAL] ++ scopeAlts0)
      (fun e => if isTransientNetErrno e then s0 else autobindUdp s0 selfFid d0)
  else if scConflict || isInvalidV6LinkOrMulticast .dgram addr d0.boundDevIf then
    emitErr obs? s0 Errno.EINVAL ([Errno.ENETUNREACH, Errno.EACCES] ++ scopeAlts0)
      (fun e => if isTransientNetErrno e then s0 else autobindUdp s0 selfFid d0)
  else
    let d := match ipv6ScopedIfindex? .dgram addr with
      | some sc => { d0 with boundDevIf := sc }
      | none => d0
    let s := if d.boundDevIf != d0.boundDevIf then setFileSocket s0 selfFid d else s0
    let scopeAlts := if sockAddrHasScope rawAddr || d.boundDevIf != 0 then [Errno.ENODEV] else []
    match v6MappedNativeMismatchErrno? bind.addr? addr bind.isAddrLocked (loDownWasUp s.loState) with
    | some misErr =>
      emitErr obs? s0 misErr ([Errno.EAFNOSUPPORT, Errno.ENETUNREACH, Errno.EINVAL] ++ (if isBcastTargetAddr addr then [Errno.EACCES] else []) ++ scopeAlts)
        (fun e => if isTransientNetErrno e then s0 else autobindUdp s selfFid d)
    | none =>
      let sOk := applyUdpConnectOk s selfFid d fam bind addr
      if d.boundDevIf != 0 && d.boundDevIf != 1 then
        let allowExtUnit :=
          match addr with
          | .ipv6 0 0 _ _ _ | .ipv6 0 1 _ _ _ => false
          | _ => !isBcastTargetAddr addr
        emitErr obs? s0 Errno.ENETUNREACH ([Errno.ENODEV, Errno.EADDRNOTAVAIL, Errno.EINVAL, Errno.EACCES] ++ scopeAlts)
          (fun e => if isTransientNetErrno e then s0 else autobindUdp s selfFid d)
          (allowUnit? := if allowExtUnit then some sOk else none)
      else
        if isBcastTargetAddr addr then
          let loDown := match s.loState with | .down _ _ => true | _ => false
          let loWasUp127 := match s.loState with | .down _ true => true | _ => false
          let canonErr := if loDown then Errno.ENETUNREACH else Errno.EACCES
          emitErr obs? s0 canonErr ([Errno.ENETUNREACH, Errno.EACCES, Errno.EINVAL, Errno.EADDRNOTAVAIL] ++ scopeAlts)
            (fun e => if isTransientNetErrno e then s0 else autobindUdp s selfFid d)
            (allowUnit? := if loWasUp127 && isDirectedLoopBcastAddr addr then some sOk else none)
        else if isLoopbackTargetAddr addr then
          match s.loState with
          | .down _ false =>
            emitErr obs? s0 Errno.ENETUNREACH ([Errno.EADDRNOTAVAIL] ++ scopeAlts)
              (fun e => if isTransientNetErrno e then s0 else autobindUdp s selfFid d)
          | .down _ true =>
            emitErr obs? s0 Errno.ENETUNREACH ([Errno.EADDRNOTAVAIL] ++ scopeAlts)
              (fun e => if isTransientNetErrno e then s0 else autobindUdp s selfFid d)
              (allowUnit? := some sOk)
          | .unpinned _ =>
            emitUnit obs? s0 sOk ([Errno.ENETUNREACH, Errno.EADDRNOTAVAIL, Errno.EACCES, Errno.EINVAL] ++ scopeAlts)
              (fun e => if isTransientNetErrno e then s0 else autobindUdp s selfFid d)
          | .up _ =>
            let bcastSrcAlts := if (bind.addr?.map isBcastTargetAddr).getD false then [Errno.ENETUNREACH] else []
            emitUnit obs? s0 sOk (bcastSrcAlts ++ [Errno.EACCES, Errno.EINVAL] ++ scopeAlts)
              (fun e => if isTransientNetErrno e then s0 else autobindUdp s selfFid d)
        else
          emitUnit obs? s0 sOk ([Errno.ENETUNREACH, Errno.EACCES, Errno.EINVAL, Errno.EADDRNOTAVAIL] ++ scopeAlts)
            (fun e => if isTransientNetErrno e then s0 else autobindUdp s selfFid d)

/-- Model transition helper for `AF_UNIX` stream/seqpacket `connect`. -/
def stepUnixStreamConnect (s : NetState) (selfFid : FileId) (d : SockDesc)
    (isSeq : Bool) (bp? : Option ByteArray) (conn : UnixConnState)
    (addr : SockAddr) (obs? : Option NetOutcome) : Option (NetOutcome × NetState) :=
  if addr.domain != .unix then
    emitErr obs? s Errno.EINVAL []
  else
    match findMatchingListener s selfFid .unix d.sockType addr with
    | none =>
      let expectedErr :=
        match addr with
        | .unix p =>
          match findBoundUnixSocket s d.sockType p with
          | some (_, bd) => if bd.sockType != d.sockType then Errno.EPROTOTYPE else Errno.ECONNREFUSED
          | none =>
            if bytesListContains s.boundUnixPaths p || isAbstractUnixPath p then Errno.ECONNREFUSED
            else Errno.ENOENT
        | _ => Errno.EINVAL
      let selfListenFull :=
        match conn, d.localAddr?, addr with
        | .listen lBl lAq, some (.unix lp), .unix tp =>
          d.nonblock && bytesEq lp tp && lAq.length > lBl.toNat
        | _, _, _ => false
      let alts := [Errno.ECONNREFUSED, Errno.EACCES, Errno.ENOTDIR, Errno.ELOOP, Errno.ENAMETOOLONG] ++
        (if selfListenFull then [Errno.EAGAIN] else []) ++
        match conn with
        | .listen .. => [Errno.EINVAL, Errno.EISCONN, Errno.EOPNOTSUPP]
        | .connected .. => [Errno.EISCONN]
        | .idle => []
      emitErr obs? s expectedErr alts
    | some (lFid, lDesc, _) =>
      match lDesc.proto with
      | .unixStream lSeq lBp (.listen lBacklog aq) =>
        if lDesc.shut.rd then
          let shutAlts := match conn with | .listen .. => [Errno.EINVAL] | _ => []
          emitErr obs? s Errno.ECONNREFUSED shutAlts
        else
          let queueAlts := if d.nonblock && aq.length > lBacklog.toNat then [Errno.EAGAIN] else []
          match conn with
          | .listen .. => emitErr obs? s Errno.EINVAL ([Errno.EISCONN, Errno.EOPNOTSUPP] ++ queueAlts)
          | .connected .. => emitErr obs? s Errno.EISCONN queueAlts
          | .idle =>
            if aq.length > lBacklog.toNat then
              emitErr obs? s (if d.nonblock then Errno.EAGAIN else Errno.ECONNREFUSED)
                (if d.nonblock then [Errno.EAGAIN] else [])
            else
              let childFid := s.nextFileId
              let childDesc : SockDesc :=
                { proto := .unixStream lSeq lBp (.connected (some selfFid) false d.shut.rd false false)
                  nonblock := false, reuseAddr := false, unixAddrInherited := true }
              let cliPeer := match bp? with | some p => .unix p | none => defaultUnboundAddr .unix
              let accEntry : AcceptEntry :=
                { childFid, peerAddr := cliPeer, peerPortPinned := true, matchKind := .sameFamily }
              let s1 := setFileSocket s childFid childDesc
              let s2 := setFileSocket s1 lFid { lDesc with proto := .unixStream lSeq lBp (.listen lBacklog (aq ++ [accEntry])) }
              let cliDesc : SockDesc :=
                { d with soError := 0, proto := .unixStream isSeq bp? (.connected (some childFid) false false false false) }
              let sOk := { (setFileSocket s2 selfFid cliDesc) with nextFileId := childFid + 1 }
              emitUnit obs? s sOk (if d.nonblock then [Errno.EAGAIN] else [])
      | _ => emitErr obs? s Errno.ECONNREFUSED

/-- Model transition helper for TCP self-connect. -/
def stepTcpSelfConnect (s : NetState) (selfFid : FileId) (d : SockDesc)
    (fam : InetFamily) (bind : InetBind) (tainted : Bool) (addr : SockAddr)
    (obs? : Option NetOutcome) : Option (NetOutcome × NetState) :=
  let resolvedAddr := resolveTargetAddrForClient bind.addr? addr
  let selfLoc :=
    match bind.addr? with
    | some sa => concretizeSelfConnectLocal sa resolvedAddr d.inetSaddrZero
    | none => resolvedAddr
  let nextBind := InetBind.hashed selfLoc false bind.isPortLocked bind.isAddrLocked
  let nextTainted := tainted || (fam == .v6 && isIpv4MappedV6Addr resolvedAddr)
  let selfShutTear := d.shut.wr
  let loDownAlts := match s.loState with
    | .up _ => []
    | .down _ _ | .unpinned _ => [Errno.ENETUNREACH, Errno.EADDRNOTAVAIL]
  let bcastSrcAlts := if !d.inetSaddrZero && (bind.addr?.map isBcastTargetAddr).getD false then [Errno.ENETUNREACH] else []
  let connectAlts := loDownAlts ++ bcastSrcAlts ++ [Errno.ECONNREFUSED, Errno.EADDRNOTAVAIL]
  let mkState (ss : PosixSockState) (nextTcp : TcpState) (b : InetBind) : NetState :=
    setFileSocket s selfFid { d with soError := 0, inetSaddrZero := false, proto := .tcp fam b ss nextTcp nextTainted }
  if d.nonblock then
    let selfTcp :=
      if selfShutTear then TcpState.closedAfterConn selfLoc .selfShutRstPossible
      else TcpState.established (some selfFid) selfLoc
    let sInprog := mkState (.connecting false) selfTcp
      (if selfShutTear then nextBind.unhashUnlocked else nextBind)
    match obs? with
    | none => some (.err Errno.EINPROGRESS, sInprog)
    | some (.err e) =>
      if e == Errno.EINPROGRESS then some (.err e, sInprog)
      else if connectAlts.contains e || isTransientNetErrno e then some (.err e, s)
      else none
    | some .unit =>
      let sUnit := mkState .connected (.established (some selfFid) selfLoc)
        (if selfShutTear then nextBind.unhashUnlocked else nextBind)
      some (.unit, sUnit)
    | some _ => none
  else if selfShutTear then
    let sReset := resetDisconnectedTcp { d with soError := 0, proto := .tcp fam nextBind.unhashUnlocked .unconnected .idle nextTainted }
    let sUnit := mkState .connected (.established (some selfFid) selfLoc) nextBind.unhashUnlocked
    emitErr obs? s Errno.ECONNABORTED connectAlts (fun e => if e == Errno.ECONNABORTED then setFileSocket s selfFid sReset else s)
      (allowUnit? := some sUnit)
  else
    let sOk := mkState .connected (.established (some selfFid) selfLoc) nextBind
    emitUnit obs? s sOk connectAlts

/-- Resolve client local address for fresh TCP `connect` (`Addr` + ephemeral-port flag + updated `nextPort`). -/
def tcpConnectLocalBind (domain : SockDomain) (bind : InetBind) (addr : SockAddr)
    (ep nextP sNextPort : UInt16) (keepBoundMcastBcast : Bool := false)
    (inetSaddrZero : Bool := false) : SockAddr × Bool × UInt16 :=
  let resolveExisting (existing : SockAddr) : SockAddr :=
    if keepBoundMcastBcast then concretizeClientLocalAddr existing (some addr)
    else concretizeStreamOrClientLocalAddr .stream existing addr inetSaddrZero
  match bind with
  | .hashed existing eph _ _ =>
    (resolveExisting existing, eph, sNextPort)
  | .unhashed existing _ true =>
    ((resolveExisting existing).withPort ep, true, nextP)
  | .unbound | .unhashed _ _ false =>
    (defaultAutoClientAddr domain addr ep, true, nextP)

/-- Model listener lookup/refusal helper for fresh TCP `connect` once loopback reachability is checked. -/
def stepTcpConnectLookupListener (s : NetState) (selfFid : FileId) (d : SockDesc)
    (fam : InetFamily) (bind : InetBind) (nextTainted : Bool) (ep nextP : UInt16)
    (addr : SockAddr) (obs? : Option NetOutcome) : Option (NetOutcome × NetState) :=
  let (cliSa, eph, nextPVal) := tcpConnectLocalBind d.domain bind addr ep nextP s.nextPort false d.inetSaddrZero
  let resolvedAddr := resolveTargetAddrForClient (some cliSa) addr
  let boundLockedZero := (bind.addr?.map isAddrLockedZeroInetSaddr).getD false
  let isExtV4Wire := !isLoopbackTargetAddr resolvedAddr && (d.domain == .inet || isIpv4MappedV6Addr resolvedAddr)
  let nextMcastRouted := d.tcpMcastRoutedIp || (boundLockedZero && isExtV4Wire)
  let sUntaint :=
    if fam == .v6 && isIpv4MappedV6Addr resolvedAddr then
      setFileSocket s selfFid { d with proto := .tcp fam bind .unconnected .idle false }
    else s
  if !eph && hasTcpFourTupleConflict s selfFid cliSa resolvedAddr then
    emitErr obs? s Errno.EADDRNOTAVAIL []
      (fun e => if isTransientNetErrno e then s else sUntaint)
  else
  match findMatchingListener s selfFid d.domain .stream resolvedAddr with
  | some (lFid, lDesc, matchKind) =>
    match lDesc.proto with
    | .tcp lFam lBind lSs (.listen lBacklog aq) lTaint =>
      let isOverflowDrop := aq.length > lBacklog.toNat
      let cliBind := InetBind.hashed cliSa eph bind.isPortLocked bind.isAddrLocked
      let (sQueue, nextTcpState) :=
        if isOverflowDrop then
          (s, TcpState.synSent addr)
        else
          let (peerSaForLis, srvLocalSa) := computeLoopbackEndpoints cliSa resolvedAddr lDesc matchKind
          let childFid := s.nextFileId
          let srvBind := InetBind.hashed srvLocalSa false false (isBindAddrLockedSa srvLocalSa)
          let initChildTcp : TcpState :=
            if lDesc.shut.wr then .finWait (some selfFid) peerSaForLis
            else .established (some selfFid) peerSaForLis
          let childDesc : SockDesc :=
            { proto := .tcp lFam srvBind .connected initChildTcp lTaint
              nonblock := false, reuseAddr := lDesc.reuseAddr, shut := lDesc.shut, boundDevIf := lDesc.boundDevIf }
          let accEntry : AcceptEntry :=
            { childFid, peerAddr := peerSaForLis, peerPortPinned := !eph, matchKind,
              crossFamily := (matchKind != .sameFamily), peerRoutedV4 := nextMcastRouted }
          let s1 := setFileSocket s childFid childDesc
          let s2 := setFileSocket s1 lFid { lDesc with proto := .tcp lFam lBind lSs (.listen lBacklog (aq ++ [accEntry])) lTaint }
          let lisTaintedNative := lFam == .v6 && lTaint && isNativeV6PeerAddr peerSaForLis
          let cliTcp : TcpState :=
            if lDesc.shut.wr && !lisTaintedNative then .closeWait (some childFid) srvLocalSa false
            else .established (some childFid) srvLocalSa
          ({ s2 with nextFileId := childFid + 1 }, cliTcp)
      let sWithQueue := { sQueue with nextPort := nextPVal }
      let mkCliState (ss : PosixSockState) : NetState :=
        setFileSocket sWithQueue selfFid { d with soError := 0, inetSaddrZero := false, tcpMcastRoutedIp := nextMcastRouted, proto := .tcp fam cliBind ss nextTcpState nextTainted }
      let unpinnedAlts := match s.loState with | .unpinned _ => [Errno.ENETUNREACH, Errno.EADDRNOTAVAIL] | _ => []
      let bcastSrcAlts := if !d.inetSaddrZero && (bind.addr?.map isBcastTargetAddr).getD false then [Errno.ENETUNREACH] else []
      let crossAlts := if matchKind != .sameFamily && !d.nonblock then [Errno.ECONNREFUSED, Errno.ENETUNREACH, Errno.EADDRNOTAVAIL] else []
      let reuseAlts := if d.reuseAddr then [Errno.EADDRNOTAVAIL] else []
      let allAlts := unpinnedAlts ++ bcastSrcAlts ++ crossAlts ++ reuseAlts
      if d.nonblock then
        let sInprog := mkCliState (.connecting (matchKind != .sameFamily))
        let sUnit := mkCliState .connected
        emitErr obs? s Errno.EINPROGRESS allAlts
          (fun e => if e == Errno.EINPROGRESS then sInprog else if e == Errno.ECONNREFUSED then s else sUntaint)
          (allowUnit? := some sUnit)
      else if isOverflowDrop then
        let sInprog := mkCliState (.connecting false)
        let sOverflowFail :=
          setFileSocket sWithQueue selfFid
            (resetDisconnectedTcp { d with soError := 0, inetSaddrZero := false, tcpMcastRoutedIp := nextMcastRouted, proto := .tcp fam cliBind.unhashUnlocked .unconnected .idle nextTainted })
        let ovfAlts := [Errno.EINTR, Errno.ECONNREFUSED] ++ allAlts
        emitErr obs? s Errno.ETIMEDOUT ovfAlts
          (fun e =>
            if e == Errno.EINTR then sInprog
            else if e == Errno.ETIMEDOUT || e == Errno.ECONNREFUSED then sOverflowFail
            else sUntaint)
      else
        emitUnit obs? s (mkCliState .connected) allAlts
          (fun e => if e == Errno.ECONNREFUSED || isTransientNetErrno e then s else sUntaint)
    | _ => emitErr obs? s Errno.ECONNREFUSED
  | none =>
    let nextBind := (InetBind.hashed cliSa eph bind.isPortLocked bind.isAddrLocked).unhashUnlocked
    let sInprog := { (setFileSocket s selfFid { d with soError := Errno.ECONNREFUSED, inetSaddrZero := false, tcpMcastRoutedIp := nextMcastRouted, proto := .tcp fam nextBind (.connecting false) (.synSent addr) nextTainted }) with nextPort := nextPVal }
    if d.nonblock then
      let alts := [Errno.ETIMEDOUT, Errno.EHOSTUNREACH, Errno.EADDRNOTAVAIL, Errno.ENETUNREACH, Errno.EINVAL, Errno.EACCES, Errno.ECONNREFUSED]
      emitErr obs? s Errno.EINPROGRESS alts (fun e =>
        if e == Errno.EINPROGRESS then sInprog
        else if e == Errno.ECONNREFUSED || e == Errno.ETIMEDOUT || e == Errno.EHOSTUNREACH then
          { (setFileSocket s selfFid { d with soError := 0, shut := {}, inetSaddrZero := false, tcpMcastRoutedIp := nextMcastRouted, proto := .tcp fam nextBind .unconnected .idle nextTainted }) with nextPort := nextPVal }
        else sUntaint)
    else
      let sRefused :=
        { (setFileSocket s selfFid
            (resetDisconnectedTcp { d with soError := 0, shut := {}, inetSaddrZero := false, tcpMcastRoutedIp := nextMcastRouted, proto := .tcp fam nextBind .unconnected .idle nextTainted })) with nextPort := nextPVal }
      let alts := [Errno.ETIMEDOUT, Errno.EHOSTUNREACH, Errno.EADDRNOTAVAIL, Errno.ENETUNREACH, Errno.EINVAL, Errno.EACCES, Errno.EINTR]
      emitErr obs? s Errno.ECONNREFUSED alts
        (fun e =>
          if e == Errno.EINTR then sInprog
          else if e == Errno.ECONNREFUSED || e == Errno.ETIMEDOUT || e == Errno.EHOSTUNREACH then sRefused
          else sUntaint)

/-- Core post-scope helper for fresh TCP `connect`. -/
def stepTcpConnectNewCore (s : NetState) (selfFid : FileId) (d : SockDesc)
    (fam : InetFamily) (bind : InetBind) (tainted : Bool) (addr : SockAddr)
    (obs? : Option NetOutcome) : Option (NetOutcome × NetState) :=
  let scopeAlts := if sockAddrHasScope addr || d.boundDevIf != 0 then [Errno.ENODEV] else []
  let loDownLoopAlts :=
    if isLoopbackTargetAddr addr && (match s.loState with | .down _ _ => true | _ => false) then
      [Errno.EADDRNOTAVAIL]
    else []
  match v6MappedNativeMismatchErrno? bind.addr? addr bind.isAddrLocked (loDownWasUp s.loState) with
  | some misErr =>
    emitErr obs? s misErr ([Errno.EAFNOSUPPORT, Errno.ENETUNREACH, Errno.EINVAL] ++ scopeAlts ++ loDownLoopAlts)
  | none =>
    let effAddr := resolveTargetAddrForClient bind.addr? addr
    let nextTainted := tainted || (fam == .v6 && isIpv4MappedV6Addr effAddr)
    let (ep, nextP) := allocNextPort s
    if fam == .v6 && tainted && !isIpv4MappedV6Addr effAddr then
      let (locSa, eph, nextPVal) :=
        match bind with
        | .hashed sa ep0 _ _ => (sa, ep0 || !bind.isPortLocked, s.nextPort)
        | .unhashed sa _ true => (sa.withPort ep, true, nextP)
        | .unbound | .unhashed _ _ false => ((defaultUnboundAddr .inet6).withPort ep, true, nextP)
      let nextBind := (InetBind.hashed locSa eph bind.isPortLocked bind.isAddrLocked).unhashUnlocked
      let taintAlts := [Errno.ENETUNREACH, Errno.EAFNOSUPPORT, Errno.EINVAL, Errno.EADDRNOTAVAIL] ++ scopeAlts ++ loDownLoopAlts
      let sInprog := { (setFileSocket s selfFid { d with soError := 0, proto := .tcp .v6 nextBind (.connecting false) (.synSent effAddr) nextTainted }) with nextPort := nextPVal }
      if d.nonblock then
        emitErr obs? s Errno.EINPROGRESS taintAlts (fun e => if e == Errno.EINPROGRESS then sInprog else s)
      else
        let sFail := { (setFileSocket s selfFid { d with soError := 0, shut := {}, proto := .tcp .v6 nextBind .unconnected (.closedAfterConn effAddr .reset) nextTainted }) with nextPort := nextPVal }
        emitErr obs? s Errno.ETIMEDOUT ([Errno.EINTR] ++ taintAlts)
          (fun e => if e == Errno.EINTR then sInprog else if e == Errno.ETIMEDOUT then sFail else s)
    else if isMcastOrBcastTargetAddr effAddr then
      let untaintS :=
        if fam == .v6 && tainted && isIpv4MappedV6Addr effAddr then
          setFileSocket s selfFid { d with proto := .tcp fam bind .unconnected .idle false }
        else s
      let loWasUp127 := isDirectedLoopBcastAddr effAddr && match s.loState with | .down _ true => true | _ => false
      if loWasUp127 then
        let (cliSa, eph, nextPVal) := tcpConnectLocalBind d.domain bind effAddr ep nextP s.nextPort (keepBoundMcastBcast := d.tcpLoDownDirectedBcast)
        let nextBind := (InetBind.hashed cliSa eph bind.isPortLocked bind.isAddrLocked).unhashUnlocked
        let sInprog := { (setFileSocket s selfFid { d with soError := 0, proto := .tcp fam nextBind (.connecting false) (.synSent effAddr) nextTainted }) with nextPort := nextPVal }
        let sLoBcastFail :=
          { (setFileSocket s selfFid (resetDisconnectedTcp { d with soError := 0, proto := .tcp fam nextBind .unconnected .idle nextTainted })) with nextPort := nextPVal }
        if d.nonblock then
          let alts := [Errno.EADDRNOTAVAIL, Errno.ETIMEDOUT, Errno.EINPROGRESS, Errno.EACCES, Errno.EINVAL] ++ scopeAlts
          emitErr obs? s Errno.ENETUNREACH alts (fun e => if e == Errno.EINPROGRESS then sInprog else untaintS)
        else
          let alts := [Errno.EADDRNOTAVAIL, Errno.ETIMEDOUT, Errno.EINTR, Errno.EACCES, Errno.EINVAL] ++ scopeAlts
          emitErr obs? s Errno.ENETUNREACH alts
            (fun e => if e == Errno.EINTR then sInprog else if e == Errno.ETIMEDOUT then sLoBcastFail else untaintS)
      else
        emitErr obs? untaintS Errno.ENETUNREACH ([Errno.EACCES, Errno.EINVAL] ++ scopeAlts)
    else if d.boundDevIf != 0 && d.boundDevIf != 1 then
      let (cliSa, eph, nextPVal) := tcpConnectLocalBind d.domain bind effAddr ep nextP s.nextPort (keepBoundMcastBcast := false)
      let nextBind := (InetBind.hashed cliSa eph bind.isPortLocked bind.isAddrLocked).unhashUnlocked
      let untaintS :=
        if fam == .v6 && tainted && isIpv4MappedV6Addr effAddr then
          setFileSocket s selfFid { d with proto := .tcp fam bind .unconnected .idle false }
        else s
      let sSynFail := { (setFileSocket s selfFid { d with soError := 0, shut := {}, proto := .tcp fam nextBind .unconnected .idle nextTainted }) with nextPort := nextPVal }
      let sInprog := { (setFileSocket s selfFid { d with soError := Errno.ECONNREFUSED, proto := .tcp fam nextBind (.connecting false) (.synSent effAddr) nextTainted }) with nextPort := nextPVal }
      if d.nonblock then
        let alts := [Errno.ENODEV, Errno.EADDRNOTAVAIL, Errno.ETIMEDOUT, Errno.EHOSTUNREACH, Errno.EINVAL, Errno.EACCES, Errno.ECONNREFUSED, Errno.EINPROGRESS]
        emitErr obs? s Errno.ENETUNREACH alts (fun e =>
          if e == Errno.EINPROGRESS then sInprog
          else if e == Errno.ECONNREFUSED || e == Errno.ETIMEDOUT || e == Errno.EHOSTUNREACH then sSynFail
          else untaintS)
      else
        let alts := [Errno.ENODEV, Errno.EADDRNOTAVAIL, Errno.ETIMEDOUT, Errno.EHOSTUNREACH, Errno.EINVAL, Errno.EACCES, Errno.ECONNREFUSED, Errno.EINTR]
        emitErr obs? s Errno.ENETUNREACH alts (fun e =>
          if e == Errno.EINTR then sInprog
          else if e == Errno.ECONNREFUSED || e == Errno.ETIMEDOUT || e == Errno.EHOSTUNREACH then sSynFail
          else untaintS)
    else
      let isLoop := isLoopbackTargetAddr effAddr
      let loBlocked := isLoop && match s.loState with | .down _ _ => true | _ => false
      let loWasUp := isLoop && match s.loState with | .down _ true => true | _ => false
      if loBlocked then
        let untaintS :=
          if fam == .v6 && tainted && isIpv4MappedV6Addr effAddr then
            setFileSocket s selfFid { d with proto := .tcp fam bind .unconnected .idle false }
          else s
        let (cliSa, eph, nextPVal) := tcpConnectLocalBind d.domain bind effAddr ep nextP s.nextPort (keepBoundMcastBcast := d.tcpLoDownDirectedBcast)
        let nextBind := (InetBind.hashed cliSa eph bind.isPortLocked bind.isAddrLocked).unhashUnlocked
        let sInprog := { (setFileSocket s selfFid { d with soError := 0, proto := .tcp fam nextBind (.connecting false) (.synSent effAddr) nextTainted }) with nextPort := nextPVal }
        let sLoFail :=
          { (setFileSocket s selfFid (resetDisconnectedTcp { d with soError := 0, proto := .tcp fam nextBind .unconnected .idle nextTainted })) with nextPort := nextPVal }
        if d.nonblock && loWasUp then
          let alts := [Errno.EADDRNOTAVAIL, Errno.ETIMEDOUT, Errno.EINPROGRESS] ++ scopeAlts
          emitErr obs? s Errno.ENETUNREACH alts (fun e => if e == Errno.EINPROGRESS then sInprog else untaintS)
        else if loWasUp then
          let alts := [Errno.EADDRNOTAVAIL, Errno.ETIMEDOUT, Errno.EINTR] ++ scopeAlts
          emitErr obs? s Errno.ENETUNREACH alts
            (fun e => if e == Errno.EINTR then sInprog else if e == Errno.ETIMEDOUT then sLoFail else untaintS)
        else
          let alts := [Errno.EADDRNOTAVAIL] ++ scopeAlts
          emitErr obs? untaintS Errno.ENETUNREACH alts
      else if isTcpSelfConnect d effAddr then
        stepTcpSelfConnect s selfFid d fam bind tainted effAddr obs?
      else
        stepTcpConnectLookupListener s selfFid d fam bind nextTainted ep nextP effAddr obs?

/-- Model transition helper for fresh TCP `connect`. -/
def stepTcpConnectNew (s0 : NetState) (selfFid : FileId) (d0 : SockDesc)
    (fam : InetFamily) (bind : InetBind) (tainted : Bool) (addr : SockAddr)
    (obs? : Option NetOutcome) : Option (NetOutcome × NetState) :=
  let scopeAlts0 := if sockAddrHasScope addr || d0.boundDevIf != 0 then [Errno.ENODEV] else []
  let llScopeConflict := match ipv6LinkLocalScope? addr with
    | some sc => d0.boundDevIf != 0 && d0.boundDevIf != sc
    | none => false
  if addr.domain != d0.domain then
    emitErr obs? s0 (familyMismatchErrno d0.domain addr) ([Errno.EAFNOSUPPORT, Errno.EINVAL] ++ scopeAlts0)
  else if (isIpv6LinkLocalNoScope addr && d0.boundDevIf == 0) || llScopeConflict then
    emitErr obs? s0 Errno.EINVAL scopeAlts0
  else
    let d := match ipv6LinkLocalScope? addr with
      | some sc => { d0 with boundDevIf := sc }
      | none => d0
    let s := if d.boundDevIf != d0.boundDevIf then setFileSocket s0 selfFid d else s0
    stepTcpConnectNewCore s selfFid d fam bind tainted addr obs?

/-- Model transition helper for `Net.connect` on `.connected` TCP sockets. -/
def stepConnectConnected (s : NetState) (selfFid : FileId) (d : SockDesc)
    (addr : SockAddr) (obs? : Option NetOutcome) : Option (NetOutcome × NetState) :=
  match d.tcpSelfSynPending with
  | false => emitErr obs? s Errno.EISCONN []
  | true =>
    match obs? with
    | none => some (.err Errno.EISCONN, s)
    | some (.err e) =>
      if e == Errno.EISCONN || isTransientNetErrno e then some (.err e, s)
      else
        let dReset := resetDisconnectedTcp d
        match dReset.proto with
        | .tcp fam1 bind1 _ _ taint1 => stepTcpConnectNew s selfFid dReset fam1 bind1 taint1 addr obs?
        | _ => none
    | some .unit =>
      let dReset := resetDisconnectedTcp d
      match dReset.proto with
      | .tcp fam1 bind1 _ _ taint1 => stepTcpConnectNew s selfFid dReset fam1 bind1 taint1 addr obs?
      | _ => none
    | some _ => none

/-- Model transition helper for `Net.connect` on `.connecting` ready TCP states. -/
def stepConnectConnectingReady (s : NetState) (selfFid : FileId) (d : SockDesc)
    (fam : InetFamily) (bind : InetBind) (cf : Bool) (tcpState : TcpState) (tainted : Bool)
    (obs? : Option NetOutcome) : Option (NetOutcome × NetState) :=
  let sUnit := setFileSocket s selfFid { d with proto := .tcp fam bind .connected tcpState tainted }
  match obs? with
  | none => some (.unit, sUnit)
  | some o =>
    match o with
    | .unit => some (.unit, sUnit)
    | .err e =>
      if cf && (e == Errno.ECONNREFUSED || e == Errno.ECONNABORTED) then
        let dUnhashed := { d with proto := .tcp fam bind.unhashUnlocked (.connecting cf) tcpState tainted }
        some (.err e, setFileSocket s selfFid (resetDisconnectedTcp dUnhashed))
      else if e == Errno.EISCONN || e == Errno.EALREADY || isTransientNetErrno e then some (.err e, s)
      else none
    | _ => none

/-- Model transition helper for `Net.connect` on `.connecting` TCP sockets. -/
def stepConnectConnecting (s : NetState) (selfFid : FileId) (d : SockDesc)
    (fam : InetFamily) (bind : InetBind) (cf : Bool) (tcpState : TcpState) (tainted : Bool)
    (obs? : Option NetOutcome) : Option (NetOutcome × NetState) :=
  match consumePendingSoError d with
  | some pend =>
    let pendErr := pend.1
    let dCleared := pend.2
    let dReset := resetDisconnectedTcp dCleared
    match obs? with
    | none => some (.err pendErr, setFileSocket s selfFid dReset)
    | some o =>
      match o with
      | .err e =>
        if isAsyncConnectErrno pendErr e d || e == Errno.ECONNABORTED then
          some (.err e, setFileSocket s selfFid dReset)
        else if e == Errno.EALREADY || (d.tcpLoFinPending && e == Errno.EISCONN) || isTransientNetErrno e then some (.err e, s)
        else none
      | .unit =>
        if d.tcpLoFinPending then
          match dCleared.proto with
          | .tcp fam1 bind1 _ tcp1 taint1 =>
            match tcp1 with
            | .closedAfterConn pa cr1 =>
              match cr1 with
              | .reset => some (.unit, setFileSocket s selfFid { dCleared with proto := .tcp fam1 bind1 .connected (.closeWait none pa true) taint1 })
              | _ => none
            | _ => none
          | _ => none
        else none
      | _ => none
  | none =>
    match tcpState with
    | .established _ _ => stepConnectConnectingReady s selfFid d fam bind cf tcpState tainted obs?
    | .finWait _ _ => stepConnectConnectingReady s selfFid d fam bind cf tcpState tainted obs?
    | .closeWait _ _ _ => stepConnectConnectingReady s selfFid d fam bind cf tcpState tainted obs?
    | .closedAfterConn _ _ =>
      emitErr obs? s Errno.ECONNABORTED [Errno.EINVAL]
        (fun e =>
          if e == Errno.EINVAL || isTransientNetErrno e then s
          else setFileSocket s selfFid { resetDisconnectedTcp d with soError := 0 })
    | .synSent _ => emitErr obs? s Errno.EALREADY
    | .idle => emitErr obs? s Errno.EALREADY
    | .listen _ _ => emitErr obs? s Errno.EALREADY

/-- Model transition for `Net.connect`. -/
def stepConnect (s : NetState) (hid : HandleId) (addr : SockAddr) (obs? : Option NetOutcome) :
    Option (NetOutcome × NetState) :=
  withSock s hid obs? fun selfFid d =>
    match d.proto with
    | .unixDgram bp? peer? => stepUnixDgramConnect s selfFid d bp? peer? addr obs?
    | .udp fam bind _ => stepUdpConnect s selfFid d fam bind addr obs?
    | .unixStream isSeq bp? conn => stepUnixStreamConnect s selfFid d isSeq bp? conn addr obs?
    | .tcp fam bind sockState tcpState tainted =>
      match sockState with
      | .connected => stepConnectConnected s selfFid d addr obs?
      | .disconnecting =>
        let dReset := { resetDisconnectedTcp d with soError := 0 }
        emitErr obs? s Errno.ECONNABORTED [Errno.EINVAL]
          (fun e => if e == Errno.EINVAL || isTransientNetErrno e then s else setFileSocket s selfFid dReset)
      | .connecting cf => stepConnectConnecting s selfFid d fam bind cf tcpState tainted obs?
      | .unconnected =>
        match tcpState with
        | .listen .. => emitErr obs? s Errno.EISCONN [Errno.EINVAL, Errno.EOPNOTSUPP]
        | _ => stepTcpConnectNew s selfFid d fam bind tainted addr obs?

private def isTcpLoFinPendingRst (d : SockDesc) : Bool :=
  d.tcpLoFinPending &&
    match d.proto with | .tcp _ _ _ (.closedAfterConn _ .reset) _ => true | _ => false

/-- Model transition for `Net.getsockopt`. -/
def stepGetsockopt (s : NetState) (hid : HandleId) (opt : SockOpt) (obs? : Option NetOutcome) :
    Option (NetOutcome × NetState) :=
  withSock s hid obs? fun selfFid d =>
    match opt with
    | .reuseAddr =>
      emitU32 obs? s (if d.reuseAddr then 1 else 0) s
    | .error =>
      match consumePendingSoError d with
      | some (pendErr, dCleared) =>
        let isConnPending := match d.proto with | .tcp _ _ (.connecting _) _ _ => true | _ => false
        let isInetDgram := match d.proto with | .udp .. => true | _ => false
        let sOk := setFileSocket s selfFid dCleared
        match obs? with
        | none => some (.u32 pendErr, sOk)
        | some (.u32 v) =>
          if isAsyncConnectErrno pendErr v d then some (.u32 v, sOk)
          else if v == 0 && (isConnPending || isInetDgram || d.tcpLoFinPending) then some (.u32 0, s)
          else if v == Errno.ENETUNREACH && d.tcpLoSoftUnreach && (isConnPending || isInetDgram || d.tcpLoFinPending) then
            some (.u32 v, setFileSocket s selfFid { d with tcpLoSoftUnreach := false })
          else none
        | some (.err e) => if isTransientNetErrno e then some (.err e, s) else none
        | some _ => none
      | none =>
        match d.proto with
        | .unixStream isSeq bp (.connected pf? psw pwb true prGc) =>
          let cleared := setFileSocket s selfFid { d with proto := .unixStream isSeq bp (.connected pf? psw pwb false false) }
          match obs? with
          | none => some (.u32 Errno.ECONNRESET, cleared)
          | some (.u32 v) =>
            if v == Errno.ECONNRESET then some (.u32 v, cleared)
            else if v == 0 && prGc then some (.u32 0, cleared)
            else none
          | some (.err e) => if isTransientNetErrno e then some (.err e, s) else none
          | some _ => none
        | .tcp fam bind ss (.closedAfterConn pa .selfShutRstPossible) taint =>
          let resetSock := setFileSocket s selfFid { d with proto := .tcp fam bind ss (.closedAfterConn pa .reset) taint }
          match obs? with
          | none => some (.u32 0, s)
          | some (.u32 v) =>
            if v == 0 then some (.u32 0, s)
            else if v == Errno.ECONNRESET then some (.u32 v, resetSock)
            else if v == Errno.ENETUNREACH && d.tcpLoSoftUnreach then
              some (.u32 v, setFileSocket s selfFid { d with tcpLoSoftUnreach := false })
            else none
          | some (.err e) => if isTransientNetErrno e then some (.err e, s) else none
          | some _ => none
        | _ =>
          let clearCf := match d.proto with
            | .tcp fam bind (.connecting true) ts taint =>
              setFileSocket s selfFid { d with proto := .tcp fam bind (.connecting false) ts taint }
            | _ => s
          match obs? with
          | none => some (.u32 0, clearCf)
          | some (.u32 v) =>
            if v == 0 then some (.u32 0, clearCf)
            else if v == Errno.ENETUNREACH && d.tcpLoSoftUnreach then
              some (.u32 v, setFileSocket s selfFid { d with tcpLoSoftUnreach := false })
            else if (v == Errno.EPIPE || (v == Errno.ECONNRESET && d.tcpLoFinPending)) && d.tcpCloseWaitRst then
              match d.proto with
              | .tcp fam bind ss (.closeWait _ pa _) taint =>
                some (.u32 v, setFileSocket s selfFid { d with tcpCloseWaitRst := false, tcpLastAck := false, proto := .tcp fam bind.unhashUnlocked ss (.closedAfterConn pa .reset) taint })
              | _ => none
            else if v == Errno.ECONNRESET && d.tcpShutRdwrRst then
              some (.u32 v, clearTcpShutRdwrRst s selfFid d)
            else
              match d.proto with
              | .tcp _ _ (.connecting true) _ _ =>
                if v == Errno.ECONNREFUSED then some (.u32 v, setFileSocket s selfFid (resetDisconnectedTcp d))
                else none
              | _ => none
          | some (.err e) => if isTransientNetErrno e then some (.err e, s) else none
          | some _ => none

/-- Model transition for `Net.setsockopt`. -/
def stepSetsockopt (s : NetState) (hid : HandleId) (opt : SetSockOpt) (val : UInt32) (obs? : Option NetOutcome) :
    Option (NetOutcome × NetState) :=
  withSock s hid obs? fun selfFid d =>
    match opt with
    | .reuseAddr =>
      emitUnit obs? s (setFileSocket s selfFid { d with reuseAddr := val != 0 })

/-- Model transition for `Net.getsockname`. -/
def stepGetsockname (s : NetState) (hid : HandleId) (obs? : Option NetOutcome) :
    Option (NetOutcome × NetState) :=
  withSock s hid obs? fun selfFid d =>
    match d.localAddr? with
    | none =>
      let canon := defaultUnboundAddr d.domain
      emitAddr obs? s canon fun gotSa => if gotSa == canon then some s else none
    | some curSa =>
      let eph := match d.proto with
        | .tcp _ bind .. | .udp _ bind _ => bind.isEphemeral
        | _ => false
      let addrLocked := match d.proto with
        | .tcp _ bind .. | .udp _ bind _ => bind.isAddrLocked
        | _ => true
      let peer? := match d.proto with
        | .tcp _ _ _ (.synSent pa) _ | .tcp _ _ _ (.established _ pa) _
        | .tcp _ _ _ (.finWait _ pa) _ | .tcp _ _ _ (.closeWait _ pa _) _
        | .tcp _ _ _ (.closedAfterConn pa _) _ => some pa
        | .udp _ _ pa? => pa?
        | _ => none
      let matchesRouted (gotSa : SockAddr) : Bool :=
        match peer? with
        | some pa =>
          !isLoopbackTargetAddr pa &&
          match curSa, gotSa with
          | .ipv4 _ p1, .ipv4 ip2 p2 =>
            ip2 != INADDR_ANY && p2 != 0 && (eph || p1 == p2)
          | .ipv6 _ _ p1 fl1 sc1, .ipv6 hi2 lo2 p2 fl2 sc2 =>
            let expSc := if ipv6NeedsScopeId d.sockType gotSa then d.boundDevIf else 0
            !(hi2 == 0 && lo2 == 0) && p2 != 0 && fl1 == fl2 && (sc1 == sc2 || sc2 == expSc) && (eph || p1 == p2)
          | _, _ => false
        | none => false
      let matchesMcastRouted (gotSa : SockAddr) : Bool :=
        d.tcpMcastRoutedIp &&
          match curSa, gotSa with
          | .ipv4 _ p1, .ipv4 ip2 p2 =>
            ip2 != INADDR_ANY && p2 != 0 && (eph || p1 == p2)
          | .ipv6 0 lo1 p1 fl1 sc1, .ipv6 0 lo2 p2 fl2 sc2 =>
            (mappedV4Addr? 0 lo1).isSome &&
              match mappedV4Addr? 0 lo2 with
              | some ip2 => ip2 != INADDR_ANY && p2 != 0 && fl1 == fl2 && sc1 == sc2 && (eph || p1 == p2)
              | none => false
          | _, _ => false
      let withResolved (gotSa : SockAddr) : SockProtoState :=
        match d.proto with
        | .tcp fam (.hashed _ _ pl al) ss ts taint => .tcp fam (.hashed gotSa false pl al) ss ts taint
        | .tcp fam (.unhashed _ _ al) ss ts taint => .tcp fam (.unhashed gotSa false al) ss ts taint
        | .udp fam (.hashed _ _ pl al) cp => .udp fam (.hashed gotSa false pl al) cp
        | .udp fam (.unhashed _ _ al) cp => .udp fam (.unhashed gotSa false al) cp
        | other => other
      emitAddr obs? s curSa fun gotSa =>
        if gotSa == curSa then
          some (if eph then setFileSocket s selfFid { d with proto := withResolved gotSa } else s)
        else if matchesMcastRouted gotSa then
          some (setFileSocket s selfFid { d with tcpMcastRoutedIp := false, proto := withResolved gotSa })
        else if eph && (matchesEphemeralAddr curSa gotSa || matchesRouted gotSa) then
          some (setFileSocket s selfFid { d with proto := withResolved gotSa })
        else if !eph && !addrLocked && (matchesResettableLocalAddr curSa gotSa || matchesRouted gotSa) then
          some (setFileSocket s selfFid { d with proto := withResolved gotSa })
        else none

/-- Disconnect an `AF_UNIX` datagram socket if its peer FD is no longer open. -/
def disconnectUnixDgramIfPeerClosed (s : NetState) (d : SockDesc) : Option SockDesc :=
  match d.proto with
  | .unixDgram bp? (some (peerFid, _)) =>
    match lookupFileSocket s peerFid with
    | .ok _ => none
    | .error _ => some { d with proto := .unixDgram bp? none, rxQueue := [] }
  | _ => none

private def deliverRx (s : NetState) (targetFid : FileId) (unit : RxUnit) : NetState :=
  match lookupFileSocket s targetFid with
  | .ok pd => setFileSocket s targetFid { pd with rxQueue := pd.rxQueue ++ [unit] }
  | .error _ => s

private def tcpPeerWritableStatus (d : SockDesc) :
    Option (Option FileId × SockAddr × Bool) :=
  match d.proto with
  | .tcp _ _ _ (.established pf? pa) _ => some (pf?, pa, false)
  | .tcp _ _ _ (.finWait pf? pa) _ => some (pf?, pa, false)
  | .tcp _ _ _ (.closeWait pf? pa pcc) _ => some (pf?, pa, pcc)
  | _ => none

private def applyTcpCleanCloseRst (s : NetState) (selfFid : FileId) (d : SockDesc)
    (pa : SockAddr) : NetState :=
  match d.proto with
  | .tcp fam bind ss tcpState taint =>
    let err := match tcpState with | .closeWait .. => Errno.EPIPE | _ => Errno.ECONNRESET
    let d' := { d with soError := err, tcpLastAck := false, proto := .tcp fam bind.unhashUnlocked ss (.closedAfterConn pa .reset) taint }
    setFileSocket s selfFid d'
  | _ => s

/-- Returns `true` iff `d` is a disconnected/closed TCP socket returning EOF on empty RX. -/
def isTcpClosedEof (d : SockDesc) : Bool :=
  match d.proto with
  | .tcp _ _ _ (.closedAfterConn _ _) _ => true
  | .tcp _ _ .disconnecting _ _ => true
  | _ => false

/-- Returns `true` iff `d` is a TCP socket whose connect is in `.connecting`. -/
def isFailedConnectingTcp (d : SockDesc) : Bool :=
  match d.proto with | .tcp _ _ (.connecting _) _ _ => true | _ => false

/-- Returns `true` iff `d`'s remote peer has closed its write half (`closeWait`/FIN/`psw`). -/
def isPeerClosedRx (d : SockDesc) : Bool :=
  match d.proto with
  | .tcp _ _ _ (.closeWait ..) _ | .tcp _ _ _ (.closedAfterConn ..) _ => true
  | .unixStream _ _ (.connected _ psw _ _ _) => psw
  | _ => false

/-- Clear `peerReset` on a connected `AF_UNIX` `SOCK_SEQPACKET` socket before receiving. -/
def clearUnixSeqPeerReset? (d : SockDesc) : Option (SockDesc × Bool × Bool) :=
  match d.proto with
  | .unixStream true bp (.connected pf? psw pwb true prGc) =>
    some ({ d with proto := .unixStream true bp (.connected pf? psw pwb false false) }, prGc, psw)
  | _ => none

/-- Model transition body helper for `Net.recvfrom`. -/
def stepRecvfromBody (s : NetState) (selfFid : FileId) (d : SockDesc)
    (maxBytes : UInt32) (flags : MsgFlags) (obs? : Option NetOutcome) :
    Option (NetOutcome × NetState) :=
  let cap := clampMaxReadU32 maxBytes
  let isNb := d.nonblock || flags.dontwait
  if d.sockType == .dgram then
    match d.rxQueue with
    | u :: restQ =>
      let want := min u.bytes.size cap
      let canon := sliceBytes u.bytes 0 want
      let sOk :=
        if flags.peek then s
        else releaseUnusedFiles (setFileSocket s selfFid { d with rxQueue := restQ }) u.scm
      emitBytes obs? s canon
        (fun got => if got == canon then some sOk else none)
        (if d.domain != .unix && isNb then [Errno.EAGAIN] else [])
    | [] =>
      if d.shut.rd && !isNb then
        emitBytes obs? s ByteArray.empty (fun got => if got.size == 0 then some s else none)
      else
        emitErr obs? s Errno.EAGAIN (if isNb then [] else [])
          (allowTransient := true)
  else if !isEstablished d && d.rxQueue.isEmpty then
    let tcpClosedEof := isTcpClosedEof d
    let failedConnecting := isFailedConnectingTcp d
    let loFinAlts :=
      (if d.domain != .unix && isNb && d.tcpLoFinPending then [Errno.EAGAIN] else []) ++
      (if tcpClosedEof && d.domain != .unix then [Errno.ENOTCONN] else [])
    if tcpClosedEof || (d.domain != .unix && !d.proto.isListening && d.shut.rd) then
      let extraAlts :=
        loFinAlts ++
        (if failedConnecting then [Errno.ENOTCONN] ++ (if isNb then [Errno.EAGAIN] else []) else [])
      emitBytes obs? s ByteArray.empty (fun got => if got.size == 0 then some s else none) extraAlts
    else
      let alts :=
        (if d.domain == .unix then [Errno.EINVAL] else []) ++
        (if failedConnecting && isNb then [Errno.EAGAIN] else [])
      let allowBlkZero? : Option (ByteArray → Option NetState) :=
        if isConnectingTcp d && !isNb && cap == 0 then
          some (fun got => if got.size == 0 then some s else none)
        else none
      emitErr obs? s Errno.ENOTCONN alts (allowBytes? := allowBlkZero?)
  else if d.sockType == .stream then
    let (availBytes, dummyMask) := collectStreamRead (if cap == 0 then 1 else cap) d.rxQueue
    if availBytes.size > 0 then
      if cap == 0 then
        let sOk :=
          if !flags.peek && d.domain == .unix then
            let (strippedQ, droppedScm) := stripFirstStreamScm d.rxQueue
            if droppedScm.isEmpty then s
            else releaseUnusedFiles (setFileSocket s selfFid { d with rxQueue := strippedQ }) droppedScm
          else s
        emitBytes obs? s ByteArray.empty (fun got => if got.size == 0 then some sOk else none)
          (if d.domain != .unix && isNb then [Errno.EAGAIN] else [])
      else
        let canon := availBytes
        let peerClosed := isPeerClosedRx d
        match obs? with
        | none =>
          let n := canon.size
          let sOk :=
            if flags.peek then s
            else
              let droppedScm := collectConsumedStreamScm n d.rxQueue
              releaseUnusedFiles (setFileSocket s selfFid { d with rxQueue := consumeStreamQueue n d.rxQueue }) droppedScm
          some (.bytes canon, sOk)
        | some (.bytes got) =>
          let n := got.size
          if n >= 1 && n <= availBytes.size && streamBytesMatches got availBytes dummyMask then
            let sOk :=
              if flags.peek then s
              else
                let droppedScm := collectConsumedStreamScm n d.rxQueue
                releaseUnusedFiles (setFileSocket s selfFid { d with rxQueue := consumeStreamQueue n d.rxQueue }) droppedScm
            some (.bytes got, sOk)
          else if n == 0 && d.domain != .unix && (d.shut.rd || peerClosed) then
            some (.bytes got, s)
          else none
        | some (.err e) =>
          if (d.domain != .unix && isNb && e == Errno.EAGAIN) || isTransientNetErrno e then some (.err e, s)
          else none
        | some _ => none
    else
      match d.proto with
      | .unixStream isSeq bp (.connected pf? psw pwb true prGc) =>
        let sClr := setFileSocket s selfFid { d with proto := .unixStream isSeq bp (.connected pf? psw pwb false false) }
        match obs? with
        | none => some (.err Errno.ECONNRESET, sClr)
        | some (.err e) =>
          if e == Errno.ECONNRESET then some (.err e, sClr)
          else if isTransientNetErrno e then some (.err e, s)
          else none
        | some (.bytes got) =>
          if prGc && (psw || d.shut.rd) && got.size == 0 then some (.bytes got, sClr) else none
        | some _ => none
      | _ =>
        let peerClosed := isPeerClosedRx d
        if peerClosed || d.shut.rd then
          let loFinAlts := if d.domain != .unix && isNb && d.tcpLoFinPending then [Errno.EAGAIN] else []
          emitBytes obs? s ByteArray.empty (fun got => if got.size == 0 then some s else none) loFinAlts
        else
          let allowBlkZero? : Option (ByteArray → Option NetState) :=
            if d.domain != .unix && !isNb && cap == 0 then
              some (fun got => if got.size == 0 then some s else none)
            else none
          emitErr obs? s Errno.EAGAIN []
            (allowTransient := true) (allowBytes? := allowBlkZero?)
  else
    match clearUnixSeqPeerReset? d with
    | some (dClr, prGc, psw) =>
      let sClr := setFileSocket s selfFid dClr
      match obs? with
      | none => some (.err Errno.ECONNRESET, sClr)
      | some (.err e) =>
        if e == Errno.ECONNRESET then some (.err e, sClr)
        else if isTransientNetErrno e then some (.err e, s)
        else none
      | some (.bytes got) =>
        if d.rxQueue.isEmpty && prGc && (psw || d.shut.rd) && got.size == 0 then some (.bytes got, sClr) else none
      | some _ => none
    | none =>
      match d.rxQueue with
      | u :: restQ =>
        let want := min u.bytes.size cap
        let canon := sliceBytes u.bytes 0 want
        let sOk :=
          if flags.peek then s
          else releaseUnusedFiles (setFileSocket s selfFid { d with rxQueue := restQ }) u.scm
        emitBytes obs? s canon
          (fun got =>
            if (u.isScmDummy && want == 1 && got.size == 1) || got == canon then some sOk
            else none)
      | [] =>
        match d.proto with
        | .unixStream isSeq bp (.connected pf? psw pwb true prGc) =>
          let sClr := setFileSocket s selfFid { d with proto := .unixStream isSeq bp (.connected pf? psw pwb false false) }
          match obs? with
          | none => some (.err Errno.ECONNRESET, sClr)
          | some (.err e) =>
            if e == Errno.ECONNRESET then some (.err e, sClr)
            else if isTransientNetErrno e then some (.err e, s)
            else none
          | some (.bytes got) =>
            if prGc && (psw || d.shut.rd) && got.size == 0 then some (.bytes got, sClr) else none
          | some _ => none
        | .unixStream _ _ (.connected _ true ..) =>
          emitBytes obs? s ByteArray.empty (fun got => if got.size == 0 then some s else none)
        | _ =>
          if d.shut.rd then
            emitBytes obs? s ByteArray.empty (fun got => if got.size == 0 then some s else none)
          else
            emitErr obs? s Errno.EAGAIN

private def recoverTcpLoCloseWait (s : NetState) (selfFid : FileId) (d : SockDesc) : Option NetState :=
  match d.proto with
  | .tcp fam bind ss (.closedAfterConn pa .reset) taint =>
    some (setFileSocket s selfFid { d with soError := 0, proto := .tcp fam bind ss (.closeWait none pa true) taint })
  | _ => none

private def tcpLoCleanCloseRst? (s : NetState) (selfFid : FileId) (d : SockDesc) : Option NetState :=
  match d.proto with
  | .tcp fam bind ss (.closedAfterConn pa .reset) taint =>
    some (setFileSocket s selfFid { d with soError := Errno.EPIPE, proto := .tcp fam bind.unhashUnlocked ss (.closedAfterConn pa .reset) taint })
  | _ => none

/-- Model transition for `Net.recvfrom`. -/
def stepRecvfrom (s : NetState) (hid : HandleId) (maxBytes : UInt32) (flags : MsgFlags)
    (obs? : Option NetOutcome) : Option (NetOutcome × NetState) :=
  withSock s hid obs? fun selfFid d =>
    let isNb := d.nonblock || flags.dontwait
    let body := stepRecvfromBody s selfFid d maxBytes flags obs?
    match consumeRecvPendingSoError d with
    | some (pendErr, dCleared) =>
      let isOptionalDgram := d.domain != .unix && d.sockType == .dgram && pendErr == Errno.ECONNREFUSED
      let isStreamNonEmpty := d.sockType == .stream && !d.rxQueue.isEmpty
      let isOptionalErr := isOptionalDgram || isStreamNonEmpty
      let isConnPending := match d.proto with | .tcp _ _ (.connecting _) _ _ => true | _ => false
      let sCleared := setFileSocket s selfFid dCleared
      match obs? with
      | none =>
        if isStreamNonEmpty then body else some (.err pendErr, sCleared)
      | some (.err e) =>
        if isStreamNonEmpty && body.isSome then body
        else if isAsyncConnectErrno pendErr e d then some (.err e, sCleared)
        else if (isConnPending && ((isNb && e == Errno.EAGAIN) || e == Errno.ENOTCONN)) ||
            (d.domain != .unix && d.sockType == .dgram && isNb && e == Errno.EAGAIN) ||
            (d.tcpLoFinPending && isNb && e == Errno.EAGAIN) then
          some (.err e, s)
        else if isTransientNetErrno e then some (.err e, s)
        else if isOptionalErr then body
        else none
      | some (.bytes got) =>
        if isOptionalErr then body
        else if isConnPending && !isNb && maxBytes == 0 && got.size == 0 then
          some (.bytes got, s)
        else if isTcpLoFinPendingRst d && d.rxQueue.isEmpty && got.size == 0 then
          match recoverTcpLoCloseWait s selfFid d with
          | some sCw => some (.bytes got, sCw)
          | none => none
        else none
      | _ => if isOptionalErr then body else none
    | none =>
      match obs? with
      | some (.err e) =>
        if e == Errno.ECONNRESET then
          match tcpConsumeShutRdwrRecvRst? s selfFid d with
          | some sRst => some (.err Errno.ECONNRESET, sRst)
          | none => body
        else body
      | _ => body

private def setTcpLoFinPending (s : NetState) (fid : FileId) : NetState :=
  match lookupFileSocket s fid with
  | .ok pd => setFileSocket s fid { pd with tcpLoFinPending := true }
  | .error _ => s

private def markTcpLoFinPending (s : NetState) (fid : FileId) : NetState :=
  match lookupFileSocket s fid with
  | .ok pd =>
    match pd.proto with
    | .tcp _ _ _ (.closeWait ..) _ | .tcp _ _ _ (.closedAfterConn _ _) _ =>
      setFileSocket s fid { pd with tcpLoFinPending := true }
    | _ => s
  | .error _ => s

private def isTaintedV6NativePeer (d : SockDesc) (pa : SockAddr) : Bool :=
  match d.proto with
  | .tcp .v6 _ _ _ true => pa.domain == .inet6 && !isIpv4MappedV6Addr pa
  | _ => false

private def tcpDeliverOrPeerRst (s : NetState) (selfFid : FileId) (d : SockDesc)
    (pf? : Option FileId) (pa : SockAddr) (unit : RxUnit) : NetState :=
  let loUp := match s.loState with | .up _ => true | _ => false
  if isTaintedV6NativePeer d pa then s
  else if !loUp then
    let s1 := setFileSocket s selfFid { d with tcpLoStalledTx := true, tcpLoSoftUnreach := d.tcpLoSoftUnreach || (d.domain == .inet6 && !isIpv4MappedV6Addr pa) }
    match pf? with
    | some peerFid => { s1 with loPendingTcp := s1.loPendingTcp ++ [.tx selfFid peerFid unit] }
    | none => s1
  else if d.tcpLoStalledTx then s
  else
    match pf? with
  | some peerFid =>
    match lookupFileSocket s peerFid with
    | .ok pd =>
      let peerFinRdShut :=
        match pd.proto with
        | .tcp _ _ _ (.finWait ..) _ | .tcp _ _ _ (.closedAfterConn ..) _ => pd.shut.isBoth
        | _ => false
      if peerFinRdShut then
        let s1 := applyTcpCleanCloseRst s selfFid d pa
        let s2 :=
          match pd.proto with
          | .tcp pfam pbind psock ptcp ptaint =>
            let ppa := match ptcp with | .established _ a | .finWait _ a | .closeWait _ a _ | .closedAfterConn a _ => a | _ => defaultUnboundAddr pd.domain
            let nextPtcp := match ptcp with | .established .. | .finWait .. | .closeWait .. | .closedAfterConn .. => TcpState.closedAfterConn ppa .reset | other => other
            setFileSocket s1 peerFid { pd with soError := Errno.ECONNRESET, proto := .tcp pfam pbind.unhashUnlocked psock nextPtcp ptaint }
          | _ => s1
        if pd.rxQueue.isEmpty then s2
        else setTcpLoFinPending (setTcpLoFinPending s2 selfFid) peerFid
      else deliverRx s peerFid unit
    | .error _ => applyTcpCleanCloseRst s selfFid d pa
  | none => s

private def udpLoDownAlts (s : NetState) (d : SockDesc) : List Errno :=
  match d.proto with
  | .udp fam bind (some targetAddr) =>
    let bcastAlts :=
      if (bind.addr?.map isBcastTargetAddr).getD false || isBcastTargetAddr targetAddr then
        [Errno.ENETUNREACH, Errno.EACCES]
      else []
    let loAlts :=
      match s.loState with
      | .down _ _ | .unpinned _ =>
        if fam == .v6 || !isLoopbackTargetAddr targetAddr then [Errno.ENETUNREACH] else []
      | .up _ => []
    bcastAlts ++ loAlts
  | _ => []

/-- Model transition body helper for `Net.sendto`. -/
def stepSendtoBody (s : NetState) (selfFid : FileId) (d : SockDesc)
    (data : ByteArray) (flags : MsgFlags) (obs? : Option NetOutcome) :
    Option (NetOutcome × NetState) :=
  let isNb := d.nonblock || flags.dontwait
  let dgramTooBig := if d.sockType != .stream && data.size > 65507 then [Errno.EMSGSIZE] else []
  if d.sockType == .dgram && !isEstablished d then
    let unconnErr := if d.domain == .unix then (if d.shut.wr then Errno.EPIPE else Errno.ENOTCONN) else Errno.EDESTADDRREQ
    emitErr obs? s unconnErr dgramTooBig (fun e => if isTransientNetErrno e then s else autobindUdp s selfFid d)
  else if !isEstablished d then
    let connPend := match d.proto with | .tcp _ _ (.connecting _) _ _ => true | _ => false
    let selfRst := d.tcpShutRdwrRst || match d.proto with | .tcp _ _ _ (.closedAfterConn _ .selfShutRstPossible) _ => true | _ => false
    let loFinErrAlts := if isTcpLoFinPendingRst d && !d.shut.wr && isNb then [Errno.EAGAIN] else []
    let alts := [Errno.ENOTCONN] ++ (if connPend && isNb then [Errno.EAGAIN] else []) ++
      (if selfRst then [Errno.ECONNRESET] else []) ++ loFinErrAlts ++
      (if d.sockType == .seqpacket then dgramTooBig else [])
    let loFinU32? : Option (UInt32 → Option NetState) :=
      if isTcpLoFinPendingRst d && !d.shut.wr then
        some fun n =>
          if data.size == 0 then
            if n == 0 then recoverTcpLoCloseWait s selfFid d else none
          else
            let maxSend := min data.size 4294967295
            if n.toNat >= 1 && n.toNat <= maxSend then tcpLoCleanCloseRst? s selfFid d else none
      else none
    emitErr obs? s Errno.EPIPE alts (fun e =>
      if e == Errno.ECONNRESET && d.tcpShutRdwrRst then
        clearTcpShutRdwrRst s selfFid d
      else
        match d.proto with
        | .tcp fam bind ss (.closedAfterConn pa .selfShutRstPossible) taint =>
          if e == Errno.ECONNRESET then setFileSocket s selfFid { d with proto := .tcp fam bind ss (.closedAfterConn pa .reset) taint } else s
        | _ =>
          if isTcpLoFinPendingRst d && !d.shut.wr && e == Errno.EPIPE then
            setFileSocket s selfFid { d with soError := 0 }
          else s)
      (allowU32? := loFinU32?)
  else if d.domain == .unix && d.sockType == .seqpacket then
    match d.proto with
    | .unixStream isSeq bp (.connected pf? psw pwb true prGc) =>
      let sClr := setFileSocket s selfFid { d with proto := .unixStream isSeq bp (.connected pf? psw pwb false false) }
      let alts := (if prGc then [Errno.EPIPE, Errno.ESHUTDOWN] else []) ++ dgramTooBig
      emitErr obs? s Errno.ECONNRESET alts (fun e => if e != Errno.EMSGSIZE && (e == Errno.ECONNRESET || prGc) then sClr else s)
    | _ =>
      if d.shut.wr then emitErr obs? s Errno.EPIPE ([Errno.ESHUTDOWN] ++ dgramTooBig)
      else
        match d.proto with
        | .unixStream _ _ (.connected _ _ true _ _) => emitErr obs? s Errno.EPIPE ([Errno.ECONNRESET, Errno.ESHUTDOWN] ++ dgramTooBig)
        | .unixStream _ _ (.connected (some peerFid) ..) =>
          let unit : RxUnit := { bytes := data }
          let sOk := deliverRx s peerFid unit
          emitU32 obs? s (UInt32.ofNat data.size) sOk ((if isNb then [Errno.EAGAIN] else []) ++ dgramTooBig)
        | _ => emitErr obs? s Errno.EPIPE ([Errno.ECONNRESET, Errno.ESHUTDOWN] ++ dgramTooBig)
  else if d.shut.wr then
    let shutRstAlts := if d.tcpShutRdwrRst then [Errno.ECONNRESET] else []
    emitErr obs? s Errno.EPIPE ([Errno.ESHUTDOWN] ++ shutRstAlts ++ udpLoDownAlts s d ++ dgramTooBig)
      (fun e => if e == Errno.ECONNRESET && d.tcpShutRdwrRst then clearTcpShutRdwrRst s selfFid d else s)
  else
    match disconnectUnixDgramIfPeerClosed s d with
    | some dDisc =>
      emitErr obs? s Errno.ECONNREFUSED dgramTooBig
        (fun e => if isTransientNetErrno e || e == Errno.EMSGSIZE then s else releaseRxScm (setFileSocket s selfFid dDisc) d.rxQueue)
    | none =>
      match d.proto with
      | .unixDgram _ (some (peerFid, _)) =>
        match lookupFileSocket s peerFid with
        | .ok pd =>
          if isUnixDgramPeerBusy selfFid pd then emitErr obs? s Errno.EPERM dgramTooBig
          else if pd.shut.rd then emitErr obs? s Errno.EPIPE dgramTooBig
          else
            let sOk := deliverRx s peerFid { bytes := data }
            emitU32 obs? s (UInt32.ofNat data.size) sOk ((if isNb then [Errno.EAGAIN] else []) ++ dgramTooBig)
        | .error _ => emitErr obs? s Errno.ECONNREFUSED dgramTooBig
      | .unixStream _ _ (.connected (some peerFid) _ pwb _ _) =>
        if pwb then emitErr obs? s Errno.EPIPE [Errno.ECONNRESET, Errno.ESHUTDOWN]
        else if data.size == 0 then
          emitU32 obs? s 0 s (if isNb then [Errno.EAGAIN] else [])
        else
          let maxSend := min data.size 4294967295
          match obs? with
          | none =>
            let len32 := UInt32.ofNat maxSend
            let sOk := deliverRx s peerFid { bytes := sliceBytes data 0 maxSend }
            some (.u32 len32, sOk)
          | some (.u32 n) =>
            if n.toNat >= 1 && n.toNat <= maxSend then
              some (.u32 n, deliverRx s peerFid { bytes := sliceBytes data 0 n.toNat })
            else none
          | some (.err e) =>
            if (isNb && e == Errno.EAGAIN) || isTransientNetErrno e then some (.err e, s)
            else none
          | some _ => none
      | .unixStream _ _ (.connected none ..) =>
        emitErr obs? s Errno.EPIPE [Errno.ECONNRESET, Errno.ESHUTDOWN]
      | .tcp _ _ _ tcpState _ =>
        match tcpState with
        | .established pf? pa | .finWait pf? pa | .closeWait pf? pa false =>
          if data.size == 0 then
            let cwAlts := if d.tcpCloseWaitRst then [Errno.EPIPE, Errno.ECONNRESET] else []
            emitU32 obs? s 0 s ((if isNb then [Errno.EAGAIN] else []) ++ cwAlts)
              (onAltErr := fun e =>
                if d.tcpCloseWaitRst && (e == Errno.EPIPE || e == Errno.ECONNRESET) then
                  clearTcpCloseWaitRst s selfFid d
                else s)
          else
            let maxSend := min data.size 4294967295
            let doSend (n : Nat) : NetState :=
              let unit : RxUnit := { bytes := sliceBytes data 0 n }
              tcpDeliverOrPeerRst s selfFid d pf? pa unit
            match obs? with
            | none => some (.u32 (UInt32.ofNat maxSend), doSend maxSend)
            | some (.u32 n) =>
              if n.toNat >= 1 && n.toNat <= maxSend then some (.u32 n, doSend n.toNat) else none
            | some (.err e) =>
              if d.tcpCloseWaitRst && (e == Errno.EPIPE || e == Errno.ECONNRESET) then
                match d.proto with
                | .tcp fam bind ss (.closeWait _ pa _) taint =>
                  some (.err e, setFileSocket s selfFid { d with tcpCloseWaitRst := false, tcpLastAck := false, proto := .tcp fam bind.unhashUnlocked ss (.closedAfterConn pa .reset) taint })
                | _ => none
              else if (isNb && e == Errno.EAGAIN) || isTransientNetErrno e then some (.err e, s) else none
            | some _ => none
        | .closeWait none pa true =>
          if data.size == 0 then
            let cwAlts := if d.tcpCloseWaitRst then [Errno.EPIPE, Errno.ECONNRESET] else []
            emitU32 obs? s 0 s ((if isNb then [Errno.EAGAIN] else []) ++ cwAlts)
              (onAltErr := fun e =>
                if d.tcpCloseWaitRst && (e == Errno.EPIPE || e == Errno.ECONNRESET) then
                  clearTcpCloseWaitRst s selfFid d
                else s)
          else
            let maxSend := min data.size 4294967295
            let loUp := match s.loState with | .up _ => true | _ => false
            let sSent :=
              if isTaintedV6NativePeer d pa then s
              else if loUp then applyTcpCleanCloseRst s selfFid d pa
              else setFileSocket s selfFid { d with tcpLoStalledTx := true, tcpLoFinPending := true, tcpLoSoftUnreach := d.tcpLoSoftUnreach || (d.domain == .inet6 && !isIpv4MappedV6Addr pa) }
            match obs? with
            | none => some (.u32 (UInt32.ofNat maxSend), sSent)
            | some (.u32 n) =>
              if n.toNat >= 1 && n.toNat <= maxSend then some (.u32 n, sSent) else none
            | some (.err e) =>
              if d.tcpCloseWaitRst && (e == Errno.EPIPE || e == Errno.ECONNRESET) then
                some (.err e, clearTcpCloseWaitRst s selfFid d)
              else if e == Errno.EPIPE || e == Errno.ECONNRESET || (isNb && e == Errno.EAGAIN) || isTransientNetErrno e then
                some (.err e, s)
              else none
            | some _ => none
        | _ => emitErr obs? s Errno.EPIPE [Errno.ECONNRESET, Errno.ESHUTDOWN]
      | .udp fam _ (some targetAddr) =>
        if fam == .v6 && isIpv4MappedV6Addr targetAddr && targetAddr.port? == some 0 then
          emitErr obs? s Errno.EINVAL dgramTooBig
        else if d.boundDevIf != 0 && d.boundDevIf != 1 then
          let extAlts :=
            [Errno.ENODEV, Errno.EADDRNOTAVAIL, Errno.EINVAL, Errno.EACCES, Errno.ECONNREFUSED] ++
            (if isNb then [Errno.EAGAIN] else []) ++ dgramTooBig
          let extU32? : Option (UInt32 → Option NetState) :=
            if data.size <= 65507 then
              some fun n => if n == UInt32.ofNat data.size then some s else none
            else none
          emitErr obs? s Errno.ENETUNREACH extAlts (allowU32? := extU32?)
        else
          let loDownAlts := udpLoDownAlts s d
          let loUp := match s.loState with | .up _ => true | _ => false
          match ipv4AllHostsMcastPort? targetAddr with
          | some _ =>
            let peers := findBoundUdpMcastPeers s d targetAddr
            let sOk := if loUp then peers.foldl (fun acc fid => deliverRx acc fid { bytes := data }) s else s
            emitU32 obs? s (UInt32.ofNat data.size) sOk
              (loDownAlts ++ (if isNb then [Errno.EAGAIN] else []) ++ dgramTooBig)
          | none =>
            match findBoundUdpPeer s d targetAddr with
            | some (peerFid, _) =>
              let sOk := if loUp then deliverRx s peerFid { bytes := data } else s
              emitU32 obs? s (UInt32.ofNat data.size) sOk
                (loDownAlts ++ (if isNb then [Errno.EAGAIN] else []) ++ dgramTooBig)
            | none =>
              let sOk :=
                if loUp && isLoopbackTargetAddr targetAddr then
                  setFileSocket s selfFid { d with soError := Errno.ECONNREFUSED }
                else s
              emitU32 obs? s (UInt32.ofNat data.size) sOk
                (loDownAlts ++ [Errno.ECONNREFUSED] ++ (if isNb then [Errno.EAGAIN] else []) ++ dgramTooBig)
      | _ => emitErr obs? s Errno.EDESTADDRREQ

/-- Model transition for `Net.sendto`. -/
def stepSendto (s : NetState) (hid : HandleId) (data : ByteArray) (flags : MsgFlags)
    (obs? : Option NetOutcome) : Option (NetOutcome × NetState) :=
  withSock s hid obs? fun selfFid d =>
    let isNb := d.nonblock || flags.dontwait
    let body := stepSendtoBody s selfFid d data flags obs?
    match consumePendingSoError d with
    | some (pendErr, dCleared) =>
      let isOptionalDgram := d.domain != .unix && d.sockType == .dgram && pendErr == Errno.ECONNREFUSED
      let isLoPendingRst := !d.shut.wr && isTcpLoFinPendingRst d
      let isConnPending := match d.proto with | .tcp _ _ (.connecting _) _ _ => true | _ => false
      let sCleared := setFileSocket s selfFid dCleared
      match obs? with
      | none => some (.err pendErr, sCleared)
      | some (.err e) =>
        if isAsyncConnectErrno pendErr e d then some (.err e, sCleared)
        else if d.shut.wr && e == Errno.EPIPE then
          some (.err e, if d.tcpLoFinPending && pendErr != Errno.EPIPE then s else sCleared)
        else if isLoPendingRst && (e == Errno.EPIPE || e == Errno.ESHUTDOWN || (isNb && e == Errno.EAGAIN)) then body
        else if isConnPending && isNb && e == Errno.EAGAIN then some (.err e, s)
        else if (d.sockType != .stream && data.size > 65507 && e == Errno.EMSGSIZE) || isTransientNetErrno e then
          some (.err e, s)
        else if isOptionalDgram then body
        else none
      | _ => if isOptionalDgram || isLoPendingRst then body else none
    | none => body

/-- Model transition for `Net.shutdown`. -/
def stepShutdown (s : NetState) (hid : HandleId) (how : ShutHow) (obs? : Option NetOutcome) :
    Option (NetOutcome × NetState) :=
  withSock s hid obs? fun selfFid d =>
    let doRd := how == .rd || how == .rdwr
    let doWr := how == .wr || how == .rdwr
    let nextShut := d.shut.apply how
    match d.proto with
    | .tcp fam bind sockState tcpState tainted =>
      match tcpState with
      | .listen _ aq =>
        if doRd then
          let s1 := resetListenerAcceptQueue s aq
          let sOk := setFileSocket s1 selfFid { d with shut := {}, proto := .tcp fam bind.unhashUnlocked .unconnected .idle tainted }
          emitUnit obs? s sOk [Errno.ENOTCONN]
        else
          emitUnit obs? s s [Errno.ENOTCONN]
      | .idle =>
        let nextSs := match sockState with | .connecting _ => .disconnecting | other => other
        emitErr obs? s Errno.ENOTCONN [] (fun e =>
          if isTransientNetErrno e then s
          else setFileSocket s selfFid { d with shut := nextShut, proto := .tcp fam bind nextSs tcpState tainted })
      | .closedAfterConn pa reason =>
        let nextSs := match sockState with | .connecting _ => .disconnecting | other => other
        let nextReason :=
          match reason with
          | .cleanFin =>
            if nextShut.isBoth && d.tcpLoFinPending && !d.rxQueue.isEmpty then .selfShutRstPossible
            else .cleanFin
          | other => other
        let sShut := setFileSocket s selfFid { d with shut := nextShut, proto := .tcp fam bind nextSs (.closedAfterConn pa nextReason) tainted }
        let allowSelfRst := match reason with | .selfShutRstPossible => true | _ => false
        emitErr obs? s Errno.ENOTCONN [] (fun e => if isTransientNetErrno e then s else sShut)
          (allowUnit? := if d.tcpLoFinPending || allowSelfRst then some sShut else none)
      | .synSent target =>
        let dUnhashed :=
          { d with
            soError := Errno.ECONNRESET
            proto := .tcp fam bind.unhashUnlocked .unconnected .idle tainted }
        let sOk := setFileSocket s selfFid (resetDisconnectedTcp dUnhashed)
        emitUnit obs? s sOk [Errno.ENOTCONN] (fun e =>
          if isTransientNetErrno e then s
          else
            setFileSocket s selfFid
              { d with
                shut := nextShut
                proto := .tcp fam bind.unhashUnlocked .disconnecting (.closedAfterConn target .reset) tainted })
      | .established pf? pa =>
        let nextSockState := match sockState with | .connecting _ => .connected | other => other
        if nextShut.isBoth && pf? == some selfFid && !d.rxQueue.isEmpty then
          let loUp := match s.loState with | .up _ => true | _ => false
          let nextSoftUnreach := d.tcpLoSoftUnreach || (!loUp && doWr && d.domain == .inet6 && !isIpv4MappedV6Addr pa)
          let sOk := setFileSocket s selfFid
            { d with shut := nextShut, tcpLoFinPending := true, tcpLoSoftUnreach := nextSoftUnreach, proto := .tcp fam bind.unhashUnlocked nextSockState (.closedAfterConn pa .selfShutRstPossible) tainted }
          emitUnit obs? s sOk [Errno.ENOTCONN]
        else if doWr then
          let loUp := match s.loState with | .up _ => true | _ => false
          let nextBind := if pf? == some selfFid then bind.unhashUnlocked else bind
          let nextSelfTcp : TcpState := if pf? == some selfFid then .closedAfterConn pa .cleanFin else .finWait pf? pa
          let selfSynPend := d.tcpSelfSynPending || (pf? == some selfFid && match sockState with | .connecting _ => true | _ => false)
          let selfFinPend := d.tcpLoFinPending || (pf? == some selfFid) || (!loUp && pf?.isSome)
          let nextSoftUnreach := d.tcpLoSoftUnreach || (!loUp && d.domain == .inet6 && !isIpv4MappedV6Addr pa)
          let nextShutRst := d.tcpShutRdwrRst || (pf? != some selfFid && nextShut.isBoth && !d.rxQueue.isEmpty)
          let s1 := setFileSocket s selfFid { d with shut := nextShut, tcpSelfSynPending := selfSynPend, tcpLoFinPending := selfFinPend, tcpLoSoftUnreach := nextSoftUnreach, tcpShutRdwrRst := nextShutRst, proto := .tcp fam nextBind nextSockState nextSelfTcp tainted }
          let sOk := match pf? with
            | some peerFid =>
              if peerFid == selfFid || (fam == .v6 && tainted && pa.domain == .inet6 && !isIpv4MappedV6Addr pa) then s1
              else if !loUp then { s1 with loPendingTcp := s1.loPendingTcp ++ [.shutFin selfFid peerFid] }
              else
                match lookupFileSocket s1 peerFid with
                | .ok pd =>
                  match pd.proto with
                  | .tcp pfam pbind psock (.established _ ppa) ptaint =>
                    let peerTaintedNative := pfam == .v6 && ptaint && isNativeV6PeerAddr ppa
                    let delayFin := peerTaintedNative && !pd.rxQueue.isEmpty
                    setFileSocket s1 peerFid
                      { pd with
                        tcpLoFinPending := pd.tcpLoFinPending || delayFin
                        tcpCloseWaitRst := pd.tcpCloseWaitRst || nextShut.isBoth
                        proto := .tcp pfam pbind psock (.closeWait (some selfFid) ppa false) ptaint }
                  | .tcp pfam pbind psock (.finWait _ ppa) ptaint =>
                    if pfam == .v6 && ptaint && isNativeV6PeerAddr ppa then
                      let delayFin := !pd.rxQueue.isEmpty
                      setFileSocket s1 peerFid
                        { pd with
                          tcpLoFinPending := pd.tcpLoFinPending || delayFin
                          proto := .tcp pfam pbind psock (.closeWait (some selfFid) ppa false) ptaint }
                    else
                      let s2 := setFileSocket s1 peerFid { pd with proto := .tcp pfam pbind.unhashUnlocked psock (.closedAfterConn ppa .cleanFin) ptaint }
                      setFileSocket s2 selfFid { d with shut := nextShut, proto := .tcp fam bind.unhashUnlocked nextSockState (.closedAfterConn pa .cleanFin) tainted }
                  | _ => s1
                | .error _ =>
                  setFileSocket s1 selfFid { d with shut := nextShut, soError := Errno.ECONNRESET, tcpShutRdwrRst := false, proto := .tcp fam bind.unhashUnlocked nextSockState (.closedAfterConn pa .reset) tainted }
            | none => s1
          emitUnit obs? s sOk [Errno.ENOTCONN]
        else
          let sOk := setFileSocket s selfFid { d with shut := nextShut, proto := .tcp fam bind nextSockState tcpState tainted }
          emitUnit obs? s sOk [Errno.ENOTCONN]
      | .finWait pf? pa =>
        let nextSockState := match sockState with | .connecting _ => .connected | other => other
        let nextShutRst := d.tcpShutRdwrRst || (pf? != some selfFid && nextShut.isBoth && !d.rxQueue.isEmpty)
        let s1 := setFileSocket s selfFid { d with shut := nextShut, tcpShutRdwrRst := nextShutRst, proto := .tcp fam bind nextSockState (.finWait pf? pa) tainted }
        let loUp := match s.loState with | .up _ => true | _ => false
        let sOk :=
          if !nextShut.isBoth || !loUp then s1
          else
            match pf? with
            | some peerFid =>
              if peerFid == selfFid || (fam == .v6 && tainted && pa.domain == .inet6 && !isIpv4MappedV6Addr pa) then s1
              else
                match lookupFileSocket s1 peerFid with
                | .ok pd =>
                  match pd.proto with
                  | .tcp _ _ _ (.closeWait ..) _ => setFileSocket s1 peerFid { pd with tcpCloseWaitRst := true }
                  | _ => s1
                | .error _ => s1
            | none => s1
        emitUnit obs? s sOk [Errno.ENOTCONN]
          (onAltErr := fun e =>
            if e == Errno.ENOTCONN && nextShutRst then
              setFileSocket s selfFid { d with shut := nextShut, tcpShutRdwrRst := true, proto := .tcp fam bind.unhashUnlocked nextSockState (.closedAfterConn pa .reset) tainted }
            else s)
      | .closeWait pf? pa pcc =>
        let nextSockState := match sockState with | .connecting _ => .connected | other => other
        let onCwShutErr := fun (e : Errno) =>
          if e == Errno.ENOTCONN && d.tcpCloseWaitRst then
            setFileSocket s selfFid
              { d with
                shut := nextShut
                soError := if d.soError == 0 then Errno.EPIPE else d.soError
                tcpCloseWaitRst := false
                tcpLastAck := false
                proto := .tcp fam bind.unhashUnlocked nextSockState (.closedAfterConn pa .reset) tainted }
          else s
        if doWr then
          let loUp := match s.loState with | .up _ => true | _ => false
          let selfTaintedNative := fam == .v6 && tainted && isNativeV6PeerAddr pa
          let peerTaintedNative :=
            match pf? with
            | some peerFid =>
              if peerFid == selfFid then false
              else
                match lookupFileSocket s peerFid with
                | .ok pd =>
                  match pd.proto with
                  | .tcp pfam _ _ _ ptaint => pfam == .v6 && ptaint && isNativeV6PeerAddr pa
                  | _ => false
                | .error _ => false
            | none => false
          let finStuck := selfTaintedNative || (!loUp && pf? != some selfFid) || peerTaintedNative
          let nextSoftUnreach := d.tcpLoSoftUnreach || (!loUp && !selfTaintedNative && d.domain == .inet6 && !isIpv4MappedV6Addr pa)
          let nextBind := if finStuck then bind else bind.unhashUnlocked
          let nextReason : TcpCloseReason := if d.tcpCloseWaitRst then .selfShutRstPossible else .cleanFin
          let nextSelfTcp : TcpState := if finStuck then .closeWait pf? pa pcc else .closedAfterConn pa nextReason
          let s1 := setFileSocket s selfFid { d with shut := nextShut, tcpLoSoftUnreach := nextSoftUnreach, tcpCloseWaitRst := finStuck && d.tcpCloseWaitRst, tcpLastAck := finStuck, proto := .tcp fam nextBind nextSockState nextSelfTcp tainted }
          let sOk := match pf? with
            | some peerFid =>
              if peerFid == selfFid || selfTaintedNative then s1
              else if !loUp then
                if d.tcpLastAck then s1
                else { s1 with loPendingTcp := s1.loPendingTcp ++ [.shutFin selfFid peerFid] }
              else
                match lookupFileSocket s1 peerFid with
                | .ok pd =>
                  match pd.proto with
                  | .tcp pfam pbind psock ptcp ptaint =>
                    let ppa := match ptcp with | .established _ a | .finWait _ a | .closeWait _ a _ | .closedAfterConn a _ => a | _ => pa
                    if pfam == .v6 && ptaint && isNativeV6PeerAddr ppa then
                      setFileSocket s1 peerFid { pd with proto := .tcp pfam pbind psock (.closeWait (some selfFid) ppa false) ptaint }
                    else
                      setFileSocket s1 peerFid { pd with tcpLastAck := false, proto := .tcp pfam pbind.unhashUnlocked psock (.closedAfterConn ppa .cleanFin) ptaint }
                  | _ => s1
                | .error _ => s1
            | none => s1
          emitUnit obs? s sOk [Errno.ENOTCONN] (onAltErr := onCwShutErr)
        else
          let sOk := setFileSocket s selfFid { d with shut := nextShut, proto := .tcp fam bind nextSockState (.closeWait pf? pa pcc) tainted }
          emitUnit obs? s sOk [Errno.ENOTCONN] (onAltErr := onCwShutErr)
    | .udp .. | .unixDgram .. =>
      let hasPeer := match d.proto with | .udp _ _ p? => p?.isSome | .unixDgram _ p? => p?.isSome | _ => false
      if !hasPeer then
        if d.domain == .unix then
          emitUnit obs? s (setFileSocket s selfFid { d with shut := nextShut }) [Errno.ENOTCONN]
        else
          emitErr obs? s Errno.ENOTCONN []
            (fun e => if isTransientNetErrno e then s else setFileSocket s selfFid { d with shut := nextShut })
      else
        emitUnit obs? s (setFileSocket s selfFid { d with shut := nextShut }) [Errno.ENOTCONN]
    | .unixStream isSeq bp conn =>
      match conn with
      | .listen bl aq =>
        emitUnit obs? s (setFileSocket s selfFid { d with shut := nextShut, proto := .unixStream isSeq bp (.listen bl aq) }) [Errno.ENOTCONN]
      | .idle =>
        emitUnit obs? s (setFileSocket s selfFid { d with shut := nextShut }) [Errno.ENOTCONN]
      | .connected pf? _ _ _ _ =>
        let s1 := setFileSocket s selfFid { d with shut := nextShut }
        let sOk := match pf? with
          | some peerFid =>
            if peerFid == selfFid then s1
            else
              match lookupFileSocket s1 peerFid with
              | .ok pd =>
                match pd.proto with
                | .unixStream pseq pbp (.connected ppf? pPsw pPwb pPr pPrGc) =>
                  setFileSocket s1 peerFid
                    { pd with proto := .unixStream pseq pbp (.connected ppf? (pPsw || doWr) (pPwb || doRd) pPr pPrGc) }
                | _ => s1
              | .error _ => s1
          | none => s1
        emitUnit obs? s sOk [Errno.ENOTCONN]

/-- Model transition for `Net.sendmsg`. -/
def stepSendmsg (s : NetState) (hid : HandleId) (fds : Array HandleId)
    (obs? : Option NetOutcome) : Option (NetOutcome × NetState) :=
  match lookupHandleFileId s hid with
  | none => emitErr obs? s Errno.EBADF [] (allowTransient := false)
  | some selfFid =>
    if !fds.toList.all (isLiveHandle s) then
      emitErr obs? s Errno.EBADF [] (allowTransient := false)
    else
      match lookupFileSocket s selfFid with
      | .error fdErr =>
        emitErr obs? s fdErr [] (allowTransient := (fdErr == Errno.ENOTSOCK))
      | .ok d =>
      if d.domain != .unix then
        emitErr obs? s Errno.EOPNOTSUPP []
      else
      let body : Option (NetOutcome × NetState) :=
        if !isEstablished d then
          let connPend := match d.proto with | .tcp _ _ (.connecting _) _ _ => true | _ => false
          let selfRst := match d.proto with | .tcp _ _ _ (.closedAfterConn _ .selfShutRstPossible) _ => true | _ => false
          let canon := if d.domain == .unix then Errno.ENOTCONN else Errno.EDESTADDRREQ
          let alts := [Errno.ENOTCONN, Errno.EPIPE, Errno.EDESTADDRREQ] ++ (if connPend && d.nonblock then [Errno.EAGAIN] else []) ++ (if selfRst then [Errno.ECONNRESET] else [])
          emitErr obs? s canon alts (fun e =>
            match d.proto with
            | .tcp fam bind ss (.closedAfterConn pa .selfShutRstPossible) taint =>
              if e == Errno.ECONNRESET then setFileSocket s selfFid { d with proto := .tcp fam bind ss (.closedAfterConn pa .reset) taint } else s
            | _ => autobindUdp s selfFid d)
        else if d.domain == .unix && d.sockType == .seqpacket then
          match d.proto with
          | .unixStream isSeq bp (.connected pf? psw pwb true prGc) =>
            let sClr := setFileSocket s selfFid { d with proto := .unixStream isSeq bp (.connected pf? psw pwb false false) }
            let alts := if prGc then [Errno.EPIPE, Errno.ESHUTDOWN] else []
            emitErr obs? s Errno.ECONNRESET alts (fun e => if e == Errno.ECONNRESET || prGc then sClr else s)
          | _ =>
            if d.shut.wr then emitErr obs? s Errno.EPIPE [Errno.ESHUTDOWN]
            else
              match d.proto with
              | .unixStream _ _ (.connected _ _ true _ _) => emitErr obs? s Errno.EPIPE [Errno.ECONNRESET]
              | .unixStream _ _ (.connected (some peerFid) ..) =>
                let scmFids := fds.toList.filterMap (lookupHandleFileId s)
                let unit : RxUnit := { bytes := ByteArray.mk #[0], scm := scmFids, isScmDummy := true }
                emitUnit obs? s (deliverRx s peerFid unit) ((if d.nonblock then [Errno.EAGAIN] else []) ++ [Errno.ETOOMANYREFS])
              | _ => emitErr obs? s Errno.EPIPE [Errno.ECONNRESET]
        else if d.shut.wr then
          emitErr obs? s Errno.EPIPE [Errno.ESHUTDOWN]
        else
          match disconnectUnixDgramIfPeerClosed s d with
          | some dDisc =>
            emitErr obs? s Errno.ECONNREFUSED []
              (fun e => if isTransientNetErrno e then s else releaseRxScm (setFileSocket s selfFid dDisc) d.rxQueue)
          | none =>
            match d.proto with
            | .unixDgram _ (some (peerFid, _)) =>
              match lookupFileSocket s peerFid with
              | .ok pd =>
                if isUnixDgramPeerBusy selfFid pd then emitErr obs? s Errno.EPERM
                else if pd.shut.rd then emitErr obs? s Errno.EPIPE
                else
                  let scmFids := fds.toList.filterMap (lookupHandleFileId s)
                  let unit : RxUnit := { bytes := ByteArray.mk #[0], scm := scmFids, isScmDummy := true }
                  emitUnit obs? s (deliverRx s peerFid unit) ((if d.nonblock then [Errno.EAGAIN] else []) ++ [Errno.ETOOMANYREFS])
              | .error _ => emitErr obs? s Errno.ECONNREFUSED
            | .unixStream _ _ (.connected (some peerFid) _ pwb _ _) =>
              if pwb then emitErr obs? s Errno.EPIPE [Errno.ECONNRESET]
              else
                let scmFids := fds.toList.filterMap (lookupHandleFileId s)
                let unit : RxUnit := { bytes := ByteArray.mk #[0], scm := scmFids, isScmDummy := true }
                emitUnit obs? s (deliverRx s peerFid unit) ((if d.nonblock then [Errno.EAGAIN] else []) ++ [Errno.ETOOMANYREFS])
            | .unixStream _ _ (.connected none ..) =>
              emitErr obs? s Errno.EPIPE [Errno.ECONNRESET]
            | .udp _ _ (some targetAddr) =>
              let unit : RxUnit := { bytes := ByteArray.mk #[0], scm := [], isScmDummy := true }
              let loDownAlts := udpLoDownAlts s d
              match findBoundUdpPeer s d targetAddr with
              | some (peerFid, _) =>
                let loUp := match s.loState with | .up _ => true | _ => false
                let sOk := if loUp then deliverRx s peerFid unit else s
                emitUnit obs? s sOk (loDownAlts ++ (if d.nonblock then [Errno.EAGAIN] else []))
              | none =>
                let loUp := match s.loState with | .up _ => true | _ => false
                let sOk :=
                  if loUp && isLoopbackTargetAddr targetAddr then
                    setFileSocket s selfFid { d with soError := Errno.ECONNREFUSED }
                  else s
                emitUnit obs? s sOk (loDownAlts ++ [Errno.ECONNREFUSED] ++ (if d.nonblock then [Errno.EAGAIN] else []))
            | .tcp _ _ _ (.closeWait none pa true) _ =>
              let sSent := applyTcpCleanCloseRst s selfFid d pa
              match obs? with
              | none => some (.unit, sSent)
              | some .unit => some (.unit, sSent)
              | some (.err e) =>
                if e == Errno.EPIPE || e == Errno.ECONNRESET || (d.nonblock && e == Errno.EAGAIN) || isTransientNetErrno e then
                  some (.err e, s)
                else none
              | some _ => none
            | .tcp _ _ _ tcpState _ =>
              match tcpState with
              | .established pf? pa | .finWait pf? pa | .closeWait pf? pa false =>
                let unit : RxUnit := { bytes := ByteArray.mk #[0], scm := [], isScmDummy := true }
                let sOk := tcpDeliverOrPeerRst s selfFid d pf? pa unit
                match obs? with
                | some (.err e) =>
                  if d.tcpCloseWaitRst && (e == Errno.EPIPE || e == Errno.ECONNRESET) then
                    match d.proto with
                    | .tcp fam bind ss (.closeWait _ pa2 _) taint =>
                      some (.err e, setFileSocket s selfFid { d with tcpCloseWaitRst := false, tcpLastAck := false, proto := .tcp fam bind.unhashUnlocked ss (.closedAfterConn pa2 .reset) taint })
                    | _ => none
                  else emitUnit obs? s sOk (if d.nonblock then [Errno.EAGAIN] else [])
                | _ => emitUnit obs? s sOk (if d.nonblock then [Errno.EAGAIN] else [])
              | _ => emitErr obs? s Errno.EPIPE [Errno.ECONNRESET]
            | _ => emitErr obs? s Errno.ENOTCONN
      match consumePendingSoError d with
      | some (pendErr, dCleared) =>
        let isOptionalDgram := d.domain != .unix && d.sockType == .dgram && pendErr == Errno.ECONNREFUSED
        let isConnPending := match d.proto with | .tcp _ _ (.connecting _) _ _ => true | _ => false
        let sCleared := setFileSocket s selfFid dCleared
        match obs? with
        | none => some (.err pendErr, sCleared)
        | some (.err e) =>
          if isAsyncConnectErrno pendErr e d then some (.err e, sCleared)
          else if d.shut.wr && e == Errno.EPIPE then
            some (.err e, if d.tcpLoFinPending && pendErr != Errno.EPIPE then s else sCleared)
          else if isConnPending && d.nonblock && e == Errno.EAGAIN then some (.err e, s)
          else if isTransientNetErrno e then some (.err e, s)
          else if isOptionalDgram then body
          else none
        | _ => if isOptionalDgram then body else none
      | none => body

/-- Model transition body helper for `Net.recvmsg`. -/
def stepRecvmsgBody (s : NetState) (selfFid : FileId) (d : SockDesc)
    (maxFds : UInt32) (obs? : Option NetOutcome) : Option (NetOutcome × NetState) :=
  if d.sockType != .dgram && !isEstablished d && d.rxQueue.isEmpty then
    let tcpClosedEof := isTcpClosedEof d
    let failedConnecting := isFailedConnectingTcp d
    if tcpClosedEof || (d.domain != .unix && !d.proto.isListening && d.shut.rd) then
      match obs? with
      | none => some (.fds #[], s)
      | some (.fds got) => if got.size == 0 then some (.fds got, s) else none
      | some (.err e) =>
        if (d.domain != .unix && d.nonblock && d.tcpLoFinPending && e == Errno.EAGAIN) ||
            (tcpClosedEof && d.domain != .unix && e == Errno.ENOTCONN) ||
            (failedConnecting && (e == Errno.ENOTCONN || (d.nonblock && e == Errno.EAGAIN))) ||
            isTransientNetErrno e then
          some (.err e, s)
        else none
      | some _ => none
    else
      let alts := (if d.domain == .unix then [Errno.EINVAL] else []) ++
        (if failedConnecting && d.nonblock then [Errno.EAGAIN] else [])
      emitErr obs? s Errno.ENOTCONN alts
  else
    match clearUnixSeqPeerReset? d with
    | some (dClr, prGc, psw) =>
      let sClr := setFileSocket s selfFid dClr
      match obs? with
      | none => some (.err Errno.ECONNRESET, sClr)
      | some (.err e) =>
        if e == Errno.ECONNRESET then some (.err e, sClr)
        else if isTransientNetErrno e then some (.err e, s)
        else none
      | some (.fds got) =>
        if d.rxQueue.isEmpty && prGc && (psw || d.shut.rd) && got.size == 0 then some (.fds got, sClr) else none
      | some _ => none
    | none =>
      match popRecvmsgUnit d.sockType d.rxQueue with
      | some (batch, restQ) =>
        let sDrop := setFileSocket s selfFid { d with rxQueue := restQ }
        if batch.length > maxFds.toNat then
          let sTrunc := releaseUnusedFiles sDrop batch
          let alts := if d.domain != .unix && d.nonblock then [Errno.EAGAIN] else []
          emitErr obs? s Errno.EPROTO alts (fun e =>
            if isTransientNetErrno e || e == Errno.EAGAIN then s else sTrunc)
        else
          let expectedLen := batch.length
          let alts := [Errno.EMFILE, Errno.ENFILE, Errno.ENOMEM] ++
            (if !batch.isEmpty then [Errno.EPROTO] else []) ++
            (if d.domain != .unix && d.nonblock then [Errno.EAGAIN] else [])
          match obs? with
          | none =>
            let (sClone, got) := cloneScmHandles sDrop expectedLen (freshHidBase sDrop) batch []
            some (.fds got, releaseUnusedFiles sClone (batch.drop got.size))
          | some (.fds got) =>
            if got.size != expectedLen then none
            else
              match bindReceivedScmHandles sDrop got.toList batch with
              | none => none
              | some s2 => some (.fds got, s2)
          | some (.err e) =>
            if !batch.isEmpty && e == Errno.EPROTO then some (.err e, releaseUnusedFiles sDrop batch)
            else if alts.contains e || isTransientNetErrno e then some (.err e, s)
            else none
          | some _ => none
      | none =>
        match d.proto with
        | .unixStream isSeq bp (.connected pf? psw pwb true prGc) =>
          let sClr := setFileSocket s selfFid { d with proto := .unixStream isSeq bp (.connected pf? psw pwb false false) }
          match obs? with
          | none => some (.err Errno.ECONNRESET, sClr)
          | some (.err e) =>
            if e == Errno.ECONNRESET then some (.err e, sClr)
            else if isTransientNetErrno e then some (.err e, s)
            else none
          | some (.fds got) =>
            if prGc && (psw || d.shut.rd) && got.size == 0 then some (.fds got, sClr) else none
          | some _ => none
        | _ =>
          let peerClosed := isPeerClosedRx d
          let isEof := ((peerClosed || d.shut.rd) && d.sockType != .dgram) ||
            (d.sockType == .dgram && d.shut.rd && !d.nonblock)
          if isEof then
            match obs? with
            | none => some (.fds #[], s)
            | some (.fds got) => if got.size == 0 then some (.fds got, s) else none
            | some (.err e) =>
              if (d.domain != .unix && d.nonblock && d.tcpLoFinPending && e == Errno.EAGAIN) || isTransientNetErrno e then
                some (.err e, s)
              else none
            | some _ => none
          else
            emitErr obs? s Errno.EAGAIN

/-- Model transition for `Net.recvmsg`. -/
def stepRecvmsg (s : NetState) (hid : HandleId) (maxFds : UInt32)
    (obs? : Option NetOutcome) : Option (NetOutcome × NetState) :=
  withSock s hid obs? fun selfFid d =>
    let body := stepRecvmsgBody s selfFid d maxFds obs?
    match consumeRecvPendingSoError d with
    | some (pendErr, dCleared) =>
      let isOptionalDgram := d.domain != .unix && d.sockType == .dgram && pendErr == Errno.ECONNREFUSED
      let isStreamNonEmpty := d.sockType == .stream && !d.rxQueue.isEmpty
      let isOptionalErr := isOptionalDgram || isStreamNonEmpty
      let isConnPending := match d.proto with | .tcp _ _ (.connecting _) _ _ => true | _ => false
      let sCleared := setFileSocket s selfFid dCleared
      match obs? with
      | none =>
        if isStreamNonEmpty then body else some (.err pendErr, sCleared)
      | some (.err e) =>
        if isStreamNonEmpty && body.isSome then body
        else if isAsyncConnectErrno pendErr e d then some (.err e, sCleared)
        else if (isConnPending && ((d.nonblock && e == Errno.EAGAIN) || e == Errno.ENOTCONN)) ||
            (d.domain != .unix && d.sockType == .dgram && d.nonblock && e == Errno.EAGAIN) ||
            (d.tcpLoFinPending && d.nonblock && e == Errno.EAGAIN) then
          some (.err e, s)
        else if isTransientNetErrno e then some (.err e, s)
        else if isOptionalErr then body
        else none
      | some (.fds got) =>
        if isOptionalErr then body
        else if isTcpLoFinPendingRst d && d.rxQueue.isEmpty && got.size == 0 then
          match recoverTcpLoCloseWait s selfFid d with
          | some sCw => some (.fds got, sCw)
          | none => none
        else none
      | _ => if isOptionalErr then body else none
    | none =>
      match obs? with
      | some (.err e) =>
        if e == Errno.ECONNRESET then
          match tcpConsumeShutRdwrRecvRst? s selfFid d with
          | some sRst => some (.err Errno.ECONNRESET, sRst)
          | none => body
        else body
      | _ => body

private def flushOneLoTcpEvent (s : NetState) : LoPendingTcpEvent → NetState
  | .tx srcFid peerFid unit =>
    match lookupFileSocket s peerFid with
    | .ok pd =>
      let peerFinRdShut :=
        match pd.proto with
        | .tcp _ _ _ (.finWait ..) _ | .tcp _ _ _ (.closedAfterConn ..) _ => pd.shut.isBoth
        | _ => false
      if peerFinRdShut then
        let s1 :=
          match lookupFileSocket s srcFid with
          | .ok sd =>
            match sd.proto with
            | .tcp _ _ _ (.established _ pa) _ | .tcp _ _ _ (.finWait _ pa) _ | .tcp _ _ _ (.closeWait _ pa _) _ =>
              markTcpLoFinPending (applyTcpCleanCloseRst s srcFid sd pa) srcFid
            | .tcp fam bind ss (.closedAfterConn pa .cleanFin) taint =>
              setFileSocket s srcFid
                { sd with tcpLoFinPending := true, proto := .tcp fam bind ss (.closedAfterConn pa .selfShutRstPossible) taint }
            | _ => s
          | .error _ => s
        if srcFid == peerFid then s1
        else
          match pd.proto with
          | .tcp pfam pbind psock ptcp ptaint =>
            let ppa := match ptcp with | .established _ a | .finWait _ a | .closeWait _ a _ | .closedAfterConn a _ => a | _ => defaultUnboundAddr pd.domain
            let nextPtcp := match ptcp with | .established .. | .finWait .. | .closeWait .. | .closedAfterConn .. => TcpState.closedAfterConn ppa .reset | other => other
            markTcpLoFinPending
              (setFileSocket s1 peerFid { pd with soError := Errno.ECONNRESET, proto := .tcp pfam pbind.unhashUnlocked psock nextPtcp ptaint })
              peerFid
          | _ => s1
      else setTcpLoFinPending (setTcpLoFinPending (deliverRx s peerFid unit) srcFid) peerFid
    | .error _ =>
      match lookupFileSocket s srcFid with
      | .ok sd =>
        match sd.proto with
        | .tcp _ _ _ (.established _ pa) _ | .tcp _ _ _ (.finWait _ pa) _ | .tcp _ _ _ (.closeWait _ pa _) _ =>
          markTcpLoFinPending (applyTcpCleanCloseRst s srcFid sd pa) srcFid
        | .tcp fam bind ss (.closedAfterConn pa .cleanFin) taint =>
          setFileSocket s srcFid
            { sd with tcpLoFinPending := true, proto := .tcp fam bind.unhashUnlocked ss (.closedAfterConn pa .selfShutRstPossible) taint }
        | _ => s
      | .error _ => s
  | .shutFin srcFid peerFid =>
    let closeSrcClean (st : NetState) : NetState :=
      match lookupFileSocket st srcFid with
      | .ok sd =>
        match sd.proto with
        | .tcp sfam sbind ssock (.established _ spa) staint
        | .tcp sfam sbind ssock (.finWait _ spa) staint
        | .tcp sfam sbind ssock (.closeWait _ spa _) staint =>
          setFileSocket st srcFid { sd with tcpLoFinPending := true, tcpLastAck := false, proto := .tcp sfam sbind.unhashUnlocked ssock (.closedAfterConn spa .cleanFin) staint }
        | _ => st
      | .error _ => st
    let srcShutBoth := match lookupFileSocket s srcFid with
      | .ok sd => sd.shut.isBoth
      | .error _ => false
    match lookupFileSocket s peerFid with
    | .ok pd =>
      match pd.proto with
      | .tcp pfam pbind psock (.established _ ppa) ptaint =>
        setTcpLoFinPending
          (setFileSocket s peerFid { pd with tcpLoFinPending := true, tcpCloseWaitRst := pd.tcpCloseWaitRst || srcShutBoth, proto := .tcp pfam pbind psock (.closeWait (some srcFid) ppa false) ptaint })
          srcFid
      | .tcp pfam pbind psock (.finWait _ ppa) ptaint =>
        if pfam == .v6 && ptaint && isNativeV6PeerAddr ppa then
          setTcpLoFinPending
            (setFileSocket s peerFid { pd with tcpLoFinPending := true, proto := .tcp pfam pbind psock (.closeWait (some srcFid) ppa false) ptaint })
            srcFid
        else
          let s2 := setFileSocket s peerFid { pd with tcpLoFinPending := true, proto := .tcp pfam pbind.unhashUnlocked psock (.closedAfterConn ppa .cleanFin) ptaint }
          closeSrcClean s2
      | .tcp pfam pbind psock (.closeWait _ ppa _) ptaint =>
        if pfam == .v6 && ptaint && isNativeV6PeerAddr ppa then
          setTcpLoFinPending
            (setFileSocket s peerFid { pd with tcpLoFinPending := true, proto := .tcp pfam pbind psock (.closeWait (some srcFid) ppa false) ptaint })
            srcFid
        else
          let s2 := setFileSocket s peerFid { pd with tcpLoFinPending := true, tcpLastAck := false, proto := .tcp pfam pbind.unhashUnlocked psock (.closedAfterConn ppa .cleanFin) ptaint }
          closeSrcClean s2
      | .tcp _ _ _ (.closedAfterConn _ _) _ =>
        closeSrcClean s
      | _ => s
    | .error _ =>
      match lookupFileSocket s srcFid with
      | .ok sd =>
        match sd.proto with
        | .tcp sfam sbind ssock (.closeWait _ spa _) staint =>
          setFileSocket s srcFid { sd with tcpLoFinPending := true, tcpLastAck := false, proto := .tcp sfam sbind.unhashUnlocked ssock (.closedAfterConn spa .cleanFin) staint }
        | .tcp sfam sbind ssock (.established _ spa) staint
        | .tcp sfam sbind ssock (.finWait _ spa) staint =>
          setFileSocket s srcFid { sd with tcpLoFinPending := true, tcpLastAck := false, soError := Errno.ECONNRESET, proto := .tcp sfam sbind.unhashUnlocked ssock (.closedAfterConn spa .reset) staint }
        | _ => s
      | .error _ => s
  | .close _ peerFid hasUnread selfEstab selfFinWait selfCloseWait =>
    let s1 := resetTcpPeerOnClose s peerFid hasUnread selfEstab selfFinWait selfCloseWait
    markTcpLoFinPending s1 peerFid

private def flushLoPendingTcp (s : NetState) : NetState :=
  let stalledCloseWaitRsts := s.files.filterMap fun (fid, entry) =>
    match entry with
    | .socket d =>
      if d.tcpLoStalledTx then
        match d.proto with
        | .tcp _ _ _ (.closeWait none pa true) _ => some (fid, pa)
        | _ => none
      else none
    | .nonSocket => none
  let orphanLastAckFins := s.files.filterMap fun (fid, entry) =>
    match entry with
    | .socket d =>
      if d.tcpLastAck && !d.tcpLoStalledTx then
        match d.proto with
        | .tcp fam _ _ (.closeWait none pa true) tainted =>
          if fam == .v6 && tainted && isNativeV6PeerAddr pa then none else some (fid, pa)
        | _ => none
      else none
    | .nonSocket => none
  let clearedFiles := s.files.map fun (fid, entry) =>
    match entry with
    | .socket d => (fid, .socket { d with tcpLoStalledTx := false })
    | .nonSocket => (fid, entry)
  let s0 : NetState := { s with files := clearedFiles, loPendingTcp := [] }
  let s1 := s.loPendingTcp.foldl flushOneLoTcpEvent s0
  let s2 :=
    orphanLastAckFins.foldl
      (fun acc (fid, pa) =>
        match lookupFileSocket acc fid with
        | .ok d =>
          match d.proto with
          | .tcp fam bind ss (.closeWait none _ true) tainted =>
            setFileSocket acc fid { d with tcpLoFinPending := true, tcpLastAck := false, proto := .tcp fam bind.unhashUnlocked ss (.closedAfterConn pa .cleanFin) tainted }
          | _ => acc
        | .error _ => acc)
      s1
  stalledCloseWaitRsts.foldl
    (fun acc (fid, pa) =>
      match lookupFileSocket acc fid with
      | .ok d => markTcpLoFinPending (applyTcpCleanCloseRst acc fid d pa) fid
      | .error _ => acc)
    s2

/-- Model transition for `Net.ioctl`. -/
def stepIoctl (s : NetState) (hid : HandleId) (op : NetIoctlOp) (ifname : ByteArray)
    (obs? : Option NetOutcome) : Option (NetOutcome × NetState) :=
  match lookupHandleFileId s hid with
  | none => emitErr obs? s Errno.EBADF [] (allowTransient := false)
  | some selfFid =>
    match lookupFileSocket s selfFid with
    | .error fdErr =>
      if fdErr == Errno.ENOTSOCK then
        emitErr obs? s Errno.ENOTTY [Errno.ENOTSOCK]
      else emitErr obs? s fdErr [] (allowTransient := false)
    | .ok _ =>
      if ifname.size == 0 then
        match op with
        | .getIfFlags => emitErr obs? s Errno.ENODEV
        | .setIfFlags _ => emitErr obs? s Errno.EPERM [Errno.EACCES, Errno.ENODEV]
      else if bytesEq ifname loIfname then
        match s.loState, op with
        | .up fl, .getIfFlags => emitU32 obs? s fl s
        | .down fl _, .getIfFlags => emitU32 obs? s fl s
        | .unpinned defFl, .getIfFlags =>
          match obs? with
          | none =>
            if defFl <= 0xffff && (defFl &&& IFF_LOOPBACK) != 0 then
              let nextLo := if (defFl &&& IFF_UP) != 0 then LoState.up defFl else LoState.down defFl false
              some (.u32 defFl, { s with loState := nextLo })
            else none
          | some (.u32 got) =>
            if got <= 0xffff && (got &&& IFF_LOOPBACK) != 0 then
              let nextLo := if (got &&& IFF_UP) != 0 then LoState.up got else LoState.down got false
              some (.u32 got, { s with loState := nextLo })
            else none
          | some (.err e) => if isTransientNetErrno e then some (.err e, s) else none
          | some _ => none
        | loSt, .setIfFlags rawFl =>
          let (curFl, prevUp) := match loSt with
            | .up fl => (fl, true)
            | .down fl wasUp => (fl, wasUp)
            | .unpinned defFl => (defFl, (defFl &&& IFF_UP) != 0)
          let nextFl := applyIfFlags curFl rawFl
          let nextLo := if (nextFl &&& IFF_UP) != 0 then LoState.up nextFl else LoState.down nextFl prevUp
          if !s.hasNetAdmin then
            emitErr obs? s Errno.EPERM [Errno.EACCES]
          else
            let sNext := { s with loState := nextLo }
            let sOk := if (nextFl &&& IFF_UP) != 0 then flushLoPendingTcp sNext else sNext
            emitU32 obs? s 0 sOk [Errno.EPERM, Errno.EACCES]
      else
        match bytesAssocGet s.otherIfaces ifname, op with
        | none, .getIfFlags =>
          match obs? with
          | none => some (.err Errno.ENODEV, s)
          | some (.u32 got) =>
            if got <= 0xffff then
              some (.u32 got, { s with otherIfaces := bytesAssocSet s.otherIfaces ifname got })
            else none
          | some (.err e) => if e == Errno.ENODEV || isTransientNetErrno e then some (.err e, s) else none
          | some _ => none
        | none, .setIfFlags rawFl =>
          if !s.hasNetAdmin then
            emitErr obs? s Errno.EPERM [Errno.EACCES, Errno.ENODEV]
          else
            let nextFl := applyIfFlags 0 rawFl
            let sOk := { s with otherIfaces := bytesAssocSet s.otherIfaces ifname nextFl }
            let alts := [Errno.ENODEV, Errno.EPERM, Errno.EACCES]
            match obs? with
            | none => some (.err Errno.ENODEV, s)
            | some (.u32 got) => if got == 0 then some (.u32 0, sOk) else none
            | some (.err e) => if alts.contains e || isTransientNetErrno e then some (.err e, s) else none
            | some _ => none
        | some curFl, .getIfFlags =>
          emitU32 obs? s curFl s
        | some curFl, .setIfFlags rawFl =>
          if !s.hasNetAdmin then
            emitErr obs? s Errno.EPERM [Errno.EACCES]
          else
            let nextFl := applyIfFlags curFl rawFl
            let sOk := { s with otherIfaces := bytesAssocSet s.otherIfaces ifname nextFl }
            emitU32 obs? s 0 sOk [Errno.EPERM, Errno.EACCES]

/-- Single pure transition core for all 15 Net syscalls (`obs? = none` for `modelOps`, `some out` for `allowedStep`). -/
def stepNetCore (s : NetState) (req : NetReq) (obs? : Option NetOutcome) :
    Option (NetOutcome × NetState) :=
  match preCheckNet req with
  | some err => emitErr obs? s err [] (allowTransient := false)
  | none =>
    match req with
    | .socket domain sockType flags _ =>
      let desc : SockDesc := SockDesc.mkDefault domain sockType flags.nonblock
      emitAllocFd obs? s desc flags.cloexec [Errno.EMFILE, Errno.ENFILE, Errno.ENOMEM, Errno.EACCES]
    | .socketpair _ sockType flags =>
      let initConn := match sockType with
        | .dgram => SockProtoState.unixDgram none (some (s.nextFileId + 1, defaultUnboundAddr .unix))
        | .stream => SockProtoState.unixStream false none (.connected (some (s.nextFileId + 1)) false false false false)
        | .seqpacket => SockProtoState.unixStream true none (.connected (some (s.nextFileId + 1)) false false false false)
      let d0 : SockDesc := { proto := initConn, nonblock := flags.nonblock }
      let initConn1 := match sockType with
        | .dgram => SockProtoState.unixDgram none (some (s.nextFileId, defaultUnboundAddr .unix))
        | .stream => SockProtoState.unixStream false none (.connected (some s.nextFileId) false false false false)
        | .seqpacket => SockProtoState.unixStream true none (.connected (some s.nextFileId) false false false false)
      let d1 : SockDesc := { proto := initConn1, nonblock := flags.nonblock }
      emitAllocPair obs? s d0 d1 flags.cloexec [Errno.EMFILE, Errno.ENFILE, Errno.ENOMEM]
    | .bind hid addr => stepBind s hid addr obs?
    | .listen hid backlog => stepListen s hid backlog obs?
    | .accept4 hid flags => stepAccept4 s hid flags obs?
    | .connect hid addr => stepConnect s hid addr obs?
    | .getsockopt hid opt => stepGetsockopt s hid opt obs?
    | .setsockopt hid opt val => stepSetsockopt s hid opt val obs?
    | .getsockname hid => stepGetsockname s hid obs?
    | .recvfrom hid maxBytes flags => stepRecvfrom s hid maxBytes flags obs?
    | .sendto hid data flags => stepSendto s hid data flags obs?
    | .shutdown hid how => stepShutdown s hid how obs?
    | .sendmsg hid fds => stepSendmsg s hid fds obs?
    | .recvmsg hid maxFds => stepRecvmsg s hid maxFds obs?
    | .ioctl hid op ifname => stepIoctl s hid op ifname obs?

/-- Relational step verifier for all 15 curated `Net` syscalls (with `unix_gc` fallback and `ambientSeccomp`). -/
def allowedStep (s : NetState) (req : NetReq) (out : NetOutcome) : Option NetState :=
  match (stepNetCore s req (some out)).map Prod.snd with
  | some s' => some s'
  | none =>
    let candidates := collectUnixGcCandidates s
    match candidates.findSome? (fun fid => (stepNetCore (releaseUnixGcFile s fid) req (some out)).map Prod.snd) with
    | some s' => some s'
    | none =>
      match collectUnixGc s with
      | some sGc =>
        match (stepNetCore sGc req (some out)).map Prod.snd with
        | some s' => some s'
        | none => seccompFallback s req out
      | none => seccompFallback s req out
where
  seccompFallback (s : NetState) (req : NetReq) (out : NetOutcome) : Option NetState :=
    if s.ambientSeccomp then
      match out with
      | .err e => if Errno.isSafeSeccompErrno e && reachesKernelSyscall s req then some s else none
      | _ => none
    else none

/-- Execute one deterministic `stepNetCore` step inside `StateM NetState`. -/
def runModelStep {α : Type} (req : NetReq) (unpack : NetOutcome → Except Errno α) :
    StateM NetState (Except Errno α) := do
  let s ← get
  match stepNetCore s req none with
  | some (out, s') =>
    set s'
    match out with
    | .err e => return .error e
    | _ => return unpack out
  | none => return .error Errno.EINVAL

/-- Pure Lean deterministic executable model implementing `NetOpsM (StateM NetState) HandleId` via `stepNetCore`. -/
def modelOps : NetOpsM (StateM NetState) HandleId :=
  { socket := fun domain sockType flags proto =>
      runModelStep (.socket domain sockType flags proto) fun
        | .opened h => .ok h
        | _ => .error Errno.EINVAL
    socketpair := fun domain sockType flags =>
      runModelStep (.socketpair domain sockType flags) fun
        | .pair h0 h1 => .ok (h0, h1)
        | _ => .error Errno.EINVAL
    bind := fun hid addr =>
      runModelStep (.bind hid addr) fun | .unit => .ok () | _ => .error Errno.EINVAL
    listen := fun hid backlog =>
      runModelStep (.listen hid backlog) fun | .unit => .ok () | _ => .error Errno.EINVAL
    accept4 := fun hid flags =>
      runModelStep (.accept4 hid flags) fun
        | .accepted h peer => .ok (h, peer)
        | _ => .error Errno.EINVAL
    connect := fun hid addr =>
      runModelStep (.connect hid addr) fun | .unit => .ok () | _ => .error Errno.EINVAL
    getsockopt := fun hid opt =>
      runModelStep (.getsockopt hid opt) fun | .u32 v => .ok v | _ => .error Errno.EINVAL
    setsockopt := fun hid opt val =>
      runModelStep (.setsockopt hid opt val) fun | .unit => .ok () | _ => .error Errno.EINVAL
    getsockname := fun hid =>
      runModelStep (.getsockname hid) fun | .addr sa => .ok sa | _ => .error Errno.EINVAL
    recvfrom := fun hid maxBytes flags =>
      runModelStep (.recvfrom hid maxBytes flags) fun
        | .bytes b => .ok b
        | _ => .error Errno.EINVAL
    sendto := fun hid data flags =>
      runModelStep (.sendto hid data flags) fun | .u32 n => .ok n | _ => .error Errno.EINVAL
    shutdown := fun hid how =>
      runModelStep (.shutdown hid how) fun | .unit => .ok () | _ => .error Errno.EINVAL
    sendmsg := fun hid fds =>
      runModelStep (.sendmsg hid fds) fun | .unit => .ok () | _ => .error Errno.EINVAL
    recvmsg := fun hid maxFds =>
      runModelStep (.recvmsg hid maxFds) fun | .fds fds => .ok fds | _ => .error Errno.EINVAL
    ioctl := fun hid op ifname =>
      runModelStep (.ioctl hid op ifname) fun | .u32 v => .ok v | _ => .error Errno.EINVAL }

end LeanSwe.LinuxSyscall.Net
