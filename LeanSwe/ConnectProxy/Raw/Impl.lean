import Std.Sync.Mutex
import LeanSwe.ConnectProxy.Raw.Types

namespace LeanSwe.ConnectProxy.Raw.Internal

open LeanSwe.ConnectProxy.Raw
  (ProxyErrorKind ProxyError ConnectProxyRawError IpAddr ProxyLimits ValidProxyConfig
   ConnectOutcome ConnectEvent RunningProxy HeadDecision ResolveDecision
   RawConnectProxyOpsM RawConnectProxyOps)

/-- C-ABI encoded `HeadDecision` tuple `(tag, hasHost, host, hasPort, port, reason, litIpBytes)`. -/
abbrev HeadRawResult := UInt8 × UInt8 × String × UInt8 × UInt16 × String × ByteArray

/-- C-ABI encoded `ResolveDecision` tuple `(tag, reason, ipBytes)`. -/
abbrev ResolveRawResult := UInt8 × String × ByteArray

/-- C-ABI encoded `ConnectEvent` tuple `(hasHost, host, hasPort, port, outcomeTag, hasReason, reason)`. -/
abbrev EventRawTuple := UInt8 × String × UInt8 × UInt16 × UInt8 × UInt8 × String

/-- Socket and poll loop FFI hooks injected by `LeanSwe.ConnectProxy.Raw.Interface`. -/
structure CProxyFfiOps where
  /-- Bind `127.0.0.1` synchronously and allocate a proxy instance `(errTag, errnoCode, detail, hid, boundPort)`. -/
  createProxy : UInt16 → UInt64 → UInt64 → UInt64 → UInt64 → IO (UInt32 × UInt32 × String × UInt64 × UInt16)
  /-- Run the blocking C `poll()` server loop on a dedicated Lean OS thread. -/
  runLoop : UInt64 → (ByteArray → HeadRawResult) → (String → UInt16 → ByteArray → ResolveRawResult) → IO Unit
  /-- Signal loop shutdown, wait for loop exit, collect events, and free the instance. -/
  stopProxy : UInt64 → IO (UInt32 × UInt32 × String × Array EventRawTuple)
  /-- Return count of currently active proxy handles tracked in C. -/
  activeCount : IO Nat

private initialize gProxyTasks : Std.Mutex (List (Nat × Task (Except IO.Error Unit))) ←
  Std.Mutex.new []

/-- Return `msg` if non-empty, or `fallback` otherwise. -/
def nonEmptyMsg (fallback msg : String) : String :=
  if msg.isEmpty then fallback else msg

/-- Clamp a `Nat` to `UInt64` without modular wraparound. -/
def natToUInt64Sat (n : Nat) : UInt64 :=
  UInt64.ofNat (Nat.min n (UInt64.size - 1))

/-- Convert a pure `ConnectProxyRawError` into a normalized `ProxyError` with non-empty message. -/
def mapRawError : ConnectProxyRawError → ProxyError
  | .invalidArgument errno? detail =>
    { kind := .invalidInput
      errnoCode := errno?
      message := nonEmptyMsg "invalid connect-proxy argument" detail }
  | .addressInUse port errno detail =>
    { kind := .addressInUse
      errnoCode := some errno
      message := nonEmptyMsg s!"127.0.0.1:{port} is already in use" detail }
  | .permissionDenied errno detail =>
    { kind := .permissionDenied
      errnoCode := some errno
      message := nonEmptyMsg "permission denied binding 127.0.0.1 socket" detail }
  | .resourceExhausted errno detail =>
    { kind := .resourceExhausted
      errnoCode := some errno
      message := nonEmptyMsg "proxy socket or thread resource limit exhausted" detail }
  | .otherError errno detail =>
    { kind := .ioError
      errnoCode := some errno
      message := nonEmptyMsg s!"connect-proxy OS error (errno {errno})" detail }
  | .userError detail =>
    { kind := .ioError
      errnoCode := none
      message := nonEmptyMsg "connect-proxy I/O error" detail }

/-- Check that every `ProxyLimits` field in `vcfg` is strictly positive before entering C. -/
def validateStartLimits (vcfg : ValidProxyConfig) : Except ProxyError ValidProxyConfig :=
  let lim := vcfg.config.limits
  if lim.maxHeaderBytes == 0 || lim.headerTimeoutMs == 0 ||
     lim.connectTimeoutMs == 0 || lim.maxConcurrentTunnels == 0 then
    .error (mapRawError (.invalidArgument none "proxy limits must be positive"))
  else
    .ok vcfg

/-- Decode C `createProxy` or `stopProxy` error tags into `ConnectProxyRawError`. -/
def decodeFfiRawError (port : UInt16) (tag : UInt32) (errnoCode : UInt32) (detail : String) :
    ConnectProxyRawError :=
  match tag.toNat with
  | 1 => .invalidArgument (if errnoCode == 0 then none else some errnoCode) detail
  | 2 => .addressInUse port errnoCode detail
  | 3 => .permissionDenied errnoCode detail
  | 4 => .resourceExhausted errnoCode detail
  | 5 => .otherError errnoCode detail
  | _ => .userError detail

/-- Encode an `IpAddr` into a 17-byte network-order record (`[4, b0..b3, 0..0]` or `[6, b0..b15]`). -/
def encodeIpRecord (ip : IpAddr) : ByteArray :=
  match ip with
  | .v4 addr =>
    ByteArray.mk #[
      4,
      ((addr >>> 24) &&& 0xff).toUInt8,
      ((addr >>> 16) &&& 0xff).toUInt8,
      ((addr >>> 8) &&& 0xff).toUInt8,
      (addr &&& 0xff).toUInt8,
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0
    ]
  | .v6 hi lo =>
    ByteArray.mk #[
      6,
      ((hi >>> 56) &&& 0xff).toUInt8,
      ((hi >>> 48) &&& 0xff).toUInt8,
      ((hi >>> 40) &&& 0xff).toUInt8,
      ((hi >>> 32) &&& 0xff).toUInt8,
      ((hi >>> 24) &&& 0xff).toUInt8,
      ((hi >>> 16) &&& 0xff).toUInt8,
      ((hi >>> 8) &&& 0xff).toUInt8,
      (hi &&& 0xff).toUInt8,
      ((lo >>> 56) &&& 0xff).toUInt8,
      ((lo >>> 48) &&& 0xff).toUInt8,
      ((lo >>> 40) &&& 0xff).toUInt8,
      ((lo >>> 32) &&& 0xff).toUInt8,
      ((lo >>> 24) &&& 0xff).toUInt8,
      ((lo >>> 16) &&& 0xff).toUInt8,
      ((lo >>> 8) &&& 0xff).toUInt8,
      (lo &&& 0xff).toUInt8
    ]

/-- Pack an array of `IpAddr` values into concatenated 17-byte network-order records. -/
def encodeIpArray (ips : Array IpAddr) : ByteArray :=
  ips.foldl (fun acc ip => acc ++ encodeIpRecord ip) ByteArray.empty

private def readUInt64BE (bs : ByteArray) (off : Nat) : UInt64 :=
  (bs[off]!.toUInt64 <<< 56) |||
  (bs[off + 1]!.toUInt64 <<< 48) |||
  (bs[off + 2]!.toUInt64 <<< 40) |||
  (bs[off + 3]!.toUInt64 <<< 32) |||
  (bs[off + 4]!.toUInt64 <<< 24) |||
  (bs[off + 5]!.toUInt64 <<< 16) |||
  (bs[off + 6]!.toUInt64 <<< 8) |||
  bs[off + 7]!.toUInt64

private def decodeIpRecordAt (bs : ByteArray) (off : Nat) : Option IpAddr :=
  if off + 17 > bs.size then
    none
  else
    let tag := bs[off]!
    if tag == 4 then
      let addr :=
        (bs[off + 1]!.toUInt32 <<< 24) |||
        (bs[off + 2]!.toUInt32 <<< 16) |||
        (bs[off + 3]!.toUInt32 <<< 8) |||
        bs[off + 4]!.toUInt32
      some (.v4 addr)
    else if tag == 6 then
      let hi := readUInt64BE bs (off + 1)
      let lo := readUInt64BE bs (off + 9)
      some (.v6 hi lo)
    else
      none

/-- Decode concatenated 17-byte IP records from C into `Array IpAddr`. -/
def decodeIpArray (bs : ByteArray) : Array IpAddr :=
  let count := bs.size / 17
  Id.run do
    let mut out : Array IpAddr := Array.emptyWithCapacity count
    for idx in [:count] do
      match decodeIpRecordAt bs (idx * 17) with
      | some ip => out := out.push ip
      | none => pure ()
    return out

/-- Encode a `HeadDecision` callback for the C FFI boundary. -/
def wrapOnHead (onHead : ByteArray → HeadDecision) (raw : ByteArray) : HeadRawResult :=
  match onHead raw with
  | .deny host? port? reason =>
    let hasHost : UInt8 := if host?.isSome then 1 else 0
    let host := host?.getD ""
    let hasPort : UInt8 := if port?.isSome then 1 else 0
    let port := port?.getD 0
    (0, hasHost, host, hasPort, port, reason, ByteArray.empty)
  | .needResolve host port litIp? =>
    let litBytes :=
      match litIp? with
      | some ip => encodeIpRecord ip
      | none => ByteArray.empty
    (1, 1, host, 1, port, "", litBytes)

/-- Encode a `ResolveDecision` callback for the C FFI boundary. -/
def wrapOnResolved
    (onResolved : String → UInt16 → Array IpAddr → ResolveDecision)
    (host : String) (port : UInt16) (ipsBytes : ByteArray) : ResolveRawResult :=
  let ips := decodeIpArray ipsBytes
  match onResolved host port ips with
  | .deny reason => (0, reason, ByteArray.empty)
  | .dial primary fallbacks => (1, "", encodeIpArray (#[primary] ++ fallbacks))

/-- Decode a C-returned `EventRawTuple` into a `ConnectEvent`. -/
def decodeEventTuple (t : EventRawTuple) : ConnectEvent :=
  let (hasHost, host, hasPort, port, outcomeTag, hasReason, reason) := t
  let outcome : ConnectOutcome :=
    match outcomeTag.toNat with
    | 0 => .allowed
    | 1 => .denied
    | _ => .failed
  { host := if hasHost != 0 then some host else none
    port := if hasPort != 0 then some port else none
    outcome := outcome
    reason := if hasReason != 0 then some reason else none }

private def registerLoopTask (hid : Nat) (t : Task (Except IO.Error Unit)) : IO Unit :=
  gProxyTasks.atomically do
    modify fun xs => (hid, t) :: xs

private def takeLoopTask (hid : Nat) : IO (Option (Task (Except IO.Error Unit))) :=
  gProxyTasks.atomically do
    let xs ← get
    let found := (xs.find? (fun p => p.1 == hid)).map (·.2)
    set (xs.filter (fun p => p.1 != hid))
    return found

/-- Build the concrete `RawConnectProxyOps` bundle backed by injected C FFI primitives. -/
def mkRawOps (ffi : CProxyFfiOps) : RawConnectProxyOps :=
  { mapRawError := mapRawError
    startProxy := fun vcfg onHead onResolved => do
      match validateStartLimits vcfg with
      | .error err => return .error err
      | .ok _ =>
        let lim := vcfg.config.limits
        try
          let (errTag, errnoCode, detail, hid, boundPort) ←
            ffi.createProxy
              vcfg.config.listenPort
              (natToUInt64Sat lim.maxHeaderBytes)
              (natToUInt64Sat lim.headerTimeoutMs)
              (natToUInt64Sat lim.connectTimeoutMs)
              (natToUInt64Sat lim.maxConcurrentTunnels)
          if errTag != 0 then
            return .error (mapRawError (decodeFfiRawError vcfg.config.listenPort errTag errnoCode detail))
          let onHeadRaw := wrapOnHead onHead
          let onResolvedRaw := wrapOnResolved onResolved
          let task ← IO.asTask (prio := .dedicated) (ffi.runLoop hid onHeadRaw onResolvedRaw)
          registerLoopTask hid.toNat task
          return .ok { handleId := hid.toNat, port := boundPort }
        catch err =>
          return .error (mapRawError (.userError (toString err)))
    stopProxy := fun proxy => do
      try
        let hid := natToUInt64Sat proxy.handleId
        let (errTag, errnoCode, detail, rawEvents) ← ffi.stopProxy hid
        if errTag != 0 then
          return .error (mapRawError (decodeFfiRawError proxy.port errTag errnoCode detail))
        match ← takeLoopTask proxy.handleId with
        | some t => let _ ← IO.wait t
        | none => pure ()
        return .ok (rawEvents.map decodeEventTuple)
      catch err =>
        return .error (mapRawError (.userError (toString err)))
    activeProxyCount := ffi.activeCount }

end LeanSwe.ConnectProxy.Raw.Internal
