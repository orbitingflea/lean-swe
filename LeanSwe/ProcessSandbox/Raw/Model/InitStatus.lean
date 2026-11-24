namespace LeanSwe.ProcessSandbox.Raw.Model

/-- `InitStatusMsg` tag indicating pre-`execvp` setup succeeded and `psandbox_init` is waiting on `go_fd`. -/
def PS_STATUS_READY : UInt8 := 1

/-- `InitStatusMsg` tag indicating pre-`execvp` init setup failed closed (`value = errno`). -/
def PS_STATUS_INIT_ERR : UInt8 := 2

/-- `InitStatusMsg` tag indicating guest `chdir` (`flag != 0`) or `execvp` (`flag == 0`) failed (`value = errno`). -/
def PS_STATUS_EXEC_ERR : UInt8 := 3

/-- `InitStatusMsg` tag indicating guest exited normally (`value = exitCode`). -/
def PS_STATUS_EXITED : UInt8 := 4

/-- `InitStatusMsg` tag indicating guest was terminated by a signal (`value = signal`). -/
def PS_STATUS_SIGNALED : UInt8 := 5

/-- Fixed 8-byte status frame exchanged over `status_pipe` between `psandbox_init` and the host. -/
structure InitStatusMsg where
  /-- Status tag (`PS_STATUS_*`). -/
  kind : UInt8
  /-- Auxiliary flag (`1` for `chdir` failure vs `0` for `execvp` failure on `PS_STATUS_EXEC_ERR`). -/
  flag : UInt8
  /-- Little-endian signed 32-bit payload (`errno`, exit code, or signal number). -/
  value : Int32
  deriving Repr, BEq, DecidableEq, Inhabited

/-- Encode an `InitStatusMsg` into its exact 8-byte C wire layout (`[kind, flag, 0, 0, val_le32]`). -/
def encodeInitStatusMsg (m : InitStatusMsg) : ByteArray :=
  let u := m.value.toUInt32.toNat
  ByteArray.mk #[
    m.kind,
    m.flag,
    0,
    0,
    UInt8.ofNat (u % 256),
    UInt8.ofNat ((u / 256) % 256),
    UInt8.ofNat ((u / 65536) % 256),
    UInt8.ofNat ((u / 16777216) % 256)
  ]

/-- Decode an 8-byte C wire buffer into `InitStatusMsg` (`none` if `bs.size != 8`). -/
def decodeInitStatusMsg (bs : ByteArray) : Option InitStatusMsg :=
  if h : bs.size = 8 then
    let b0 := bs[0]
    let b1 := bs[1]
    let v0 := bs[4].toNat
    let v1 := bs[5].toNat
    let v2 := bs[6].toNat
    let v3 := bs[7].toNat
    let rawU := UInt32.ofNat (v0 + 256 * v1 + 65536 * v2 + 16777216 * v3)
    some { kind := b0, flag := b1, value := rawU.toInt32 }
  else
    none

end LeanSwe.ProcessSandbox.Raw.Model
