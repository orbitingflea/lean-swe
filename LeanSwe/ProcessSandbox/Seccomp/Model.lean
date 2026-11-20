namespace LeanSwe.ProcessSandbox.Model

/-- Supported 64-bit little-endian Linux architectures for `ProcessSandbox` `seccomp` BPF compilation. -/
inductive SeccompArch where
  /-- Linux `x86_64` (`AUDIT_ARCH_X86_64 = 0xc000003e`). -/
  | x86_64
  /-- Linux `aarch64` (`AUDIT_ARCH_AARCH64 = 0xc00000b7`). -/
  | aarch64
  deriving Repr, BEq, DecidableEq, Inhabited

/-- Linux `AUDIT_ARCH_X86_64` (`EM_X86_64 | __AUDIT_ARCH_64BIT | __AUDIT_ARCH_LE`). -/
def AUDIT_ARCH_X86_64 : UInt32 := 0xc000003e

/-- Linux `AUDIT_ARCH_AARCH64` (`EM_AARCH64 | __AUDIT_ARCH_64BIT | __AUDIT_ARCH_LE`). -/
def AUDIT_ARCH_AARCH64 : UInt32 := 0xc00000b7

/-- Return the Linux `AUDIT_ARCH_*` constant corresponding to `arch`. -/
def auditArchOf : SeccompArch → UInt32
  | .x86_64 => AUDIT_ARCH_X86_64
  | .aarch64 => AUDIT_ARCH_AARCH64

/-- Parse a raw Linux `AUDIT_ARCH_*` constant into `SeccompArch`, returning `none` for unsupported architectures. -/
def seccompArchOfAudit? (raw : UInt32) : Option SeccompArch :=
  if raw == AUDIT_ARCH_X86_64 then
    some .x86_64
  else if raw == AUDIT_ARCH_AARCH64 then
    some .aarch64
  else
    none

/-- Maximum number of `sock_filter` instructions accepted by the bounded C loader (`struct sock_filter buf[160]`). -/
def SECCOMP_MAX_INSNS : Nat := 160

/-- Linux `SECCOMP_RET_ALLOW` verdict (`0x7fff0000`). -/
def SECCOMP_RET_ALLOW : UInt32 := 0x7fff0000

/-- Linux `SECCOMP_RET_ERRNO` action mask (`0x00050000`). -/
def SECCOMP_RET_ERRNO : UInt32 := 0x00050000

/-- Linux `SECCOMP_RET_DATA` payload mask (`0x0000ffff`). -/
def SECCOMP_RET_DATA : UInt32 := 0x0000ffff

/-- Linux `EPERM` errno constant (`1`). -/
def LINUX_EPERM : UInt32 := 1

/-- Linux `ENOSYS` errno constant (`38` = `0x26`). -/
def LINUX_ENOSYS : UInt32 := 38

/-- Linux `SECCOMP_RET_ERRNO | EPERM` verdict (`0x00050001`). -/
def SECCOMP_RET_ERRNO_EPERM : UInt32 := 0x00050001

/-- Linux `SECCOMP_RET_ERRNO | ENOSYS` verdict (`0x00050026`). -/
def SECCOMP_RET_ERRNO_ENOSYS : UInt32 := 0x00050026

/-- Linux `x86_64` `__X32_SYSCALL_BIT` threshold (`0x40000000`). -/
def X32_SYSCALL_BIT : UInt32 := 0x40000000

/-- Combined `CLONE_NEW*` namespace-creation flag mask (`0x7e020000`, disjoint from `0xff` `CSIGNAL`). -/
def CLONE_NEW_NS_MASK : UInt32 := 0x7e020000

/-- Linux `AF_UNIX` (`PF_UNIX`) socket address family (`1`). -/
def LINUX_AF_UNIX : UInt32 := 1

/-- Linux `AF_SMC` socket address family (`43`). -/
def LINUX_AF_SMC : UInt32 := 43

/-- Linux `SOCK_STREAM` socket type (`1`). -/
def LINUX_SOCK_STREAM : UInt32 := 1

/-- Linux `SOCK_DGRAM` socket type (`2`). -/
def LINUX_SOCK_DGRAM : UInt32 := 2

/-- Linux `SOCK_SEQPACKET` socket type (`5`). -/
def LINUX_SOCK_SEQPACKET : UInt32 := 5

/-- Linux `SOCK_NONBLOCK` (`O_NONBLOCK`) socket type modifier (`0x00000800`). -/
def LINUX_SOCK_NONBLOCK : UInt32 := 0x00000800

/-- Linux `SOCK_CLOEXEC` (`O_CLOEXEC`) socket type modifier (`0x00080000`). -/
def LINUX_SOCK_CLOEXEC : UInt32 := 0x00080000

/-- Bitmask `~(SOCK_CLOEXEC | SOCK_NONBLOCK)` (`0xfff7f7ff`) isolating base socket type in `socketpair`. -/
def LINUX_SOCK_TYPE_MASK_CLEAR_FLAGS : UInt32 := 0xfff7f7ff

/-- Linux `MSG_FASTOPEN` send flag (`0x20000000`). -/
def LINUX_MSG_FASTOPEN : UInt32 := 0x20000000

/-- Per-architecture Linux syscall number table covering the 7 argument-inspected/fallback syscalls and all 33 `k_deny_nrs` syscalls. -/
structure SyscallNumbers where
  /-- `__NR_clone3` (rejected with `ENOSYS` so glibc falls back to `clone`). -/
  clone3 : UInt32
  /-- `__NR_clone` (`args[0].lo32` checked against `CLONE_NEW_NS_MASK`). -/
  clone : UInt32
  /-- `__NR_socket` (`args[0].lo32` checked for `AF_UNIX` and `AF_SMC`). -/
  socket : UInt32
  /-- `__NR_socketpair` (`args[0..2].lo32` checked for `AF_UNIX`, `SOCK_STREAM | SOCK_SEQPACKET`, `proto == 0`). -/
  socketpair : UInt32
  /-- `__NR_sendto` (`args[3].lo32` checked for `MSG_FASTOPEN`). -/
  sendto : UInt32
  /-- `__NR_sendmsg` (`args[2].lo32` checked for `MSG_FASTOPEN`). -/
  sendmsg : UInt32
  /-- `__NR_sendmmsg` (`args[3].lo32` checked for `MSG_FASTOPEN`). -/
  sendmmsg : UInt32
  /-- `__NR_reboot` unconditional `EPERM` deny entry (`1/33`). -/
  reboot : UInt32
  /-- `__NR_kexec_load` unconditional `EPERM` deny entry (`2/33`). -/
  kexec_load : UInt32
  /-- `__NR_kexec_file_load` unconditional `EPERM` deny entry (`3/33`). -/
  kexec_file_load : UInt32
  /-- `__NR_mount` unconditional `EPERM` deny entry (`4/33`). -/
  mount : UInt32
  /-- `__NR_umount2` unconditional `EPERM` deny entry (`5/33`). -/
  umount2 : UInt32
  /-- `__NR_pivot_root` unconditional `EPERM` deny entry (`6/33`). -/
  pivot_root : UInt32
  /-- `__NR_swapon` unconditional `EPERM` deny entry (`7/33`). -/
  swapon : UInt32
  /-- `__NR_swapoff` unconditional `EPERM` deny entry (`8/33`). -/
  swapoff : UInt32
  /-- `__NR_fsmount` unconditional `EPERM` deny entry (`9/33`). -/
  fsmount : UInt32
  /-- `__NR_fsopen` unconditional `EPERM` deny entry (`10/33`). -/
  fsopen : UInt32
  /-- `__NR_fspick` unconditional `EPERM` deny entry (`11/33`). -/
  fspick : UInt32
  /-- `__NR_move_mount` unconditional `EPERM` deny entry (`12/33`). -/
  move_mount : UInt32
  /-- `__NR_open_tree` unconditional `EPERM` deny entry (`13/33`). -/
  open_tree : UInt32
  /-- `__NR_mount_setattr` unconditional `EPERM` deny entry (`14/33`). -/
  mount_setattr : UInt32
  /-- `__NR_init_module` unconditional `EPERM` deny entry (`15/33`). -/
  init_module : UInt32
  /-- `__NR_finit_module` unconditional `EPERM` deny entry (`16/33`). -/
  finit_module : UInt32
  /-- `__NR_delete_module` unconditional `EPERM` deny entry (`17/33`). -/
  delete_module : UInt32
  /-- `__NR_acct` unconditional `EPERM` deny entry (`18/33`). -/
  acct : UInt32
  /-- `__NR_settimeofday` unconditional `EPERM` deny entry (`19/33`). -/
  settimeofday : UInt32
  /-- `__NR_clock_settime` unconditional `EPERM` deny entry (`20/33`). -/
  clock_settime : UInt32
  /-- `__NR_clock_adjtime` unconditional `EPERM` deny entry (`21/33`). -/
  clock_adjtime : UInt32
  /-- `__NR_adjtimex` unconditional `EPERM` deny entry (`22/33`). -/
  adjtimex : UInt32
  /-- `__NR_bpf` unconditional `EPERM` deny entry (`23/33`). -/
  bpf : UInt32
  /-- `__NR_io_uring_setup` unconditional `EPERM` deny entry (`24/33`). -/
  io_uring_setup : UInt32
  /-- `__NR_io_uring_enter` unconditional `EPERM` deny entry (`25/33`). -/
  io_uring_enter : UInt32
  /-- `__NR_io_uring_register` unconditional `EPERM` deny entry (`26/33`). -/
  io_uring_register : UInt32
  /-- `__NR_keyctl` unconditional `EPERM` deny entry (`27/33`). -/
  keyctl : UInt32
  /-- `__NR_add_key` unconditional `EPERM` deny entry (`28/33`). -/
  add_key : UInt32
  /-- `__NR_request_key` unconditional `EPERM` deny entry (`29/33`). -/
  request_key : UInt32
  /-- `__NR_perf_event_open` unconditional `EPERM` deny entry (`30/33`). -/
  perf_event_open : UInt32
  /-- `__NR_userfaultfd` unconditional `EPERM` deny entry (`31/33`). -/
  userfaultfd : UInt32
  /-- `__NR_unshare` unconditional `EPERM` deny entry (`32/33`). -/
  unshare : UInt32
  /-- `__NR_setns` unconditional `EPERM` deny entry (`33/33`). -/
  setns : UInt32
  deriving Repr, BEq, DecidableEq, Inhabited

/-- Authoritative Linux `x86_64` syscall numbers (`arch/x86/entry/syscalls/syscall_64.tbl`). -/
def x86_64SyscallNumbers : SyscallNumbers :=
  { clone3 := 435
    clone := 56
    socket := 41
    socketpair := 53
    sendto := 44
    sendmsg := 46
    sendmmsg := 307
    reboot := 169
    kexec_load := 246
    kexec_file_load := 320
    mount := 165
    umount2 := 166
    pivot_root := 155
    swapon := 167
    swapoff := 168
    fsmount := 432
    fsopen := 430
    fspick := 433
    move_mount := 429
    open_tree := 428
    mount_setattr := 442
    init_module := 175
    finit_module := 313
    delete_module := 176
    acct := 163
    settimeofday := 164
    clock_settime := 227
    clock_adjtime := 305
    adjtimex := 159
    bpf := 321
    io_uring_setup := 425
    io_uring_enter := 426
    io_uring_register := 427
    keyctl := 250
    add_key := 248
    request_key := 249
    perf_event_open := 298
    userfaultfd := 323
    unshare := 272
    setns := 308 }

/-- Authoritative Linux `aarch64` syscall numbers (`include/uapi/asm-generic/unistd.h`). -/
def aarch64SyscallNumbers : SyscallNumbers :=
  { clone3 := 435
    clone := 220
    socket := 198
    socketpair := 199
    sendto := 206
    sendmsg := 211
    sendmmsg := 269
    reboot := 142
    kexec_load := 104
    kexec_file_load := 294
    mount := 40
    umount2 := 39
    pivot_root := 41
    swapon := 224
    swapoff := 225
    fsmount := 432
    fsopen := 430
    fspick := 433
    move_mount := 429
    open_tree := 428
    mount_setattr := 442
    init_module := 105
    finit_module := 273
    delete_module := 106
    acct := 89
    settimeofday := 170
    clock_settime := 112
    clock_adjtime := 266
    adjtimex := 171
    bpf := 280
    io_uring_setup := 425
    io_uring_enter := 426
    io_uring_register := 427
    keyctl := 219
    add_key := 217
    request_key := 218
    perf_event_open := 241
    userfaultfd := 282
    unshare := 97
    setns := 268 }

/-- Look up the `SyscallNumbers` table for `arch`. -/
def syscallNumbersFor : SeccompArch → SyscallNumbers
  | .x86_64 => x86_64SyscallNumbers
  | .aarch64 => aarch64SyscallNumbers

/-- Extract the ordered 33-entry unconditional `EPERM` syscall denylist from `nrs`. -/
def denySyscallNumbers (nrs : SyscallNumbers) : List UInt32 :=
  [ nrs.reboot
  , nrs.kexec_load
  , nrs.kexec_file_load
  , nrs.mount
  , nrs.umount2
  , nrs.pivot_root
  , nrs.swapon
  , nrs.swapoff
  , nrs.fsmount
  , nrs.fsopen
  , nrs.fspick
  , nrs.move_mount
  , nrs.open_tree
  , nrs.mount_setattr
  , nrs.init_module
  , nrs.finit_module
  , nrs.delete_module
  , nrs.acct
  , nrs.settimeofday
  , nrs.clock_settime
  , nrs.clock_adjtime
  , nrs.adjtimex
  , nrs.bpf
  , nrs.io_uring_setup
  , nrs.io_uring_enter
  , nrs.io_uring_register
  , nrs.keyctl
  , nrs.add_key
  , nrs.request_key
  , nrs.perf_event_open
  , nrs.userfaultfd
  , nrs.unshare
  , nrs.setns
  ]

/-- Classic BPF opcode `BPF_LD | BPF_W | BPF_ABS` (`0x0020`). -/
def BPF_LD_W_ABS : UInt16 := 0x0020

/-- Classic BPF opcode `BPF_ALU | BPF_AND | BPF_K` (`0x0054`). -/
def BPF_ALU_AND_K : UInt16 := 0x0054

/-- Classic BPF opcode `BPF_JMP | BPF_JA` (`0x0005`). -/
def BPF_JMP_JA : UInt16 := 0x0005

/-- Classic BPF opcode `BPF_JMP | BPF_JEQ | BPF_K` (`0x0015`). -/
def BPF_JMP_JEQ_K : UInt16 := 0x0015

/-- Classic BPF opcode `BPF_JMP | BPF_JGT | BPF_K` (`0x0025`). -/
def BPF_JMP_JGT_K : UInt16 := 0x0025

/-- Classic BPF opcode `BPF_JMP | BPF_JGE | BPF_K` (`0x0035`). -/
def BPF_JMP_JGE_K : UInt16 := 0x0035

/-- Classic BPF opcode `BPF_JMP | BPF_JSET | BPF_K` (`0x0045`). -/
def BPF_JMP_JSET_K : UInt16 := 0x0045

/-- Classic BPF opcode `BPF_RET | BPF_K` (`0x0006`). -/
def BPF_RET_K : UInt16 := 0x0006

/-- Byte offset of `nr` inside Linux `struct seccomp_data` (`0`). -/
def SECCOMP_OFFSET_NR : UInt32 := 0

/-- Byte offset of `arch` inside Linux `struct seccomp_data` (`4`). -/
def SECCOMP_OFFSET_ARCH : UInt32 := 4

/-- Byte offset of the low 32-bit word of `args[i]` inside `struct seccomp_data` on 64-bit little-endian Linux (`16 + 8 * i`). -/
def seccompArgLowOffset (i : Fin 6) : UInt32 :=
  16 + 8 * UInt32.ofNat i.val

/-- Classic BPF instruction (`struct sock_filter`) loaded via `seccomp(SECCOMP_SET_MODE_FILTER, ...)`. -/
structure SockFilter where
  /-- 16-bit BPF instruction opcode. -/
  code : UInt16
  /-- Forward jump offset on branch condition `true` (`pc' = pc + 1 + jt.toNat`). -/
  jt : UInt8
  /-- Forward jump offset on branch condition `false` (`pc' = pc + 1 + jf.toNat`). -/
  jf : UInt8
  /-- 32-bit immediate constant or `struct seccomp_data` byte offset. -/
  k : UInt32
  deriving Repr, BEq, DecidableEq, Inhabited

/-- Construct a non-branching `BPF_STMT(code, k)` instruction (`jt = 0`, `jf = 0`). -/
def bpfStmt (code : UInt16) (k : UInt32) : SockFilter :=
  { code := code, jt := 0, jf := 0, k := k }

/-- Construct a conditional `BPF_JUMP(code, k, jt, jf)` instruction. -/
def bpfJump (code : UInt16) (k : UInt32) (jt jf : UInt8) : SockFilter :=
  { code := code, jt := jt, jf := jf, k := k }

/-- Six 64-bit syscall argument registers stored in Linux `struct seccomp_data.args[6]`. -/
structure SeccompArgs where
  /-- Syscall argument `args[0]`. -/
  a0 : UInt64 := 0
  /-- Syscall argument `args[1]`. -/
  a1 : UInt64 := 0
  /-- Syscall argument `args[2]`. -/
  a2 : UInt64 := 0
  /-- Syscall argument `args[3]`. -/
  a3 : UInt64 := 0
  /-- Syscall argument `args[4]`. -/
  a4 : UInt64 := 0
  /-- Syscall argument `args[5]`. -/
  a5 : UInt64 := 0
  deriving Repr, BEq, DecidableEq, Inhabited

/-- Read argument `i` (`0..5`) from `SeccompArgs`. -/
def SeccompArgs.get (args : SeccompArgs) (i : Fin 6) : UInt64 :=
  match i.val with
  | 0 => args.a0
  | 1 => args.a1
  | 2 => args.a2
  | 3 => args.a3
  | 4 => args.a4
  | _ => args.a5

/-- Pure representation of Linux's 64-byte `struct seccomp_data` input passed to cBPF filters. -/
structure SeccompData where
  /-- Syscall number word at byte offset `0` (`int nr` bit-cast as 32-bit word). -/
  nr : UInt32 := 0
  /-- Audit architecture identifier at byte offset `4` (`AUDIT_ARCH_*`). -/
  arch : UInt32 := 0
  /-- User-space instruction pointer at byte offset `8`. -/
  instructionPointer : UInt64 := 0
  /-- Six 64-bit syscall arguments at byte offsets `16 .. 63`. -/
  args : SeccompArgs := {}
  deriving Repr, BEq, DecidableEq, Inhabited

/-- Read argument `i` (`0..5`) from `SeccompData`. -/
def SeccompData.arg (inp : SeccompData) (i : Fin 6) : UInt64 :=
  inp.args.get i

/-- Return `true` iff `off` is `offsetof(nr)` (`0`), `offsetof(arch)` (`4`), or a little-endian low-32-bit `args[i]` offset (`16 + 8 * i`). -/
def isSeccompLowWordOffset (off : UInt32) : Bool :=
  off == 0 || off == 4 || off == 16 || off == 24 || off == 32 || off == 40 || off == 48 || off == 56

/-- Read the 4-byte-aligned 32-bit word at byte offset `off` from `struct seccomp_data` on 64-bit little-endian Linux (`x86_64` / `aarch64`). -/
def readSeccompDataWord (inp : SeccompData) (off : UInt32) : Option UInt32 :=
  if off == 0 then some inp.nr
  else if off == 4 then some inp.arch
  else if off == 8 then some inp.instructionPointer.toUInt32
  else if off == 12 then some (inp.instructionPointer >>> 32).toUInt32
  else if off == 16 then some inp.args.a0.toUInt32
  else if off == 20 then some (inp.args.a0 >>> 32).toUInt32
  else if off == 24 then some inp.args.a1.toUInt32
  else if off == 28 then some (inp.args.a1 >>> 32).toUInt32
  else if off == 32 then some inp.args.a2.toUInt32
  else if off == 36 then some (inp.args.a2 >>> 32).toUInt32
  else if off == 40 then some inp.args.a3.toUInt32
  else if off == 44 then some (inp.args.a3 >>> 32).toUInt32
  else if off == 48 then some inp.args.a4.toUInt32
  else if off == 52 then some (inp.args.a4 >>> 32).toUInt32
  else if off == 56 then some inp.args.a5.toUInt32
  else if off == 60 then some (inp.args.a5 >>> 32).toUInt32
  else none

/-- Check that `insn` at index `pc` in a program of length `progSize` uses a `seccomp_check_filter`-legal opcode, valid `BPF_ABS` low-word offset, and in-bounds forward targets. -/
def isValidSeccompInsn (progSize pc : Nat) (insn : SockFilter) : Bool :=
  if insn.code == BPF_LD_W_ABS then
    isSeccompLowWordOffset insn.k && decide (pc + 1 < progSize)
  else if insn.code == BPF_ALU_AND_K then
    decide (pc + 1 < progSize)
  else if insn.code == BPF_JMP_JA then
    decide (pc + 1 + insn.k.toNat < progSize)
  else if insn.code == BPF_JMP_JEQ_K || insn.code == BPF_JMP_JGT_K ||
      insn.code == BPF_JMP_JGE_K || insn.code == BPF_JMP_JSET_K then
    decide (pc + 1 + insn.jt.toNat < progSize) && decide (pc + 1 + insn.jf.toNat < progSize)
  else if insn.code == BPF_RET_K then
    true
  else
    false

/-- Recursively check `isValidSeccompInsn` across `insns` starting at index `pc`. -/
def allValidSeccompInsnsFrom (progSize pc : Nat) : List SockFilter → Bool
  | [] => true
  | insn :: rest =>
    isValidSeccompInsn progSize pc insn && allValidSeccompInsnsFrom progSize (pc + 1) rest

/-- Return `true` iff `prog` has `1 .. 160` instructions and every instruction passes `isValidSeccompInsn` (which also forces `prog.back` to be `BPF_RET | BPF_K`). -/
def isValidLinuxSeccompProg (prog : Array SockFilter) : Bool :=
  decide (0 < prog.size) && decide (prog.size ≤ SECCOMP_MAX_INSNS) &&
    allValidSeccompInsnsFrom prog.size 0 prog.toList

/-- Propositional structural validity invariant for a Linux `seccomp` cBPF program (`0 < size ≤ 160`, legal opcodes, aligned low-word `BPF_ABS` offsets, and in-bounds forward jumps). -/
def ValidLinuxSeccompProg (prog : Array SockFilter) : Prop :=
  isValidLinuxSeccompProg prog = true

/-- Step-bounded pure classic BPF interpreter over the forward-jumping instruction suffix `insns`. -/
def evalBpfSteps (inp : SeccompData) : Nat → List SockFilter → UInt32 → Option UInt32
  | 0, _, _ => none
  | _ + 1, [], _ => none
  | fuel + 1, insn :: rest, acc =>
    if insn.code == BPF_LD_W_ABS then
      match readSeccompDataWord inp insn.k with
      | none => none
      | some w => evalBpfSteps inp fuel rest w
    else if insn.code == BPF_ALU_AND_K then
      evalBpfSteps inp fuel rest (acc &&& insn.k)
    else if insn.code == BPF_JMP_JA then
      evalBpfSteps inp fuel (rest.drop insn.k.toNat) acc
    else if insn.code == BPF_JMP_JEQ_K then
      let step := if acc == insn.k then insn.jt.toNat else insn.jf.toNat
      evalBpfSteps inp fuel (rest.drop step) acc
    else if insn.code == BPF_JMP_JGT_K then
      let step := if acc > insn.k then insn.jt.toNat else insn.jf.toNat
      evalBpfSteps inp fuel (rest.drop step) acc
    else if insn.code == BPF_JMP_JGE_K then
      let step := if acc ≥ insn.k then insn.jt.toNat else insn.jf.toNat
      evalBpfSteps inp fuel (rest.drop step) acc
    else if insn.code == BPF_JMP_JSET_K then
      let step := if (acc &&& insn.k) != 0 then insn.jt.toNat else insn.jf.toNat
      evalBpfSteps inp fuel (rest.drop step) acc
    else if insn.code == BPF_RET_K then
      some insn.k
    else
      none

/-- Pure total evaluator for a Linux `seccomp` cBPF program on `inp` (`A = 0` at `pc = 0`). -/
def evalBpf (prog : Array SockFilter) (inp : SeccompData) : Option UInt32 :=
  let insns := prog.toList
  evalBpfSteps inp insns.length insns 0

/-- Serialize one `SockFilter` instruction into its 8-byte little-endian Linux `struct sock_filter` wire layout (`u16LE code`, `u8 jt`, `u8 jf`, `u32LE k`). -/
def encodeSockFilterBytes (insn : SockFilter) : List UInt8 :=
  let c := insn.code.toNat
  let k := insn.k.toNat
  [ UInt8.ofNat (c % 256)
  , UInt8.ofNat ((c / 256) % 256)
  , insn.jt
  , insn.jf
  , UInt8.ofNat (k % 256)
  , UInt8.ofNat ((k / 256) % 256)
  , UInt8.ofNat ((k / 65536) % 256)
  , UInt8.ofNat ((k / 16777216) % 256)
  ]

/-- Reference specification serializing an `Array SockFilter` into contiguous `8 * prog.size`-byte little-endian bytes. -/
def encodeSeccompBpfModel (prog : Array SockFilter) : ByteArray :=
  ByteArray.mk (prog.toList.flatMap encodeSockFilterBytes).toArray

/-- Socket types passed to anonymous `socketpair(AF_UNIX, ...)` inside the box. -/
inductive UnixSocketpairType where
  /-- `SOCK_STREAM` anonymous IPC pair (allowed by `seccomp`). -/
  | stream
  /-- `SOCK_SEQPACKET` anonymous IPC pair (allowed by `seccomp`). -/
  | seqpacket
  /-- Any other socket type such as `SOCK_DGRAM` or `SOCK_RAW`, or non-zero protocol (blocked by `seccomp`). -/
  | disallowedOther
  deriving Repr, BEq, DecidableEq, Inhabited

/-- Privileged or escape operations blocked by `seccomp` BPF, `PR_SET_NO_NEW_PRIVS`, and namespaces. -/
inductive AdminOp where
  /-- `reboot`, `kexec_load`, or `kexec_file_load`. -/
  | rebootOrKexec
  /-- `settimeofday`, `clock_settime`, `clock_adjtime`, or `adjtimex`. -/
  | setHostClock
  /-- `init_module`, `finit_module`, or `delete_module`. -/
  | kernelModuleOp (moduleName : String)
  /-- `mount`, `umount2`, `pivot_root`, `swapon`, `swapoff`, `fsmount`, `fsopen`, `fspick`, `move_mount`, `open_tree`, or `mount_setattr`. -/
  | mountOrSwapOp
  /-- `acct` process-accounting toggle. -/
  | processAcctOp
  /-- `bpf`, `perf_event_open`, or `userfaultfd`. -/
  | bpfOrPerfOp
  /-- `io_uring_setup`, `io_uring_enter`, or `io_uring_register`. -/
  | ioUringOp
  /-- `keyctl`, `add_key`, or `request_key`. -/
  | keyringOp
  /-- `unshare` or `setns` namespace escape attempt. -/
  | namespaceEscapeOp
  /-- `socket(AF_UNIX, ...)`, `AF_SMC`, non-`AF_UNIX` `socketpair`, or `MSG_FASTOPEN` send attempt. -/
  | unixSocketOrSmcOp (socketToken : String)
  /-- Non-native ABI or `x32` syscall attempt. -/
  | nonNativeArchSyscall
  deriving Repr, BEq, DecidableEq, Inhabited

/-- Guest syscall surface modeled across the shared Linux kernel boundary. -/
inductive GuestSyscall where
  /-- Privileged admin, kernel-escape, `acct`, `io_uring`, `bpf`, or `socket(AF_UNIX, ...)` syscall. -/
  | adminOp (op : AdminOp)
  /-- Anonymous `socketpair(AF_UNIX, sockType, 0, sv)` IPC syscall (`SOCK_STREAM | SOCK_SEQPACKET` allowed box-locally). -/
  | anonUnixSocketpair (sockType : UnixSocketpairType)
  /-- Attempt to signal a host PID outside the box's isolated PID namespace. -/
  | signalHostPid (hostPid : Nat)
  /-- `clone3` syscall, rejected with `ENOSYS` by `seccomp` so glibc falls back cleanly to `clone`. -/
  | clone3Attempt
  /-- Read metadata or bytes from `boxPath` inside the box. -/
  | fsRead (boxPath : String)
  /-- Write `data` to `boxPath` inside the box. -/
  | fsWrite (boxPath : String) (data : ByteArray)
  /-- Allocate `bytes` of anonymous memory (`mmap` / `brk`) on the shared kernel. -/
  | mmapAnon (bytes : Nat)
  /-- Fork/clone a child `newBoxPid` via `clone` (`hasCloneNewFlags = true` attempts `CLONE_NEW*` namespace creation). -/
  | cloneProc (newBoxPid : Nat) (hasCloneNewFlags : Bool := false)
  /-- Send TCP `payload` to `(destIsLoopback, port)` from inside the box's network namespace. -/
  | tcpSend (destIsLoopback : Bool) (port : UInt16) (payload : ByteArray)
  deriving BEq, DecidableEq, Inhabited

instance : Repr GuestSyscall where
  reprPrec
    | .adminOp op, _ => "GuestSyscall.adminOp (" ++ repr op ++ ")"
    | .anonUnixSocketpair st, _ => "GuestSyscall.anonUnixSocketpair (" ++ repr st ++ ")"
    | .signalHostPid pid, _ => "GuestSyscall.signalHostPid " ++ repr pid
    | .clone3Attempt, _ => "GuestSyscall.clone3Attempt"
    | .fsRead bp, _ => "GuestSyscall.fsRead " ++ repr bp
    | .fsWrite bp bs, _ => "GuestSyscall.fsWrite " ++ repr bp ++ " " ++ repr bs.toList
    | .mmapAnon n, _ => "GuestSyscall.mmapAnon " ++ repr n
    | .cloneProc p flg, _ => "GuestSyscall.cloneProc " ++ repr p ++ " " ++ repr flg
    | .tcpSend lo pt bs, _ =>
      "GuestSyscall.tcpSend " ++ repr lo ++ " " ++ repr pt ++ " " ++ repr bs.toList

/-- Classify any `nr` in the 33-entry unconditional `seccomp` denylist into its corresponding `AdminOp`. -/
def classifyDeniedSyscallNr (nrs : SyscallNumbers) (nr : UInt32) : Option AdminOp :=
  if nr == nrs.reboot || nr == nrs.kexec_load || nr == nrs.kexec_file_load then
    some .rebootOrKexec
  else if nr == nrs.mount || nr == nrs.umount2 || nr == nrs.pivot_root ||
      nr == nrs.swapon || nr == nrs.swapoff || nr == nrs.fsmount ||
      nr == nrs.fsopen || nr == nrs.fspick || nr == nrs.move_mount ||
      nr == nrs.open_tree || nr == nrs.mount_setattr then
    some .mountOrSwapOp
  else if nr == nrs.init_module || nr == nrs.finit_module || nr == nrs.delete_module then
    some (.kernelModuleOp "")
  else if nr == nrs.acct then
    some .processAcctOp
  else if nr == nrs.settimeofday || nr == nrs.clock_settime ||
      nr == nrs.clock_adjtime || nr == nrs.adjtimex then
    some .setHostClock
  else if nr == nrs.bpf || nr == nrs.perf_event_open || nr == nrs.userfaultfd then
    some .bpfOrPerfOp
  else if nr == nrs.io_uring_setup || nr == nrs.io_uring_enter || nr == nrs.io_uring_register then
    some .ioUringOp
  else if nr == nrs.keyctl || nr == nrs.add_key || nr == nrs.request_key then
    some .keyringOp
  else if nr == nrs.unshare || nr == nrs.setns then
    some .namespaceEscapeOp
  else
    none

/-- Total classifier mapping a raw `SeccompData` frame on `arch` to the `seccomp`-governed `GuestSyscall` (or `none` for syscalls left to namespaces, Landlock, `rlimit`, and `cgroup v2`). -/
def decodeSeccompSyscall (arch : SeccompArch) (inp : SeccompData) : Option GuestSyscall :=
  if inp.arch != auditArchOf arch then
    some (.adminOp .nonNativeArchSyscall)
  else if arch == .x86_64 && inp.nr ≥ X32_SYSCALL_BIT then
    some (.adminOp .nonNativeArchSyscall)
  else
    let nrs := syscallNumbersFor arch
    if inp.nr == nrs.clone3 then
      some .clone3Attempt
    else if inp.nr == nrs.clone then
      let hasNewNs := (inp.args.a0.toUInt32 &&& CLONE_NEW_NS_MASK) != 0
      some (.cloneProc 2 hasNewNs)
    else if inp.nr == nrs.socket then
      let domain := inp.args.a0.toUInt32
      if domain == LINUX_AF_UNIX then
        some (.adminOp (.unixSocketOrSmcOp "AF_UNIX"))
      else if domain == LINUX_AF_SMC then
        some (.adminOp (.unixSocketOrSmcOp "AF_SMC"))
      else
        none
    else if inp.nr == nrs.socketpair then
      let domain := inp.args.a0.toUInt32
      let sockType := inp.args.a1.toUInt32 &&& LINUX_SOCK_TYPE_MASK_CLEAR_FLAGS
      let proto := inp.args.a2.toUInt32
      if domain != LINUX_AF_UNIX then
        some (.adminOp (.unixSocketOrSmcOp "socketpair"))
      else if proto != 0 then
        some (.anonUnixSocketpair .disallowedOther)
      else if sockType == LINUX_SOCK_STREAM then
        some (.anonUnixSocketpair .stream)
      else if sockType == LINUX_SOCK_SEQPACKET then
        some (.anonUnixSocketpair .seqpacket)
      else
        some (.anonUnixSocketpair .disallowedOther)
    else if inp.nr == nrs.sendto then
      if (inp.args.a3.toUInt32 &&& LINUX_MSG_FASTOPEN) != 0 then
        some (.adminOp (.unixSocketOrSmcOp "MSG_FASTOPEN"))
      else
        none
    else if inp.nr == nrs.sendmsg then
      if (inp.args.a2.toUInt32 &&& LINUX_MSG_FASTOPEN) != 0 then
        some (.adminOp (.unixSocketOrSmcOp "MSG_FASTOPEN"))
      else
        none
    else if inp.nr == nrs.sendmmsg then
      if (inp.args.a3.toUInt32 &&& LINUX_MSG_FASTOPEN) != 0 then
        some (.adminOp (.unixSocketOrSmcOp "MSG_FASTOPEN"))
      else
        none
    else
      match classifyDeniedSyscallNr nrs inp.nr with
      | some op => some (.adminOp op)
      | none => none

/-- Allowed BPF compilation contract for `Seccomp.compileSeccompBpf`. -/
def allowedCompileSeccompBpf (arch : SeccompArch) (prog : Array SockFilter) : Prop :=
  isValidLinuxSeccompProg prog = true ∧
    ∀ inp : SeccompData,
      evalBpf prog inp =
        some (match decodeSeccompSyscall arch inp with
          | none => SECCOMP_RET_ALLOW
          | some .clone3Attempt => SECCOMP_RET_ERRNO_ENOSYS
          | some (.anonUnixSocketpair .stream) => SECCOMP_RET_ALLOW
          | some (.anonUnixSocketpair .seqpacket) => SECCOMP_RET_ALLOW
          | some (.cloneProc _ false) => SECCOMP_RET_ALLOW
          | some _ => SECCOMP_RET_ERRNO_EPERM)

end LeanSwe.ProcessSandbox.Model
