import Aeneas

open Aeneas Aeneas.Std Result

set_option linter.dupNamespace false
set_option linter.style.longLine false
set_option linter.style.setOption false

namespace LeanSwe.ProcessSandbox.Init.World

/-- Raw byte sequence representing CLI tokens, serialized plan payloads, or status frames. -/
abbrev Bytes := List Std.U8

/-- Pure state of an owned `PlanBuf` buffer in `psandbox_init::init_sys`. -/
structure PlanBufState where
  /-- Current accumulated plan bytes. -/
  bytes : Bytes := []
  /-- Current allocated byte capacity. -/
  cap : Nat := 0
  deriving DecidableEq, Repr, Inhabited

/-- Pure state of a pre-fork `ExecTable` string and pointer table in `psandbox_init::init_sys`. -/
structure ExecTableState where
  /-- Expected `argc` count (`argv[1..=argc]`). -/
  argc : Std.U32 := 0#u32
  /-- Expected `envc` count (`envp[0..envc]`). -/
  envc : Std.U32 := 0#u32
  /-- Stored guest `program` (`argv[0]`). -/
  program : Bytes := []
  /-- Stored guest working directory `cwd`. -/
  cwd : Bytes := []
  /-- Stored guest argument entries `(idx, bytes)`. -/
  args : List (Std.U32 × Bytes) := []
  /-- Stored guest environment entries `(idx, key, val)`. -/
  env : List (Std.U32 × Bytes × Bytes) := []
  deriving DecidableEq, Repr, Inhabited

/-- Pure single-process state modeled across `psandbox_init::init_sys` calls. -/
structure InitState where
  /-- Command-line argument vector `argv[0..argc]`. -/
  cliArgs : List Bytes := []
  /-- Remaining unread bytes on `plan_fd`. -/
  planStream : Bytes := []
  /-- Current loopback interface flags (`SIOCGIFFLAGS`). -/
  loFlags : Std.I16 := 0#i16
  /-- Kernel Landlock ABI version (`>= 4` on supported hosts). -/
  landlockAbi : Std.I32 := 4#i32
  /-- Recorded `(fd, bytes)` writes issued via `write_fd`. -/
  writes : List (Std.I32 × Bytes) := []
  /-- Recorded descriptors closed via `close_fd`. -/
  closedFds : List Std.I32 := []
  /-- Optional terminal `_exit` code if `exit_now` was invoked. -/
  exitCode? : Option Std.I32 := none
  deriving DecidableEq, Repr, Inhabited

end LeanSwe.ProcessSandbox.Init.World

/-- `psandbox_init::init_sys::Sys`: container `psandbox-init` OS state. -/
abbrev init_sys.Sys : Type := LeanSwe.ProcessSandbox.Init.World.InitState

/-- `psandbox_init::init_sys::PlanBuf`: owned `LSWP0002` byte buffer. -/
abbrev init_sys.PlanBuf : Type := LeanSwe.ProcessSandbox.Init.World.PlanBufState

/-- `psandbox_init::init_sys::ExecTable`: pre-fork guest `argv`/`envp` table. -/
abbrev init_sys.ExecTable : Type := LeanSwe.ProcessSandbox.Init.World.ExecTableState
