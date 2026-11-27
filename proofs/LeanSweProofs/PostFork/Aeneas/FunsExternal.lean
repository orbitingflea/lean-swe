import Aeneas
import LeanSweProofs.PostFork.Aeneas.Types
import LeanSweProofs.PostFork.Aeneas.Model.World
import LeanSweProofs.PostFork.Aeneas.Model.Sys

/-!
# PostFork Aeneas External-Function Shims

Thin `_root_.sys.*` `abbrev` shims confining the Aeneas `-split-files` external
symbol namespace to this `.impl` module while delegating definitionally (`rfl`)
to `LeanSwe.PostFork.Aeneas.Internal.Sys`.
-/

namespace sys

/-- External-function shim for `postfork::sys::setpgid_self` delegating by `rfl` to `Internal.Sys.setpgid_self`. -/
abbrev setpgid_self := LeanSwe.PostFork.Aeneas.Internal.Sys.setpgid_self
/-- External-function shim for `postfork::sys::sig_dfl` delegating by `rfl` to `Internal.Sys.sig_dfl`. -/
abbrev sig_dfl := LeanSwe.PostFork.Aeneas.Internal.Sys.sig_dfl
/-- External-function shim for `postfork::sys::sig_ign` delegating by `rfl` to `Internal.Sys.sig_ign`. -/
abbrev sig_ign := LeanSwe.PostFork.Aeneas.Internal.Sys.sig_ign
/-- External-function shim for `postfork::sys::sig_unblock` delegating by `rfl` to `Internal.Sys.sig_unblock`. -/
abbrev sig_unblock := LeanSwe.PostFork.Aeneas.Internal.Sys.sig_unblock
/-- External-function shim for `postfork::sys::close` delegating by `rfl` to `Internal.Sys.close`. -/
abbrev close := LeanSwe.PostFork.Aeneas.Internal.Sys.close
/-- External-function shim for `postfork::sys::dup2` delegating by `rfl` to `Internal.Sys.dup2`. -/
abbrev dup2 := LeanSwe.PostFork.Aeneas.Internal.Sys.dup2
/-- External-function shim for `postfork::sys::fcntl_getfd` delegating by `rfl` to `Internal.Sys.fcntl_getfd`. -/
abbrev fcntl_getfd := LeanSwe.PostFork.Aeneas.Internal.Sys.fcntl_getfd
/-- External-function shim for `postfork::sys::fcntl_setfd` delegating by `rfl` to `Internal.Sys.fcntl_setfd`. -/
abbrev fcntl_setfd := LeanSwe.PostFork.Aeneas.Internal.Sys.fcntl_setfd
/-- External-function shim for `postfork::sys::fcntl_dupfd_cloexec` delegating by `rfl` to `Internal.Sys.fcntl_dupfd_cloexec`. -/
abbrev fcntl_dupfd_cloexec := LeanSwe.PostFork.Aeneas.Internal.Sys.fcntl_dupfd_cloexec
/-- External-function shim for `postfork::sys::close_range` delegating by `rfl` to `Internal.Sys.close_range`. -/
abbrev close_range := LeanSwe.PostFork.Aeneas.Internal.Sys.close_range
/-- External-function shim for `postfork::sys::open_proc_self_fd` delegating by `rfl` to `Internal.Sys.open_proc_self_fd`. -/
abbrev open_proc_self_fd := LeanSwe.PostFork.Aeneas.Internal.Sys.open_proc_self_fd
/-- External-function shim for `postfork::sys::getdents64` delegating by `rfl` to `Internal.Sys.getdents64`. -/
abbrev getdents64 := LeanSwe.PostFork.Aeneas.Internal.Sys.getdents64
/-- External-function shim for `postfork::sys::read1` delegating by `rfl` to `Internal.Sys.read1`. -/
abbrev read1 := LeanSwe.PostFork.Aeneas.Internal.Sys.read1
/-- External-function shim for `postfork::sys::write` delegating by `rfl` to `Internal.Sys.write`. -/
abbrev write := LeanSwe.PostFork.Aeneas.Internal.Sys.write
/-- External-function shim for `postfork::sys::chdir` delegating by `rfl` to `Internal.Sys.chdir`. -/
abbrev chdir := LeanSwe.PostFork.Aeneas.Internal.Sys.chdir
/-- External-function shim for `postfork::sys::execve` delegating by `rfl` to `Internal.Sys.execve`. -/
abbrev execve := LeanSwe.PostFork.Aeneas.Internal.Sys.execve
/-- External-function shim for `postfork::sys::exit` delegating by `rfl` to `Internal.Sys.exit`. -/
abbrev exit := LeanSwe.PostFork.Aeneas.Internal.Sys.exit

end sys
