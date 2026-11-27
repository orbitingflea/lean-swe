import LeanSwe.PostFork.Aeneas.Model.World

open _root_.Aeneas _root_.Aeneas.Std Result

namespace LeanSwe.PostFork.Aeneas.Internal.Sys

open LeanSwe.PostFork.Aeneas.Internal.World

/-- `setpgid(0, 0)`: fails with `EPERM` if caller is a session leader (`pid == sid ∧ pid > 0`), else sets `pgid := pid`. -/
def setpgid_self (s : ChildState) :
    Result ((core.result.Result Unit Std.I32) × ChildState) :=
  runUnitSyscall s .setpgidSelf
    (if s.pid == s.sid && s.pid > 0 then some EPERM else none)
    (fun s => { s with pgid := s.pid })

/-- `rt_sigaction(sig, SIG_DFL, NULL)`. -/
def sig_dfl (s : ChildState) (sig : Std.I32) :
    Result ((core.result.Result Unit Std.I32) × ChildState) :=
  if s.status == .running && isUserspaceInvalidSigactionSig sig then
    ok (.Err EINVAL, s)
  else
    runUnitSyscall s (.sigDfl sig)
      (if isKernelInvalidSigactionSig sig then some EINVAL else none)
      (fun s => s.putSig sig.val .default)

/-- `rt_sigaction(sig, SIG_IGN, NULL)`. -/
def sig_ign (s : ChildState) (sig : Std.I32) :
    Result ((core.result.Result Unit Std.I32) × ChildState) :=
  if s.status == .running && isUserspaceInvalidSigactionSig sig then
    ok (.Err EINVAL, s)
  else
    runUnitSyscall s (.sigIgn sig)
      (if isKernelInvalidSigactionSig sig then some EINVAL else none)
      (fun s => s.putSig sig.val .ignore)

/-- `rt_sigprocmask(SIG_UNBLOCK, {sig}, NULL, 8)`. -/
def sig_unblock (s : ChildState) (sig : Std.I32) :
    Result ((core.result.Result Unit Std.I32) × ChildState) :=
  if s.status == .running && (sig.val < 1 || sig.val > 64) then
    ok (.Err EINVAL, s)
  else
    runUnitSyscall s (.sigUnblock sig) none
      (fun s => { s with blockedSigs := s.blockedSigs.filter (· != sig.val) })

/-- `close(fd)`: fails with `EBADF` when closed; otherwise detaches `fd` on both `Ok` and `Err`. -/
def close (s : ChildState) (fd : Std.I32) :
    Result ((core.result.Result Unit Std.I32) × ChildState) :=
  runUnitSyscall s (.close fd)
    (if s.isOpen fd.val then none else some EBADF)
    (fun s => s.closeSlot fd.val)
    (fun s => s.closeSlot fd.val)

/-- `dup2(oldfd, newfd)`: `oldfd == newfd` checks only `isOpen oldfd` (preserving flags even when `oldfd >= fdLimit`);
    `oldfd != newfd` also checks `0 ≤ newfd < fdLimit` and installs `cloexec = false`. -/
def dup2 (s : ChildState) (oldfd newfd : Std.I32) :
    Result ((core.result.Result Unit Std.I32) × ChildState) :=
  let forcedErr? :=
    if !s.isOpen oldfd.val then some EBADF
    else if oldfd.val == newfd.val then none
    else if newfd.val < 0 || newfd.val ≥ s.fdLimit then some EBADF
    else none
  runUnitSyscall s (.dup2 oldfd newfd) forcedErr?
    (fun s =>
      if oldfd.val == newfd.val then s
      else
        match s.getFd oldfd.val with
        | some e => s.putSlot newfd.val { desc := e.desc, cloexec := false, extraFdFlags := 0#i32 }
        | none => s)

/-- `fcntl(fd, F_GETFD)`. -/
def fcntl_getfd (s : ChildState) (fd : Std.I32) :
    Result ((core.result.Result Std.I32 Std.I32) × ChildState) :=
  match s.getFd fd.val with
  | none => runI32Syscall s (.fcntlGetfd fd) (some EBADF) (fun s => (0#i32, s))
  | some e => runI32Syscall s (.fcntlGetfd fd) none (fun s => (fdFlagsWord e, s))

/-- `fcntl(fd, F_SETFD, flags)`. -/
def fcntl_setfd (s : ChildState) (fd flags : Std.I32) :
    Result ((core.result.Result Unit Std.I32) × ChildState) :=
  runUnitSyscall s (.fcntlSetfd fd flags)
    (if s.isOpen fd.val then none else some EBADF)
    (fun s =>
      match s.getFd fd.val with
      | some e => s.putSlot fd.val (updateFdFlags s.kernelMasksSetfd flags e)
      | none => s)

/-- `fcntl(fd, F_DUPFD_CLOEXEC, min_fd)`: `EBADF` precedes `min_fd` `EINVAL`, then `EMFILE` when `[min_fd, fdLimit)` is full. -/
def fcntl_dupfd_cloexec (s : ChildState) (fd minFd : Std.I32) :
    Result ((core.result.Result Std.I32 Std.I32) × ChildState) :=
  match s.getFd fd.val with
  | none => runI32Syscall s (.fcntlDupfdCloexec fd minFd) (some EBADF) (fun s => (0#i32, s))
  | some e =>
    if minFd.val < 0 || minFd.val ≥ s.fdLimit then
      runI32Syscall s (.fcntlDupfdCloexec fd minFd) (some EINVAL) (fun s => (0#i32, s))
    else
      match findLowestFreeFd s minFd.val with
      | none => runI32Syscall s (.fcntlDupfdCloexec fd minFd) (some EMFILE) (fun s => (0#i32, s))
      | some dst =>
        runI32Syscall s (.fcntlDupfdCloexec fd minFd) none
          (fun s => (mkI32 dst, s.putSlot dst { desc := e.desc, cloexec := true, extraFdFlags := 0#i32 }))

/-- `close_range(first, last, flags)`: checks `closeRangeSupported` (`ENOSYS` / `seccomp` `EPERM` at syscall entry) before
    rejecting `first > last` and unknown flags with `EINVAL`, and closes (or sets `FD_CLOEXEC` when `CLOSE_RANGE_CLOEXEC = 4` is set)
    all open descriptors in `[first, last]`. -/
def close_range (s : ChildState) (first last flags : Std.U32) :
    Result ((core.result.Result Unit Std.I32) × ChildState) :=
  let forcedErr? :=
    if !s.closeRangeSupported then
      some (sanitizeErrno s.closeRangeErrno)
    else if first.val > last.val || (flags &&& 4294967289#u32) != 0#u32 then
      some EINVAL
    else
      none
  runUnitSyscall s (.closeRange first last flags) forcedErr?
    (fun s =>
      let inRange (fd : Int) : Bool := decide (first.val ≤ fd ∧ fd ≤ last.val)
      if (flags &&& 4#u32) != 0#u32 then
        { s with fds := (dedupFdEntries s.fds).map fun (fd, e) =>
            if inRange fd then (fd, { e with cloexec := true }) else (fd, e) }
      else
        { s with fds := s.fds.filter (fun p => !inRange p.1) })

/-- `open("/proc/self/fd", O_RDONLY | O_DIRECTORY | O_CLOEXEC)`. -/
def open_proc_self_fd (s : ChildState) :
    Result ((core.result.Result Std.I32 Std.I32) × ChildState) :=
  match findLowestFreeFd s 0 with
  | none => runI32Syscall s .openProcSelfFd (some EMFILE) (fun s => (0#i32, s))
  | some dirfd =>
    if !s.procSelfFdAvailable then
      runI32Syscall s .openProcSelfFd (some (sanitizeErrno s.procOpenErrno)) (fun s => (0#i32, s))
    else
      runI32Syscall s .openProcSelfFd none fun s =>
        let d := freshDescId s
        let s1 := s.putDesc d (.procSelfFd (-2))
        let s2 := s1.putSlot dirfd { desc := d, cloexec := true, extraFdFlags := 0#i32 }
        (mkI32 dirfd, s2)

/-- `getdents64(dirfd, buf, 256)` emitting binary `linux_dirent64` records and advancing the `/proc/self/fd` cursor. -/
def getdents64 (s : ChildState) (dirfd : Std.I32) (buf : Array Std.U8 256#usize) :
    Result ((core.result.Result Std.Usize Std.I32) × ChildState × (Array Std.U8 256#usize)) :=
  match s.status with
  | .running =>
    match currentFault s with
    | .seccomp rawE =>
      let err := sanitizeErrno rawE
      ok (.Err err, { s with trace := s.trace ++ [⟨.getdents64 dirfd, .err err⟩] }, buf)
    | fault =>
      match s.getFd dirfd.val with
      | none =>
        ok (.Err EBADF, { s with trace := s.trace ++ [⟨.getdents64 dirfd, .err EBADF⟩] }, buf)
      | some e =>
        match s.getDesc e.desc with
        | .stream .. =>
          ok (.Err ENOTDIR, { s with trace := s.trace ++ [⟨.getdents64 dirfd, .err ENOTDIR⟩] }, buf)
        | .directory cursor =>
          match fault with
          | .fail rawE =>
            let err := sanitizeErrno rawE
            ok (.Err err, { s with trace := s.trace ++ [⟨.getdents64 dirfd, .err err⟩] }, buf)
          | _ =>
            let maxEnt := match fault with
              | .dentsBatch k => k + 1
              | _ => 64
            let cands := ([(0, [46#u8]), (1, [46#u8, 46#u8])]).filter (fun p => decide (cursor ≤ p.1))
            let (payload, nextCur?) := packDirDotEntries cands maxEnt [] none
            let s1 := match nextCur? with
              | some nc => s.putDesc e.desc (.directory nc)
              | none => s
            let buf' := overlayBuf256 payload buf
            let n := payload.length
            let s2 := { s1 with trace := s1.trace ++ [⟨.getdents64 dirfd, .okVal (Int.ofNat n)⟩] }
            ok (.Ok (mkUsize n), s2, buf')
        | .procSelfFd cursor =>
          match fault with
          | .fail rawE =>
            let err := sanitizeErrno rawE
            ok (.Err err, { s with trace := s.trace ++ [⟨.getdents64 dirfd, .err err⟩] }, buf)
          | _ =>
            let maxEnt := match fault with
              | .dentsBatch k => k + 1
              | _ => 64
            let cands := procSelfFdEntriesFrom s cursor
            let (payload, nextCur?) := packProcDirents (procEofCursor s) cands maxEnt [] none
            let s1 := match nextCur? with
              | some nextCur => s.putDesc e.desc (.procSelfFd nextCur)
              | none => s
            let buf' := overlayBuf256 payload buf
            let n := payload.length
            let s2 := { s1 with trace := s1.trace ++ [⟨.getdents64 dirfd, .okVal (Int.ofNat n)⟩] }
            ok (.Ok (mkUsize n), s2, buf')
  | _ => ok (.Ok 0#usize, s, buf)

/-- `read(fd, buf, 1)`: checks seccomp, then `EBADF` and `EISDIR`, handles `EINTR`/errors, and consumes up to 1 byte from `readBytes`. -/
def read1 (s : ChildState) (fd : Std.I32) (buf : Array Std.U8 1#usize) :
    Result ((core.result.Result Std.Usize Std.I32) × ChildState × (Array Std.U8 1#usize)) :=
  match s.status with
  | .running =>
    match currentFault s with
    | .seccomp rawE =>
      let err := sanitizeErrno rawE
      ok (.Err err, { s with trace := s.trace ++ [⟨.read1 fd, .err err⟩] }, buf)
    | fault =>
      match s.getFd fd.val with
      | none =>
        ok (.Err EBADF, { s with trace := s.trace ++ [⟨.read1 fd, .err EBADF⟩] }, buf)
      | some e =>
        match s.getDesc e.desc with
        | .directory _ | .procSelfFd _ =>
          ok (.Err EISDIR, { s with trace := s.trace ++ [⟨.read1 fd, .err EISDIR⟩] }, buf)
        | .stream false _ _ _ =>
          ok (.Err EBADF, { s with trace := s.trace ++ [⟨.read1 fd, .err EBADF⟩] }, buf)
        | .stream true writable broken stream =>
          match fault with
          | .fail rawE =>
            let err := sanitizeErrno rawE
            ok (.Err err, { s with trace := s.trace ++ [⟨.read1 fd, .err err⟩] }, buf)
          | .normal | .seccomp _ | .partialWrite _ | .dentsBatch _ =>
            match stream with
            | [] =>
              ok (.Ok 0#usize, { s with trace := s.trace ++ [⟨.read1 fd, .okVal 0⟩] }, buf)
            | b :: rest =>
              let s1 := s.putDesc e.desc (.stream true writable broken rest)
              let buf' := Array.make 1#usize [b]
              ok (.Ok 1#usize, { s1 with trace := s1.trace ++ [⟨.read1 fd, .okVal 1⟩] }, buf')
  | _ => ok (.Ok 0#usize, s, buf)

/-- `write(fd, buf, len)`: checks seccomp, then `EBADF`, delivers fatal `SIGPIPE` (`13`) on broken pipe when `SIGPIPE == .default`
    (or returns `EPIPE` when ignored), supports `EINTR` and partial writes, and logs written bytes to `writeLog`. -/
def write (s : ChildState) (fd : Std.I32) (buf : Slice Std.U8) :
    Result ((core.result.Result Std.Usize Std.I32) × ChildState) :=
  let bytes := buf.val
  match s.status with
  | .running =>
    match currentFault s with
    | .seccomp rawE =>
      let err := sanitizeErrno rawE
      ok (.Err err, { s with trace := s.trace ++ [⟨.write fd bytes, .err err⟩] })
    | fault =>
      match s.getFd fd.val with
      | none =>
        ok (.Err EBADF, { s with trace := s.trace ++ [⟨.write fd bytes, .err EBADF⟩] })
      | some e =>
        match s.getDesc e.desc with
        | .directory _ | .procSelfFd _ =>
          ok (.Err EBADF, { s with trace := s.trace ++ [⟨.write fd bytes, .err EBADF⟩] })
        | .stream _ false _ _ =>
          ok (.Err EBADF, { s with trace := s.trace ++ [⟨.write fd bytes, .err EBADF⟩] })
        | .stream _ true broken _ =>
          if bytes.isEmpty then
            match fault with
            | .fail rawE =>
              let err := sanitizeErrno rawE
              ok (.Err err, { s with trace := s.trace ++ [⟨.write fd bytes, .err err⟩] })
            | .normal | .seccomp _ | .partialWrite _ | .dentsBatch _ =>
              ok (.Ok 0#usize, { s with trace := s.trace ++ [⟨.write fd bytes, .okVal 0⟩] })
          else if broken then
            if s.getSig 13 == .default && s.pid != 1 && !s.isSigBlocked 13 then
              let sDead := { s with status := .signaled 13#i32, trace := s.trace ++ [⟨.write fd bytes, .fatalSig 13#i32⟩] }
              ok (.Err EPIPE, sDead)
            else
              ok (.Err EPIPE, { s with trace := s.trace ++ [⟨.write fd bytes, .err EPIPE⟩] })
          else
            match fault with
            | .fail rawE =>
              let err := sanitizeErrno rawE
              ok (.Err err, { s with trace := s.trace ++ [⟨.write fd bytes, .err err⟩] })
            | .partialWrite maxMinusOne =>
              let n := Nat.min bytes.length (maxMinusOne + 1)
              let chunk := bytes.take n
              let s1 := { s with
                writeLog := s.writeLog ++ [(e.desc, chunk)]
                trace := s.trace ++ [⟨.write fd bytes, .okVal (Int.ofNat n)⟩] }
              ok (.Ok (mkUsize n), s1)
            | .normal | .seccomp _ | .dentsBatch _ =>
              let n := bytes.length
              let s1 := { s with
                writeLog := s.writeLog ++ [(e.desc, bytes)]
                trace := s.trace ++ [⟨.write fd bytes, .okVal (Int.ofNat n)⟩] }
              ok (.Ok (mkUsize n), s1)
  | _ => ok (.Ok 0#usize, s)

/-- `chdir(path)`. -/
def chdir (s : ChildState) (path : Bytes) :
    Result ((core.result.Result Unit Std.I32) × ChildState) :=
  runUnitSyscall s (.chdir path)
    (if path.isEmpty then some ENOENT else none)
    (fun s => { s with cwd := resolveChdirTarget s path })

/-- `execve(path, argv, envp)`: checks seccomp, then replaces process image (`status := .execd ...`) on success or returns positive `errno` on failure. -/
def execve (s : ChildState) (path : Bytes) (argv envp : List Bytes) :
    Result (Std.I32 × ChildState) :=
  match s.status with
  | .running =>
    match currentFault s with
    | .seccomp rawE =>
      let e := sanitizeErrno rawE
      ok (e, { s with trace := s.trace ++ [⟨.execve path argv envp, .err e⟩] })
    | .fail rawE =>
      if path.isEmpty then
        ok (ENOENT, { s with trace := s.trace ++ [⟨.execve path argv envp, .err ENOENT⟩] })
      else
        let e := sanitizeErrno rawE
        ok (e, { s with trace := s.trace ++ [⟨.execve path argv envp, .err e⟩] })
    | .normal | .partialWrite _ | .dentsBatch _ =>
      if path.isEmpty then
        ok (ENOENT, { s with trace := s.trace ++ [⟨.execve path argv envp, .err ENOENT⟩] })
      else
        let img := imageOf s path argv envp
        let s' := { s with status := .execd img, trace := s.trace ++ [⟨.execve path argv envp, .okVal 0⟩] }
        ok (0#i32, s')
  | _ => ok (0#i32, s)

/-- `_exit(code)`: terminates the running child with exit status `code`. -/
def exit (s : ChildState) (code : Std.I32) : Result ChildState :=
  match s.status with
  | .running => ok { s with status := .exited code, trace := s.trace ++ [⟨.exit code, .okVal 0⟩] }
  | _ => ok s

end LeanSwe.PostFork.Aeneas.Internal.Sys
