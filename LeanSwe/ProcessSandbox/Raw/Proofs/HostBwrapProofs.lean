import LeanSwe.ProcessSandbox.Raw.SysBridge.Bwrap

namespace LeanSwe.ProcessSandbox.Raw.Proofs.HostBwrap

open LeanSwe.LinuxSyscall
open LeanSwe.PostFork
open LeanSwe.ProcessSandbox.Raw
open LeanSwe.ProcessSandbox.Raw.SysBridge.Bwrap

/-- `detectHostAuditArch` maps Linux `x86_64-*` and `aarch64-*` targets to their exact `AUDIT_ARCH_*` constants and fails closed (`0`) on non-Linux or unsupported targets. -/
theorem detectHostAuditArch_exact :
    detectHostAuditArch true "x86_64-unknown-linux-gnu" = 0xc000003e ∧
    detectHostAuditArch true "aarch64-unknown-linux-gnu" = 0xc00000b7 ∧
    detectHostAuditArch false "x86_64-unknown-linux-gnu" = 0 ∧
    detectHostAuditArch true "riscv64-unknown-linux-gnu" = 0 := by
  decide

/-- `detectHostAuditArch` always returns `0` when `isLinux = false`. -/
theorem detectHostAuditArch_nonLinux (target : String) :
    detectHostAuditArch false target = 0 := by
  simp [detectHostAuditArch]

/-- `decodeHostAuditArch (detectHostAuditArch false target)` always fails closed with `.unavailable`. -/
theorem decodeHostAuditArch_nonLinux_unavailable (target : String) :
    ∃ err, Internal.decodeHostAuditArch (detectHostAuditArch false target) = .error err ∧
      err.kind = .unavailable ∧ err.message ≠ "" := by
  rw [detectHostAuditArch_nonLinux]
  refine ⟨_, rfl, rfl, by decide⟩

/-- `decodeEmbeddedInitBytes` fails closed with a non-empty error whenever Base64 decoding fails, yields empty bytes, or exceeds `MAX_INIT_ELF_BYTES`. -/
theorem decodeEmbeddedInitBytes_fails_closed (b64 : String) :
    (∀ err, LeanSwe.Base64.decode b64 = .error err →
      ∃ msg, decodeEmbeddedInitBytes b64 = .error msg ∧ msg ≠ "") ∧
    (∀ bs, LeanSwe.Base64.decode b64 = .ok bs → bs.size = 0 →
      ∃ msg, decodeEmbeddedInitBytes b64 = .error msg ∧ msg ≠ "") ∧
    (∀ bs, LeanSwe.Base64.decode b64 = .ok bs → bs.size > MAX_INIT_ELF_BYTES →
      ∃ msg, decodeEmbeddedInitBytes b64 = .error msg ∧ msg ≠ "") := by
  refine ⟨?_, ?_, ?_⟩
  · intro err h
    unfold decodeEmbeddedInitBytes
    rw [h]
    refine ⟨_, rfl, ?_⟩
    intro heq
    simp only [String.append_eq_empty_iff] at heq
    exact absurd heq.1 (by decide)
  · intro bs h h0
    unfold decodeEmbeddedInitBytes
    rw [h]
    dsimp only
    rw [h0]
    exact ⟨"embedded init binary is empty", rfl, by decide⟩
  · intro bs h hbig
    unfold decodeEmbeddedInitBytes
    rw [h]
    dsimp only
    have hnz : (bs.size == 0) = false := by
      have : bs.size ≠ 0 := by omega
      simp [this]
    rw [hnz]
    simp only [Bool.false_eq_true, ↓reduceIte, hbig]
    exact ⟨"embedded init binary exceeds size cap", rfl, by decide⟩

/-- Whenever `decodeEmbeddedInitBytes` succeeds with `bs`, `0 < bs.size ≤ MAX_INIT_ELF_BYTES` and `bs` matches `Base64.decode`. -/
theorem decodeEmbeddedInitBytes_ok_bounds (b64 : String) (bs : ByteArray)
    (hok : decodeEmbeddedInitBytes b64 = .ok bs) :
    0 < bs.size ∧ bs.size ≤ MAX_INIT_ELF_BYTES ∧ LeanSwe.Base64.decode b64 = .ok bs := by
  unfold decodeEmbeddedInitBytes at hok
  cases hd : LeanSwe.Base64.decode b64 with
  | error e => rw [hd] at hok; cases hok
  | ok raw =>
    rw [hd] at hok
    by_cases h0 : raw.size = 0
    · simp [h0] at hok
    · have h0b : (raw.size == 0) = false := by simp [h0]
      simp only [h0b, Bool.false_eq_true, ↓reduceIte] at hok
      by_cases hbig : raw.size > MAX_INIT_ELF_BYTES
      · simp [hbig] at hok
      · simp only [hbig, ↓reduceIte] at hok
        cases hok
        exact ⟨by omega, by omega, rfl⟩

/-- `mapPathErrnoToSandboxError` maps `ENOENT`/`ENOTDIR` to `.notFound`, `EACCES`/`EPERM` to `.permissionDenied`, and other errnos to `.ioError`, always preserving path, errno, and non-empty message. -/
theorem mapPathErrnoToSandboxError_classification (path ctx : String) (e : Errno) :
    let err := mapPathErrnoToSandboxError path ctx e
    err.path = some path ∧
    err.errnoCode = some e ∧
    err.message ≠ "" ∧
    ((e = Errno.ENOENT ∨ e = Errno.ENOTDIR) → err.kind = .notFound) ∧
    ((e = Errno.EACCES ∨ e = Errno.EPERM) → err.kind = .permissionDenied) := by
  dsimp only [mapPathErrnoToSandboxError]
  have hdetail : s!"{ctx}: {Errno.name e}" ≠ "" := by
    intro h
    simp only [String.append_eq_empty_iff] at h
    exact absurd h.1.2 (by decide)
  have hneMsg : ∀ fb : String, (if s!"{ctx}: {Errno.name e}".isEmpty then fb else s!"{ctx}: {Errno.name e}") ≠ "" := by
    intro fb
    have hnot : (s!"{ctx}: {Errno.name e}").isEmpty = false := String.isEmpty_eq_false_iff.mpr hdetail
    simp [hnot, hdetail]
  split
  · next hnf =>
    refine ⟨rfl, rfl, hneMsg _, fun _ => rfl, ?_⟩
    intro hperm
    rcases Bool.or_eq_true _ _ |>.mp hnf with h1 | h2
    · have he := beq_iff_eq.mp h1; subst he; rcases hperm with h | h <;> cases h
    · have he := beq_iff_eq.mp h2; subst he; rcases hperm with h | h <;> cases h
  · next hnotnf =>
    split
    · next hperm =>
      refine ⟨rfl, rfl, hneMsg _, ?_, fun _ => rfl⟩
      intro hnf
      rcases hnf with rfl | rfl <;> simp [Errno.ENOENT, Errno.ENOTDIR] at hnotnf
    · next hnotperm =>
      refine ⟨rfl, rfl, hneMsg _, ?_, ?_⟩
      · intro hnf
        rcases hnf with rfl | rfl <;> simp [Errno.ENOENT, Errno.ENOTDIR] at hnotnf
      · intro hperm
        rcases hperm with rfl | rfl <;> simp [Errno.EACCES, Errno.EPERM] at hnotperm

/-- `buildProbeBwrapArgv` always enforces namespace isolation, `--clearenv`, `--remount-ro /`, and `--probe`. -/
theorem buildProbeBwrapArgv_contains_hardening {fd : Type} (bwrapPath : String)
    (sysEntries : Array PresetSystemEntry) (hasLdCache : Bool) (initFd : fd) :
    let argv := (buildProbeBwrapArgv bwrapPath sysEntries hasLdCache initFd).toList
    ArgToken.lit "--unshare-all" ∈ argv ∧
    ArgToken.lit "--as-pid-1" ∈ argv ∧
    ArgToken.lit "--die-with-parent" ∈ argv ∧
    ArgToken.lit "--clearenv" ∈ argv ∧
    ArgToken.lit "--remount-ro" ∈ argv ∧
    ArgToken.lit "--probe" ∈ argv ∧
    ArgToken.fdDecimal (.handle initFd) ∈ argv := by
  dsimp only [buildProbeBwrapArgv]
  have hfold : ∀ (es : List PresetSystemEntry) (acc : Array (ArgToken fd)) (t : ArgToken fd),
      t ∈ acc.toList →
      t ∈ (es.foldl (fun a e => match e with
        | .topSymlink lp tgt => a.push (.lit "--symlink") |>.push (.lit tgt) |>.push (.lit lp)
        | .readOnlyDir p => a.push (.lit "--ro-bind") |>.push (.lit p) |>.push (.lit p)) acc).toList := by
    intro es
    induction es with
    | nil => intro acc t ht; exact ht
    | cons e rest ih =>
      intro acc t ht
      simp only [List.foldl_cons]
      apply ih
      cases e <;> simp [Array.toList_push, ht]
  have hmemSys : ∀ t, t ∈ (#[ArgToken.lit bwrapPath, .lit "--unshare-all", .lit "--as-pid-1",
      .lit "--die-with-parent", .lit "--clearenv"] : Array (ArgToken fd)).toList →
      t ∈ (sysEntries.foldl (fun a e => match e with
        | .topSymlink lp tgt => a.push (.lit "--symlink") |>.push (.lit tgt) |>.push (.lit lp)
        | .readOnlyDir p => a.push (.lit "--ro-bind") |>.push (.lit p) |>.push (.lit p))
        #[.lit bwrapPath, .lit "--unshare-all", .lit "--as-pid-1", .lit "--die-with-parent", .lit "--clearenv"]).toList := by
    intro t ht
    rw [← Array.foldl_toList]
    exact hfold sysEntries.toList _ t ht
  have hmemLd : ∀ t, t ∈ (#[ArgToken.lit bwrapPath, .lit "--unshare-all", .lit "--as-pid-1",
      .lit "--die-with-parent", .lit "--clearenv"] : Array (ArgToken fd)).toList →
      t ∈ (if hasLdCache then
        (sysEntries.foldl (fun a e => match e with
          | .topSymlink lp tgt => a.push (.lit "--symlink") |>.push (.lit tgt) |>.push (.lit lp)
          | .readOnlyDir p => a.push (.lit "--ro-bind") |>.push (.lit p) |>.push (.lit p))
          #[.lit bwrapPath, .lit "--unshare-all", .lit "--as-pid-1", .lit "--die-with-parent", .lit "--clearenv"]).push (.lit "--ro-bind") |>.push (.lit "/etc/ld.so.cache") |>.push (.lit "/etc/ld.so.cache")
      else
        sysEntries.foldl (fun a e => match e with
          | .topSymlink lp tgt => a.push (.lit "--symlink") |>.push (.lit tgt) |>.push (.lit lp)
          | .readOnlyDir p => a.push (.lit "--ro-bind") |>.push (.lit p) |>.push (.lit p))
          #[.lit bwrapPath, .lit "--unshare-all", .lit "--as-pid-1", .lit "--die-with-parent", .lit "--clearenv"]).toList := by
    intro t ht
    cases hasLdCache
    · exact hmemSys t ht
    · simp [Array.toList_push, hmemSys t ht]
  rw [Array.toList_append]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact List.mem_append_left _ (hmemLd _ (by simp))
  · exact List.mem_append_left _ (hmemLd _ (by simp))
  · exact List.mem_append_left _ (hmemLd _ (by simp))
  · exact List.mem_append_left _ (hmemLd _ (by simp))
  · exact List.mem_append_right _ (by simp)
  · exact List.mem_append_right _ (by simp)
  · exact List.mem_append_right _ (by simp)

/-- `buildSpawnBwrapArgv` always passes `--remount-ro /`, `--plan-fd`, `--status-fd`, `--go-fd`, and exact `--ctrl-fd` (`"-1"` when `ctrlW? = none`, `.fdDecimal (.handle cw)` when `some cw`). -/
theorem buildSpawnBwrapArgv_trailer {fd : Type} (bwrapPath : String) (plan : CompiledSandboxPlan)
    (initFd hostsFd planFd statusW goR : fd) (ctrlW? : Option fd) :
    let argv := (buildSpawnBwrapArgv bwrapPath plan initFd hostsFd planFd statusW goR ctrlW?).toList
    ArgToken.lit "--remount-ro" ∈ argv ∧
    ArgToken.lit "--plan-fd" ∈ argv ∧
    ArgToken.fdDecimal (.handle planFd) ∈ argv ∧
    ArgToken.lit "--status-fd" ∈ argv ∧
    ArgToken.fdDecimal (.handle statusW) ∈ argv ∧
    ArgToken.lit "--go-fd" ∈ argv ∧
    ArgToken.fdDecimal (.handle goR) ∈ argv ∧
    ArgToken.lit "--ctrl-fd" ∈ argv ∧
    (match ctrlW? with
     | some cw => ArgToken.fdDecimal (.handle cw) ∈ argv
     | none => ArgToken.lit "-1" ∈ argv) := by
  dsimp only [buildSpawnBwrapArgv]
  rw [Array.toList_append]
  refine ⟨List.mem_append_right _ (by simp),
    List.mem_append_right _ (by simp),
    List.mem_append_right _ (by simp),
    List.mem_append_right _ (by simp),
    List.mem_append_right _ (by simp),
    List.mem_append_right _ (by simp),
    List.mem_append_right _ (by simp),
    List.mem_append_right _ (by simp), ?_⟩
  cases ctrlW? <;> exact List.mem_append_right _ (by simp)

/-- `isSafeAbsPathDir` guarantees that `s` starts with `"/"` and contains no NUL byte. -/
theorem isSafeAbsPathDir_startsWith_slash (s : String) (h : isSafeAbsPathDir s = true) :
    s.startsWith "/" = true ∧ !s.toList.contains '\x00' = true := by
  unfold isSafeAbsPathDir at h
  split at h
  · next rest hlist =>
    refine ⟨by simp [hlist], ?_⟩
    simp only [hlist, List.contains_cons, Bool.not_eq_true'] at h ⊢
    rw [h]
    decide
  · cases h

/-- Every directory returned by `absoluteBwrapPathDirs` is an absolute path (`d.startsWith "/" = true`) free of NUL bytes (never `""`, `"."`, or a relative path). -/
theorem absoluteBwrapPathDirs_all_abs (rawPath : ByteArray) (d : String)
    (h : d ∈ absoluteBwrapPathDirs rawPath) :
    d.startsWith "/" = true ∧ !d.toList.contains '\x00' = true := by
  unfold absoluteBwrapPathDirs filterAbsoluteBwrapDirs at h
  have hsafe : isSafeAbsPathDir d = true := (List.mem_filter.mp h).2
  exact isSafeAbsPathDir_startsWith_slash d hsafe

/-- `filterAbsoluteBwrapDirs` rejects empty/dot/relative/NUL-containing `PATH` entries across `":/usr/bin"`, `"/usr/bin:"`, `"/bin::/usr/bin"`, `".:/usr/bin"`, and `"rel/dir:/usr/bin"`, and `bwrapCandidatePath` normalizes `"/"` to `"/bwrap"`. -/
theorem filterAbsoluteBwrapDirs_examples :
    let splitPosixStr (p : String) : List String :=
      (LeanSwe.ProcessSandbox.Raw.SysBridge.Cgroup.splitChar ':' p.toList).map fun seg =>
        if seg.isEmpty then "." else String.ofList seg
    filterAbsoluteBwrapDirs (splitPosixStr ":/usr/bin") = ["/usr/bin"] ∧
    filterAbsoluteBwrapDirs (splitPosixStr "/usr/bin:") = ["/usr/bin"] ∧
    filterAbsoluteBwrapDirs (splitPosixStr "/bin::/usr/bin") = ["/bin", "/usr/bin"] ∧
    filterAbsoluteBwrapDirs (splitPosixStr ".:/usr/bin") = ["/usr/bin"] ∧
    filterAbsoluteBwrapDirs (splitPosixStr "rel/dir:/usr/bin") = ["/usr/bin"] ∧
    filterAbsoluteBwrapDirs ["", ".", "rel/dir", "/bad\x00dir", "/", "/usr/bin"] = ["/", "/usr/bin"] ∧
    bwrapCandidatePath "/" = "/bwrap" ∧
    bwrapCandidatePath "/usr/bin" = "/usr/bin/bwrap" := by
  decide

end LeanSwe.ProcessSandbox.Raw.Proofs.HostBwrap
