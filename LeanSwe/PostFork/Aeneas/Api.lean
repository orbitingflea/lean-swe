import LeanSwe.PostFork.Aeneas.Funs
import LeanSwe.PostFork.Aeneas.Model

namespace LeanSwe.PostFork.Aeneas

/-- Default `PostForkAeneasApi` backed by Charon/Aeneas-translated `postfork` wire constants and functions. -/
noncomputable def rustAeneasApi : Internal.PostForkAeneasApi where
  wireMagic := postfork.child.WIRE_MAGIC
  wireVersion := postfork.child.WIRE_VERSION
  stageValidate := postfork.child.STAGE_VALIDATE
  stageProcessGroup := postfork.child.STAGE_PROCESS_GROUP
  stageSignalReset := postfork.child.STAGE_SIGNAL_RESET
  stageFdSetup := postfork.child.STAGE_FD_SETUP
  stageCloseUnkept := postfork.child.STAGE_CLOSE_UNKEPT
  stageChdir := postfork.child.STAGE_CHDIR
  stageExecve := postfork.child.STAGE_EXECVE
  encodeFailureReport := postfork.child.encode_failure_report
  validateChildArgs := postfork.child.validate_child_args
  clearCloexec := postfork.fd_ops.clear_cloexec
  setCloexec := postfork.fd_ops.set_cloexec
  relocateRepAbove2 := postfork.fd_ops.relocate_rep_above2
  setupStdio := postfork.fd_ops.setup_stdio
  closeFdsAbove2Except := postfork.fd_ops.close_fds_above2_except
  parseDirentName := postfork.fd_ops.parse_dirent_name
  readSyncByte := postfork.child.read_sync_byte
  writeAll := postfork.child.write_all
  runChild := postfork.child.run_child

end LeanSwe.PostFork.Aeneas
