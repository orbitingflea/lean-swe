import LeanSweProofs.LinuxSyscall.Process.Proofs.ModelSoundnessWaitpid
import LeanSweProofs.LinuxSyscall.Process.Proofs.ModelSoundnessBasic
import LeanSweProofs.LinuxSyscall.Process.Proofs.ModelSoundnessKill
import LeanSweProofs.LinuxSyscall.Process.Proofs.ModelSoundnessPidfd

namespace LeanSwe.LinuxSyscall.Process

/-- Soundness of `execProcessReq modelOps` against `allowedStep` for every `ProcessReq`. -/
theorem modelOps_execProcessReq_sound (s : ProcessSysState) (req : ProcessReq) :
    let r := (execProcessReq modelOps req).run s
    allowedStep s req r.1 = some r.2 := by
  cases req with
  | getpid => exact modelOps_getpid_sound s
  | getuid => exact modelOps_getuid_sound s
  | pipe2 flags => exact modelOps_pipe2_sound s flags
  | waitpid pid flags => exact modelOps_waitpid_sound s pid flags
  | kill pidOrNegPgid sig => exact modelOps_kill_sound s pidOrNegPgid sig
  | pidfd_open pid flags => exact modelOps_pidfd_open_sound s pid flags
  | pidfd_send_signal hid sig flags => exact modelOps_pidfd_send_signal_sound s hid sig flags

end LeanSwe.LinuxSyscall.Process
