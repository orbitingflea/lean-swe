import LeanSwe.LinuxSyscall.Fuzz.Main

/-- Top-level executable entry point delegating to `LeanSwe.LinuxSyscall.Fuzz.Main.main`. -/
def main (args : List String) : IO UInt32 :=
  LeanSwe.LinuxSyscall.Fuzz.Main.main args
