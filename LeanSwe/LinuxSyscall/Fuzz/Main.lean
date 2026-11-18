import LeanSwe.LinuxSyscall.Fuzz.SandboxFuzz

namespace LeanSwe.LinuxSyscall.Fuzz.Main

private structure CliArgs where
  suite : String := "sandbox"
  steps : Nat := 1000000
  seed : UInt64 := 0x517cc1b727220a95
  selfTestShrink : Bool := false

private def parseArgs : List String → Except String CliArgs
  | [] => .ok {}
  | "--suite" :: s :: rest => do
    let acc ← parseArgs rest
    return { acc with suite := s }
  | "--steps" :: nStr :: rest => do
    let acc ← parseArgs rest
    match nStr.toNat? with
    | some n => return { acc with steps := n }
    | none => .error s!"invalid --steps value: {nStr}"
  | "--seed" :: sStr :: rest => do
    let acc ← parseArgs rest
    match sStr.toNat? with
    | some n => return { acc with seed := UInt64.ofNat n }
    | none => .error s!"invalid --seed value: {sStr}"
  | "--self-test-shrink" :: rest => do
    let acc ← parseArgs rest
    return { acc with selfTestShrink := true }
  | other :: _ => .error s!"unknown argument: {other}"

/-- CLI entry point for `leanswe-world-fuzz`. -/
def main (args : List String) : IO UInt32 := do
  match parseArgs args with
  | .error msg =>
    IO.eprintln s!"leanswe-world-fuzz: {msg}"
    return 2
  | .ok cfg =>
    match cfg.suite with
    | "sandbox" =>
      SandboxFuzz.runFuzz {
        seed := cfg.seed
        steps := cfg.steps
        selfTestShrink := cfg.selfTestShrink
      }
    | other =>
      IO.eprintln s!"unknown fuzz suite: {other}"
      return 2

end LeanSwe.LinuxSyscall.Fuzz.Main
