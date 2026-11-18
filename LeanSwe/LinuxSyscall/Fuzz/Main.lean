import LeanSwe.LinuxSyscall.Fuzz.SandboxFuzz

namespace LeanSwe.LinuxSyscall.Fuzz.Main

private structure CliArgs where
  suite : String := "sandbox"
  steps : Nat := 1000000
  seed : UInt64 := 0x517cc1b727220a95
  randomSeed : Bool := false
  selfTestShrink : Bool := false
  requireMemfdStrict : Bool := false

private def readUrandomU64 : IO UInt64 := do
  let h ← IO.FS.Handle.mk "/dev/urandom" .read
  let bs : ByteArray ← h.read 8
  if bs.size < 8 then
    let ns ← IO.monoNanosNow
    return UInt64.ofNat ns
  let mut acc : UInt64 := 0
  for i in List.range 8 do
    acc := acc ||| ((UInt64.ofNat (bs.get! i).toNat) <<< UInt64.ofNat (i * 8))
  return acc

private def parseArgs (args : List String) (acc : CliArgs := {}) : Except String CliArgs :=
  match args with
  | [] => .ok acc
  | ["--suite"] => .error "missing value for --suite"
  | "--suite" :: s :: rest => parseArgs rest { acc with suite := s }
  | ["--steps"] => .error "missing value for --steps"
  | "--steps" :: nStr :: rest =>
    match nStr.toNat? with
    | some n =>
      if n > 0 then
        parseArgs rest { acc with steps := n }
      else
        .error s!"invalid --steps value (must be >= 1): {nStr}"
    | none => .error s!"invalid --steps value: {nStr}"
  | ["--seed"] => .error "missing value for --seed"
  | "--seed" :: sStr :: rest =>
    match sStr.toNat? with
    | some n =>
      if n < UInt64.size then
        parseArgs rest { acc with seed := UInt64.ofNat n, randomSeed := false }
      else
        .error s!"--seed out of UInt64 range: {sStr}"
    | none => .error s!"invalid --seed value: {sStr}"
  | "--random-seed" :: rest => parseArgs rest { acc with randomSeed := true }
  | "--self-test-shrink" :: rest => parseArgs rest { acc with selfTestShrink := true }
  | "--require-memfd-strict" :: rest => parseArgs rest { acc with requireMemfdStrict := true }
  | other :: _ => .error s!"unknown argument: {other}"

/-- CLI entry point for `leanswe-world-fuzz`. -/
def main (args : List String) : IO UInt32 := do
  match parseArgs args with
  | .error msg =>
    IO.eprintln s!"leanswe-world-fuzz: {msg}"
    return 2
  | .ok cfg =>
    let effectiveSeed ← if cfg.randomSeed then
        let s ← readUrandomU64
        IO.println s!"SEED={s}"
        pure s
      else
        pure cfg.seed
    match cfg.suite with
    | "sandbox" =>
      SandboxFuzz.runFuzz {
        seed := effectiveSeed
        steps := cfg.steps
        selfTestShrink := cfg.selfTestShrink
        requireMemfdStrict := cfg.requireMemfdStrict
      }
    | other =>
      IO.eprintln s!"unknown fuzz suite: {other}"
      return 2

end LeanSwe.LinuxSyscall.Fuzz.Main
