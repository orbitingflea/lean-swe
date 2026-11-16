import LeanSwe

open LeanSwe

/-- Entrypoint running runtime tests for all `lean-swe` packages. -/
def main (args : List String) : IO UInt32 := do
  match args with
  | "--cmdline-probe" :: rest =>
    return (← CmdLine.RuntimeTests.probeMain rest)
  | "--slotpool-probe" :: rest =>
    return (← SlotPool.RuntimeTests.probeMain rest)
  | _ =>
    RegExp.RuntimeTests.runAll
    Glob.RuntimeTests.runAll
    Fs.Raw.RuntimeTests.runAll
    Fs.RuntimeTests.runAll
    Process.Raw.RuntimeTests.runAll
    Process.RuntimeTests.runAll
    Time.RuntimeTests.runAll
    Json.RuntimeTests.runAll
    EnvVars.Raw.RuntimeTests.runAll
    EnvVars.RuntimeTests.runAll
    Uuid.Raw.RuntimeTests.runAll
    Uuid.RuntimeTests.runAll
    Sqlite.Raw.RuntimeTests.runAll
    Sqlite.RuntimeTests.runAll
    Git.RuntimeTests.runAll
    CmdLine.RuntimeTests.runAll
    NumParse.RuntimeTests.runAll
    Toml.RuntimeTests.runAll
    TempDir.RuntimeTests.runAll
    Compress.RuntimeTests.runAll
    Base64.RuntimeTests.runAll
    CryptoHash.Raw.RuntimeTests.runAll
    CryptoHash.RuntimeTests.runAll
    Tar.RuntimeTests.runAll
    ProcessSandbox.Raw.RuntimeTests.runAll
    ProcessSandbox.RuntimeTests.runAll
    ConnectProxy.Raw.RuntimeTests.runAll
    ConnectProxy.RuntimeTests.runAll
    SlotPool.RuntimeTests.runAll
    match RegExp.findAll "[0-9]+" "a1b22" with
    | .ok xs =>
      if xs.map (·.matched) != #["1", "22"] then
        throw (IO.userError s!"unexpected RegExp.findAll result: {repr xs}")
    | .error e =>
      throw (IO.userError s!"unexpected RegExp.findAll error: {e.message}")
    IO.println "ALL_LEAN_SWE_TESTS_PASSED"
    return 0
