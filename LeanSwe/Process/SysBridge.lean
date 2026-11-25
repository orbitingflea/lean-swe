import LeanSwe.Process.SysBridge.ErrorAndEnv
import LeanSwe.Process.SysBridge.PathAndSpawn
import LeanSwe.Process.SysBridge.StreamIo
import LeanSwe.Process.SysBridge.WaitAndLifecycle

/-!
Capability-parameterized OS bridge for `LeanSwe.Process`, re-exporting error/environment
helpers, `PATH` resolution and `PostFork` child spawning, `ppoll`-driven pipe streaming,
and `waitpid` / process-group / `StateCellM` lifecycle operations.
-/
