import LeanSwe.PostFork.Types
import LeanSwe.PostFork.Impl

namespace LeanSwe.PostFork

open LeanSwe.LinuxSyscall
open LeanSwe.PostFork.Impl

@[extern "leanswe_postfork_spawn"]
private opaque rawSpawn :
    UInt32 →
    @& Option RawFd → UInt32 →
    @& Option RawFd → UInt32 →
    @& Option RawFd → UInt32 →
    @& Option String → @& String → @& Array String → @& Array ByteArray →
    BaseIO (Except RawSpawnErr Pid)

private def posixSpawnOps : RawSpawnOpsM IO RawFd where
  spawnRaw flags sIn sOut sErr cwd path argv envp :=
    let (inH, inR) := Internal.splitFdRef sIn
    let (outH, outR) := Internal.splitFdRef sOut
    let (errH, errR) := Internal.splitFdRef sErr
    liftM (rawSpawn flags inH inR.toUInt32 outH outR.toUInt32 errH errR.toUInt32 cwd path argv envp)

/-- Default `IO` capability bundle backed by `Internal.mkHostOps` and `postfork_shim.c`. -/
def defaultOps : PostForkOps :=
  Internal.mkHostOps posixSpawnOps

/-- Validate `spec`, fork, run post-`fork` child setup, verify `execve` via EOF, and return the live `SpawnedChild`. -/
@[inline] def spawn (spec : ChildSpec) : IO (Except PostForkError SpawnedChild) :=
  defaultOps.spawn spec

end LeanSwe.PostFork
