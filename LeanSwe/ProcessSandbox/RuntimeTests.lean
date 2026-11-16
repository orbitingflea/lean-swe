import LeanSwe.ProcessSandbox.Interface
import LeanSwe.ProcessSandbox.Raw.Interface
import LeanSwe.Process.Interface
import LeanSwe.Fs.Raw.Interface

namespace LeanSwe.ProcessSandbox.RuntimeTests

open LeanSwe.ProcessSandbox

private def assertTrue (cond : Bool) (msg : String) : IO Unit := do
  if !cond then
    throw (IO.userError s!"ASSERTION FAILED: {msg}")

private def assertOk {ε α : Type} [Repr ε] (res : Except ε α) (msg : String) : IO α := do
  match res with
  | .ok v => return v
  | .error e => throw (IO.userError s!"ASSERTION FAILED: {msg} (unexpected error: {repr e})")

private def assertErrKind {α : Type} (res : Except SandboxError α) (expected : SandboxErrorKind)
    (msg : String) : IO Unit := do
  match res with
  | .ok _ => throw (IO.userError s!"ASSERTION FAILED: {msg} (expected {repr expected}, got ok)")
  | .error e =>
    if e.kind != expected || e.message.isEmpty then
      throw (IO.userError s!"ASSERTION FAILED: {msg} (got {repr e}, expected {repr expected})")

private def isSystemRootPrefix (p : String) : Bool :=
  ["/usr/", "/bin/", "/sbin/", "/lib/", "/lib64/"].any (fun pre => p.startsWith pre)

private def probeCCode : String :=
  "#define _GNU_SOURCE\n" ++
  "#include <arpa/inet.h>\n" ++
  "#include <dirent.h>\n" ++
  "#include <errno.h>\n" ++
  "#include <fcntl.h>\n" ++
  "#include <netinet/in.h>\n" ++
  "#include <pthread.h>\n" ++
  "#include <sched.h>\n" ++
  "#include <signal.h>\n" ++
  "#include <stdint.h>\n" ++
  "#include <stdio.h>\n" ++
  "#include <stdlib.h>\n" ++
  "#include <string.h>\n" ++
  "#include <sys/file.h>\n" ++
  "#include <sys/ioctl.h>\n" ++
  "#include <sys/socket.h>\n" ++
  "#include <sys/syscall.h>\n" ++
  "#include <sys/wait.h>\n" ++
  "#include <termios.h>\n" ++
  "#include <unistd.h>\n" ++
  "#ifndef __NR_clone3\n" ++
  "#define __NR_clone3 435\n" ++
  "#endif\n" ++
  "#ifndef __NR_io_uring_setup\n" ++
  "#define __NR_io_uring_setup 425\n" ++
  "#endif\n" ++
  "static void *thr_fn(void *a) { (void)a; return (void *)(uintptr_t)42; }\n" ++
  "int main(int argc, char **argv) {\n" ++
  "  if (argc < 2) return 2;\n" ++
  "  if (strcmp(argv[1], \"--exit\") == 0) return atoi(argv[2]);\n" ++
  "  if (strcmp(argv[1], \"--pids1\") == 0) {\n" ++
  "    pid_t p = fork();\n" ++
  "    if (p == 0) _exit(0);\n" ++
  "    int err = (p < 0) ? errno : 0;\n" ++
  "    if (p > 0) waitpid(p, NULL, 0);\n" ++
  "    printf(\"fork_rc=%d errno=%d\\n\", p < 0 ? -1 : 0, err);\n" ++
  "    return (p < 0 && err == EAGAIN) ? 0 : 1;\n" ++
  "  }\n" ++
  "  if (strcmp(argv[1], \"--seccomp\") == 0) {\n" ++
  "    int sp1[2], sp2[2], sp3[2];\n" ++
  "    if (socketpair(AF_UNIX, SOCK_STREAM | SOCK_CLOEXEC, 0, sp1) != 0) return 10;\n" ++
  "    close(sp1[0]); close(sp1[1]);\n" ++
  "    if (socketpair(AF_UNIX, SOCK_SEQPACKET | SOCK_NONBLOCK, 0, sp2) != 0) return 11;\n" ++
  "    close(sp2[0]); close(sp2[1]);\n" ++
  "    if (socketpair(AF_UNIX, SOCK_DGRAM, 0, sp3) == 0 || errno != EPERM) return 12;\n" ++
  "    if (socket(AF_UNIX, SOCK_STREAM, 0) >= 0 || errno != EPERM) return 13;\n" ++
  "    pthread_t th;\n" ++
  "    void *ret = NULL;\n" ++
  "    if (pthread_create(&th, NULL, thr_fn, NULL) != 0) return 14;\n" ++
  "    pthread_join(th, &ret);\n" ++
  "    if ((uintptr_t)ret != 42) return 15;\n" ++
  "    if (unshare(CLONE_NEWUSER) == 0 || errno != EPERM) return 16;\n" ++
  "    long c3 = syscall(__NR_clone3, NULL, 0);\n" ++
  "    if (c3 >= 0 || errno != ENOSYS) return 17;\n" ++
  "    if (syscall(__NR_io_uring_setup, 16, NULL) >= 0 || errno != EPERM) return 18;\n" ++
  "    if (syscall(__NR_bpf, 0, NULL, 0) >= 0 || errno != EPERM) return 19;\n" ++
  "    if (syscall(__NR_reboot, 0, 0, 0, 0) >= 0 || errno != EPERM) return 20;\n" ++
  "    DIR *fdd = opendir(\"/proc/self/fd\");\n" ++
  "    if (fdd == NULL) return 26;\n" ++
  "    int fdd_fd = dirfd(fdd);\n" ++
  "    struct dirent *de;\n" ++
  "    while ((de = readdir(fdd)) != NULL) {\n" ++
  "      if (de->d_name[0] >= '0' && de->d_name[0] <= '9') {\n" ++
  "        int fd = atoi(de->d_name);\n" ++
  "        if (fd > 2 && fd != fdd_fd) { closedir(fdd); return 27; }\n" ++
  "      }\n" ++
  "    }\n" ++
  "    closedir(fdd);\n" ++
  "    int ifd = open(\"/etc/.leanswe-psandbox-init\", O_RDONLY);\n" ++
  "    if (ifd >= 0 || errno != EACCES) return 21;\n" ++
  "    errno = 0;\n" ++
  "    if (syscall(__NR_clone, (unsigned long)(0x10000000UL | SIGCHLD), NULL, NULL, NULL, 0) >= 0 || errno != EPERM) return 22;\n" ++
  "    errno = 0;\n" ++
  "    if (syscall(__NR_clone, (unsigned long)0x80UL, NULL, NULL, NULL, 0) >= 0 || errno == EPERM) return 23;\n" ++
  "    int ptmx = open(\"/dev/ptmx\", O_RDWR);\n" ++
  "    if (ptmx < 0) return 24;\n" ++
  "    int ptyn = -1;\n" ++
  "    if (ioctl(ptmx, TIOCGPTN, &ptyn) != 0) { close(ptmx); return 25; }\n" ++
  "    close(ptmx);\n" ++
  "    printf(\"SECCOMP_ALL_OK\\n\");\n" ++
  "    return 0;\n" ++
  "  }\n" ++
  "  if (strcmp(argv[1], \"--mem2\") == 0) {\n" ++
  "    pid_t c = fork();\n" ++
  "    size_t sz = 16U * 1024U * 1024U;\n" ++
  "    char *buf = (char *)malloc(sz);\n" ++
  "    if (buf != NULL) {\n" ++
  "      for (size_t i = 0; i < sz; i += 4096) buf[i] = 1;\n" ++
  "    }\n" ++
  "    if (c == 0) { sleep(5); _exit(0); }\n" ++
  "    int st = 0; waitpid(c, &st, 0);\n" ++
  "    return 0;\n" ++
  "  }\n" ++
  "  if (strcmp(argv[1], \"--mem-child\") == 0) {\n" ++
  "    size_t psz = 4U * 1024U * 1024U;\n" ++
  "    volatile char *pbuf = (volatile char *)malloc(psz);\n" ++
  "    if (pbuf == NULL) return 1;\n" ++
  "    for (size_t i = 0; i < psz; i += 4096) pbuf[i] = 1;\n" ++
  "    pid_t c = fork();\n" ++
  "    if (c < 0) return 1;\n" ++
  "    if (c == 0) {\n" ++
  "      size_t csz = 18U * 1024U * 1024U;\n" ++
  "      volatile char *cbuf = (volatile char *)malloc(csz);\n" ++
  "      if (cbuf == NULL) _exit(1);\n" ++
  "      for (size_t i = 0; i < csz; i += 4096) cbuf[i] = 1;\n" ++
  "      sleep(5);\n" ++
  "      _exit(0);\n" ++
  "    }\n" ++
  "    int st = 0; waitpid(c, &st, 0);\n" ++
  "    return pbuf[0] - 1;\n" ++
  "  }\n" ++
  "  if (strcmp(argv[1], \"--tcp-connect\") == 0) {\n" ++
  "    int port = atoi(argv[2]);\n" ++
  "    int half_close = (argc > 3 && strcmp(argv[3], \"--half-close\") == 0);\n" ++
  "    int s = socket(AF_INET, SOCK_STREAM, 0);\n" ++
  "    if (s < 0) return 30;\n" ++
  "    struct sockaddr_in sa;\n" ++
  "    memset(&sa, 0, sizeof(sa));\n" ++
  "    sa.sin_family = AF_INET;\n" ++
  "    sa.sin_addr.s_addr = htonl(INADDR_LOOPBACK);\n" ++
  "    sa.sin_port = htons((uint16_t)port);\n" ++
  "    if (connect(s, (struct sockaddr *)&sa, sizeof(sa)) != 0) {\n" ++
  "      printf(\"connect_errno=%d\\n\", errno);\n" ++
  "      close(s);\n" ++
  "      return 31;\n" ++
  "    }\n" ++
  "    if (half_close) {\n" ++
  "      const char *req = \"PING\";\n" ++
  "      if (send(s, req, 4, 0) != 4) return 32;\n" ++
  "      if (shutdown(s, SHUT_WR) != 0) return 33;\n" ++
  "      char rbuf[64]; ssize_t n = recv(s, rbuf, sizeof(rbuf) - 1, 0);\n" ++
  "      if (n <= 0) return 34;\n" ++
  "      rbuf[n] = '\\0';\n" ++
  "      printf(\"%s\\n\", rbuf);\n" ++
  "    }\n" ++
  "    close(s);\n" ++
  "    return 0;\n" ++
  "  }\n" ++
  "  if (strcmp(argv[1], \"--tcp-ring\") == 0) {\n" ++
  "    int port = atoi(argv[2]);\n" ++
  "    int s = socket(AF_INET, SOCK_STREAM, 0);\n" ++
  "    if (s < 0) return 35;\n" ++
  "    struct sockaddr_in sa;\n" ++
  "    memset(&sa, 0, sizeof(sa));\n" ++
  "    sa.sin_family = AF_INET;\n" ++
  "    sa.sin_addr.s_addr = htonl(INADDR_LOOPBACK);\n" ++
  "    sa.sin_port = htons((uint16_t)port);\n" ++
  "    if (connect(s, (struct sockaddr *)&sa, sizeof(sa)) != 0) return 36;\n" ++
  "    size_t total = 65536;\n" ++
  "    uint8_t *buf = (uint8_t *)malloc(total);\n" ++
  "    for (size_t i = 0; i < total; i++) buf[i] = (uint8_t)(i & 0xff);\n" ++
  "    size_t off = 0;\n" ++
  "    while (off < total) {\n" ++
  "      ssize_t w = send(s, buf + off, total - off, 0);\n" ++
  "      if (w <= 0) return 37;\n" ++
  "      off += (size_t)w;\n" ++
  "    }\n" ++
  "    if (shutdown(s, SHUT_WR) != 0) return 38;\n" ++
  "    size_t got = 0;\n" ++
  "    uint8_t *rb = (uint8_t *)malloc(total);\n" ++
  "    while (got < total) {\n" ++
  "      ssize_t r = recv(s, rb + got, total - got, 0);\n" ++
  "      if (r <= 0) break;\n" ++
  "      got += (size_t)r;\n" ++
  "    }\n" ++
  "    int ok = (got == total && memcmp(buf, rb, total) == 0);\n" ++
  "    free(buf); free(rb); close(s);\n" ++
  "    if (!ok) return 39;\n" ++
  "    printf(\"RING_64K_OK\\n\");\n" ++
  "    return 0;\n" ++
  "  }\n" ++
  "  if (strcmp(argv[1], \"--tcp-burst\") == 0) {\n" ++
  "    int port = atoi(argv[2]);\n" ++
  "    int fds[140];\n" ++
  "    struct sockaddr_in sa;\n" ++
  "    memset(&sa, 0, sizeof(sa));\n" ++
  "    sa.sin_family = AF_INET;\n" ++
  "    sa.sin_addr.s_addr = htonl(INADDR_LOOPBACK);\n" ++
  "    sa.sin_port = htons((uint16_t)port);\n" ++
  "    for (int i = 0; i < 140; i++) {\n" ++
  "      fds[i] = socket(AF_INET, SOCK_STREAM, 0);\n" ++
  "      if (fds[i] < 0 || connect(fds[i], (struct sockaddr *)&sa, sizeof(sa)) != 0) return 60;\n" ++
  "      if (send(fds[i], \"B\", 1, 0) != 1 || shutdown(fds[i], SHUT_WR) != 0) return 61;\n" ++
  "    }\n" ++
  "    for (int i = 0; i < 140; i++) {\n" ++
  "      char ch = 0;\n" ++
  "      if (recv(fds[i], &ch, 1, 0) != 1 || ch != 'B') return 62;\n" ++
  "      close(fds[i]);\n" ++
  "    }\n" ++
  "    printf(\"BURST_140_OK\\n\");\n" ++
  "    return 0;\n" ++
  "  }\n" ++
  "  if (strcmp(argv[1], \"--tcp-half-rst\") == 0) {\n" ++
  "    int port = atoi(argv[2]);\n" ++
  "    struct sockaddr_in sa;\n" ++
  "    memset(&sa, 0, sizeof(sa));\n" ++
  "    sa.sin_family = AF_INET;\n" ++
  "    sa.sin_addr.s_addr = htonl(INADDR_LOOPBACK);\n" ++
  "    sa.sin_port = htons((uint16_t)port);\n" ++
  "    int s1 = socket(AF_INET, SOCK_STREAM, 0);\n" ++
  "    if (s1 < 0 || connect(s1, (struct sockaddr *)&sa, sizeof(sa)) != 0) return 63;\n" ++
  "    if (send(s1, \"DELAY\", 5, 0) != 5 || shutdown(s1, SHUT_WR) != 0) return 64;\n" ++
  "    usleep(15000);\n" ++
  "    struct linger lg = {1, 0};\n" ++
  "    setsockopt(s1, SOL_SOCKET, SO_LINGER, &lg, sizeof(lg));\n" ++
  "    close(s1);\n" ++
  "    usleep(120000);\n" ++
  "    int s2 = socket(AF_INET, SOCK_STREAM, 0);\n" ++
  "    if (s2 < 0 || connect(s2, (struct sockaddr *)&sa, sizeof(sa)) != 0) return 65;\n" ++
  "    if (send(s2, \"OK\", 2, 0) != 2 || shutdown(s2, SHUT_WR) != 0) return 66;\n" ++
  "    char buf[8]; memset(buf, 0, sizeof(buf));\n" ++
  "    if (recv(s2, buf, 2, 0) != 2 || memcmp(buf, \"OK\", 2) != 0) return 67;\n" ++
  "    close(s2);\n" ++
  "    printf(\"HALF_RST_OK\\n\");\n" ++
  "    return 0;\n" ++
  "  }\n" ++
  "  if (strcmp(argv[1], \"--tcp-loopback-self\") == 0) {\n" ++
  "    int ls = socket(AF_INET, SOCK_STREAM, 0);\n" ++
  "    struct sockaddr_in sa;\n" ++
  "    memset(&sa, 0, sizeof(sa));\n" ++
  "    sa.sin_family = AF_INET;\n" ++
  "    sa.sin_addr.s_addr = htonl(INADDR_LOOPBACK);\n" ++
  "    sa.sin_port = htons(18777);\n" ++
  "    if (bind(ls, (struct sockaddr *)&sa, sizeof(sa)) != 0) { printf(\"bind_errno=%d\\n\", errno); return 40; }\n" ++
  "    if (listen(ls, 4) != 0) return 41;\n" ++
  "    int cs = socket(AF_INET, SOCK_STREAM, 0);\n" ++
  "    if (connect(cs, (struct sockaddr *)&sa, sizeof(sa)) != 0) return 42;\n" ++
  "    int afd = accept(ls, NULL, NULL);\n" ++
  "    if (afd < 0) return 43;\n" ++
  "    write(cs, \"LO\", 2); char b[8]; ssize_t rn = read(afd, b, 2);\n" ++
  "    close(afd); close(cs); close(ls);\n" ++
  "    if (rn != 2 || memcmp(b, \"LO\", 2) != 0) return 44;\n" ++
  "    printf(\"BOX_LO_OK\\n\");\n" ++
  "    return 0;\n" ++
  "  }\n" ++
  "  if (strcmp(argv[1], \"--double-fork-flock\") == 0) {\n" ++
  "    const char *path = argv[2];\n" ++
  "    int pfd[2]; if (pipe(pfd) != 0) return 50;\n" ++
  "    pid_t c = fork();\n" ++
  "    if (c == 0) {\n" ++
  "      pid_t gc = fork();\n" ++
  "      if (gc == 0) {\n" ++
  "        close(pfd[0]);\n" ++
  "        int fd = open(path, O_CREAT | O_RDWR, 0644);\n" ++
  "        if (fd < 0) _exit(51);\n" ++
  "        if (flock(fd, LOCK_EX) != 0) _exit(52);\n" ++
  "        write(pfd[1], \"L\", 1);\n" ++
  "        close(pfd[1]);\n" ++
  "        sleep(60);\n" ++
  "        _exit(0);\n" ++
  "      }\n" ++
  "      _exit(0);\n" ++
  "    }\n" ++
  "    close(pfd[1]);\n" ++
  "    char ch = 0; read(pfd[0], &ch, 1); close(pfd[0]);\n" ++
  "    waitpid(c, NULL, 0);\n" ++
  "    printf(\"PARENT_EXITED\\n\");\n" ++
  "    return 0;\n" ++
  "  }\n" ++
  "  return 2;\n" ++
  "}\n"

private def halfCloseServerPy : String :=
  "import socket, sys\n" ++
  "s = socket.socket()\n" ++
  "s.settimeout(15.0)\n" ++
  "s.bind(('127.0.0.1', 0))\n" ++
  "s.listen(4)\n" ++
  "print(s.getsockname()[1], flush=True)\n" ++
  "c, _ = s.accept()\n" ++
  "chunks = []\n" ++
  "while True:\n" ++
  "    d = c.recv(1024)\n" ++
  "    if not d:\n" ++
  "        break\n" ++
  "    chunks.append(d)\n" ++
  "assert b''.join(chunks) == b'PING', chunks\n" ++
  "c.sendall(b'HALF_CLOSE_OK')\n" ++
  "c.close()\n" ++
  "s.close()\n"

private def silentListenerPy : String :=
  "import socket, sys, time\n" ++
  "s = socket.socket()\n" ++
  "s.bind(('127.0.0.1', 0))\n" ++
  "s.listen(4)\n" ++
  "print(s.getsockname()[1], flush=True)\n" ++
  "time.sleep(10)\n"

private def echoHalfCloseServerPy : String :=
  "import socket, threading, time\n" ++
  "s = socket.socket()\n" ++
  "s.bind(('127.0.0.1', 0))\n" ++
  "s.listen(256)\n" ++
  "print(s.getsockname()[1], flush=True)\n" ++
  "def handle(c):\n" ++
  "    bufs = []\n" ++
  "    while True:\n" ++
  "        d = c.recv(65536)\n" ++
  "        if not d: break\n" ++
  "        bufs.append(d)\n" ++
  "    payload = b''.join(bufs)\n" ++
  "    if payload == b'DELAY':\n" ++
  "        time.sleep(0.08)\n" ++
  "    try:\n" ++
  "        c.sendall(payload)\n" ++
  "    except OSError:\n" ++
  "        pass\n" ++
  "    c.close()\n" ++
  "while True:\n" ++
  "    try:\n" ++
  "        c, _ = s.accept()\n" ++
  "        threading.Thread(target=handle, args=(c,), daemon=True).start()\n" ++
  "    except OSError:\n" ++
  "        break\n"

private def findDelegatedCgroupParentDir : IO (Option String) := do
  let raw ← IO.FS.readFile "/proc/self/cgroup"
  for line in raw.splitOn "\n" do
    if line.startsWith "0::" then
      let rel := (line.drop 3).toString
      let parent := (System.FilePath.mk ("/sys/fs/cgroup" ++ rel)).parent
      return parent.map (·.toString)
  return none

private def countLeftoverCgroups (parent? : Option String) : IO Nat := do
  match parent? with
  | none => return 0
  | some p =>
    let entries ← System.FilePath.readDir p
    return entries.foldl (fun acc e => if e.fileName.startsWith "leanswe-psandbox-" then acc + 1 else acc) 0

/-- Execute end-to-end OS runtime verification tests for `LeanSwe.ProcessSandbox`. -/
def runAll : IO Unit := do
  let baseCounts ← ProcessSandbox.Raw.activeResourceCounts
  assertTrue (baseCounts == { openPlans := 0, activeBoxes := 0, activeForwarders := 0 })
    "initial ProcessSandbox activeResourceCounts == 0"

  assertErrKind (ProcessSandbox.validateSpec { program := "" }) .invalidInput "empty program"
  assertErrKind (ProcessSandbox.validateSpec { program := "a\x00b" }) .invalidInput "NUL program"
  assertErrKind (ProcessSandbox.validateSpec { program := "sh", args := #["x\x00y"] }) .invalidInput "NUL arg"
  assertErrKind (ProcessSandbox.validateSpec { program := "sh", cwd := some "rel/dir" }) .invalidInput "relative cwd"
  assertErrKind (ProcessSandbox.validateSpec { program := "sh", mounts := #[.scratch "/usr/bad"] }) .invalidInput "reserved /usr"
  assertErrKind (ProcessSandbox.validateSpec { program := "sh", mounts := #[.scratch "/"] }) .invalidInput "reserved /"
  assertErrKind (ProcessSandbox.validateSpec { program := "sh", mounts := #[.scratch "/work", .scratch "/work/"] }) .invalidInput "dup boxPath"
  assertErrKind (ProcessSandbox.validateSpec { program := "sh", portForwards := #[{ boxPort := 0, hostPort := 80 }] }) .invalidInput "port 0"
  assertErrKind (ProcessSandbox.validateSpec { program := "sh", limits := { timeoutMs := 0 } }) .invalidInput "timeoutMs 0"
  assertErrKind (ProcessSandbox.validateSpec { program := "sh", limits := { memoryMaxBytes := some 0 } }) .invalidInput "memoryMaxBytes 0"
  assertErrKind (ProcessSandbox.validateSpec { program := "sh", limits := { pidsMax := some 0 } }) .invalidInput "pidsMax 0"
  assertErrKind (ProcessSandbox.validateSpec { program := "sh", env := #[("A=B", "1")] }) .invalidInput "env key ="

  let avail ← ProcessSandbox.isAvailable
  if !avail then
    assertErrKind (← ProcessSandbox.run { program := "/bin/true" }) .unavailable
      "ProcessSandbox.run fails closed .unavailable when unavailable"
    assertTrue ((← ProcessSandbox.Raw.activeResourceCounts) == baseCounts)
      "unavailable run leaves zero leaked resources"
    IO.println "SKIP: LeanSwe.ProcessSandbox Linux runtime tests (isAvailable = false)"
    return

  let cgParent ← findDelegatedCgroupParentDir
  let cgBefore ← countLeftoverCgroups cgParent

  let tmpDir ← IO.FS.createTempDir
  try
    let probeSrc := tmpDir / "probe.c"
    let probeBin := tmpDir / "probe"
    IO.FS.writeFile probeSrc probeCCode
    let ccRes ← LeanSwe.Process.runCommandChecked "cc"
      #["-O2", "-Wall", "-Wextra", "-Werror", "-pthread", probeSrc.toString, "-o", probeBin.toString]
    let _ ← match ccRes with
      | .ok r => pure r
      | .error e => throw (IO.userError s!"failed to compile sandbox test probe: {e.message}")

    let emptyRootRes ← assertOk (← ProcessSandbox.run {
      program := "/bin/sh"
      args := #["-c",
        "test ! -e /home || exit 11; pwd; cat /etc/hosts; ls / >/dev/null || exit 12; touch /etc/evil 2>/dev/null && exit 13; touch /tmp/ephem.txt && echo OK"]
    }) "empty root, ! -e /home, default /tmp, cwd=/tmp, RO /etc"
    assertTrue (emptyRootRes.outcome == .exited 0) "empty root script exited 0"
    let emptyOut := String.fromUTF8! emptyRootRes.stdout
    assertTrue (emptyOut == "/tmp\n127.0.0.1 localhost\n::1 localhost\nOK\n")
      s!"empty root output mismatch: {repr emptyOut}"

    let ephemCheck ← assertOk (← ProcessSandbox.run {
      program := "/bin/sh"
      args := #["-c", "test ! -e /tmp/ephem.txt && echo CLEAN"]
    }) "scratch /tmp ephemeral across runs"
    assertTrue (ephemCheck.outcome == .exited 0 && String.fromUTF8! ephemCheck.stdout == "CLEAN\n")
      "scratch /tmp does not persist across runs"

    match ← IO.getEnv "HOME" with
    | some h =>
      if isSystemRootPrefix h then
        if ← System.FilePath.isDir h then
          let maskRes ← assertOk (← ProcessSandbox.run {
            program := "/bin/sh"
            args := #["-c", "ls \"$1\" >/dev/null 2>&1; echo rc=$?", "sh", h]
          }) "masked system-nested HOME"
          assertTrue (maskRes.outcome == .exited 0 &&
            (String.fromUTF8! maskRes.stdout).trimAscii.toString != "rc=0")
            "masked nested $HOME denies opendir"
    | none => pure ()

    let customTmpHost := tmpDir / "custom_tmp"
    IO.FS.createDirAll customTmpHost
    let tmpOverrideRes ← assertOk (← ProcessSandbox.run {
      program := "/bin/sh"
      args := #["-c", "printf 'override' > /tmp/saved.txt"]
      mounts := #[.readWrite customTmpHost.toString "/tmp"]
    }) "custom /tmp override"
    assertTrue (tmpOverrideRes.outcome == .exited 0) "custom /tmp override exited 0"
    assertTrue ((← IO.FS.readFile (customTmpHost / "saved.txt")) == "override")
      "custom /tmp override persisted on host"

    let roDir := tmpDir / "ro"
    let rwDir := tmpDir / "rw"
    let nestedRo := rwDir / "ro_sub"
    IO.FS.createDirAll roDir
    IO.FS.createDirAll nestedRo
    IO.FS.writeFile (roDir / "hello.txt") "ro_val"
    IO.FS.writeFile (nestedRo / "locked.txt") "sub_val"
    let mountRes ← assertOk (← ProcessSandbox.run {
      program := "/bin/sh"
      args := #["-c",
        "cat /ro/hello.txt; touch /ro/fail 2>/dev/null && exit 21; cat /rw/ro_sub/locked.txt; touch /rw/ro_sub/fail 2>/dev/null && exit 22; printf 'rw_ok' > /rw/out.txt; printf 'scr_ok' > /scr/f.txt && cat /scr/f.txt"]
      mounts :=
        #[ .readOnly roDir.toString "/ro"
         , .readWrite rwDir.toString "/rw"
         , .readOnly nestedRo.toString "/rw/ro_sub"
         , .scratch "/scr" ]
    }) "readOnly vs readWrite vs scratch and nested mounts"
    assertTrue (mountRes.outcome == .exited 0 &&
      String.fromUTF8! mountRes.stdout == "ro_valsub_valscr_ok") "mount read/write semantics"
    assertTrue ((← IO.FS.readFile (rwDir / "out.txt")) == "rw_ok") "readWrite wrote host file"

    let singleFile := tmpDir / "single.txt"
    IO.FS.writeFile singleFile "single_file_content"
    let fileMountRes ← assertOk (← ProcessSandbox.run {
      program := "/bin/cat"
      args := #["/data/single.txt"]
      mounts := #[.readOnly singleFile.toString "/data/single.txt"]
    }) "single file Landlock !S_ISDIR mount"
    assertTrue (fileMountRes.outcome == .exited 0 &&
      String.fromUTF8! fileMountRes.stdout == "single_file_content") "single file mount readable"

    let seccompRes ← assertOk (← ProcessSandbox.run {
      program := "/box/probe"
      args := #["--seccomp"]
      mounts := #[.readOnly probeBin.toString "/box/probe"]
    }) "seccomp + clone3 ENOSYS + pthread_create + socketpair vs socket(AF_UNIX) + Landlock init mask"
    assertTrue (seccompRes.outcome == .exited 0 &&
      String.fromUTF8! seccompRes.stdout == "SECCOMP_ALL_OK\n")
      s!"seccomp probe outcome: {repr seccompRes.outcome} err={String.fromUTF8! seccompRes.stderr}"

    let envDefaultRes ← assertOk (← ProcessSandbox.run { program := "/usr/bin/env" }) "clean env default PATH"
    assertTrue (envDefaultRes.outcome == .exited 0 &&
      (String.fromUTF8! envDefaultRes.stdout).trimAscii.toString == "PATH=/usr/bin:/bin")
      "clean env inherits zero host vars and injects default PATH"

    let envCustomRes ← assertOk (← ProcessSandbox.run {
      program := "/usr/bin/env"
      env := #[("K", "old"), ("K", "new"), ("PATH", "/bin:/usr/bin")]
    }) "clean env last-write-wins"
    let envCustomOut := String.fromUTF8! envCustomRes.stdout
    assertTrue (envCustomRes.outcome == .exited 0 &&
      (envCustomOut == "PATH=/bin:/usr/bin\nK=new\n" || envCustomOut == "K=new\nPATH=/bin:/usr/bin\n"))
      s!"custom env output: {repr envCustomOut}"

    let privProc ← IO.Process.spawn {
      cmd := "python3"
      args := #["-c", silentListenerPy]
      stdout := .piped
      stderr := .null
    }
    let privPort : UInt16 ← try
      let line ← privProc.stdout.getLine
      match line.trimAscii.toString.toNat? with
      | some n => pure (UInt16.ofNat n)
      | none => throw (IO.userError s!"invalid port line: {repr line}")
    catch err =>
      let _ ← privProc.kill
      let _ ← privProc.wait
      throw err
    try
      let blockedNetRes ← assertOk (← ProcessSandbox.run {
        program := "/box/probe"
        args := #["--tcp-connect", toString privPort.toNat]
        mounts := #[.readOnly probeBin.toString "/box/probe"]
        allowBoxLocalhost := false
      }) "allowBoxLocalhost=false blocks TCP connect to unforwarded host port"
      assertTrue (blockedNetRes.outcome == .exited 31 &&
        (String.fromUTF8! blockedNetRes.stdout).trimAscii.toString == "connect_errno=13")
        s!"Landlock blocks connect with EACCES: {String.fromUTF8! blockedNetRes.stdout}"

      let isoLoRes ← assertOk (← ProcessSandbox.run {
        program := "/box/probe"
        args := #["--tcp-connect", toString privPort.toNat]
        mounts := #[.readOnly probeBin.toString "/box/probe"]
        allowBoxLocalhost := true
      }) "allowBoxLocalhost=true cannot reach host 127.0.0.1"
      assertTrue (isoLoRes.outcome == .exited 31 &&
        (String.fromUTF8! isoLoRes.stdout).trimAscii.toString == "connect_errno=111")
        s!"isolated netns ECONNREFUSED on host loopback: {String.fromUTF8! isoLoRes.stdout}"
    finally
      let _ ← privProc.kill
      let _ ← privProc.wait

    let selfLoRes ← assertOk (← ProcessSandbox.run {
      program := "/box/probe"
      args := #["--tcp-loopback-self"]
      mounts := #[.readOnly probeBin.toString "/box/probe"]
      allowBoxLocalhost := true
    }) "allowBoxLocalhost=true permits bind and connect inside box 127.0.0.1"
    assertTrue (selfLoRes.outcome == .exited 0 &&
      String.fromUTF8! selfLoRes.stdout == "BOX_LO_OK\n") "box self loopback ok"

    let halfProc ← IO.Process.spawn {
      cmd := "python3"
      args := #["-c", halfCloseServerPy]
      stdout := .piped
      stderr := .piped
    }
    let halfHostPort : UInt16 ← try
      let line ← halfProc.stdout.getLine
      match line.trimAscii.toString.toNat? with
      | some n => pure (UInt16.ofNat n)
      | none => throw (IO.userError s!"invalid half-close port: {repr line}")
    catch err =>
      let _ ← halfProc.kill
      let _ ← halfProc.wait
      throw err
    try
      let fwdRes ← assertOk (← ProcessSandbox.run {
        program := "/box/probe"
        args := #["--tcp-connect", "19201", "--half-close"]
        mounts := #[.readOnly probeBin.toString "/box/probe"]
        allowBoxLocalhost := false
        portForwards := #[{ boxPort := 19201, hostPort := halfHostPort }]
      }) "portForwards directional SHUT_WR half-close roundtrip"
      assertTrue (fwdRes.outcome == .exited 0 &&
        String.fromUTF8! fwdRes.stdout == "HALF_CLOSE_OK\n")
        s!"portForwards half-close failed: {repr fwdRes.outcome} out={String.fromUTF8! fwdRes.stdout} err={String.fromUTF8! fwdRes.stderr}"
    catch err =>
      let _ ← halfProc.kill
      let _ ← halfProc.wait
      throw err
    let _ ← halfProc.wait

    let echoProc ← IO.Process.spawn {
      cmd := "python3"
      args := #["-c", echoHalfCloseServerPy]
      stdout := .piped
      stderr := .null
    }
    let echoHostPort : UInt16 ← try
      let line ← echoProc.stdout.getLine
      match line.trimAscii.toString.toNat? with
      | some n => pure (UInt16.ofNat n)
      | none => throw (IO.userError s!"invalid echo port: {repr line}")
    catch err =>
      let _ ← echoProc.kill
      let _ ← echoProc.wait
      throw err
    try
      let ringRes ← assertOk (← ProcessSandbox.run {
        program := "/box/probe"
        args := #["--tcp-ring", "19202"]
        mounts := #[.readOnly probeBin.toString "/box/probe"]
        portForwards := #[{ boxPort := 19202, hostPort := echoHostPort }]
      }) "64 KiB ring buffer half-close roundtrip"
      assertTrue (ringRes.outcome == .exited 0 &&
        String.fromUTF8! ringRes.stdout == "RING_64K_OK\n")
        s!"64 KiB ring test failed: {repr ringRes.outcome}"

      let burstRes ← assertOk (← ProcessSandbox.run {
        program := "/box/probe"
        args := #["--tcp-burst", "19203"]
        mounts := #[.readOnly probeBin.toString "/box/probe"]
        portForwards := #[{ boxPort := 19203, hostPort := echoHostPort }]
      }) "140-connection burst over MAX_RELAY_SLOTS = 128"
      assertTrue (burstRes.outcome == .exited 0 &&
        String.fromUTF8! burstRes.stdout == "BURST_140_OK\n")
        s!"burst test failed: {repr burstRes.outcome}"

      let rstRes ← assertOk (← ProcessSandbox.run {
        program := "/box/probe"
        args := #["--tcp-half-rst", "19204"]
        mounts := #[.readOnly probeBin.toString "/box/probe"]
        portForwards := #[{ boxPort := 19204, hostPort := echoHostPort }]
      }) "half-close followed by RST while peer holds open"
      assertTrue (rstRes.outcome == .exited 0 &&
        String.fromUTF8! rstRes.stdout == "HALF_RST_OK\n")
        s!"half-close RST test failed: {repr rstRes.outcome}"

      let fwdTasks ← (List.range 4).mapM fun idx => IO.asTask do
        ProcessSandbox.run {
          program := "/box/probe"
          args := #["--tcp-ring", toString (19210 + idx)]
          mounts := #[.readOnly probeBin.toString "/box/probe"]
          portForwards := #[{ boxPort := UInt16.ofNat (19210 + idx), hostPort := echoHostPort }]
          limits := { timeoutMs := 15_000 }
        }
      for (idx, t) in (List.range 4).zip fwdTasks do
        let tr := t.get
        match tr with
        | .error ioErr => throw (IO.userError s!"concurrent fwd task {idx} threw IO error: {ioErr}")
        | .ok r =>
          let okR ← assertOk r s!"concurrent fwd task {idx}"
          assertTrue (okR.outcome == .exited 0 && String.fromUTF8! okR.stdout == "RING_64K_OK\n")
            s!"concurrent fwd task {idx} failed"
    finally
      let _ ← echoProc.kill
      let _ ← echoProc.wait

    let pids1Res ← assertOk (← ProcessSandbox.run {
      program := "/box/probe"
      args := #["--pids1"]
      mounts := #[.readOnly probeBin.toString "/box/probe"]
      limits := { timeoutMs := 10_000, pidsMax := some 1 }
    }) "pidsMax = some 1 runs 1 guest task and blocks 2nd fork"
    assertTrue (pids1Res.outcome == .exited 0)
      s!"pidsMax=1 outcome: {repr pids1Res.outcome} out={String.fromUTF8! pids1Res.stdout}"

    let oomRes ← assertOk (← ProcessSandbox.run {
      program := "/box/probe"
      args := #["--mem2"]
      mounts := #[.readOnly probeBin.toString "/box/probe"]
      limits := { timeoutMs := 15_000, memoryMaxBytes := some (20 * 1024 * 1024), pidsMax := some 8 }
    }) "whole-box multi-child cgroup v2 memory.max enforcement"
    assertTrue (oomRes.outcome == .signaled 9)
      s!"expected cgroup OOM SIGKILL (signaled 9), got {repr oomRes.outcome}"

    let oomChildRes ← assertOk (← ProcessSandbox.run {
      program := "/box/probe"
      args := #["--mem-child"]
      mounts := #[.readOnly probeBin.toString "/box/probe"]
      limits := { timeoutMs := 15_000, memoryMaxBytes := some (20 * 1024 * 1024), pidsMax := some 8 }
    }) "child OOM kills whole box atomically via cgroup memory.oom.group"
    assertTrue (oomChildRes.outcome == .signaled 9)
      s!"expected atomic whole-box OOM SIGKILL (signaled 9), got {repr oomChildRes.outcome}"

    let fsizeRes ← assertOk (← ProcessSandbox.run {
      program := "/bin/sh"
      args := #["-c", "dd if=/dev/zero of=/tmp/big bs=1024 count=64 2>/dev/null; echo rc=$?"]
      limits := { timeoutMs := 10_000, fileSizeMaxBytes := some 4096 }
    }) "RLIMIT_FSIZE enforces fileSizeMaxBytes"
    assertTrue (fsizeRes.outcome != .exited 0 ||
      (String.fromUTF8! fsizeRes.stdout).trimAscii.toString != "rc=0")
      s!"fileSizeMaxBytes did not block 64 KiB write: {repr fsizeRes.outcome} out={String.fromUTF8! fsizeRes.stdout}"

    let tasks ← (List.range 4).mapM fun idx => IO.asTask do
      ProcessSandbox.run {
        program := "/bin/cat"
        stdin := s!"task-{idx}".toUTF8
        limits := { timeoutMs := 15_000 }
      }
    for (idx, t) in (List.range 4).zip tasks do
      let tr := t.get
      match tr with
      | .error ioErr => throw (IO.userError s!"concurrent task {idx} threw IO error: {ioErr}")
      | .ok r =>
        let okR ← assertOk r s!"concurrent task {idx}"
        assertTrue (okR.outcome == .exited 0 && String.fromUTF8! okR.stdout == s!"task-{idx}")
          s!"concurrent task {idx} stdout mismatch"

    for code in ([97, 98, 125, 126, 127, 255] : List Int) do
      let codeRes ← assertOk (← ProcessSandbox.run {
        program := "/box/probe"
        args := #["--exit", toString code]
        mounts := #[.readOnly probeBin.toString "/box/probe"]
      }) s!"magic exit code {code} verbatim"
      assertTrue (codeRes.outcome == .exited code) s!"expected exited {code}, got {repr codeRes.outcome}"

    assertErrKind (← ProcessSandbox.run { program := "/no/such/binary_999" }) .notFound "missing program"
    assertErrKind (← ProcessSandbox.run { program := "/bin/true", cwd := some "/no/such/cwd" }) .notFound
      "missing cwd"
    let noExec := tmpDir / "noexec_script"
    IO.FS.writeFile noExec "#!/bin/sh\necho nope\n"
    let _ ← assertOk (← LeanSwe.Fs.Raw.chmod noExec.toString 0o644) "chmod 0644"
    assertErrKind (← ProcessSandbox.run {
      program := "/box/noexec"
      mounts := #[.readOnly noExec.toString "/box/noexec"]
    }) .permissionDenied "non-executable program"

    let toRes ← assertOk (← ProcessSandbox.run {
      program := "/bin/sleep"
      args := #["10"]
      limits := { timeoutMs := 150 }
    }) "timeoutMs"
    assertTrue (toRes.outcome == .timedOut) s!"expected timedOut, got {repr toRes.outcome}"

    let zeroCapOk ← assertOk (← ProcessSandbox.run {
      program := "/bin/true"
      limits := { timeoutMs := 10_000, maxOutputBytes := some 0 }
    }) "maxOutputBytes = some 0 allows 0 emitted bytes"
    assertTrue (zeroCapOk.outcome == .exited 0) "maxOutputBytes=0 with silent command exited 0"

    let overOut ← assertOk (← ProcessSandbox.run {
      program := "/usr/bin/printf"
      args := #["1234567890"]
      limits := { timeoutMs := 10_000, maxOutputBytes := some 4 }
    }) "maxOutputBytes = some 4"
    assertTrue (overOut.outcome == .outputLimitExceeded &&
      overOut.stdout.size + overOut.stderr.size <= 4)
      s!"outputLimitExceeded mismatch: {repr overOut.outcome}"

    let flockDir := tmpDir / "flock_rw"
    IO.FS.createDirAll flockDir
    let flockFile := flockDir / "grandchild.lock"
    let dfRes ← assertOk (← ProcessSandbox.run {
      program := "/box/probe"
      args := #["--double-fork-flock", "/flock/grandchild.lock"]
      mounts := #[.readOnly probeBin.toString "/box/probe", .readWrite flockDir.toString "/flock"]
      limits := { timeoutMs := 10_000 }
    }) "double-forked grandchild killed and reaped"
    assertTrue (dfRes.outcome == .exited 0 &&
      String.fromUTF8! dfRes.stdout == "PARENT_EXITED\n") "parent exited cleanly"
    let lh ← match ← LeanSwe.Fs.Raw.acquireLock flockFile.toString .exclusive true true with
      | .ok h => pure h
      | .error e => throw (IO.userError s!"double-forked grandchild still holds flock: {e.message}")
    let _ ← LeanSwe.Fs.Raw.releaseLock lh

    assertTrue ((← ProcessSandbox.Raw.activeResourceCounts) == baseCounts)
      "final ProcessSandbox activeResourceCounts == 0"
    let cgAfter ← countLeftoverCgroups cgParent
    assertTrue (cgAfter <= cgBefore) "zero leftover cgroup v2 directories"
  finally
    IO.FS.removeDirAll tmpDir
  IO.println "PASS: LeanSwe.ProcessSandbox runtime tests"

end LeanSwe.ProcessSandbox.RuntimeTests
