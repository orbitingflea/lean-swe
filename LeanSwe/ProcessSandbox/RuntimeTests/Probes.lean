import LeanSwe.ProcessSandbox.Interface
import LeanSwe.ProcessSandbox.Raw.Interface

namespace LeanSwe.ProcessSandbox.RuntimeTests.Probes

open LeanSwe.ProcessSandbox

/-- Fail with `IO.userError` when `cond` is `false`. -/
def assertTrue (cond : Bool) (msg : String) : IO Unit := do
  if !cond then
    throw (IO.userError s!"ASSERTION FAILED: {msg}")

/-- Unwrap `.ok v` or fail with `IO.userError` on unexpected `.error e`. -/
def assertOk {ε α : Type} [Repr ε] (res : Except ε α) (msg : String) : IO α := do
  match res with
  | .ok v => return v
  | .error e => throw (IO.userError s!"ASSERTION FAILED: {msg} (unexpected error: {repr e})")

/-- Assert that `res` returned `.error e` with exact `expected` `SandboxErrorKind` and non-empty message. -/
def assertErrKind {α : Type} (res : Except SandboxError α) (expected : SandboxErrorKind)
    (msg : String) : IO Unit := do
  match res with
  | .ok _ => throw (IO.userError s!"ASSERTION FAILED: {msg} (expected {repr expected}, got ok)")
  | .error e =>
    if e.kind != expected || e.message.isEmpty then
      throw (IO.userError s!"ASSERTION FAILED: {msg} (got {repr e}, expected {repr expected})")

/-- Return `true` iff `p` lies beneath an immutable top-level system root directory. -/
def isSystemRootPrefix (p : String) : Bool :=
  ["/usr/", "/bin/", "/sbin/", "/lib/", "/lib64/"].any (fun pre => p.startsWith pre)

/-- Baseline mocked `RawProcessSandboxOps` failing `preflight` with `.unavailable`. -/
def mockPreflightUnavailableOps : RawProcessSandboxOps :=
  { Raw.defaultOps with
    preflight := fun _ => pure (.error { kind := .unavailable, message := "mock preflight unavailable" }) }

/-- Baseline mocked `RawProcessSandboxOps` passing preflight/seal and failing `spawnBox` with `err`. -/
def mockSpawnFailOps (err : SandboxError) : RawProcessSandboxOps :=
  { Raw.defaultOps with
    preflight := fun _ => pure (.ok ())
    hostSeccompArch := pure (.ok .x86_64)
    discoverHostPreset := pure (.ok {})
    sealPlan := fun _ _ => pure (.ok { handleId := 1 })
    closePlan := fun _ => pure (.ok ())
    spawnBox := fun _ => pure (.error err) }

/-- C probe binary source exercising seccomp, cgroups, TCP relays, and grandchild reaping inside the box. -/
def probeCCode : String :=
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
  "#ifndef __NR_mount_setattr\n" ++
  "#define __NR_mount_setattr 442\n" ++
  "#endif\n" ++
  "#ifndef MSG_FASTOPEN\n" ++
  "#define MSG_FASTOPEN 0x20000000\n" ++
  "#endif\n" ++
  "#ifndef AF_SMC\n" ++
  "#define AF_SMC 43\n" ++
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
  "    if (socketpair(AF_INET, SOCK_STREAM, 0, sp3) == 0 || errno != EPERM) return 12;\n" ++
  "    if (socketpair(AF_UNIX, SOCK_STREAM, 1, sp3) == 0 || errno != EPERM) return 12;\n" ++
  "    if (socket(AF_UNIX, SOCK_STREAM, 0) >= 0 || errno != EPERM) return 13;\n" ++
  "    if (socket(AF_SMC, SOCK_STREAM, 0) >= 0 || errno != EPERM) return 13;\n" ++
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
  "    if (syscall(__NR_acct, NULL) >= 0 || errno != EPERM) return 28;\n" ++
  "    if (syscall(__NR_mount_setattr, -1, NULL, 0, NULL, 0) >= 0 || errno != EPERM) return 29;\n" ++
  "    char msg_byte = 'x';\n" ++
  "    struct iovec msg_iov = { &msg_byte, 1 };\n" ++
  "    struct msghdr mh; memset(&mh, 0, sizeof(mh));\n" ++
  "    mh.msg_iov = &msg_iov; mh.msg_iovlen = 1;\n" ++
  "    struct mmsghdr vmh; memset(&vmh, 0, sizeof(vmh));\n" ++
  "    vmh.msg_hdr = mh;\n" ++
  "    errno = 0; if (sendto(-1, &msg_byte, 1, MSG_FASTOPEN, NULL, 0) >= 0 || errno != EPERM) return 30;\n" ++
  "    errno = 0; if (sendto(-1, &msg_byte, 1, 0, NULL, 0) >= 0 || errno == EPERM) return 31;\n" ++
  "    errno = 0; if (sendmsg(-1, &mh, MSG_FASTOPEN) >= 0 || errno != EPERM) return 32;\n" ++
  "    errno = 0; if (sendmsg(-1, &mh, 0) >= 0 || errno == EPERM) return 33;\n" ++
  "    errno = 0; if (sendmmsg(-1, &vmh, 1, MSG_FASTOPEN) >= 0 || errno != EPERM) return 34;\n" ++
  "    errno = 0; if (sendmmsg(-1, &vmh, 1, 0) >= 0 || errno == EPERM) return 35;\n" ++
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
  "    pid_t cpid = (pid_t)syscall(__NR_clone, (unsigned long)SIGCHLD, NULL, NULL, NULL, 0);\n" ++
  "    if (cpid == 0) _exit(0);\n" ++
  "    if (cpid <= 0) return 23;\n" ++
  "    int cst = 0; pid_t wrc;\n" ++
  "    do { wrc = waitpid(cpid, &cst, 0); } while (wrc < 0 && errno == EINTR);\n" ++
  "    if (wrc != cpid || !WIFEXITED(cst) || WEXITSTATUS(cst) != 0) return 23;\n" ++
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
  "    if (write(cs, \"LO\", 2) != 2) { close(afd); close(cs); close(ls); return 45; }\n" ++
  "    char b[8]; ssize_t rn = read(afd, b, 2);\n" ++
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
  "        if (write(pfd[1], \"L\", 1) != 1) _exit(53);\n" ++
  "        close(pfd[1]);\n" ++
  "        sleep(60);\n" ++
  "        _exit(0);\n" ++
  "      }\n" ++
  "      _exit(0);\n" ++
  "    }\n" ++
  "    close(pfd[1]);\n" ++
  "    char ch = 0; ssize_t r = read(pfd[0], &ch, 1); close(pfd[0]);\n" ++
  "    if (r != 1 || ch != 'L') return 54;\n" ++
  "    waitpid(c, NULL, 0);\n" ++
  "    printf(\"PARENT_EXITED\\n\");\n" ++
  "    return 0;\n" ++
  "  }\n" ++
  "  return 2;\n" ++
  "}\n"

/-- Python helper server verifying directional `SHUT_WR` half-close TCP forwarding. -/
def halfCloseServerPy : String :=
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

/-- Python helper server listening silently on host loopback for network-isolation checks. -/
def silentListenerPy : String :=
  "import socket, sys, time\n" ++
  "s = socket.socket()\n" ++
  "s.bind(('127.0.0.1', 0))\n" ++
  "s.listen(4)\n" ++
  "print(s.getsockname()[1], flush=True)\n" ++
  "time.sleep(10)\n"

/-- Python helper server echoing half-closed payloads for 64 KiB ring, burst, and RST tests. -/
def echoHalfCloseServerPy : String :=
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

/-- Locate the parent delegated `cgroup v2` directory for leak accounting. -/
def findDelegatedCgroupParentDir : IO (Option String) := do
  let raw ← IO.FS.readFile "/proc/self/cgroup"
  for line in raw.splitOn "\n" do
    if line.startsWith "0::" then
      let rel := (line.drop 3).toString
      let parent := (System.FilePath.mk ("/sys/fs/cgroup" ++ rel)).parent
      return parent.map (·.toString)
  return none

/-- Count leftover `leanswe-psandbox-*` sibling directories inside `parent?`. -/
def countLeftoverCgroups (parent? : Option String) : IO Nat := do
  match parent? with
  | none => return 0
  | some p =>
    let entries ← System.FilePath.readDir p
    return entries.foldl (fun acc e => if e.fileName.startsWith "leanswe-psandbox-" then acc + 1 else acc) 0

end LeanSwe.ProcessSandbox.RuntimeTests.Probes
