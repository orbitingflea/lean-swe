#define _POSIX_C_SOURCE 200809L

#include <errno.h>
#include <fcntl.h>
#include <lean/lean.h>
#include <stdint.h>
#include <string.h>
#include <unistd.h>

#ifdef __linux__
#include <sys/random.h>
#endif

static int read_urandom_16(uint8_t *buf) {
  int fd;
  do {
    fd = open("/dev/urandom", O_RDONLY | O_CLOEXEC);
  } while (fd < 0 && errno == EINTR);
  if (fd < 0) {
    return errno;
  }

  size_t off = 0;
  while (off < 16) {
    ssize_t n = read(fd, buf + off, 16 - off);
    if (n < 0) {
      if (errno == EINTR) {
        continue;
      }
      int err = errno;
      close(fd);
      return err;
    }
    if (n == 0) {
      close(fd);
      return EIO;
    }
    off += (size_t)n;
  }

  close(fd);
  return 0;
}

LEAN_EXPORT lean_obj_res leanswe_uuid_random_bytes16(lean_obj_arg w) {
  (void)w;
  uint8_t buf[16];
  const char *source = "getrandom";

#ifdef __linux__
  size_t off = 0;
  int use_fallback = 0;
  while (off < 16) {
    ssize_t n = getrandom(buf + off, 16 - off, 0);
    if (n < 0) {
      if (errno == EINTR) {
        continue;
      }
      if (errno == ENOSYS) {
        use_fallback = 1;
        break;
      }
      int err = errno;
      lean_obj_res src_obj = lean_mk_string(source);
      lean_obj_res io_err = lean_decode_io_error(err, src_obj);
      lean_dec(src_obj);
      return lean_io_result_mk_error(io_err);
    }
    if (n == 0) {
      use_fallback = 1;
      break;
    }
    off += (size_t)n;
  }
  if (use_fallback) {
    source = "/dev/urandom";
    int err = read_urandom_16(buf);
    if (err != 0) {
      lean_obj_res src_obj = lean_mk_string(source);
      lean_obj_res io_err = lean_decode_io_error(err, src_obj);
      lean_dec(src_obj);
      return lean_io_result_mk_error(io_err);
    }
  }
#else
  source = "/dev/urandom";
  int err = read_urandom_16(buf);
  if (err != 0) {
    lean_obj_res src_obj = lean_mk_string(source);
    lean_obj_res io_err = lean_decode_io_error(err, src_obj);
    lean_dec(src_obj);
    return lean_io_result_mk_error(io_err);
  }
#endif

  lean_obj_res ba = lean_alloc_sarray(1, 16, 16);
  memcpy(lean_sarray_cptr(ba), buf, 16);
  return lean_io_result_mk_ok(ba);
}
