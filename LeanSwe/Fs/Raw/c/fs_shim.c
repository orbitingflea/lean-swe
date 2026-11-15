#define _POSIX_C_SOURCE 200809L

#include <errno.h>
#include <fcntl.h>
#include <lean/lean.h>
#include <pthread.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>
#include <sys/file.h>
#include <sys/stat.h>
#include <unistd.h>

typedef struct LockSlot {
  uint64_t id;
  int fd;
  struct LockSlot *next;
} LockSlot;

static pthread_mutex_t g_lock_mutex = PTHREAD_MUTEX_INITIALIZER;
static uint64_t g_next_lock_id = 1;
static LockSlot *g_locks = NULL;

static lean_obj_res mk_acquire_result(uint8_t status, uint64_t handle_id, uint32_t err_code) {
  lean_obj_res inner = lean_alloc_ctor(0, 2, 0);
  lean_ctor_set(inner, 0, lean_box_uint64(handle_id));
  lean_ctor_set(inner, 1, lean_box_uint32(err_code));
  lean_obj_res outer = lean_alloc_ctor(0, 2, 0);
  lean_ctor_set(outer, 0, lean_box((unsigned)status));
  lean_ctor_set(outer, 1, inner);
  return outer;
}

LEAN_EXPORT lean_obj_res leanswe_fs_chmod(b_lean_obj_arg path_obj, uint32_t mode, lean_obj_arg w) {
  (void)w;
  const char *cpath = lean_string_cstr(path_obj);
  if (chmod(cpath, (mode_t)mode) != 0) {
    return lean_io_result_mk_error(lean_decode_io_error(errno, path_obj));
  }
  return lean_io_result_mk_ok(lean_box(0));
}

LEAN_EXPORT lean_obj_res leanswe_fs_symlink(
    b_lean_obj_arg target_obj, b_lean_obj_arg link_obj, lean_obj_arg w) {
  (void)w;
  const char *target = lean_string_cstr(target_obj);
  const char *linkpath = lean_string_cstr(link_obj);
  if (symlink(target, linkpath) != 0) {
    return lean_io_result_mk_error(lean_decode_io_error(errno, link_obj));
  }
  return lean_io_result_mk_ok(lean_box(0));
}

LEAN_EXPORT lean_obj_res leanswe_fs_readlink(b_lean_obj_arg path_obj, lean_obj_arg w) {
  (void)w;
  const char *cpath = lean_string_cstr(path_obj);
  size_t cap = 256;
  for (;;) {
    char *buf = (char *)malloc(cap);
    if (buf == NULL) {
      return lean_io_result_mk_error(lean_decode_io_error(ENOMEM, path_obj));
    }
    ssize_t n = readlink(cpath, buf, cap - 1);
    if (n < 0) {
      int err = errno;
      free(buf);
      return lean_io_result_mk_error(lean_decode_io_error(err, path_obj));
    }
    if ((size_t)n < cap - 1) {
      buf[n] = '\0';
      lean_obj_res res = lean_mk_string(buf);
      free(buf);
      return lean_io_result_mk_ok(res);
    }
    free(buf);
    if (cap >= (1u << 20)) {
      return lean_io_result_mk_error(lean_decode_io_error(ENAMETOOLONG, path_obj));
    }
    cap *= 2;
  }
}

LEAN_EXPORT lean_obj_res leanswe_fs_stat_mode(
    b_lean_obj_arg path_obj, uint8_t follow_symlinks, lean_obj_arg w) {
  (void)w;
  const char *cpath = lean_string_cstr(path_obj);
  struct stat st;
  int rc = follow_symlinks ? stat(cpath, &st) : lstat(cpath, &st);
  if (rc != 0) {
    return lean_io_result_mk_error(lean_decode_io_error(errno, path_obj));
  }
  uint32_t perms = (uint32_t)(st.st_mode & 07777);
  return lean_io_result_mk_ok(lean_box_uint32(perms));
}

static int validate_raw_path(b_lean_obj_arg path_obj) {
  size_t sz = lean_string_size(path_obj);
  size_t slen = (sz > 0) ? (sz - 1) : 0;
  const char *cpath = lean_string_cstr(path_obj);
  if (slen == 0 || strlen(cpath) != slen) {
    return 0;
  }
  if (slen > 1 && cpath[slen - 1] == '/') {
    return 0;
  }
  return 1;
}

LEAN_EXPORT lean_obj_res leanswe_fs_read_regular_bytes(b_lean_obj_arg path_obj, lean_obj_arg w) {
  (void)w;
  if (!validate_raw_path(path_obj)) {
    return lean_io_result_mk_error(lean_decode_io_error(EINVAL, path_obj));
  }
  const char *cpath = lean_string_cstr(path_obj);
  int fd = -1;
  for (;;) {
    fd = open(cpath, O_RDONLY | O_NONBLOCK | O_CLOEXEC | O_NOCTTY);
    if (fd >= 0 || errno != EINTR) {
      break;
    }
  }
  if (fd < 0) {
    int err = errno;
    if (err == ENXIO) {
      struct stat st;
      if (stat(cpath, &st) == 0 || lstat(cpath, &st) == 0) {
        if (S_ISDIR(st.st_mode)) {
          return lean_io_result_mk_error(lean_decode_io_error(EISDIR, path_obj));
        }
      }
      return lean_io_result_mk_error(lean_decode_io_error(EINVAL, path_obj));
    }
    return lean_io_result_mk_error(lean_decode_io_error(err, path_obj));
  }

  struct stat st;
  if (fstat(fd, &st) != 0) {
    int err = errno;
    close(fd);
    return lean_io_result_mk_error(lean_decode_io_error(err, path_obj));
  }
  if (S_ISDIR(st.st_mode)) {
    close(fd);
    return lean_io_result_mk_error(lean_decode_io_error(EISDIR, path_obj));
  }
  if (!S_ISREG(st.st_mode)) {
    close(fd);
    return lean_io_result_mk_error(lean_decode_io_error(EINVAL, path_obj));
  }

  int flags = fcntl(fd, F_GETFL, 0);
  if (flags < 0) {
    int err = errno;
    close(fd);
    return lean_io_result_mk_error(lean_decode_io_error(err, path_obj));
  }
  if ((flags & O_NONBLOCK) != 0) {
    if (fcntl(fd, F_SETFL, flags & ~O_NONBLOCK) != 0) {
      int err = errno;
      close(fd);
      return lean_io_result_mk_error(lean_decode_io_error(err, path_obj));
    }
  }

  size_t cap = 4096;
  if (st.st_size > 0 && (uint64_t)st.st_size <= (uint64_t)(SIZE_MAX - 4096)) {
    size_t hint = (size_t)st.st_size + 1;
    if (hint > cap) {
      cap = hint;
    }
  }
  uint8_t *buf = (uint8_t *)malloc(cap);
  if (buf == NULL) {
    close(fd);
    return lean_io_result_mk_error(lean_decode_io_error(ENOMEM, path_obj));
  }
  size_t len = 0;
  for (;;) {
    if (len == cap) {
      if (cap > SIZE_MAX / 2) {
        free(buf);
        close(fd);
        return lean_io_result_mk_error(lean_decode_io_error(ENOMEM, path_obj));
      }
      size_t new_cap = cap * 2;
      uint8_t *new_buf = (uint8_t *)realloc(buf, new_cap);
      if (new_buf == NULL) {
        free(buf);
        close(fd);
        return lean_io_result_mk_error(lean_decode_io_error(ENOMEM, path_obj));
      }
      buf = new_buf;
      cap = new_cap;
    }
    size_t space = cap - len;
    size_t chunk = (space > 65536) ? 65536 : space;
    ssize_t n = read(fd, buf + len, chunk);
    if (n < 0) {
      int err = errno;
      if (err == EINTR || err == EAGAIN || err == EWOULDBLOCK) {
        continue;
      }
      free(buf);
      close(fd);
      return lean_io_result_mk_error(lean_decode_io_error(err, path_obj));
    }
    if (n == 0) {
      break;
    }
    len += (size_t)n;
  }

  if (close(fd) != 0) {
    int err = errno;
    if (err != EINTR) {
      free(buf);
      return lean_io_result_mk_error(lean_decode_io_error(err, path_obj));
    }
  }

  lean_obj_res ba = lean_alloc_sarray(1, len, len);
  if (len > 0) {
    memcpy(lean_sarray_cptr(ba), buf, len);
  }
  free(buf);
  return lean_io_result_mk_ok(ba);
}

LEAN_EXPORT lean_obj_res leanswe_fs_create_file_new(
    b_lean_obj_arg path_obj, b_lean_obj_arg bytes_obj, lean_obj_arg w) {
  (void)w;
  if (!validate_raw_path(path_obj)) {
    return lean_io_result_mk_error(lean_decode_io_error(EINVAL, path_obj));
  }
  const char *cpath = lean_string_cstr(path_obj);
  int fd = -1;
  for (;;) {
    fd = open(cpath, O_WRONLY | O_CREAT | O_EXCL | O_NOFOLLOW | O_CLOEXEC, (mode_t)0644);
    if (fd >= 0 || errno != EINTR) {
      break;
    }
  }
  if (fd < 0) {
    return lean_io_result_mk_error(lean_decode_io_error(errno, path_obj));
  }

  size_t total = lean_sarray_size(bytes_obj);
  const uint8_t *ptr = (total > 0) ? lean_sarray_cptr((lean_object *)bytes_obj) : NULL;
  size_t off = 0;
  while (off < total) {
    ssize_t n = write(fd, ptr + off, total - off);
    if (n < 0) {
      int err = errno;
      if (err == EINTR) {
        continue;
      }
      close(fd);
      (void)unlink(cpath);
      return lean_io_result_mk_error(lean_decode_io_error(err, path_obj));
    }
    if (n == 0) {
      close(fd);
      (void)unlink(cpath);
      return lean_io_result_mk_error(lean_decode_io_error(EIO, path_obj));
    }
    off += (size_t)n;
  }

  if (close(fd) != 0) {
    int err = errno;
    if (err != EINTR) {
      (void)unlink(cpath);
      return lean_io_result_mk_error(lean_decode_io_error(err, path_obj));
    }
  }
  return lean_io_result_mk_ok(lean_box(0));
}

LEAN_EXPORT lean_obj_res leanswe_fs_acquire_lock(
    b_lean_obj_arg path_obj, uint8_t mode, uint8_t create_if_missing, uint8_t non_blocking,
    lean_obj_arg w) {
  (void)w;
  if (!validate_raw_path(path_obj)) {
    return lean_io_result_mk_ok(mk_acquire_result(2, 0, (uint32_t)EINVAL));
  }
  const char *cpath = lean_string_cstr(path_obj);

  int base_flags = O_RDONLY | O_NOFOLLOW | O_CLOEXEC | O_NONBLOCK;
  int fd = -1;
  for (;;) {
    fd = open(cpath, base_flags);
    if (fd >= 0 || errno != EINTR) {
      break;
    }
  }
  if (fd < 0 && errno == ENOENT && create_if_missing != 0) {
    for (;;) {
      fd = open(cpath, base_flags | O_CREAT, (mode_t)0644);
      if (fd >= 0 || errno != EINTR) {
        break;
      }
    }
  }
  if (fd < 0) {
    int err = errno;
    if (err == ELOOP) {
      return lean_io_result_mk_ok(mk_acquire_result(2, 0, (uint32_t)err));
    }
    return lean_io_result_mk_error(lean_decode_io_error(err, path_obj));
  }

  struct stat st;
  if (fstat(fd, &st) != 0) {
    int err = errno;
    close(fd);
    return lean_io_result_mk_error(lean_decode_io_error(err, path_obj));
  }
  if (S_ISDIR(st.st_mode)) {
    close(fd);
    return lean_io_result_mk_error(lean_decode_io_error(EISDIR, path_obj));
  }
  if (!S_ISREG(st.st_mode)) {
    close(fd);
    return lean_io_result_mk_ok(mk_acquire_result(2, 0, (uint32_t)EINVAL));
  }

  int lock_op = (mode == 0) ? LOCK_SH : LOCK_EX;
  if (non_blocking != 0) {
    lock_op |= LOCK_NB;
  }
  for (;;) {
    if (flock(fd, lock_op) == 0) {
      break;
    }
    int err = errno;
    if (err == EINTR) {
      continue;
    }
    close(fd);
    if (err == EWOULDBLOCK || err == EAGAIN) {
      return lean_io_result_mk_ok(mk_acquire_result(1, 0, (uint32_t)err));
    }
    return lean_io_result_mk_error(lean_decode_io_error(err, path_obj));
  }

  LockSlot *slot = (LockSlot *)malloc(sizeof(LockSlot));
  if (slot == NULL) {
    (void)flock(fd, LOCK_UN);
    close(fd);
    return lean_io_result_mk_error(lean_decode_io_error(ENOMEM, path_obj));
  }

  pthread_mutex_lock(&g_lock_mutex);
  uint64_t id = g_next_lock_id++;
  if (g_next_lock_id == 0) {
    g_next_lock_id = 1;
  }
  slot->id = id;
  slot->fd = fd;
  slot->next = g_locks;
  g_locks = slot;
  pthread_mutex_unlock(&g_lock_mutex);

  return lean_io_result_mk_ok(mk_acquire_result(0, id, 0));
}

LEAN_EXPORT lean_obj_res leanswe_fs_release_lock(
    uint64_t id, b_lean_obj_arg path_obj, lean_obj_arg w) {
  (void)w;
  if (id == 0) {
    return lean_io_result_mk_error(lean_decode_io_error(EINVAL, path_obj));
  }

  pthread_mutex_lock(&g_lock_mutex);
  LockSlot **pp = &g_locks;
  LockSlot *found = NULL;
  while (*pp != NULL) {
    if ((*pp)->id == id) {
      found = *pp;
      *pp = found->next;
      break;
    }
    pp = &(*pp)->next;
  }
  pthread_mutex_unlock(&g_lock_mutex);

  if (found == NULL) {
    return lean_io_result_mk_error(lean_decode_io_error(EINVAL, path_obj));
  }

  int fd = found->fd;
  free(found);

  int unlock_err = 0;
  for (;;) {
    if (flock(fd, LOCK_UN) == 0) {
      break;
    }
    int err = errno;
    if (err == EINTR) {
      continue;
    }
    unlock_err = err;
    break;
  }

  int close_err = 0;
  if (close(fd) != 0) {
    int err = errno;
    if (err != EINTR) {
      close_err = err;
    }
  }
  int final_err = (unlock_err != 0) ? unlock_err : close_err;
  if (final_err != 0) {
    return lean_io_result_mk_error(lean_decode_io_error(final_err, path_obj));
  }
  return lean_io_result_mk_ok(lean_box(0));
}
