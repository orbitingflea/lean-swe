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

LEAN_EXPORT lean_obj_res leanswe_fs_acquire_lock(
    b_lean_obj_arg path_obj, uint8_t mode, uint8_t create_if_missing, uint8_t non_blocking,
    lean_obj_arg w) {
  (void)w;
  size_t sz = lean_string_size(path_obj);
  size_t slen = (sz > 0) ? (sz - 1) : 0;
  const char *cpath = lean_string_cstr(path_obj);
  if (slen == 0 || strlen(cpath) != slen) {
    return lean_io_result_mk_ok(mk_acquire_result(2, 0, (uint32_t)EINVAL));
  }
  if (slen > 1 && cpath[slen - 1] == '/') {
    return lean_io_result_mk_ok(mk_acquire_result(2, 0, (uint32_t)EINVAL));
  }

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
