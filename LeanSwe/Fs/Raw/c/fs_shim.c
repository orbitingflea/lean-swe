#define _POSIX_C_SOURCE 200809L

#include <dirent.h>
#include <errno.h>
#include <fcntl.h>
#include <lean/lean.h>
#include <pthread.h>
#include <stdint.h>
#include <stdio.h>
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

typedef struct DirSlot {
  uint64_t id;
  int fd;
  uint64_t refs;
  uint8_t closing;
  pthread_mutex_t read_mutex;
  struct DirSlot *next;
} DirSlot;

static pthread_mutex_t g_lock_mutex = PTHREAD_MUTEX_INITIALIZER;
static uint64_t g_next_lock_id = 1;
static LockSlot *g_locks = NULL;

static pthread_mutex_t g_dir_mutex = PTHREAD_MUTEX_INITIALIZER;
static uint64_t g_next_dir_id = 1;
static DirSlot *g_dirs = NULL;

static uint64_t g_temp_nonce = 1;

static lean_obj_res mk_pair(lean_obj_arg a, lean_obj_arg b) {
  lean_obj_res p = lean_alloc_ctor(0, 2, 0);
  lean_ctor_set(p, 0, a);
  lean_ctor_set(p, 1, b);
  return p;
}

static lean_obj_res mk_acquire_result(uint8_t status, uint64_t handle_id, uint32_t err_code) {
  lean_obj_res inner = mk_pair(lean_box_uint64(handle_id), lean_box_uint32(err_code));
  return mk_pair(lean_box((unsigned)status), inner);
}

static lean_obj_res mk_stat_tuple(const struct stat *st) {
  uint8_t kind = 3;
  if (S_ISREG(st->st_mode)) {
    kind = 0;
  } else if (S_ISDIR(st->st_mode)) {
    kind = 1;
  } else if (S_ISLNK(st->st_mode)) {
    kind = 2;
  }
  uint64_t sz = (st->st_size >= 0) ? (uint64_t)st->st_size : 0;
  uint32_t mode = (uint32_t)(st->st_mode & 07777);
  lean_obj_res m_sec = lean_int64_to_int((int64_t)st->st_mtim.tv_sec);
  lean_obj_res m_nsec = lean_box_uint32((uint32_t)st->st_mtim.tv_nsec);
  lean_obj_res a_sec = lean_int64_to_int((int64_t)st->st_atim.tv_sec);
  lean_obj_res a_nsec = lean_box_uint32((uint32_t)st->st_atim.tv_nsec);
  lean_obj_res p6 = mk_pair(a_sec, a_nsec);
  lean_obj_res p5 = mk_pair(m_nsec, p6);
  lean_obj_res p4 = mk_pair(m_sec, p5);
  lean_obj_res p3 = mk_pair(lean_box_uint32(mode), p4);
  lean_obj_res p2 = mk_pair(lean_box_uint64(sz), p3);
  return mk_pair(lean_box((unsigned)kind), p2);
}

static int has_embedded_nul(b_lean_obj_arg s) {
  size_t sz = lean_string_size(s);
  size_t slen = (sz > 0) ? (sz - 1) : 0;
  const char *cstr = lean_string_cstr(s);
  return slen == 0 || strlen(cstr) != slen;
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

static int validate_entry_name(b_lean_obj_arg name_obj) {
  size_t sz = lean_string_size(name_obj);
  size_t slen = (sz > 0) ? (sz - 1) : 0;
  const char *cname = lean_string_cstr(name_obj);
  if (slen == 0 || strlen(cname) != slen) {
    return 0;
  }
  if (strchr(cname, '/') != NULL) {
    return 0;
  }
  if (strcmp(cname, ".") == 0 || strcmp(cname, "..") == 0) {
    return 0;
  }
  return 1;
}

static uint64_t dir_slot_insert(int fd) {
  DirSlot *slot = (DirSlot *)malloc(sizeof(DirSlot));
  if (slot == NULL) {
    return 0;
  }
  if (pthread_mutex_init(&slot->read_mutex, NULL) != 0) {
    free(slot);
    return 0;
  }
  pthread_mutex_lock(&g_dir_mutex);
  uint64_t id = g_next_dir_id++;
  if (g_next_dir_id == 0) {
    g_next_dir_id = 1;
  }
  slot->id = id;
  slot->fd = fd;
  slot->refs = 1;
  slot->closing = 0;
  slot->next = g_dirs;
  g_dirs = slot;
  pthread_mutex_unlock(&g_dir_mutex);
  return id;
}

static DirSlot *dir_slot_acquire(uint64_t id) {
  if (id == 0) {
    return NULL;
  }
  pthread_mutex_lock(&g_dir_mutex);
  DirSlot *cur = g_dirs;
  while (cur != NULL) {
    if (cur->id == id) {
      if (cur->closing != 0) {
        pthread_mutex_unlock(&g_dir_mutex);
        return NULL;
      }
      cur->refs++;
      pthread_mutex_unlock(&g_dir_mutex);
      return cur;
    }
    cur = cur->next;
  }
  pthread_mutex_unlock(&g_dir_mutex);
  return NULL;
}

static void dir_slot_release(DirSlot *slot) {
  if (slot == NULL) {
    return;
  }
  int fd_to_close = -1;
  int should_free = 0;
  pthread_mutex_lock(&g_dir_mutex);
  slot->refs--;
  if (slot->closing != 0 && slot->refs == 0) {
    fd_to_close = slot->fd;
    should_free = 1;
  }
  pthread_mutex_unlock(&g_dir_mutex);
  if (should_free) {
    (void)pthread_mutex_destroy(&slot->read_mutex);
    free(slot);
  }
  if (fd_to_close >= 0) {
    (void)close(fd_to_close);
  }
}

static lean_obj_res read_regular_fd(int fd, b_lean_obj_arg path_obj) {
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

static int write_all_and_close(int fd, b_lean_obj_arg bytes_obj) {
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
      return err;
    }
    if (n == 0) {
      close(fd);
      return EIO;
    }
    off += (size_t)n;
  }

  if (close(fd) != 0) {
    int err = errno;
    if (err != EINTR) {
      return err;
    }
  }
  return 0;
}

static lean_obj_res finish_lock_fd(
    int fd, uint8_t mode, uint8_t non_blocking, b_lean_obj_arg path_obj) {
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
  return read_regular_fd(fd, path_obj);
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

  int werr = write_all_and_close(fd, bytes_obj);
  if (werr != 0) {
    (void)unlink(cpath);
    return lean_io_result_mk_error(lean_decode_io_error(werr, path_obj));
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
  return finish_lock_fd(fd, mode, non_blocking, path_obj);
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

LEAN_EXPORT lean_obj_res leanswe_fs_open_dir(b_lean_obj_arg root_obj, lean_obj_arg w) {
  (void)w;
  if (!validate_raw_path(root_obj)) {
    return lean_io_result_mk_error(lean_decode_io_error(EINVAL, root_obj));
  }
  const char *cpath = lean_string_cstr(root_obj);
  int fd = -1;
  for (;;) {
    fd = open(cpath, O_RDONLY | O_DIRECTORY | O_CLOEXEC);
    if (fd >= 0 || errno != EINTR) {
      break;
    }
  }
  if (fd < 0) {
    int err = errno;
    if (err == EMFILE || err == ENFILE) {
      err = EINVAL;
    }
    return lean_io_result_mk_error(lean_decode_io_error(err, root_obj));
  }
  uint64_t id = dir_slot_insert(fd);
  if (id == 0) {
    close(fd);
    return lean_io_result_mk_error(lean_decode_io_error(ENOMEM, root_obj));
  }
  return lean_io_result_mk_ok(lean_box_uint64(id));
}

LEAN_EXPORT lean_obj_res leanswe_fs_open_dir_at(
    uint64_t dir_id, b_lean_obj_arg name_obj, lean_obj_arg w) {
  (void)w;
  if (!validate_entry_name(name_obj)) {
    return lean_io_result_mk_error(lean_decode_io_error(EINVAL, name_obj));
  }
  DirSlot *slot = dir_slot_acquire(dir_id);
  if (slot == NULL) {
    return lean_io_result_mk_error(lean_decode_io_error(EINVAL, name_obj));
  }
  const char *cname = lean_string_cstr(name_obj);
  int fd = -1;
  for (;;) {
    fd = openat(slot->fd, cname, O_RDONLY | O_DIRECTORY | O_NOFOLLOW | O_CLOEXEC);
    if (fd >= 0 || errno != EINTR) {
      break;
    }
  }
  if (fd < 0) {
    int err = errno;
    if (err == ELOOP) {
      err = EINVAL;
    } else if (err == ENOTDIR) {
      struct stat st;
      if (fstatat(slot->fd, cname, &st, AT_SYMLINK_NOFOLLOW) == 0 && S_ISLNK(st.st_mode)) {
        err = EINVAL;
      }
    } else if (err == EMFILE || err == ENFILE) {
      err = EINVAL;
    }
    dir_slot_release(slot);
    return lean_io_result_mk_error(lean_decode_io_error(err, name_obj));
  }
  dir_slot_release(slot);

  uint64_t id = dir_slot_insert(fd);
  if (id == 0) {
    close(fd);
    return lean_io_result_mk_error(lean_decode_io_error(ENOMEM, name_obj));
  }
  return lean_io_result_mk_ok(lean_box_uint64(id));
}

LEAN_EXPORT lean_obj_res leanswe_fs_close_dir(
    uint64_t dir_id, b_lean_obj_arg path_obj, lean_obj_arg w) {
  (void)w;
  if (dir_id == 0) {
    return lean_io_result_mk_error(lean_decode_io_error(EINVAL, path_obj));
  }
  pthread_mutex_lock(&g_dir_mutex);
  DirSlot **pp = &g_dirs;
  DirSlot *found = NULL;
  while (*pp != NULL) {
    if ((*pp)->id == dir_id) {
      found = *pp;
      if (found->closing != 0) {
        pthread_mutex_unlock(&g_dir_mutex);
        return lean_io_result_mk_error(lean_decode_io_error(EINVAL, path_obj));
      }
      found->closing = 1;
      found->refs--;
      *pp = found->next;
      break;
    }
    pp = &(*pp)->next;
  }
  if (found == NULL) {
    pthread_mutex_unlock(&g_dir_mutex);
    return lean_io_result_mk_error(lean_decode_io_error(EINVAL, path_obj));
  }
  int fd_to_close = -1;
  int should_free = 0;
  if (found->refs == 0) {
    fd_to_close = found->fd;
    should_free = 1;
  }
  pthread_mutex_unlock(&g_dir_mutex);

  if (should_free) {
    (void)pthread_mutex_destroy(&found->read_mutex);
    free(found);
  }

  if (fd_to_close >= 0) {
    if (close(fd_to_close) != 0) {
      int err = errno;
      if (err != EINTR) {
        return lean_io_result_mk_error(lean_decode_io_error(err, path_obj));
      }
    }
  }
  return lean_io_result_mk_ok(lean_box(0));
}

LEAN_EXPORT lean_obj_res leanswe_fs_fstat_dir(
    uint64_t dir_id, b_lean_obj_arg path_obj, lean_obj_arg w) {
  (void)w;
  DirSlot *slot = dir_slot_acquire(dir_id);
  if (slot == NULL) {
    return lean_io_result_mk_error(lean_decode_io_error(EINVAL, path_obj));
  }
  struct stat st;
  int rc = fstat(slot->fd, &st);
  int err = errno;
  dir_slot_release(slot);
  if (rc != 0) {
    return lean_io_result_mk_error(lean_decode_io_error(err, path_obj));
  }
  return lean_io_result_mk_ok(mk_stat_tuple(&st));
}

LEAN_EXPORT lean_obj_res leanswe_fs_lstat_at(
    uint64_t dir_id, b_lean_obj_arg name_obj, lean_obj_arg w) {
  (void)w;
  if (!validate_entry_name(name_obj)) {
    return lean_io_result_mk_error(lean_decode_io_error(EINVAL, name_obj));
  }
  DirSlot *slot = dir_slot_acquire(dir_id);
  if (slot == NULL) {
    return lean_io_result_mk_error(lean_decode_io_error(EINVAL, name_obj));
  }
  const char *cname = lean_string_cstr(name_obj);
  struct stat st;
  int rc = fstatat(slot->fd, cname, &st, AT_SYMLINK_NOFOLLOW);
  int err = errno;
  dir_slot_release(slot);
  if (rc != 0) {
    return lean_io_result_mk_error(lean_decode_io_error(err, name_obj));
  }
  return lean_io_result_mk_ok(mk_stat_tuple(&st));
}

LEAN_EXPORT lean_obj_res leanswe_fs_read_dir_at(
    uint64_t dir_id, b_lean_obj_arg path_obj, lean_obj_arg w) {
  (void)w;
  DirSlot *slot = dir_slot_acquire(dir_id);
  if (slot == NULL) {
    return lean_io_result_mk_error(lean_decode_io_error(EINVAL, path_obj));
  }
  pthread_mutex_lock(&slot->read_mutex);
  int dup_fd = fcntl(slot->fd, F_DUPFD_CLOEXEC, 0);
  if (dup_fd < 0) {
    int err = errno;
    pthread_mutex_unlock(&slot->read_mutex);
    dir_slot_release(slot);
    if (err == EMFILE || err == ENFILE) {
      err = EINVAL;
    }
    return lean_io_result_mk_error(lean_decode_io_error(err, path_obj));
  }
  DIR *d = fdopendir(dup_fd);
  if (d == NULL) {
    int derr = errno;
    close(dup_fd);
    pthread_mutex_unlock(&slot->read_mutex);
    dir_slot_release(slot);
    if (derr == EMFILE || derr == ENFILE) {
      derr = EINVAL;
    }
    return lean_io_result_mk_error(lean_decode_io_error(derr, path_obj));
  }
  rewinddir(d);

  lean_obj_res arr = lean_alloc_array(0, 16);
  for (;;) {
    errno = 0;
    struct dirent *ent = readdir(d);
    if (ent == NULL) {
      int rerr = errno;
      if (rerr != 0) {
        lean_dec(arr);
        closedir(d);
        pthread_mutex_unlock(&slot->read_mutex);
        dir_slot_release(slot);
        return lean_io_result_mk_error(lean_decode_io_error(rerr, path_obj));
      }
      break;
    }
    if (strcmp(ent->d_name, ".") == 0 || strcmp(ent->d_name, "..") == 0) {
      continue;
    }
    arr = lean_array_push(arr, lean_mk_string(ent->d_name));
  }
  if (closedir(d) != 0) {
    int cerr = errno;
    if (cerr != EINTR) {
      lean_dec(arr);
      pthread_mutex_unlock(&slot->read_mutex);
      dir_slot_release(slot);
      return lean_io_result_mk_error(lean_decode_io_error(cerr, path_obj));
    }
  }
  pthread_mutex_unlock(&slot->read_mutex);
  dir_slot_release(slot);
  return lean_io_result_mk_ok(arr);
}

LEAN_EXPORT lean_obj_res leanswe_fs_create_dir_at(
    uint64_t dir_id, b_lean_obj_arg name_obj, lean_obj_arg w) {
  (void)w;
  if (!validate_entry_name(name_obj)) {
    return lean_io_result_mk_error(lean_decode_io_error(EINVAL, name_obj));
  }
  DirSlot *slot = dir_slot_acquire(dir_id);
  if (slot == NULL) {
    return lean_io_result_mk_error(lean_decode_io_error(EINVAL, name_obj));
  }
  const char *cname = lean_string_cstr(name_obj);
  int rc = mkdirat(slot->fd, cname, (mode_t)0755);
  int err = errno;
  dir_slot_release(slot);
  if (rc != 0) {
    return lean_io_result_mk_error(lean_decode_io_error(err, name_obj));
  }
  return lean_io_result_mk_ok(lean_box(0));
}

LEAN_EXPORT lean_obj_res leanswe_fs_read_regular_at(
    uint64_t dir_id, b_lean_obj_arg name_obj, lean_obj_arg w) {
  (void)w;
  if (!validate_entry_name(name_obj)) {
    return lean_io_result_mk_error(lean_decode_io_error(EINVAL, name_obj));
  }
  DirSlot *slot = dir_slot_acquire(dir_id);
  if (slot == NULL) {
    return lean_io_result_mk_error(lean_decode_io_error(EINVAL, name_obj));
  }
  const char *cname = lean_string_cstr(name_obj);
  int fd = -1;
  for (;;) {
    fd = openat(slot->fd, cname, O_RDONLY | O_NOFOLLOW | O_NONBLOCK | O_CLOEXEC | O_NOCTTY);
    if (fd >= 0 || errno != EINTR) {
      break;
    }
  }
  if (fd < 0) {
    int err = errno;
    if (err == ELOOP) {
      dir_slot_release(slot);
      return lean_io_result_mk_error(lean_decode_io_error(EINVAL, name_obj));
    }
    if (err == ENXIO) {
      struct stat st;
      if (fstatat(slot->fd, cname, &st, AT_SYMLINK_NOFOLLOW) == 0 && S_ISDIR(st.st_mode)) {
        dir_slot_release(slot);
        return lean_io_result_mk_error(lean_decode_io_error(EISDIR, name_obj));
      }
      dir_slot_release(slot);
      return lean_io_result_mk_error(lean_decode_io_error(EINVAL, name_obj));
    }
    if (err == EMFILE || err == ENFILE) {
      err = EINVAL;
    }
    dir_slot_release(slot);
    return lean_io_result_mk_error(lean_decode_io_error(err, name_obj));
  }
  dir_slot_release(slot);
  return read_regular_fd(fd, name_obj);
}

LEAN_EXPORT lean_obj_res leanswe_fs_create_file_at(
    uint64_t dir_id, b_lean_obj_arg name_obj, b_lean_obj_arg bytes_obj, lean_obj_arg w) {
  (void)w;
  if (!validate_entry_name(name_obj)) {
    return lean_io_result_mk_error(lean_decode_io_error(EINVAL, name_obj));
  }
  DirSlot *slot = dir_slot_acquire(dir_id);
  if (slot == NULL) {
    return lean_io_result_mk_error(lean_decode_io_error(EINVAL, name_obj));
  }
  const char *cname = lean_string_cstr(name_obj);
  int fd = -1;
  for (;;) {
    fd = openat(slot->fd, cname, O_WRONLY | O_CREAT | O_EXCL | O_NOFOLLOW | O_CLOEXEC, (mode_t)0644);
    if (fd >= 0 || errno != EINTR) {
      break;
    }
  }
  if (fd < 0) {
    int err = errno;
    if (err == EMFILE || err == ENFILE) {
      err = EINVAL;
    }
    dir_slot_release(slot);
    return lean_io_result_mk_error(lean_decode_io_error(err, name_obj));
  }

  int werr = write_all_and_close(fd, bytes_obj);
  if (werr != 0) {
    (void)unlinkat(slot->fd, cname, 0);
    dir_slot_release(slot);
    return lean_io_result_mk_error(lean_decode_io_error(werr, name_obj));
  }
  dir_slot_release(slot);
  return lean_io_result_mk_ok(lean_box(0));
}

LEAN_EXPORT lean_obj_res leanswe_fs_rename_at(
    uint64_t src_id, b_lean_obj_arg src_name_obj,
    uint64_t dst_id, b_lean_obj_arg dst_name_obj, lean_obj_arg w) {
  (void)w;
  if (!validate_entry_name(src_name_obj)) {
    return lean_io_result_mk_error(lean_decode_io_error(EINVAL, src_name_obj));
  }
  if (!validate_entry_name(dst_name_obj)) {
    return lean_io_result_mk_error(lean_decode_io_error(EINVAL, dst_name_obj));
  }
  DirSlot *src_slot = dir_slot_acquire(src_id);
  if (src_slot == NULL) {
    return lean_io_result_mk_error(lean_decode_io_error(EINVAL, src_name_obj));
  }
  DirSlot *dst_slot = dir_slot_acquire(dst_id);
  if (dst_slot == NULL) {
    dir_slot_release(src_slot);
    return lean_io_result_mk_error(lean_decode_io_error(EINVAL, dst_name_obj));
  }
  const char *csrc = lean_string_cstr(src_name_obj);
  const char *cdst = lean_string_cstr(dst_name_obj);
  int rc = renameat(src_slot->fd, csrc, dst_slot->fd, cdst);
  int err = errno;
  dir_slot_release(dst_slot);
  dir_slot_release(src_slot);
  if (rc != 0) {
    return lean_io_result_mk_error(lean_decode_io_error(err, src_name_obj));
  }
  return lean_io_result_mk_ok(lean_box(0));
}

LEAN_EXPORT lean_obj_res leanswe_fs_unlink_at(
    uint64_t dir_id, b_lean_obj_arg name_obj, uint8_t is_dir, lean_obj_arg w) {
  (void)w;
  if (!validate_entry_name(name_obj)) {
    return lean_io_result_mk_error(lean_decode_io_error(EINVAL, name_obj));
  }
  DirSlot *slot = dir_slot_acquire(dir_id);
  if (slot == NULL) {
    return lean_io_result_mk_error(lean_decode_io_error(EINVAL, name_obj));
  }
  const char *cname = lean_string_cstr(name_obj);
  int flags = (is_dir != 0) ? AT_REMOVEDIR : 0;
  int rc = unlinkat(slot->fd, cname, flags);
  int err = errno;
  dir_slot_release(slot);
  if (rc != 0) {
    return lean_io_result_mk_error(lean_decode_io_error(err, name_obj));
  }
  return lean_io_result_mk_ok(lean_box(0));
}

LEAN_EXPORT lean_obj_res leanswe_fs_symlink_at(
    b_lean_obj_arg target_obj, uint64_t dir_id, b_lean_obj_arg name_obj, lean_obj_arg w) {
  (void)w;
  if (has_embedded_nul(target_obj)) {
    return lean_io_result_mk_error(lean_decode_io_error(EINVAL, name_obj));
  }
  if (!validate_entry_name(name_obj)) {
    return lean_io_result_mk_error(lean_decode_io_error(EINVAL, name_obj));
  }
  DirSlot *slot = dir_slot_acquire(dir_id);
  if (slot == NULL) {
    return lean_io_result_mk_error(lean_decode_io_error(EINVAL, name_obj));
  }
  const char *ctarget = lean_string_cstr(target_obj);
  const char *cname = lean_string_cstr(name_obj);
  int rc = symlinkat(ctarget, slot->fd, cname);
  int err = errno;
  dir_slot_release(slot);
  if (rc != 0) {
    return lean_io_result_mk_error(lean_decode_io_error(err, name_obj));
  }
  return lean_io_result_mk_ok(lean_box(0));
}

LEAN_EXPORT lean_obj_res leanswe_fs_acquire_lock_at(
    uint64_t dir_id, b_lean_obj_arg name_obj, uint8_t mode,
    uint8_t create_if_missing, uint8_t non_blocking, lean_obj_arg w) {
  (void)w;
  if (!validate_entry_name(name_obj)) {
    return lean_io_result_mk_ok(mk_acquire_result(2, 0, (uint32_t)EINVAL));
  }
  DirSlot *slot = dir_slot_acquire(dir_id);
  if (slot == NULL) {
    return lean_io_result_mk_ok(mk_acquire_result(2, 0, (uint32_t)EINVAL));
  }
  const char *cname = lean_string_cstr(name_obj);
  int base_flags = O_RDONLY | O_NOFOLLOW | O_CLOEXEC | O_NONBLOCK;
  int fd = -1;
  for (;;) {
    fd = openat(slot->fd, cname, base_flags);
    if (fd >= 0 || errno != EINTR) {
      break;
    }
  }
  if (fd < 0 && errno == ENOENT && create_if_missing != 0) {
    for (;;) {
      fd = openat(slot->fd, cname, base_flags | O_CREAT, (mode_t)0644);
      if (fd >= 0 || errno != EINTR) {
        break;
      }
    }
  }
  int err = errno;
  dir_slot_release(slot);
  if (fd < 0) {
    if (err == ELOOP || err == ENXIO || err == EMFILE || err == ENFILE) {
      return lean_io_result_mk_ok(mk_acquire_result(2, 0, (uint32_t)EINVAL));
    }
    return lean_io_result_mk_error(lean_decode_io_error(err, name_obj));
  }
  return finish_lock_fd(fd, mode, non_blocking, name_obj);
}

LEAN_EXPORT lean_obj_res leanswe_fs_fresh_temp_nonce(lean_obj_arg w) {
  (void)w;
  uint64_t val = __atomic_fetch_add(&g_temp_nonce, 1, __ATOMIC_RELAXED);
  return lean_io_result_mk_ok(lean_box_uint64(val));
}
