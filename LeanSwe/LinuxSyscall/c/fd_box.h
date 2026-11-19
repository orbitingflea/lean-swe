#ifndef LEANSWE_LINUX_FD_BOX_H
#define LEANSWE_LINUX_FD_BOX_H

#include <errno.h>
#include <pthread.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>
#include <lean/lean.h>

typedef struct {
  pthread_mutex_t mu;
  int fd;
  uint32_t in_use;
  uint8_t closed;
} LeanFdBox;

extern lean_external_class *leanswe_get_fd_class(void);

static inline lean_obj_res leanswe_mk_fd_obj(int fd) {
  LeanFdBox *box = (LeanFdBox *)malloc(sizeof(LeanFdBox));
  if (box == NULL) {
    close(fd);
    return NULL;
  }
  pthread_mutex_init(&box->mu, NULL);
  box->fd = fd;
  box->in_use = 0;
  box->closed = 0;
  return lean_alloc_external(leanswe_get_fd_class(), box);
}

static inline int leanswe_fd_box_pin(LeanFdBox *box, int *out_fd) {
  pthread_mutex_lock(&box->mu);
  if (box->closed || box->fd < 0) {
    pthread_mutex_unlock(&box->mu);
    return EBADF;
  }
  box->in_use++;
  *out_fd = box->fd;
  pthread_mutex_unlock(&box->mu);
  return 0;
}

static inline void leanswe_fd_box_unpin(LeanFdBox *box) {
  pthread_mutex_lock(&box->mu);
  if (box->in_use > 0) {
    box->in_use--;
  }
  pthread_mutex_unlock(&box->mu);
}

static inline int leanswe_fd_box_close(LeanFdBox *box) {
  pthread_mutex_lock(&box->mu);
  if (box->closed || box->fd < 0) {
    pthread_mutex_unlock(&box->mu);
    return EBADF;
  }
  if (box->in_use > 0) {
    pthread_mutex_unlock(&box->mu);
    return EBUSY;
  }
  int fd = box->fd;
  box->fd = -1;
  box->closed = 1;
  pthread_mutex_unlock(&box->mu);
  if (close(fd) < 0) {
    return errno;
  }
  return 0;
}

static inline void leanswe_abort_on_efault(int err) {
  if (__builtin_expect(err == EFAULT, 0)) {
    abort();
  }
}

static inline lean_obj_res leanswe_mk_ok(lean_obj_res val) {
  lean_obj_res r = lean_alloc_ctor(1, 1, 0);
  lean_ctor_set(r, 0, val);
  return lean_io_result_mk_ok(r);
}

static inline lean_obj_res leanswe_mk_errno(int err) {
  leanswe_abort_on_efault(err);
  lean_obj_res r = lean_alloc_ctor(0, 1, 0);
  lean_ctor_set(r, 0, lean_box_uint32((uint32_t)err));
  return lean_io_result_mk_ok(r);
}

#endif
