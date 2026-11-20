#include "fd_box.h"

static lean_external_class *g_leanswe_fd_class = NULL;
static pthread_once_t g_leanswe_fd_class_once = PTHREAD_ONCE_INIT;

static void leanswe_fd_box_finalize(void *ptr) {
  int saved = errno;
  LeanFdBox *box = (LeanFdBox *)ptr;
  if (box != NULL) {
    if (!box->closed && box->fd >= 0) {
      close(box->fd);
      box->fd = -1;
      box->closed = 1;
    }
    pthread_mutex_destroy(&box->mu);
    free(box);
  }
  errno = saved;
}

static void leanswe_fd_box_foreach(void *ptr, b_lean_obj_arg f) {
  (void)ptr;
  (void)f;
}

static void leanswe_init_fd_class(void) {
  g_leanswe_fd_class = lean_register_external_class(
      leanswe_fd_box_finalize, leanswe_fd_box_foreach);
}

__attribute__((weak)) LEAN_EXPORT lean_external_class *leanswe_get_fd_class(void) {
  pthread_once(&g_leanswe_fd_class_once, leanswe_init_fd_class);
  return g_leanswe_fd_class;
}
