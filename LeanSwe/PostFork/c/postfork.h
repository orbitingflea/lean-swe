#ifndef LEANSWE_POSTFORK_H
#define LEANSWE_POSTFORK_H

#include <stddef.h>
#include <stdint.h>

#define LEANSWE_PF_FLAG_SET_PGID 1u
#define LEANSWE_PF_FLAG_RESET_SIGPIPE 2u
#define LEANSWE_PF_FLAG_HAS_SYNC_BARRIER 4u
#define LEANSWE_PF_FLAG_REDIRECT_STDIO 8u
#define LEANSWE_PF_FLAG_CLOSE_UNKEPT_ABOVE2 16u
#define LEANSWE_PF_FLAG_CLOSE_STDIO_SOURCES 32u

#define LEANSWE_PF_STAGE_VALIDATE 1
#define LEANSWE_PF_STAGE_PROCESS_GROUP 2
#define LEANSWE_PF_STAGE_SIGNAL_RESET 3
#define LEANSWE_PF_STAGE_FD_SETUP 4
#define LEANSWE_PF_STAGE_CLOSE_UNKEPT 5
#define LEANSWE_PF_STAGE_CHDIR 6
#define LEANSWE_PF_STAGE_EXECVE 7

typedef struct LeanswePostForkChildArgs {
  uint32_t flags;
  int32_t sync_r;
  int32_t stdin_fd;
  int32_t stdout_fd;
  int32_t stderr_fd;
  int32_t rep_w;
  const int32_t *close_fds;
  size_t n_close_fds;
  const int32_t *keep_fds;
  size_t n_keep_fds;
  const char *cwd;
  const char *path;
  const char *const *argv;
  const char *const *envp;
} LeanswePostForkChildArgs;

void leanswe_postfork_run_child(const LeanswePostForkChildArgs *args);
int32_t leanswe_postfork_close_fds_above2_except(
    int32_t extra_keep_fd,
    const int32_t *keep_fds,
    size_t n_keep_fds);

#endif
