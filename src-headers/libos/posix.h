#pragma once
#ifdef __cplusplus
extern "C" {
#endif
#include "types.h"

int libos_open(const char *path, int flags);
int libos_read(int fd, void *buf, size_t n);
int libos_write(int fd, const void *buf, size_t n);
int libos_close(int fd);
int libos_spawn(const char *path, char *const argv[]);
int libos_execve(const char *path, char *const argv[]);
int libos_mkdir(const char *path);
int libos_rmdir(const char *path);
int libos_signal(int sig, void (*handler)(int));
int libos_dup(int fd);
int libos_pipe(int fd[2]);
int libos_fork(void);
int libos_waitpid(int pid);
int libos_sigsend(int pid, int sig);
int libos_sigcheck(void);
#ifdef __cplusplus
}
#endif
