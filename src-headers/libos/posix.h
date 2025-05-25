#pragma once
#include "types.h"
#include <stddef.h>

int libos_open(const char *path, int flags);
int libos_read(int fd, void *buf, size_t n);
int libos_write(int fd, const void *buf, size_t n);
int libos_close(int fd);
int libos_spawn(const char *path, char *const argv[]);
int libos_execve(const char *path, char *const argv[]);
int libos_mkdir(const char *path);
int libos_rmdir(const char *path);
int libos_signal(int sig, void (*handler)(int));

typedef unsigned long libos_sigset_t;

struct libos_sigaction {
    void (*sa_handler)(int);
    libos_sigset_t sa_mask;
    int sa_flags;
};

int libos_sigaction(int sig, const struct libos_sigaction *act,
                    struct libos_sigaction *old);
int libos_dup(int fd);
int libos_pipe(int fd[2]);
int libos_fork(void);
int libos_waitpid(int pid);
int libos_sigsend(int pid, int sig);
int libos_sigcheck(void);

/* Additional POSIX helpers */
struct stat;

int libos_stat(const char *path, struct stat *st);
long libos_lseek(int fd, long off, int whence);
int libos_ftruncate(int fd, long length);
void *libos_mmap(void *addr, size_t len, int prot, int flags, int fd, long off);
int libos_munmap(void *addr, size_t len);

int libos_sigemptyset(libos_sigset_t *set);
int libos_sigfillset(libos_sigset_t *set);
int libos_sigaddset(libos_sigset_t *set, int sig);
int libos_sigdelset(libos_sigset_t *set, int sig);
int libos_sigismember(const libos_sigset_t *set, int sig);
int libos_sigprocmask(int how, const libos_sigset_t *set, libos_sigset_t *old);

int libos_getpgrp(void);
int libos_setpgid(int pid, int pgid);
int libos_killpg(int pgid, int sig);

struct sockaddr;
typedef unsigned socklen_t;
int libos_socket(int domain, int type, int protocol);
int libos_bind(int fd, const struct sockaddr *addr, socklen_t len);
int libos_listen(int fd, int backlog);
int libos_accept(int fd, struct sockaddr *addr, socklen_t *len);
int libos_connect(int fd, const struct sockaddr *addr, socklen_t len);
long libos_send(int fd, const void *buf, size_t len, int flags);
long libos_recv(int fd, void *buf, size_t len, int flags);
