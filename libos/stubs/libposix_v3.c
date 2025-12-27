#include "libos/posix.h"
#include <arpa/inet.h>
#include <fcntl.h>
#include <signal.h>
#include <stdlib.h>
#include <string.h>
#include <sys/mman.h>
#include <sys/socket.h>
#include <sys/stat.h>
#include <sys/types.h>
#include <unistd.h>

/* Host-backed implementation of the libOS POSIX wrappers. */

/* File operations */
int libos_open(const char *path, int flags, int mode) { return open(path, flags, mode); }
int libos_read(int fd, void *buf, size_t n) { return (int)read(fd, buf, n); }
int libos_write(int fd, const void *buf, size_t n) { return (int)write(fd, buf, n); }
int libos_close(int fd) { return close(fd); }

/* Process control */
int libos_spawn(const char *path, char *const argv[]) {
  int pid = fork();
  if (pid == 0) {
    execv(path, argv);
    _exit(1);
  }
  return pid;
}
int libos_execve(const char *path, char *const argv[], char *const envp[]) { return execve(path, argv, envp); }
int libos_mkdir(const char *path) { return mkdir(path, 0777); }
int libos_rmdir(const char *path) { return rmdir(path); }

/* Signals */
int libos_signal(int sig, void (*handler)(int)) {
  return (signal(sig, handler) == SIG_ERR) ? -1 : 0;
}
int libos_dup(int fd) { return dup(fd); }
int libos_pipe(int fd[2]) { return pipe(fd); }
int libos_fork(void) { return fork(); }
int libos_waitpid(int pid, int *status, int flags) { return waitpid(pid, status, flags); }
int libos_sigsend(int pid, int sig) { return kill(pid, sig); }
int libos_sigcheck(void) { return 0; }
int libos_sigaction(int sig, const struct sigaction *act, struct sigaction *oact) { return sigaction(sig, act, oact); }

static libos_sigset_t cur_mask;
int libos_sigprocmask(int how, const libos_sigset_t *set, libos_sigset_t *old) {
  if (old)
    *old = cur_mask;
  if (!set)
    return 0;
  switch (how) {
  case 0:
    cur_mask |= *set;
    break; /* SIG_BLOCK */
  case 1:
    cur_mask &= ~(*set);
    break; /* SIG_UNBLOCK */
  case 2:
    cur_mask = *set;
    break; /* SIG_SETMASK */
  default:
    return -1;
  }
  return 0;
}
int libos_killpg(int pgrp, int sig) { return killpg(pgrp, sig); }

/* File helpers */
int libos_stat(const char *path, struct stat *st) { return stat(path, st); }
long libos_lseek(int fd, long off, int whence) { return (long)lseek(fd, off, whence); }
int libos_ftruncate(int fd, long length) { return ftruncate(fd, length); }
void *libos_mmap(void *addr, size_t len, int prot, int flags, int fd, long off) {
  return mmap(addr, len, prot, flags, fd, off);
}
int libos_munmap(void *addr, size_t len) { return munmap(addr, len); }

/* Signal set utilities */
int libos_sigemptyset(libos_sigset_t *set) {
  *set = 0;
  return 0;
}
int libos_sigfillset(libos_sigset_t *set) {
  *set = ~0UL;
  return 0;
}
int libos_sigaddset(libos_sigset_t *set, int sig) {
  if (sig < 0 || sig >= 32)
    return -1;
  *set |= (1UL << sig);
  return 0;
}
int libos_sigdelset(libos_sigset_t *set, int sig) {
  if (sig < 0 || sig >= 32)
    return -1;
  *set &= ~(1UL << sig);
  return 0;
}
int libos_sigismember(const libos_sigset_t *set, int sig) {
  if (sig < 0 || sig >= 32)
    return 0;
  return (*set & (1UL << sig)) != 0;
}

/* Process groups */
int libos_getpgrp(void) { return (int)getpgrp(); }
int libos_setpgid(int pid, int pgid) { return setpgid(pid, pgid); }

/* Socket helpers */
int libos_socket(int domain, int type, int protocol) { return socket(domain, type, protocol); }
int libos_bind(int fd, const struct sockaddr *addr, socklen_t len) { return bind(fd, addr, len); }
int libos_listen(int fd, int backlog) { return listen(fd, backlog); }
int libos_accept(int fd, struct sockaddr *addr, socklen_t *len) { return accept(fd, addr, len); }
int libos_connect(int fd, const struct sockaddr *addr, socklen_t len) { return connect(fd, addr, len); }
long libos_send(int fd, const void *buf, size_t len, int flags) { return send(fd, buf, len, flags); }
long libos_recv(int fd, void *buf, size_t len, int flags) { return recv(fd, buf, len, flags); }

int libos_rename(const char *oldpath, const char *newpath) { return rename(oldpath, newpath); }
int libos_unlink(const char *path) { return unlink(path); }

/* Environment utilities */
int libos_setenv(const char *name, const char *value) { return setenv(name, value, 1); }
const char *libos_getenv(const char *name) { return getenv(name); }
int libos_chdir(const char *path) { return chdir(path); }
char *libos_getcwd(char *buf, size_t size) { return getcwd(buf, size); }

/* IPC helpers remain unimplemented on the host */
int libos_msgq_send(exo_cap dest, const void *buf, size_t len) {
  (void)dest;
  (void)buf;
  (void)len;
  return -1;
}
int libos_msgq_recv(exo_cap src, void *buf, size_t len) {
  (void)src;
  (void)buf;
  (void)len;
  return -1;
}
int libos_sem_post(exo_cap sem) {
  (void)sem;
  return -1;
}
int libos_sem_wait(exo_cap sem) {
  (void)sem;
  return -1;
}
exo_cap libos_shm_alloc(void) {
  exo_cap c = {0};
  return c;
}
int libos_shm_free(exo_cap cap) {
  (void)cap;
  return 0;
}

