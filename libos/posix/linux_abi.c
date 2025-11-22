#include <stdint.h>
#include <stddef.h>
#include <errno.h>
#include "linux_compat.h"

/* Extern declarations for LibOS POSIX functions */
extern int libos_open(const char *path, int flags, int mode);
extern int libos_close(int fd);
extern int libos_read(int fd, void *buf, size_t count);
extern int libos_write(int fd, const void *buf, size_t count);
extern long libos_lseek(int fd, long offset, int whence);
extern int libos_stat(const char *path, void *st);
extern int libos_mkdir(const char *path);
extern int libos_rmdir(const char *path);
extern int libos_unlink(const char *path);
extern int libos_rename(const char *oldpath, const char *newpath);
extern int libos_getpid(void);
extern int libos_fork(void);
extern int libos_execve(const char *path, char *const argv[], char *const envp[]);
extern void libos_exit(int status);
extern int libos_waitpid(int pid, int *status, int flags);
extern void *libos_mmap(void *addr, size_t length, int prot, int flags, int fd, long offset);
extern int libos_munmap(void *addr, size_t length);
extern int libos_socket(int domain, int type, int protocol);
extern int libos_bind(int fd, const void *addr, int len);
extern int libos_connect(int fd, const void *addr, int len);
extern int libos_listen(int fd, int backlog);
extern int libos_accept(int fd, void *addr, int *len);
extern int libos_send(int fd, const void *buf, size_t len, int flags);
extern int libos_recv(int fd, void *buf, size_t len, int flags);
extern long libos_sendto(int fd, const void *buf, size_t len, int flags, const void *dest_addr, int addrlen);
extern long libos_recvfrom(int fd, void *buf, size_t len, int flags, void *src_addr, int *addrlen);
extern int libos_chdir(const char *path);
extern char *libos_getcwd(char *buf, size_t size);

/* Stub implementations */
static int libos_brk(void *addr) {
    (void)addr;
    return -ENOMEM; /* TODO: Implement brk */
}

static int libos_ioctl(int fd, unsigned long request, ...) {
    (void)fd; (void)request;
    return -EINVAL; /* Stub */
}

/* Central Linux Syscall Dispatcher */
long linux_syscall_dispatch(long sysno, long a1, long a2, long a3, long a4, long a5, long a6) {
    switch (sysno) {
        case LINUX_SYS_read:
            return libos_read((int)a1, (void *)a2, (size_t)a3);
        case LINUX_SYS_write:
            return libos_write((int)a1, (const void *)a2, (size_t)a3);
        case LINUX_SYS_open:
            return libos_open((const char *)a1, (int)a2, (int)a3);
        case LINUX_SYS_close:
            return libos_close((int)a1);
        case LINUX_SYS_lseek:
            return libos_lseek((int)a1, a2, (int)a3);
        case LINUX_SYS_mmap:
            /* Note: Linux mmap has 6 args. a4=flags, a5=fd, a6=off */
            return (long)libos_mmap((void *)a1, (size_t)a2, (int)a3, (int)a4, (int)a5, a6);
        case LINUX_SYS_munmap:
            return libos_munmap((void *)a1, (size_t)a2);
        case LINUX_SYS_brk:
            return libos_brk((void *)a1);
        case LINUX_SYS_ioctl:
            return libos_ioctl((int)a1, (unsigned long)a2, a3);
        case LINUX_SYS_stat:
            return libos_stat((const char *)a1, (void *)a2);
        case LINUX_SYS_getpid:
            return libos_getpid();
        case LINUX_SYS_fork:
            return libos_fork();
        case LINUX_SYS_execve:
            return libos_execve((const char *)a1, (char *const *)a2, (char *const *)a3);
        case LINUX_SYS_exit:
            libos_exit((int)a1);
            return 0; /* Should not return */
        case LINUX_SYS_wait4:
            return libos_waitpid((int)a1, (int *)a2, (int)a3);
        case LINUX_SYS_mkdir:
            return libos_mkdir((const char *)a1);
        case LINUX_SYS_rmdir:
            return libos_rmdir((const char *)a1);
        case LINUX_SYS_unlink:
            return libos_unlink((const char *)a1);
        case LINUX_SYS_rename:
            return libos_rename((const char *)a1, (const char *)a2);
        case LINUX_SYS_getcwd:
            return (long)libos_getcwd((char *)a1, (size_t)a2);
        case LINUX_SYS_chdir:
            return libos_chdir((const char *)a1);

        case LINUX_SYS_sched_setscheduler:
            return 0; // Stub: Success
        case LINUX_SYS_sched_getparam:
            return 0; // Stub: Success
        case LINUX_SYS_sched_getscheduler:
            return 0; // Stub: SCHED_OTHER

        /* Networking */
        case LINUX_SYS_socket:
            return libos_socket((int)a1, (int)a2, (int)a3);
        case LINUX_SYS_bind:
            return libos_bind((int)a1, (const void *)a2, (int)a3);
        case LINUX_SYS_listen:
            return libos_listen((int)a1, (int)a2);
        case LINUX_SYS_accept:
            return libos_accept((int)a1, (void *)a2, (int *)a3);
        case LINUX_SYS_connect:
            return libos_connect((int)a1, (const void *)a2, (int)a3);
        /* Note: send/recv in Linux are often via socketcall or sendto/recvfrom.
           But assuming direct syscalls exist or mapped: */
        case LINUX_SYS_sendto:
            return libos_sendto((int)a1, (const void *)a2, (size_t)a3, (int)a4, (const void *)a5, (int)a6);
        case LINUX_SYS_recvfrom:
            return libos_recvfrom((int)a1, (void *)a2, (size_t)a3, (int)a4, (void *)a5, (int *)a6);

        default:
            return -ENOSYS;
    }
}
