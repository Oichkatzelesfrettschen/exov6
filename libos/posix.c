#include "posix.h"
#include "file.h"
#include "libfs.h"
#include "string.h"
#include "user.h"
#include "signal.h"

#define LIBOS_MAXFD 16

static struct file *fd_table[LIBOS_MAXFD];
static void (*sig_handlers[32])(int);

int libos_open(const char *path, int flags) {
    struct file *f = libfs_open(path, flags);
    if(!f)
        return -1;
    for(int i = 0; i < LIBOS_MAXFD; i++) {
        if(!fd_table[i]) {
            fd_table[i] = f;
            return i;
        }
    }
    fileclose(f);
    return -1;
}

int libos_read(int fd, void *buf, size_t n) {
    if(fd < 0 || fd >= LIBOS_MAXFD || !fd_table[fd])
        return -1;
    return libfs_read(fd_table[fd], buf, n);
}

int libos_write(int fd, const void *buf, size_t n) {
    if(fd < 0 || fd >= LIBOS_MAXFD || !fd_table[fd])
        return -1;
    return libfs_write(fd_table[fd], buf, n);
}

int libos_close(int fd) {
    if(fd < 0 || fd >= LIBOS_MAXFD || !fd_table[fd])
        return -1;
    libfs_close(fd_table[fd]);
    fd_table[fd] = 0;
    return 0;
}

int libos_spawn(const char *path, char *const argv[]) {
    int pid = fork();
    if(pid == 0) {
        exec((char *)path, (char **)argv);
        exit();
    }
    return pid;
}

int libos_execve(const char *path, char *const argv[]) {
    return exec((char *)path, (char **)argv);
}

int libos_mkdir(const char *path) {
    return mkdir((char *)path);
}

int libos_rmdir(const char *path) {
    return unlink((char *)path);
}

int libos_dup(int fd) {
    if(fd < 0 || fd >= LIBOS_MAXFD || !fd_table[fd])
        return -1;
    struct file *f = filedup(fd_table[fd]);
    for(int i = 0; i < LIBOS_MAXFD; i++) {
        if(!fd_table[i]) {
            fd_table[i] = f;
            return i;
        }
    }
    fileclose(f);
    return -1;
}

int libos_pipe(int fd[2]) {
    return pipe(fd);
}

int libos_fork(void) {
    return fork();
}

int libos_waitpid(int pid) {
    int w;
    while((w = wait()) >= 0) {
        if(w == pid)
            return w;
    }
    return -1;
}

int libos_sigsend(int pid, int sig) {
    return sigsend(pid, sig);
}

int libos_sigcheck(void) {
    int pending = sigcheck();
    for(int s = 0; s < 32; s++) {
        if((pending & (1<<s)) && sig_handlers[s])
            sig_handlers[s](s);
    }
    return pending;
}

int libos_signal(int sig, void (*handler)(int)) {
    if(sig < 0 || sig >= 32)
        return -1;
    sig_handlers[sig] = handler;
    return 0;
}
