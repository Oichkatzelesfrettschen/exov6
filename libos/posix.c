#include "posix.h"
#include "file.h"
#include "libfs.h"
#include "string.h"
#include "user.h"
#include "signal.h"
#include <stdlib.h>
#include "stat.h"
#include <unistd.h>
#include <sys/socket.h>
#include <fcntl.h>

#define LIBOS_MAXFD 16
#define FIFO_MAX    8
#define FIFO_BUFSZ  512

struct fifo {
    char name[32];
    int used;
    char *buf;
    size_t r, w;
};

struct fd_entry {
    enum { FD_FREE, FD_FILE, FD_FIFO } type;
    union {
        struct file *f;
        struct fifo *fifo;
    } u;
};

static struct fd_entry fd_table[LIBOS_MAXFD];
static struct fifo fifo_table[FIFO_MAX];
static void (*sig_handlers[32])(int);

static int alloc_fd(void) {
    for(int i=0;i<LIBOS_MAXFD;i++)
        if(fd_table[i].type==FD_FREE)
            return i;
    return -1;
}

static struct fifo *lookup_fifo(const char *name) {
    for(int i=0;i<FIFO_MAX;i++)
        if(fifo_table[i].used && strcmp(fifo_table[i].name,name)==0)
            return &fifo_table[i];
    return 0;
}

static struct fifo *create_fifo(const char *name) {
    for(int i=0;i<FIFO_MAX;i++) {
        if(!fifo_table[i].used) {
            struct fifo *f=&fifo_table[i];
            strncpy(f->name,name,sizeof(f->name)-1);
            f->name[sizeof(f->name)-1]='\0';
            f->buf = malloc(FIFO_BUFSZ);
            if(!f->buf)
                return 0;
            f->r=f->w=0;
            f->used=1;
            return f;
        }
    }
    return 0;
}

int libos_open(const char *path, int flags) {
    struct fifo *fifo = lookup_fifo(path);
    int fd = alloc_fd();
    if(fd < 0)
        return -1;
    if(fifo) {
        fd_table[fd].type = FD_FIFO;
        fd_table[fd].u.fifo = fifo;
        return fd;
    }
    struct file *f = libfs_open(path, flags);
    if(!f)
        return -1;
    fd_table[fd].type = FD_FILE;
    fd_table[fd].u.f = f;
    return fd;
}

int libos_read(int fd, void *buf, size_t n) {
    if(fd < 0 || fd >= LIBOS_MAXFD || fd_table[fd].type==FD_FREE)
        return -1;
    if(fd_table[fd].type == FD_FILE)
        return libfs_read(fd_table[fd].u.f, buf, n);
    struct fifo *f = fd_table[fd].u.fifo;
    size_t avail = f->w - f->r;
    if(n > avail) n = avail;
    for(size_t i=0;i<n;i++)
        ((char*)buf)[i] = f->buf[(f->r+i)%FIFO_BUFSZ];
    f->r += n;
    return (int)n;
}

int libos_write(int fd, const void *buf, size_t n) {
    if(fd < 0 || fd >= LIBOS_MAXFD || fd_table[fd].type==FD_FREE)
        return -1;
    if(fd_table[fd].type == FD_FILE)
        return libfs_write(fd_table[fd].u.f, buf, n);
    struct fifo *f = fd_table[fd].u.fifo;
    size_t space = FIFO_BUFSZ - (f->w - f->r);
    if(n > space) n = space;
    for(size_t i=0;i<n;i++)
        f->buf[(f->w+i)%FIFO_BUFSZ] = ((const char*)buf)[i];
    f->w += n;
    return (int)n;
}

int libos_close(int fd) {
    if(fd < 0 || fd >= LIBOS_MAXFD || fd_table[fd].type==FD_FREE)
        return -1;
    if(fd_table[fd].type == FD_FILE)
        libfs_close(fd_table[fd].u.f);
    fd_table[fd].type = FD_FREE;
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
    if(fd < 0 || fd >= LIBOS_MAXFD || fd_table[fd].type==FD_FREE)
        return -1;
    int nfd = alloc_fd();
    if(nfd < 0)
        return -1;
    fd_table[nfd] = fd_table[fd];
    if(fd_table[nfd].type == FD_FILE)
        filedup(fd_table[nfd].u.f);
    return nfd;
}

int libos_pipe(int fd[2]) {
    return pipe(fd);
}

int libos_mkfifo(const char *path, int mode) {
    (void)mode;
    if(lookup_fifo(path))
        return -1;
    return create_fifo(path) ? 0 : -1;
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

int libos_stat(const char *path, struct stat *st) {
    struct file *f = libfs_open(path, 0);
    if(!f)
        return -1;
    int r = filestat(f, st);
    libfs_close(f);
    return r;
}

long libos_lseek(int fd, long off, int whence) {
    if(fd < 0 || fd >= LIBOS_MAXFD || fd_table[fd].type != FD_FILE)
        return -1;
    struct file *f = fd_table[fd].u.f;
    switch(whence){
    case 0: /* SEEK_SET */
        f->off = off;
        break;
    case 1: /* SEEK_CUR */
        f->off += off;
        break;
    case 2: {
        struct stat st;
        if(filestat(f, &st) < 0)
            return -1;
        f->off = st.size + off;
        break;
    }
    default:
        return -1;
    }
    return f->off;
}

int libos_ftruncate(int fd, long length) {
    if(fd < 0 || fd >= LIBOS_MAXFD || fd_table[fd].type != FD_FILE)
        return -1;
    (void)length;
    /* The simple in-memory filesystem ignores size changes. */
    return 0;
}

void *libos_mmap(void *addr, size_t len, int prot, int flags, int fd, long off) {
    (void)addr; (void)prot; (void)flags; (void)fd; (void)off;
    void *p = malloc(len);
    return p ? p : (void*)-1;
}

int libos_munmap(void *addr, size_t len) {
    (void)len;
    free(addr);
    return 0;
}

int libos_sigemptyset(libos_sigset_t *set){ *set = 0; return 0; }
int libos_sigfillset(libos_sigset_t *set){ *set = ~0UL; return 0; }
int libos_sigaddset(libos_sigset_t *set,int sig){ if(sig<0||sig>=32) return -1; *set |= (1UL<<sig); return 0; }
int libos_sigdelset(libos_sigset_t *set,int sig){ if(sig<0||sig>=32) return -1; *set &= ~(1UL<<sig); return 0; }
int libos_sigismember(const libos_sigset_t *set,int sig){ if(sig<0||sig>=32) return 0; return (*set & (1UL<<sig))!=0; }

int libos_getpgrp(void){
    return (int)getpgrp();
}

int libos_setpgid(int pid, int pgid){
    return setpgid(pid, pgid);
}

int libos_socket(int domain, int type, int protocol){
    return socket(domain, type, protocol);
}

int libos_bind(int fd,const struct sockaddr *addr,socklen_t len){
    return bind(fd, addr, len);
}

int libos_listen(int fd,int backlog){
    return listen(fd, backlog);
}

int libos_accept(int fd,struct sockaddr *addr,socklen_t *len){
    return accept(fd, addr, len);
}

int libos_connect(int fd,const struct sockaddr *addr,socklen_t len){
    return connect(fd, addr, len);
}

long libos_send(int fd,const void *buf,size_t len,int flags){
    return send(fd, buf, len, flags);
}

long libos_recv(int fd,void *buf,size_t len,int flags){
    return recv(fd, buf, len, flags);
}
