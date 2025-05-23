#include "posix.h"
#include "file.h"
#include "libfs.h"
#include "string.h"
#include "user.h"
#include "signal.h"

#define LIBOS_MAXFD 16
#define LIBOS_MAXFILES 8

static struct file *fd_table[LIBOS_MAXFD];
static void (*sig_handlers[32])(int);

struct vfile {
    char path[32];
    int used;
    struct exo_blockcap cap;
};

static struct vfile vfiles[LIBOS_MAXFILES];

static struct vfile *lookup_vfile(const char *path) {
    for(int i = 0; i < LIBOS_MAXFILES; i++) {
        if(vfiles[i].used && strcmp(vfiles[i].path, path) == 0)
            return &vfiles[i];
    }
    return 0;
}

static struct vfile *create_vfile(const char *path) {
    for(int i = 0; i < LIBOS_MAXFILES; i++) {
        if(!vfiles[i].used) {
            if(fs_alloc_block(1, EXO_RIGHT_R | EXO_RIGHT_W, &vfiles[i].cap) < 0)
                return 0;
            strncpy(vfiles[i].path, path, sizeof(vfiles[i].path)-1);
            vfiles[i].path[sizeof(vfiles[i].path)-1] = '\0';
            vfiles[i].used = 1;
            return &vfiles[i];
        }
    }
    return 0;
}

int libos_open(const char *path, int flags) {
    (void)flags;
    struct file *f = filealloc();
    if(!f)
        return -1;
    struct vfile *vf = lookup_vfile(path);
    if(!vf)
        vf = create_vfile(path);
    if(!vf) {
        free(f);
        return -1;
    }
    f->cap = vf->cap;
    f->readable = 1;
    f->writable = 1;
    f->off = 0;
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
    return fileread(fd_table[fd], buf, n);
}

int libos_write(int fd, const void *buf, size_t n) {
    if(fd < 0 || fd >= LIBOS_MAXFD || !fd_table[fd])
        return -1;
    return filewrite(fd_table[fd], (char *)buf, n);
}

int libos_close(int fd) {
    if(fd < 0 || fd >= LIBOS_MAXFD || !fd_table[fd])
        return -1;
    fileclose(fd_table[fd]);
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
