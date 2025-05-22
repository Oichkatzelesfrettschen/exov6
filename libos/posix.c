#include "posix.h"
#include "file.h"
#include "libfs.h"
#include "string.h"
#include "user.h"

#define LIBOS_MAXFD 16
#define LIBOS_MAXFILES 8

static struct file *fd_table[LIBOS_MAXFD];

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

int libos_fstat(int fd, struct stat *st) {
    if(fd < 0 || fd >= LIBOS_MAXFD || !fd_table[fd])
        return -1;
    return filestat(fd_table[fd], st);
}

int libos_stat(const char *path, struct stat *st) {
    int fd = libos_open(path, 0);
    if(fd < 0)
        return -1;
    int r = libos_fstat(fd, st);
    libos_close(fd);
    return r;
}

int libos_unlink(const char *path) {
    struct vfile *vf = lookup_vfile(path);
    if(!vf)
        return -1;
    vf->used = 0;
    // close descriptors referring to this vfile
    for(int i = 0; i < LIBOS_MAXFD; i++) {
        if(fd_table[i] && fd_table[i]->cap.id == vf->cap.id) {
            fileclose(fd_table[i]);
            fd_table[i] = 0;
        }
    }
    return 0;
}

int libos_lseek(int fd, size_t off, int whence) {
    if(fd < 0 || fd >= LIBOS_MAXFD || !fd_table[fd])
        return -1;
    struct file *f = fd_table[fd];
    size_t newoff;
    switch(whence) {
    case 0: // SEEK_SET
        newoff = off;
        break;
    case 1: // SEEK_CUR
        newoff = f->off + off;
        break;
    case 2: {
        struct stat st;
        if(libos_fstat(fd, &st) < 0)
            return -1;
        newoff = st.size + off;
        break;
    }
    default:
        return -1;
    }
    f->off = newoff;
    return newoff;
}
