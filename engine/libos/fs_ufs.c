#include "libfs.h"
#include "string.h"
#include "stdlib.h"

#define MAX_VFILES 16

struct vfile {
    char path[32];
    int used;
    size_t size;
    struct exo_blockcap cap;
};

static struct vfile vfiles[MAX_VFILES];

static struct vfile *lookup_vfile(const char *path) {
    for(int i=0;i<MAX_VFILES;i++)
        if(vfiles[i].used && strcmp(vfiles[i].path, path)==0)
            return &vfiles[i];
    return 0;
}

static struct vfile *create_vfile(const char *path) {
    for(int i=0;i<MAX_VFILES;i++) {
        if(!vfiles[i].used) {
            if(fs_alloc_block(1, EXO_RIGHT_R|EXO_RIGHT_W, &vfiles[i].cap) < 0)
                return 0;
            strncpy(vfiles[i].path, path, sizeof(vfiles[i].path)-1);
            vfiles[i].path[sizeof(vfiles[i].path)-1] = '\0';
            vfiles[i].size = 0;
            vfiles[i].used = 1;
            return &vfiles[i];
        }
    }
    return 0;
}

void libfs_init(void) {
    memset(vfiles, 0, sizeof(vfiles));
}

struct file *libfs_open(const char *path, int flags) {
    (void)flags;
    struct vfile *vf = lookup_vfile(path);
    if(!vf)
        vf = create_vfile(path);
    if(!vf)
        return 0;
    struct file *f = filealloc();
    if(!f)
        return 0;
    f->cap = vf->cap;
    f->sizep = &vf->size;
    f->readable = 1;
    f->writable = 1;
    f->off = 0;
    return f;
}

int libfs_read(struct file *f, void *buf, size_t n) {
    return fileread(f, buf, n);
}

int libfs_write(struct file *f, const void *buf, size_t n) {
    int r = filewrite(f, (char*)buf, n);
    if(r > 0 && f->sizep && f->off > *f->sizep)
        *f->sizep = f->off;
    return r;
}

void libfs_close(struct file *f) {
    fileclose(f);
}

int libfs_unlink(const char *path) {
    struct vfile *vf = lookup_vfile(path);
    if(!vf)
        return -1;
    vf->used = 0;
    vf->size = 0;
    return 0;
}

int libfs_rename(const char *oldpath, const char *newpath) {
    struct vfile *vf = lookup_vfile(oldpath);
    if(!vf)
        return -1;
    struct vfile *dst = lookup_vfile(newpath);
    if(dst)
        dst->used = 0;
    strncpy(vf->path, newpath, sizeof(vf->path)-1);
    vf->path[sizeof(vf->path)-1] = '\0';
    return 0;
}

int libfs_truncate(struct file *f, size_t length){
    if(!f || !f->sizep)
        return -1;
    if(length > BSIZE)
        length = BSIZE;
    *f->sizep = length;
    if(f->off > length)
        f->off = length;
    if(length == 0){
        char zero[BSIZE] = {0};
        fs_write_block(f->cap, zero);
    }
    return 0;
}

