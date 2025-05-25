#include "libfs.h"
#include "string.h"
#include "stdlib.h"

#define MAX_VFILES 16

struct vfile {
    char path[32];
    int used;
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
    f->readable = 1;
    f->writable = 1;
    f->off = 0;
    return f;
}

int libfs_read(struct file *f, void *buf, size_t n) {
    return fileread(f, buf, n);
}

int libfs_write(struct file *f, const void *buf, size_t n) {
    return filewrite(f, (char*)buf, n);
}

void libfs_close(struct file *f) {
    fileclose(f);
}

