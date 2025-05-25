#include "libfs.h"
#include "string.h"
#include "stdlib.h"
#include "fcntl.h"
#include "include/exokernel.h"

#define MAX_VFILES 16
#define VF_READ  0x1
#define VF_WRITE 0x2

struct vfile {
    char path[32];
    int used;
    unsigned perm; /* simple read/write permission bits */
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
            vfiles[i].perm = VF_READ|VF_WRITE;
            return &vfiles[i];
        }
    }
    return 0;
}

void libfs_init(void) {
    memset(vfiles, 0, sizeof(vfiles));
}

struct file *libfs_open(const char *path, int flags) {
    struct vfile *vf = lookup_vfile(path);
    if(!vf) {
        if(!(flags & O_CREATE))
            return 0;
        vf = create_vfile(path);
    }
    if(!vf)
        return 0;
    int want_r = (flags & O_WRONLY) ? 0 : 1;
    if(flags & O_RDWR)
        want_r = 1;
    int want_w = (flags & O_WRONLY) || (flags & O_RDWR);
    if((want_r && !(vf->perm & VF_READ)) || (want_w && !(vf->perm & VF_WRITE)))
        return 0;

    struct file *f = filealloc();
    if(!f)
        return 0;
    f->cap = vf->cap;
    f->readable = want_r;
    f->writable = want_w;
    f->off = 0;
    return f;
}

int libfs_read(struct file *f, void *buf, size_t n) {
    if(!cap_has_rights(f->cap.rights, EXO_RIGHT_R))
        return -1;
    return fileread(f, buf, n);
}

int libfs_write(struct file *f, const void *buf, size_t n) {
    if(!cap_has_rights(f->cap.rights, EXO_RIGHT_W))
        return -1;
    return filewrite(f, (char*)buf, n);
}

void libfs_close(struct file *f) {
    fileclose(f);
}

