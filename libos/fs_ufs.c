#include "libfs.h"
#include "string.h"
#include "stdlib.h"
#include "file.h"

#define MAX_VFILES 16

struct vfile {
    char path[32];
    int used;
    int type; /* 0=file, 1=fifo */
    struct exo_blockcap cap;
    struct fifo *fifo;
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
            vfiles[i].type = 0;
            vfiles[i].fifo = 0;
            return &vfiles[i];
        }
    }
    return 0;
}

static struct vfile *create_fifo(const char *path) {
    for(int i=0;i<MAX_VFILES;i++) {
        if(!vfiles[i].used) {
            struct fifo *q = malloc(sizeof(struct fifo));
            if(!q)
                return 0;
            if(fs_alloc_block(1, EXO_RIGHT_R|EXO_RIGHT_W, &q->cap) < 0){
                free(q);
                return 0;
            }
            q->rpos = q->wpos = 0;
            strncpy(vfiles[i].path, path, sizeof(vfiles[i].path)-1);
            vfiles[i].path[sizeof(vfiles[i].path)-1] = '\0';
            vfiles[i].used = 1;
            vfiles[i].type = 1;
            vfiles[i].fifo = q;
            return &vfiles[i];
        }
    }
    return 0;
}

void libfs_init(void) {
    memset(vfiles, 0, sizeof(vfiles));
}

int libfs_mkfifo(const char *path, int mode){
    (void)mode;
    if(lookup_vfile(path))
        return -1;
    return create_fifo(path) ? 0 : -1;
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
    f->readable = 1;
    f->writable = 1;
    if(vf->type == 1){
        f->type = FD_FIFO;
        f->fifo = vf->fifo;
    } else {
        f->type = FD_CAP;
        f->cap = vf->cap;
        f->off = 0;
    }
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

