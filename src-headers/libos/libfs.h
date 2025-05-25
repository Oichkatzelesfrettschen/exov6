#pragma once
#include "file.h"
#include "fs.h"
#include "include/exokernel.h"

int fs_read_block(struct exo_blockcap cap, void *dst);
int fs_write_block(struct exo_blockcap cap, const void *src);
int fs_alloc_block(uint32_t dev, uint32_t rights, struct exo_blockcap *cap);
int fs_bind_block(struct exo_blockcap *cap, void *data, int write);
void libfs_init(void);
int libfs_mkfifo(const char *path, int mode);
struct file *libfs_open(const char *path, int flags);
int libfs_read(struct file *f, void *buf, size_t n);
int libfs_write(struct file *f, const void *buf, size_t n);
void libfs_close(struct file *f);
