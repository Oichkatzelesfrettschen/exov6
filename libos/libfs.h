#pragma once
<<<<<<< HEAD
#include "fs.h"
#include "file.h"

int fs_read_block(struct exo_blockcap cap, void *dst);
int fs_write_block(struct exo_blockcap cap, const void *src);
=======
#include "file.h"
#include "fs.h"
#include "include/exokernel.h"

int fs_read_block(struct exo_blockcap cap, void *dst);
int fs_write_block(struct exo_blockcap cap, const void *src);
int fs_alloc_block(uint32_t dev, uint32_t rights, struct exo_blockcap *cap);
int fs_bind_block(struct exo_blockcap *cap, void *data, int write);
void libfs_init(void);
struct file *libfs_open(const char *path, int flags);
int libfs_read(struct file *f, void *buf, size_t n);
int libfs_write(struct file *f, const void *buf, size_t n);
void libfs_close(struct file *f);
int libfs_unlink(const char *path);
int libfs_rename(const char *oldpath, const char *newpath);
int libfs_truncate(struct file *f, size_t length);
>>>>>>> origin/feature/epoch-cache-design-progress
