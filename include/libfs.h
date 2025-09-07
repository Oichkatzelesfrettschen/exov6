#pragma once
#include "file.h"
#include "fs.h"
#include "exokernel.h"
#include <sys/stat.h>
#include <sys/types.h>

int fs_read_block(struct exo_blockcap cap, void *dst);
int fs_write_block(struct exo_blockcap cap, const void *src);
int fs_alloc_block(uint32_t dev, uint32_t rights, struct exo_blockcap *cap);
int fs_bind_block(struct exo_blockcap *cap, void *data, int write);

// LibFS functions needed by libos
struct file* libfs_open(const char* path, int flags);
int libfs_read(struct file* f, void* buf, size_t count);
int libfs_write(struct file* f, const void* buf, size_t count);
int libfs_truncate(struct file* f, off_t length);
int libfs_close(struct file* f);
int fileclose(struct file* f);  // Legacy alias
int filestat(struct file* f, struct stat* st);
int libfs_unlink(const char* path);
int libfs_rename(const char* oldpath, const char* newpath);
int libfs_mkdir(const char* path);

// Additional stubs
struct file* filedup(struct file* f);
int sigcheck(void);
int sigsend(int pgrp, int sig);

// Pthread capability management
exo_cap pthread_get_scheduler_cap(pthread_t thread);
