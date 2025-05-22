#pragma once
#include "types.h"

#define SEEK_SET 0
#define SEEK_CUR 1
#define SEEK_END 2

int libos_open(const char *path, int flags);
int libos_read(int fd, void *buf, size_t n);
int libos_write(int fd, const void *buf, size_t n);
int libos_close(int fd);
int libos_spawn(const char *path, char *const argv[]);
int libos_fstat(int fd, struct stat *st);
int libos_stat(const char *path, struct stat *st);
int libos_unlink(const char *path);
int libos_lseek(int fd, size_t off, int whence);
