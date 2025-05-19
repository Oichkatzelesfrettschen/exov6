#include "types.h"
#include "user.h"
#include "sleeplock.h"
#include "spinlock.h"
#include "fs.h"
#include "file.h"

// Basic wrappers to illustrate linking a user-space filesystem library.

struct file dummy_file;

void fileinit(void) {}

struct file *filealloc(void) {
    return &dummy_file;
}

struct file *filedup(struct file *f) {
    return f;
}

void fileclose(struct file *f) {}

int filestat(struct file *f, struct stat *st) { return fstat(0, st); }

int fileread(struct file *f, char *addr, size_t n) {
    return read(0, addr, n);
}

int filewrite(struct file *f, char *addr, size_t n) {
    return write(0, addr, n);
}
