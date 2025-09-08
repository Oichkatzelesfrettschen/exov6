#pragma once

#include <stddef.h>
#include <stdint.h>
#include "exokernel.h"
#include "fs.h"
#include "sleeplock.h"

struct file {
  enum { FD_NONE, FD_CAP } type;
  size_t ref; // reference count
  char readable;
  char writable;
  struct exo_blockcap cap; // backing storage capability
  size_t off;
  size_t *sizep;           // pointer to shared file length
};

// in-memory copy of an inode
struct inode {
  uint32_t dev;              // Device number
  uint32_t inum;             // Inode number
  size_t ref;            // Reference count
  struct sleeplock lock; // protects everything below here
  int valid;             // inode has been read from disk?

  short type; // copy of disk inode
  short major;
  short minor;
  short nlink;
  size_t size;
  uint32_t addrs[NDIRECT + 1];
};

// table mapping major device number to
// device functions
struct devsw {
  int (*read)(struct inode *, char *, size_t);
  int (*write)(struct inode *, char *, size_t);
};

extern struct devsw devsw[];

#define CONSOLE 1

#include <sys/stat.h>

void fileinit(void);
struct file *filealloc(void);
struct file *filedup(struct file *f);
void fileclose(struct file *f);
int filestat(struct file *f, struct stat *st);
int fileread(struct file *f, char *addr, size_t n);
int filewrite(struct file *f, char *addr, size_t n);
