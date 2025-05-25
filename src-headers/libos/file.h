#pragma once

#include "include/exokernel.h"

struct fifo {
  char data[512];
  size_t rpos;
  size_t wpos;
  struct exo_blockcap cap;
};

struct file {
  enum { FD_NONE, FD_CAP, FD_FIFO } type;
  size_t ref; // reference count
  char readable;
  char writable;
  struct exo_blockcap cap; // backing storage capability for regular files
  struct fifo *fifo;        // for FIFO files
  size_t off;
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
