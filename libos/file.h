#pragma once

<<<<<<< HEAD
struct file {
  enum { FD_NONE, FD_PIPE, FD_INODE } type;
  size_t ref; // reference count
  char readable;
  char writable;
  struct pipe *pipe;
  struct inode *ip;
  size_t off;
};


// in-memory copy of an inode
struct inode {
  uint dev;           // Device number
  uint inum;          // Inode number
  size_t ref;            // Reference count
  struct sleeplock lock; // protects everything below here
  int valid;          // inode has been read from disk?

  short type;         // copy of disk inode
=======
#include <stddef.h>
#include <stdint.h>
#include "include/exokernel.h"
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
>>>>>>> origin/feature/epoch-cache-design-progress
  short major;
  short minor;
  short nlink;
  size_t size;
<<<<<<< HEAD
  uint addrs[NDIRECT+1];
=======
  uint32_t addrs[NDIRECT + 1];
>>>>>>> origin/feature/epoch-cache-design-progress
};

// table mapping major device number to
// device functions
struct devsw {
<<<<<<< HEAD
  int (*read)(struct inode*, char*, size_t);
  int (*write)(struct inode*, char*, size_t);
=======
  int (*read)(struct inode *, char *, size_t);
  int (*write)(struct inode *, char *, size_t);
>>>>>>> origin/feature/epoch-cache-design-progress
};

extern struct devsw devsw[];

#define CONSOLE 1
<<<<<<< HEAD
=======

#include <sys/stat.h>

void fileinit(void);
struct file *filealloc(void);
struct file *filedup(struct file *f);
void fileclose(struct file *f);
int filestat(struct file *f, struct stat *st);
int fileread(struct file *f, char *addr, size_t n);
int filewrite(struct file *f, char *addr, size_t n);
>>>>>>> origin/feature/epoch-cache-design-progress
