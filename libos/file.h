#pragma once

#include <stddef.h>
#include <stdint.h>
#include <sys/stat.h>
#include "exokernel.h"
#include "fs.h"
#include "sleeplock.h"

/* Forward declarations */
struct pipe;

/* File descriptor types */
struct file {
  enum { FD_NONE, FD_PIPE, FD_INODE, FD_CAP } type;
  size_t ref;                    /* Reference count */
  char readable;
  char writable;
  struct pipe *pipe;             /* For pipe files */
  struct inode *ip;              /* For inode files */
  exo_blockcap cap;              /* For capability files */
  size_t off;                    /* Current offset */
  size_t *sizep;                 /* Optional pointer to shared file length */
  int flags;                     /* File flags */
};

/* In-memory copy of an inode */
struct inode {
  uint32_t dev;                  /* Device number */
  uint32_t inum;                 /* Inode number */
  size_t ref;                    /* Reference count */
  struct sleeplock lock;         /* Protects members below */
  int valid;                     /* Inode has been read from disk? */

  /* Copy of disk inode */
  short type;
  short major;
  short minor;
  short nlink;
  uint32_t mode;                 /* File permissions/mode */
  uint32_t uid;                  /* Owner user ID */
  uint32_t gid;                  /* Owner group ID */
  size_t size;
  uint32_t addrs[NDIRECT + 1];
};

/* Device switch table */
struct devsw {
  int (*read)(struct inode *, char *, size_t);
  int (*write)(struct inode *, char *, size_t);
};

extern struct devsw devsw[];

#define CONSOLE 1

/* Basic file API used by libfs and tests */
void fileinit(void);
struct file *filealloc(void);
struct file *filedup(struct file *f);
int fileclose(struct file *f);
int filestat(struct file *f, struct stat *st);
int fileread(struct file *f, char *addr, size_t n);
int filewrite(struct file *f, char *addr, size_t n);