#pragma once

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
  short major;
  short minor;
  short nlink;
  size_t size;
  uint addrs[NDIRECT+1];
};

// table mapping major device number to
// device functions
struct devsw {
  int (*read)(struct inode*, char*, size_t);
  int (*write)(struct inode*, char*, size_t);
};

extern struct devsw devsw[];

#define CONSOLE 1
