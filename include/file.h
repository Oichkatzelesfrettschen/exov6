#pragma once

#include <stdint.h>
#include <stddef.h>
#include <sys/stat.h> // For struct stat
#include "fs.h"  // For NDIRECT
#include "exokernel.h"  // For exo_blockcap

// Forward declaration
struct sleeplock;
struct pipe;

struct file {
  enum { FD_NONE, FD_PIPE, FD_INODE, FD_CAP } type;
  size_t ref; // reference count
  char readable;
  char writable;
  struct pipe *pipe;
  struct inode *ip;
  size_t off;
  int flags;
  exo_blockcap cap;     // Exokernel block capability for file operations
  size_t *sizep;        // Pointer to file size (for extending files)
};


// in-memory copy of an inode
struct inode {
  uint32_t dev;           // Device number
  uint32_t inum;          // Inode number
  size_t ref;            // Reference count
  struct sleeplock* lock; // protects everything below here (using pointer for forward decl)
  int valid;          // inode has been read from disk?

  short type;         // copy of disk inode
  short major;
  short minor;
  short nlink;
  uint32_t mode;      // File permissions/mode
  uint32_t uid;       // Owner user ID
  uint32_t gid;       // Owner group ID
  size_t size;
  uint32_t addrs[NDIRECT+1];
};
// Must match on-disk inode layout when compiled for 32-bit targets.
#ifndef __x86_64__
_Static_assert(sizeof(struct inode) == 156, "struct inode size incorrect");
#endif

// table mapping major device number to
// device functions
struct devsw {
  int (*read)(struct inode*, char*, size_t);
  int (*write)(struct inode*, char*, size_t);
};

extern struct devsw devsw[];

#define CONSOLE 1

/**
 * @brief Initialize the file table.
 */
void fileinit(void);

/**
 * @brief Allocate a new file structure.
 *
 * @return Pointer to the allocated file or NULL on failure.
 */
struct file *filealloc(void);

/**
 * @brief Increment the reference count of a file.
 *
 * @param f File to duplicate.
 * @return The same file pointer.
 */
struct file *filedup(struct file *f);

/**
 * @brief Close a file and release its resources.
 *
 * @param f File to close.
 */
void fileclose(struct file *f);

/**
 * @brief Retrieve file metadata.
 *
 * @param f  File handle.
 * @param st Destination stat structure.
 * @return 0 on success, negative error code otherwise.
 */
int filestat(struct file *f, struct stat *st);

/**
 * @brief Read data from a file.
 *
 * @param f     File handle.
 * @param addr  Destination buffer.
 * @param n     Number of bytes to read.
 * @return Number of bytes read or negative error code.
 */
int fileread(struct file *f, char *addr, size_t n);

/**
 * @brief Write data to a file.
 *
 * @param f     File handle.
 * @param addr  Source buffer.
 * @param n     Number of bytes to write.
 * @return Number of bytes written or negative error code.
 */
int filewrite(struct file *f, char *addr, size_t n);
