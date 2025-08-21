#pragma once

#include <stddef.h>
#include <stdint.h>
#include <sys/stat.h>

#include "exokernel.h"
#include "fs.h"
#include "sleeplock.h"

/**
 * @brief Per-file state for the capability-based file system.
 */
struct file {
  enum { FD_NONE, FD_CAP } type; /**< File descriptor type. */
  size_t ref;                    /**< Reference count. */
  char readable;                 /**< Read permission flag. */
  char writable;                 /**< Write permission flag. */
  struct exo_blockcap cap;       /**< Backing storage capability. */
  size_t off;                    /**< Current file offset. */
  size_t *sizep;                 /**< Pointer to shared file length. */
};

/**
 * @brief In-memory representation of an inode.
 */
struct inode {
  uint32_t dev;          /**< Device number. */
  uint32_t inum;         /**< Inode number. */
  size_t ref;            /**< Reference count. */
  struct sleeplock lock; /**< Protects fields below. */
  int valid;             /**< Has inode been read from disk? */

  short type;                  /**< Copy of disk inode type. */
  short major;                 /**< Major device number. */
  short minor;                 /**< Minor device number. */
  short nlink;                 /**< Number of directory links. */
  size_t size;                 /**< File size in bytes. */
  uint32_t addrs[NDIRECT + 1]; /**< Data block addresses. */
};

/** Device switch table entry. */
struct devsw {
  int (*read)(struct inode *, char *, size_t);
  int (*write)(struct inode *, char *, size_t);
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
