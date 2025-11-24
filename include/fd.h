/**
 * @file fd.h
 * @brief File Descriptor API (Phase 11.2)
 *
 * LibOS file descriptor abstraction. Provides POSIX-like file descriptor
 * semantics on top of the IPC-based file system.
 *
 * Usage:
 *   fd_init();                      // Initialize (auto-called on first use)
 *   int fd = fd_open("/hello", 0);  // Open file
 *   fd_read(fd, buf, sizeof(buf));  // Read data
 *   fd_close(fd);                   // Close file
 */

#ifndef FD_H
#define FD_H

#include <stdint.h>

/* Standard file descriptors (pre-opened as console) */
#define FD_STDIN    0
#define FD_STDOUT   1
#define FD_STDERR   2

/* Seek whence values */
#define SEEK_SET    0   /* Set offset to offset */
#define SEEK_CUR    1   /* Set offset to current + offset */
#define SEEK_END    2   /* Set offset to end + offset */

/**
 * Initialize file descriptor table
 *
 * Sets up stdin/stdout/stderr as console devices.
 * Called automatically on first fd_open().
 */
void fd_init(void);

/**
 * Open a file
 * @param path File path
 * @param flags Open flags (FS_O_RDONLY, etc.)
 * @return File descriptor (>= 0) or error (< 0)
 */
int fd_open(const char *path, int flags);

/**
 * Close a file descriptor
 * @param fd File descriptor
 * @return 0 on success, -1 on error
 */
int fd_close(int fd);

/**
 * Read from a file descriptor
 * @param fd File descriptor
 * @param buf Buffer to read into
 * @param n Maximum bytes to read
 * @return Bytes read (>= 0) or error (< 0)
 */
int fd_read(int fd, void *buf, int n);

/**
 * Write to a file descriptor
 * @param fd File descriptor
 * @param buf Buffer to write from
 * @param n Bytes to write
 * @return Bytes written (>= 0) or error (< 0)
 */
int fd_write(int fd, const void *buf, int n);

/**
 * Duplicate a file descriptor
 * @param fd File descriptor to duplicate
 * @return New file descriptor (>= 0) or error (< 0)
 */
int fd_dup(int fd);

/**
 * Duplicate to a specific file descriptor
 * @param oldfd Source file descriptor
 * @param newfd Target file descriptor (closed if open)
 * @return newfd on success, -1 on error
 */
int fd_dup2(int oldfd, int newfd);

/**
 * Seek in a file
 * @param fd File descriptor
 * @param offset Offset value
 * @param whence SEEK_SET, SEEK_CUR, or SEEK_END
 * @return New offset (>= 0) or error (< 0)
 */
int fd_lseek(int fd, int offset, int whence);

/**
 * Check if file descriptor is a terminal
 * @param fd File descriptor
 * @return 1 if terminal (console), 0 otherwise
 */
int fd_isatty(int fd);

/**
 * Create a pipe
 * @param pipefd Array to receive [read_fd, write_fd]
 * @return 0 on success, -1 on error
 *
 * Example usage for shell pipeline "cmd1 | cmd2":
 *   int pipefd[2];
 *   fd_pipe(pipefd);
 *   // Spawn cmd1 with stdout = pipefd[1]
 *   // Spawn cmd2 with stdin = pipefd[0]
 *   fd_close(pipefd[0]);
 *   fd_close(pipefd[1]);
 */
int fd_pipe(int pipefd[2]);

/**
 * Remove a file
 * @param path Path to file to remove
 * @return 0 on success, -1 on error
 */
int fd_unlink(const char *path);

#endif /* FD_H */
