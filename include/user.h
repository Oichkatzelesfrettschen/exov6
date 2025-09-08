#pragma once
#include "types.h"
#include "exo.h"
#include "stat.h"

/* Prevent conflicts with system headers */
#ifndef PHOENIX_USER_H_DECLS
#define PHOENIX_USER_H_DECLS

/**
 * @brief Replace the current process image with a new program.
 *
 * @param path Path to the executable.
 * @param argv Null-terminated argument vector.
 * @return 0 on success, or -1 on failure.
 */
int exec(char *path, char **argv);

/**
 * @brief Send a signal to a process.
 *
 * @param pid Target process identifier.
 * @param sig Signal number to deliver.
 * @return 0 on success, or -1 on failure.
 */
int sigsend(int pid, int sig);

/**
 * @brief Check for pending signals.
 *
 * @return Pending signal number, or 0 if none are pending.
 */
int sigcheck(void);

/**
 * @brief Minimal printf for userland applications.
 *
 * @param fd  Destination file descriptor.
 * @param fmt Format string.
 * @param ... Additional arguments.
 */
#pragma clang diagnostic push
#pragma clang diagnostic ignored "-Wincompatible-library-redeclaration"
void printf(int fd, const char *fmt, ...);
#pragma clang diagnostic pop

/**
 * @brief Allocate dynamic memory.
 *
 * @param size Number of bytes to allocate.
 * @return Pointer to the allocated block, or nullptr on failure.
 */
void *malloc(size_t size);

/**
 * @brief Release dynamic memory.
 *
 * @param ptr Pointer previously returned by malloc().
 */
void free(void *ptr);

/**
 * @brief Register a timer upcall handler.
 *
 * @param handler Function invoked on timer events.
 * @return 0 on success, or -1 on failure.
 */
int set_timer_upcall(void (*handler)(void));

/**
 * @brief Set the available gas (execution budget) for the process.
 *
 * @param amount Number of gas units to assign.
 * @return Previous gas amount.
 */
int set_gas(uint64_t amount);

/**
 * @brief Retrieve the remaining gas for the process.
 *
 * @return Remaining gas units.
 */
int get_gas(void);

/**
 * @brief Flush a block capability to the backing store.
 *
 * @param cap  Block capability to flush.
 * @param data Buffer containing the block data.
 */
void exo_flush_block(exo_blockcap *cap, void *data);

/**
 * @brief Increase the data segment by the requested amount.
 *
 * @param nbytes Number of bytes to grow.
 * @return Pointer to the previous program break, or (void *)-1 on failure.
 */
void *sbrk(int nbytes);

/**
 * @brief Write data to a file descriptor.
 *
 * @param fd    Destination file descriptor.
 * @param buf   Buffer containing data to write.
 * @param count Number of bytes to write.
 * @return Number of bytes written, or -1 on error.
 */
int write(int fd, const void *buf, int count);

/**
 * @brief Read data from a file descriptor.
 *
 * @param fd    Source file descriptor.
 * @param buf   Destination buffer.
 * @param count Maximum number of bytes to read.
 * @return Number of bytes read, or -1 on error.
 */
int read(int fd, void *buf, int count);

/**
 * @brief Open a file.
 *
 * @param path File path.
 * @param mode Opening mode flags.
 * @param ...  Optional permission argument when creating files.
 * @return File descriptor on success, or -1 on error.
 */
int open(const char *path, int mode, ...);

/**
 * @brief Close an open file descriptor.
 *
 * @param fd File descriptor to close.
 * @return 0 on success, or -1 on error.
 */
int close(int fd);

/**
 * @brief Create a special or device file.
 *
 * @param path  Destination path for the node.
 * @param type  File type identifier.
 * @param major Major device number.
 * @return 0 on success, or -1 on failure.
 */
int mknod(const char *path, short type, short major);

/**
 * @brief Duplicate an existing file descriptor.
 *
 * @param fd File descriptor to duplicate.
 * @return New descriptor referencing the same open file, or -1 on error.
 */
int dup(int fd);

/**
 * @brief Create a new process.
 *
 * The child receives a copy of the parent's address space.
 *
 * @return 0 in the child, child's PID in the parent, or -1 on error.
 */
int fork(void);

/**
 * @brief Wait for a child process to exit.
 *
 * @return PID of the terminated child, or -1 if none remain.
 */
int wait(void);

/**
 * @brief Create a unidirectional data channel.
 *
 * @param fd Two-element array receiving the read and write descriptors.
 * @return 0 on success, or -1 on failure.
 */
int pipe(int fd[2]);

/**
 * @brief Send a termination signal to a process.
 *
 * @param pid Target process identifier.
 * @return 0 on success, or -1 on error.
 */
int kill(int pid);

/**
 * @brief Remove a directory entry.
 *
 * @param path Path of the file to unlink.
 * @return 0 on success, or -1 on failure.
 */
int unlink(const char *path);

/**
 * @brief Create a hard link between two paths.
 *
 * @param old Existing file path.
 * @param newp New link path.
 * @return 0 on success, or -1 on failure.
 */
int link(const char *old, const char *newp);

/**
 * @brief Retrieve file status information.
 *
 * @param fd File descriptor to query.
 * @param st Output structure for file metadata.
 * @return 0 on success, or -1 on failure.
 */
int fstat(int fd, struct stat *st);

/**
 * @brief Change the current working directory.
 *
 * @param path Path of the new working directory.
 * @return 0 on success, or -1 on error.
 */
int chdir(const char *path);

/**
 * @brief Obtain the calling process identifier.
 *
 * @return The PID of the current process.
 */
int getpid(void);

/**
 * @brief Suspend execution for a number of clock ticks.
 *
 * @param ticks Duration to sleep.
 * @return 0 on success, or -1 on failure.
 */
int sleep(int ticks);

/**
 * @brief Retrieve the system tick count since boot.
 *
 * @return Number of ticks since system start.
 */
int uptime(void);

/**
 * @brief Terminate the calling process.
 */
#pragma clang diagnostic push
#pragma clang diagnostic ignored "-Wincompatible-library-redeclaration"
[[noreturn]] void exit(void);
#pragma clang diagnostic pop

/**
 * @brief Copy string @p t into buffer @p s.
 *
 * Implements a basic C library routine using a simple loop. The
 * destination buffer must have space for the source string including its
 * terminating null byte.
 *
 * @param s Destination buffer.
 * @param t Null-terminated source string.
 * @return Pointer to @p s for convenience.
 */
char *strcpy(char *s, const char *t);

/**
 * @brief Lexicographically compare two strings.
 *
 * @param p First string.
 * @param q Second string.
 * @return Negative, zero or positive if @p p is respectively less than,
 *         equal to or greater than @p q.
 */
int strcmp(const char *p, const char *q);

/**
 * @brief Compute the length of a string.
 *
 * @param s Null-terminated string.
 * @return Number of bytes preceding the terminating null.
 */
size_t strlen(const char *s);

/**
 * @brief Fill a memory region with a byte value.
 *
 * @param dst Destination buffer.
 * @param c   Byte value to write.
 * @param n   Number of bytes to set.
 * @return Pointer to @p dst.
 */
void *memset(void *dst, int c, size_t n);

/**
 * @brief Locate a character within a string.
 *
 * @param s String to scan.
 * @param c Character to search for.
 * @return Pointer to the first occurrence or NULL if absent.
 */
char *strchr(const char *s, int c);

/**
 * @brief Read a line from standard input.
 *
 * Reads at most @p max-1 bytes from file descriptor zero and terminates
 * the buffer with a null byte.
 *
 * @param buf Destination buffer.
 * @param max Buffer capacity in bytes.
 * @return Pointer to @p buf.
 */
char *gets(char *buf, size_t max);

/**
 * @brief Obtain file status information.
 *
 * @param n   Path to the file.
 * @param st  Output structure for file metadata.
 * @return 0 on success, or -1 on failure.
 */
int stat(const char *n, struct stat *st);

/**
 * @brief Convert a string to an integer.
 *
 * Parses a sequence of decimal digits and stops at the first
 * non-numeric character.
 *
 * @param s Input string.
 * @return Parsed integer value.
 */
int atoi(const char *s);

/**
 * @brief Move a memory region even if the ranges overlap.
 *
 * @param vdst Destination buffer.
 * @param vsrc Source buffer.
 * @param n    Number of bytes to move.
 * @return Pointer to @p vdst.
 */
void *memmove(void *vdst, const void *vsrc, size_t n);

#endif /* PHOENIX_USER_H_DECLS */
