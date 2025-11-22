#pragma once

/**
 * @file fcntl.h
 * @brief File control operations - unified for exokernel
 */

#include <stdint.h>

// File access modes
#define O_RDONLY   0x000
#define O_WRONLY   0x001
#define O_RDWR     0x002
#define O_ACCMODE  0x003

// File creation flags
#define O_CREATE   0x200  // Legacy compat
#define O_CREAT    0x200  // POSIX standard
#define O_EXCL     0x080
#define O_TRUNC    0x400
#define O_APPEND   0x008
#define O_NONBLOCK 0x400

// fcntl commands
#define F_DUPFD    0
#define F_GETFD    1
#define F_SETFD    2
#define F_GETFL    3
#define F_SETFL    4

// File descriptor flags
#define FD_CLOEXEC 1

// Function declarations (stubs for now)
int open(const char* pathname, int flags, ...);
int fcntl(int fd, int cmd, ...);
int creat(const char* pathname, unsigned int mode);
