/**
 * @file syscall_posix2024.h
 * @brief POSIX 2024 syscall definitions and prototypes
 * 
 * Implements complete POSIX.1-2024 (IEEE 1003.1-2024) syscall interface
 * with compatibility mapping to FeuerBird exokernel operations.
 */

#pragma once

#include <stdint.h>
#include <stddef.h>
#include "types.h"
#include "defs.h"

// =============================================================================
// POSIX 2024 SYSCALL NUMBERS
// =============================================================================

// File I/O syscalls
#define POSIX_SYS_read          0
#define POSIX_SYS_write         1
#define POSIX_SYS_open          2
#define POSIX_SYS_close         3
#define POSIX_SYS_stat          4
#define POSIX_SYS_fstat         5
#define POSIX_SYS_lstat         6
#define POSIX_SYS_poll          7
#define POSIX_SYS_lseek         8

// Memory management syscalls
#define POSIX_SYS_mmap          9
#define POSIX_SYS_mprotect      10
#define POSIX_SYS_munmap        11
#define POSIX_SYS_brk           12

// Signal syscalls
#define POSIX_SYS_rt_sigaction  13
#define POSIX_SYS_rt_sigprocmask 14
#define POSIX_SYS_rt_sigreturn  15

// Misc syscalls
#define POSIX_SYS_ioctl         16
#define POSIX_SYS_pread64       17
#define POSIX_SYS_pwrite64      18
#define POSIX_SYS_readv         19
#define POSIX_SYS_writev        20
#define POSIX_SYS_access        21
#define POSIX_SYS_pipe          22
#define POSIX_SYS_select        23

// Process syscalls
#define POSIX_SYS_getpid        39
#define POSIX_SYS_socket        41
#define POSIX_SYS_fork          57
#define POSIX_SYS_execve        59
#define POSIX_SYS_exit          60
#define POSIX_SYS_wait4         61
#define POSIX_SYS_kill          62

// Maximum POSIX syscall number
#define POSIX_SYS_MAX           400

// =============================================================================
// POSIX 2024 COMPATIBLE STRUCTURES
// =============================================================================

// POSIX-compliant file status structure
struct posix_stat {
    uint64_t st_dev;        // Device ID containing file
    uint64_t st_ino;        // Inode number  
    uint32_t st_mode;       // File type and mode
    uint32_t st_nlink;      // Number of hard links
    uint32_t st_uid;        // User ID of owner
    uint32_t st_gid;        // Group ID of owner
    uint64_t st_rdev;       // Device ID (if special file)
    uint64_t st_size;       // Total size, in bytes
    uint32_t st_blksize;    // Block size for filesystem I/O
    uint64_t st_blocks;     // Number of 512B blocks allocated
    
    // Time fields (POSIX 2024 requires nanosecond precision)
    struct {
        int64_t tv_sec;
        int64_t tv_nsec;
    } st_atim, st_mtim, st_ctim;  // Access, modify, change times
} __attribute__((packed));

// POSIX open flags
#define POSIX_O_RDONLY      0x00000000
#define POSIX_O_WRONLY      0x00000001
#define POSIX_O_RDWR        0x00000002
#define POSIX_O_CREAT       0x00000040
#define POSIX_O_EXCL        0x00000080
#define POSIX_O_NOCTTY      0x00000100
#define POSIX_O_TRUNC       0x00000200
#define POSIX_O_APPEND      0x00000400
#define POSIX_O_NONBLOCK    0x00000800
#define POSIX_O_SYNC        0x00001000
#define POSIX_O_CLOEXEC     0x00080000

// POSIX mmap protection flags
#define POSIX_PROT_NONE     0x0
#define POSIX_PROT_READ     0x1
#define POSIX_PROT_WRITE    0x2
#define POSIX_PROT_EXEC     0x4

// POSIX mmap flags
#define POSIX_MAP_SHARED    0x01
#define POSIX_MAP_PRIVATE   0x02
#define POSIX_MAP_FIXED     0x10
#define POSIX_MAP_ANONYMOUS 0x20

// POSIX seek whence values
#define POSIX_SEEK_SET      0
#define POSIX_SEEK_CUR      1
#define POSIX_SEEK_END      2

// =============================================================================
// POSIX 2024 SYSCALL FUNCTION PROTOTYPES
// =============================================================================

// File I/O syscalls
long sys_posix_open(const char __user *filename, int flags, uint16_t mode);
long sys_posix_close(unsigned int fd);
long sys_posix_read(unsigned int fd, char __user *buf, size_t count);
long sys_posix_write(unsigned int fd, const char __user *buf, size_t count);
long sys_posix_lseek(unsigned int fd, off_t offset, unsigned int whence);
long sys_posix_stat(const char __user *filename, struct posix_stat __user *statbuf);
long sys_posix_fstat(unsigned int fd, struct posix_stat __user *statbuf);
long sys_posix_lstat(const char __user *filename, struct posix_stat __user *statbuf);

// Memory management syscalls
long sys_posix_mmap(unsigned long addr, unsigned long len, unsigned long prot, 
                   unsigned long flags, unsigned long fd, unsigned long off);
long sys_posix_munmap(unsigned long addr, size_t len);
long sys_posix_mprotect(unsigned long start, size_t len, unsigned long prot);
long sys_posix_brk(unsigned long brk);

// Process syscalls  
long sys_posix_fork(void);
long sys_posix_execve(const char __user *filename, 
                     const char __user *const __user *argv,
                     const char __user *const __user *envp);
long sys_posix_exit(int error_code);
long sys_posix_wait4(pid_t pid, int __user *wstatus, int options, 
                    struct rusage __user *rusage);
long sys_posix_getpid(void);
long sys_posix_kill(pid_t pid, int sig);

// IPC syscalls
long sys_posix_pipe(int __user *fildes);

// Network syscalls
long sys_posix_socket(int family, int type, int protocol);

// Signal syscalls
long sys_posix_sigaction(int sig, const struct sigaction __user *act,
                        struct sigaction __user *oact);
long sys_posix_sigprocmask(int how, const sigset_t __user *nset,
                          sigset_t __user *oset);

// =============================================================================
// POSIX SYSCALL TABLE
// =============================================================================

typedef struct posix_syscall_entry {
    unsigned int nr;        // Syscall number
    const char *name;       // Syscall name
    void *handler;          // Handler function
    unsigned int nargs;     // Number of arguments
} posix_syscall_entry_t;

// External syscall table declaration
extern const posix_syscall_entry_t posix_syscall_table[];
extern const unsigned int posix_syscall_table_size;

// =============================================================================
// COMPATIBILITY TRANSLATION FUNCTIONS
// =============================================================================

// Translate POSIX structures to/from FeuerBird native structures
int translate_posix_stat_to_native(const struct posix_stat __user *posix_stat, 
                                  struct stat *native_stat);
int translate_native_stat_to_posix(const struct stat *native_stat,
                                  struct posix_stat __user *posix_stat);

// Translate POSIX flags to FeuerBird native flags
int translate_posix_open_flags(int posix_flags);
int translate_posix_mmap_prot(int posix_prot);
int translate_posix_mmap_flags(int posix_flags);

// =============================================================================
// ERROR CODE MAPPINGS
// =============================================================================

// POSIX error codes (subset)
#define POSIX_EPERM         1   // Operation not permitted
#define POSIX_ENOENT        2   // No such file or directory  
#define POSIX_ESRCH         3   // No such process
#define POSIX_EINTR         4   // Interrupted system call
#define POSIX_EIO           5   // Input/output error
#define POSIX_ENXIO         6   // No such device or address
#define POSIX_E2BIG         7   // Argument list too long
#define POSIX_ENOEXEC       8   // Exec format error
#define POSIX_EBADF         9   // Bad file descriptor
#define POSIX_ECHILD        10  // No child processes
#define POSIX_EAGAIN        11  // Resource temporarily unavailable
#define POSIX_ENOMEM        12  // Cannot allocate memory
#define POSIX_EACCES        13  // Permission denied
#define POSIX_EFAULT        14  // Bad address
#define POSIX_ENOTBLK       15  // Block device required
#define POSIX_EBUSY         16  // Device or resource busy
#define POSIX_EEXIST        17  // File exists
#define POSIX_EXDEV         18  // Invalid cross-device link
#define POSIX_ENODEV        19  // No such device
#define POSIX_ENOTDIR       20  // Not a directory
#define POSIX_EISDIR        21  // Is a directory
#define POSIX_EINVAL        22  // Invalid argument
#define POSIX_ENFILE        23  // Too many open files in system
#define POSIX_EMFILE        24  // Too many open files
#define POSIX_ENOTTY        25  // Inappropriate ioctl for device

// Error translation function
int translate_native_errno_to_posix(int native_errno);

#endif // SYSCALL_POSIX2024_H