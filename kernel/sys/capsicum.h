/**
 * @file capsicum.h
 * @brief FreeBSD-compatible Capsicum Interface
 *
 * Cleanroom implementation of Capsicum for FeuerBird exokernel.
 * Uses isolation domains for capability mode enforcement.
 *
 * Capsicum provides:
 * - Capability mode (sandbox with no global namespace access)
 * - Capability rights on file descriptors
 * - Sandboxed process execution
 */
#pragma once

#include <stdint.h>

/**
 * Capability rights type
 */
typedef uint64_t cap_rights_t;

/**
 * Capability rights mask structure (FreeBSD 10+)
 */
struct cap_rights {
    uint64_t cr_rights[2];  /* Rights bitmask */
};
typedef struct cap_rights cap_rights_v1_t;

/**
 * Capability rights definitions
 */

/* Generic rights */
#define CAP_READ            (1ULL << 0)     /* Read data */
#define CAP_WRITE           (1ULL << 1)     /* Write data */
#define CAP_SEEK            (1ULL << 2)     /* Seek */
#define CAP_MMAP            (1ULL << 3)     /* Memory map */
#define CAP_IOCTL           (1ULL << 4)     /* ioctl */
#define CAP_FSTAT           (1ULL << 5)     /* fstat */
#define CAP_FCHFLAGS        (1ULL << 6)     /* fchflags */
#define CAP_FCHMOD          (1ULL << 7)     /* fchmod */
#define CAP_FCHOWN          (1ULL << 8)     /* fchown */
#define CAP_FCNTL           (1ULL << 9)     /* fcntl */
#define CAP_FPATHCONF       (1ULL << 10)    /* fpathconf */
#define CAP_FLOCK           (1ULL << 11)    /* flock */
#define CAP_FSYNC           (1ULL << 12)    /* fsync */
#define CAP_FTRUNCATE       (1ULL << 13)    /* ftruncate */
#define CAP_CREATE          (1ULL << 14)    /* Create file */
#define CAP_DELETE          (1ULL << 15)    /* Delete file */
#define CAP_MKDIR           (1ULL << 16)    /* Create directory */
#define CAP_RMDIR           (1ULL << 17)    /* Remove directory */
#define CAP_MKFIFO          (1ULL << 18)    /* Create FIFO */
#define CAP_MKNOD           (1ULL << 19)    /* Create device node */
#define CAP_SYMLINK         (1ULL << 20)    /* Create symlink */
#define CAP_LINK            (1ULL << 21)    /* Create hard link */
#define CAP_UNLINK          (1ULL << 22)    /* Unlink file */
#define CAP_RENAME          (1ULL << 23)    /* Rename file */
#define CAP_LOOKUP          (1ULL << 24)    /* Lookup in directory */
#define CAP_CHDIR           (1ULL << 25)    /* fchdir */
#define CAP_FEXECVE         (1ULL << 26)    /* fexecve */
#define CAP_FSTATAT         (1ULL << 27)    /* fstatat */
#define CAP_LINKAT          (1ULL << 28)    /* linkat */
#define CAP_MKDIRAT         (1ULL << 29)    /* mkdirat */
#define CAP_MKFIFOAT        (1ULL << 30)    /* mkfifoat */
#define CAP_MKNODAT         (1ULL << 31)    /* mknodat */
#define CAP_RENAMEAT        (1ULL << 32)    /* renameat */
#define CAP_SYMLINKAT       (1ULL << 33)    /* symlinkat */
#define CAP_UNLINKAT        (1ULL << 34)    /* unlinkat */
#define CAP_ACCEPT          (1ULL << 35)    /* accept */
#define CAP_BIND            (1ULL << 36)    /* bind */
#define CAP_CONNECT         (1ULL << 37)    /* connect */
#define CAP_GETPEERNAME     (1ULL << 38)    /* getpeername */
#define CAP_GETSOCKNAME     (1ULL << 39)    /* getsockname */
#define CAP_GETSOCKOPT      (1ULL << 40)    /* getsockopt */
#define CAP_LISTEN          (1ULL << 41)    /* listen */
#define CAP_PEELOFF         (1ULL << 42)    /* peeloff */
#define CAP_RECV            (1ULL << 43)    /* recv/recvfrom/recvmsg */
#define CAP_SEND            (1ULL << 44)    /* send/sendto/sendmsg */
#define CAP_SETSOCKOPT      (1ULL << 45)    /* setsockopt */
#define CAP_SHUTDOWN        (1ULL << 46)    /* shutdown */
#define CAP_SOCK_CLIENT     (1ULL << 47)    /* Socket client ops */
#define CAP_SOCK_SERVER     (1ULL << 48)    /* Socket server ops */
#define CAP_MAC_GET         (1ULL << 49)    /* MAC get */
#define CAP_MAC_SET         (1ULL << 50)    /* MAC set */
#define CAP_SEM_GETVALUE    (1ULL << 51)    /* Semaphore getvalue */
#define CAP_SEM_POST        (1ULL << 52)    /* Semaphore post */
#define CAP_SEM_WAIT        (1ULL << 53)    /* Semaphore wait */
#define CAP_EVENT           (1ULL << 54)    /* Event notification */
#define CAP_KQUEUE_EVENT    (1ULL << 55)    /* kqueue event operations */
#define CAP_KQUEUE_CHANGE   (1ULL << 56)    /* kqueue change operations */
#define CAP_KQUEUE          (CAP_KQUEUE_EVENT | CAP_KQUEUE_CHANGE)
#define CAP_PDGETPID        (1ULL << 57)    /* pdgetpid */
#define CAP_PDKILL          (1ULL << 58)    /* pdkill */
#define CAP_PDWAIT4         (1ULL << 59)    /* pdwait4 */
#define CAP_PREAD           (CAP_READ | CAP_SEEK)
#define CAP_PWRITE          (CAP_WRITE | CAP_SEEK)
#define CAP_MMAP_R          (CAP_MMAP | CAP_READ)
#define CAP_MMAP_W          (CAP_MMAP | CAP_WRITE)
#define CAP_MMAP_RW         (CAP_MMAP | CAP_READ | CAP_WRITE)
#define CAP_MMAP_X          (CAP_MMAP)      /* Execute-only mapping */
#define CAP_MMAP_RX         (CAP_MMAP | CAP_READ)
#define CAP_MMAP_RWX        (CAP_MMAP | CAP_READ | CAP_WRITE)

/**
 * All rights mask
 */
#define CAP_ALL             ((1ULL << 60) - 1)

/**
 * Enter capability mode
 *
 * After this call, the process cannot access global namespaces.
 * Only file descriptors with appropriate rights can be used.
 *
 * @return          0 on success, -errno on failure
 */
int sys_cap_enter(void);

/**
 * Check if in capability mode
 *
 * @param in_capability_mode    Output: non-zero if in capability mode
 * @return                      0 on success, -errno on failure
 */
int sys_cap_getmode(int *in_capability_mode);

/**
 * Limit capability rights on a file descriptor
 *
 * @param fd        File descriptor
 * @param rights    Rights to limit to
 * @return          0 on success, -errno on failure
 */
int sys_cap_rights_limit(int fd, const cap_rights_t *rights);

/**
 * Get capability rights on a file descriptor
 *
 * @param fd        File descriptor
 * @param rights    Output rights
 * @return          0 on success, -errno on failure
 */
int sys_cap_rights_get(int fd, cap_rights_t *rights);

/**
 * Create a capability from an existing file descriptor
 *
 * @param fd        File descriptor
 * @param rights    Rights for the capability
 * @return          New capability fd, or -errno on failure
 */
int sys_cap_new(int fd, cap_rights_t rights);

/**
 * Check if fd has specific rights
 *
 * @param fd        File descriptor
 * @param rights    Rights to check
 * @return          0 if has rights, -ENOTCAPABLE if not
 */
int sys_cap_rights_check(int fd, cap_rights_t rights);

/**
 * Initialize rights structure
 *
 * @param rights    Rights structure to initialize
 * @param ...       Rights to include (terminated by 0)
 */
void cap_rights_init(cap_rights_t *rights, ...);

/**
 * Set rights in structure
 *
 * @param rights    Rights structure
 * @param ...       Rights to add (terminated by 0)
 */
void cap_rights_set(cap_rights_t *rights, ...);

/**
 * Clear rights in structure
 *
 * @param rights    Rights structure
 * @param ...       Rights to remove (terminated by 0)
 */
void cap_rights_clear(cap_rights_t *rights, ...);

/**
 * Check if rights are set
 *
 * @param rights    Rights structure to check
 * @param ...       Rights to check for (terminated by 0)
 * @return          Non-zero if all specified rights are set
 */
int cap_rights_is_set(const cap_rights_t *rights, ...);

/**
 * Initialize capsicum subsystem
 */
void capsicum_init(void);

