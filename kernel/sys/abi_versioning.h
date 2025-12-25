/**
 * @file abi_versioning.h
 * @brief ABI structure versioning for cross-platform compatibility
 * 
 * Provides versioned structures and translation mechanisms for
 * maintaining binary compatibility across different UNIX variants
 * and versions.
 */

#pragma once

#include <stdint.h>
#include <stddef.h>

// =============================================================================
// VERSION DETECTION
// =============================================================================

typedef enum {
    ABI_VERSION_V6      = 0x0600,   // UNIX V6 (1975)
    ABI_VERSION_V7      = 0x0700,   // UNIX V7 (1979)
    ABI_VERSION_BSD42   = 0x4200,   // 4.2BSD (1983)
    ABI_VERSION_BSD43   = 0x4300,   // 4.3BSD (1986)
    ABI_VERSION_BSD44   = 0x4400,   // 4.4BSD (1993)
    ABI_VERSION_SVR3    = 0x0300,   // System V R3 (1986)
    ABI_VERSION_SVR4    = 0x0400,   // System V R4 (1988)
    ABI_VERSION_LINUX26 = 0x0206,   // Linux 2.6
    ABI_VERSION_LINUX3  = 0x0300,   // Linux 3.x
    ABI_VERSION_LINUX4  = 0x0400,   // Linux 4.x
    ABI_VERSION_LINUX5  = 0x0500,   // Linux 5.x
    ABI_VERSION_LINUX6  = 0x0600,   // Linux 6.x
    ABI_VERSION_FBSD11  = 0x1100,   // FreeBSD 11
    ABI_VERSION_FBSD12  = 0x1200,   // FreeBSD 12
    ABI_VERSION_FBSD13  = 0x1300,   // FreeBSD 13
    ABI_VERSION_FBSD14  = 0x1400,   // FreeBSD 14
    ABI_VERSION_ILLUMOS = 0x5000,   // Illumos/OpenSolaris
    ABI_VERSION_POSIX24 = 0x2024,   // POSIX.1-2024
} abi_version_t;

// =============================================================================
// VERSIONED STAT STRUCTURES
// =============================================================================

// Original V6 stat (smallest)
struct stat_v6 {
    uint16_t st_dev;
    uint16_t st_ino;
    uint16_t st_mode;
    uint8_t  st_nlink;
    uint8_t  st_uid;
    uint8_t  st_gid;
    uint8_t  st_size0;    // High byte of size
    uint16_t st_size1;    // Low word of size
    uint16_t st_atime[2]; // Access time
    uint16_t st_mtime[2]; // Modification time
};

// V7 stat (slightly larger)
struct stat_v7 {
    uint16_t st_dev;
    uint16_t st_ino;
    uint16_t st_mode;
    uint16_t st_nlink;
    uint16_t st_uid;
    uint16_t st_gid;
    uint16_t st_rdev;
    uint32_t st_size;
    uint32_t st_atime;
    uint32_t st_mtime;
    uint32_t st_ctime;
};

// BSD 4.3 stat
struct stat_bsd43 {
    uint32_t st_dev;
    uint32_t st_ino;
    uint16_t st_mode;
    uint16_t st_nlink;
    uint16_t st_uid;
    uint16_t st_gid;
    uint32_t st_rdev;
    uint32_t st_size;
    uint32_t st_atime;
    uint32_t st_spare1;
    uint32_t st_mtime;
    uint32_t st_spare2;
    uint32_t st_ctime;
    uint32_t st_spare3;
    uint32_t st_blksize;
    uint32_t st_blocks;
    uint32_t st_flags;
    uint32_t st_gen;
};

// SVR4 stat
struct stat_svr4 {
    uint32_t st_dev;
    uint32_t st_pad1[3];
    uint64_t st_ino;
    uint32_t st_mode;
    uint32_t st_nlink;
    uint32_t st_uid;
    uint32_t st_gid;
    uint32_t st_rdev;
    uint32_t st_pad2[2];
    int64_t  st_size;
    uint32_t st_pad3;
    struct {
        int32_t tv_sec;
        int32_t tv_nsec;
    } st_atim;
    struct {
        int32_t tv_sec;
        int32_t tv_nsec;
    } st_mtim;
    struct {
        int32_t tv_sec;
        int32_t tv_nsec;
    } st_ctim;
    uint32_t st_blksize;
    int64_t  st_blocks;
    char     st_fstype[16];
    uint32_t st_pad4[8];
};

// Modern Linux stat64
struct stat_linux64 {
    uint64_t st_dev;
    uint64_t st_ino;
    uint64_t st_nlink;
    uint32_t st_mode;
    uint32_t st_uid;
    uint32_t st_gid;
    uint32_t __pad0;
    uint64_t st_rdev;
    int64_t  st_size;
    int64_t  st_blksize;
    int64_t  st_blocks;
    struct {
        int64_t tv_sec;
        int64_t tv_nsec;
    } st_atim;
    struct {
        int64_t tv_sec;
        int64_t tv_nsec;
    } st_mtim;
    struct {
        int64_t tv_sec;
        int64_t tv_nsec;
    } st_ctim;
    int64_t  __unused[3];
};

// =============================================================================
// VERSIONED DIRENT STRUCTURES
// =============================================================================

// V7 directory entry
struct dirent_v7 {
    uint16_t d_ino;
    char     d_name[14];
};

// BSD directory entry
struct dirent_bsd {
    uint32_t d_fileno;
    uint16_t d_reclen;
    uint8_t  d_type;
    uint8_t  d_namlen;
    char     d_name[256];
};

// Linux directory entry
struct dirent_linux {
    uint64_t d_ino;
    int64_t  d_off;
    uint16_t d_reclen;
    uint8_t  d_type;
    char     d_name[256];
};

// =============================================================================
// VERSIONED SIGNAL STRUCTURES
// =============================================================================

// V7 signal action
struct sigaction_v7 {
    void (*sa_handler)(int);
    uint32_t sa_mask;
    int sa_flags;
};

// POSIX signal action
struct sigaction_posix {
    union {
        void (*sa_handler)(int);
        void (*sa_sigaction)(int, siginfo_t *, void *);
    };
    sigset_t sa_mask;
    int sa_flags;
    void (*sa_restorer)(void);
};

// Linux signal action
struct sigaction_linux {
    union {
        void (*sa_handler)(int);
        void (*sa_sigaction)(int, siginfo_t *, void *);
    };
    unsigned long sa_flags;
    void (*sa_restorer)(void);
    sigset_t sa_mask;
};

// =============================================================================
// VERSIONED TIME STRUCTURES
// =============================================================================

// Original timeval (32-bit)
struct timeval32 {
    int32_t tv_sec;
    int32_t tv_usec;
};

// Modern timeval (64-bit)
struct timeval64 {
    int64_t tv_sec;
    int64_t tv_usec;
};

// High precision timespec
struct timespec64 {
    int64_t tv_sec;
    int64_t tv_nsec;
};

// =============================================================================
// TRANSLATION FUNCTIONS
// =============================================================================

/**
 * Detect ABI version from binary
 */
abi_version_t detect_abi_version(const void *elf_header);

/**
 * Translate stat structure between versions
 */
int translate_stat_version(void *src, abi_version_t src_ver,
                          void *dst, abi_version_t dst_ver);

/**
 * Translate dirent structure between versions
 */
int translate_dirent_version(void *src, abi_version_t src_ver,
                            void *dst, abi_version_t dst_ver);

/**
 * Translate signal action between versions
 */
int translate_sigaction_version(void *src, abi_version_t src_ver,
                               void *dst, abi_version_t dst_ver);

/**
 * Translate time structure between versions
 */
int translate_time_version(void *src, abi_version_t src_ver,
                          void *dst, abi_version_t dst_ver);

// =============================================================================
// SIZE CONVERSION HELPERS
// =============================================================================

/**
 * Convert between different integer sizes
 */
static inline uint64_t expand_size(uint32_t size32) {
    return (uint64_t)size32;
}

static inline uint32_t truncate_size(uint64_t size64) {
    return (size64 > 0xFFFFFFFF) ? 0xFFFFFFFF : (uint32_t)size64;
}

/**
 * Convert V6 3-byte size to modern size
 */
static inline uint32_t v6_size_to_modern(uint8_t size0, uint16_t size1) {
    return ((uint32_t)size0 << 16) | size1;
}

/**
 * Convert modern size to V6 3-byte size
 */
static inline void modern_to_v6_size(uint32_t size, uint8_t *size0, uint16_t *size1) {
    *size0 = (size >> 16) & 0xFF;
    *size1 = size & 0xFFFF;
}

// =============================================================================
// ERRNO TRANSLATION
// =============================================================================

/**
 * Translate errno between ABI versions
 */
int translate_errno_version(int errno_val, abi_version_t src_ver, abi_version_t dst_ver);

// V7 errno values
#define V7_EPERM    1
#define V7_ENOENT   2
#define V7_ESRCH    3
#define V7_EINTR    4
#define V7_EIO      5
#define V7_ENXIO    6
#define V7_E2BIG    7
#define V7_ENOEXEC  8
#define V7_EBADF    9
#define V7_ECHILD   10
#define V7_EAGAIN   11
#define V7_ENOMEM   12
#define V7_EACCES   13
#define V7_EFAULT   14
#define V7_ENOTBLK  15
#define V7_EBUSY    16
#define V7_EEXIST   17
#define V7_EXDEV    18
#define V7_ENODEV   19
#define V7_ENOTDIR  20
#define V7_EISDIR   21
#define V7_EINVAL   22
#define V7_ENFILE   23
#define V7_EMFILE   24
#define V7_ENOTTY   25
#define V7_ETXTBSY  26
#define V7_EFBIG    27
#define V7_ENOSPC   28
#define V7_ESPIPE   29
#define V7_EROFS    30
#define V7_EMLINK   31
#define V7_EPIPE    32
#define V7_EDOM     33
#define V7_ERANGE   34

// SVR4 additions
#define SVR4_EDEADLK    35
#define SVR4_ENAMETOOLONG 36
#define SVR4_ENOLCK     37
#define SVR4_ENOSYS     38
#define SVR4_ENOTEMPTY  39

// BSD additions
#define BSD_EWOULDBLOCK 35
#define BSD_EINPROGRESS 36
#define BSD_EALREADY    37
#define BSD_ENOTSOCK    38
#define BSD_EDESTADDRREQ 39
#define BSD_EMSGSIZE    40
#define BSD_EPROTOTYPE  41
#define BSD_ENOPROTOOPT 42
#define BSD_EPROTONOSUPPORT 43
#define BSD_ESOCKTNOSUPPORT 44
#define BSD_EOPNOTSUPP  45
#define BSD_EPFNOSUPPORT 46
#define BSD_EAFNOSUPPORT 47
#define BSD_EADDRINUSE  48
#define BSD_EADDRNOTAVAIL 49
#define BSD_ENETDOWN    50
#define BSD_ENETUNREACH 51
#define BSD_ENETRESET   52
#define BSD_ECONNABORTED 53
#define BSD_ECONNRESET  54
#define BSD_ENOBUFS     55
#define BSD_EISCONN     56
#define BSD_ENOTCONN    57
#define BSD_ESHUTDOWN   58
#define BSD_ETOOMANYREFS 59
#define BSD_ETIMEDOUT   60
#define BSD_ECONNREFUSED 61

// =============================================================================
// COMPATIBILITY MATRIX
// =============================================================================

/**
 * Structure compatibility matrix
 * Defines which structure versions can be safely converted
 */
typedef struct {
    abi_version_t from_version;
    abi_version_t to_version;
    int (*translator)(void *src, void *dst);
    size_t src_size;
    size_t dst_size;
} compat_matrix_entry_t;

extern const compat_matrix_entry_t stat_compat_matrix[];
extern const compat_matrix_entry_t dirent_compat_matrix[];
extern const compat_matrix_entry_t sigaction_compat_matrix[];

/**
 * Find compatible translator
 */
const compat_matrix_entry_t *find_translator(
    const compat_matrix_entry_t *matrix,
    abi_version_t from_ver,
    abi_version_t to_ver
);

#endif // ABI_VERSIONING_H