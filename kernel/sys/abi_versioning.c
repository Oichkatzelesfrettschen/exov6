/**
 * @file abi_versioning.c
 * @brief ABI structure versioning implementation
 * 
 * Provides translation between different UNIX ABI versions for
 * binary compatibility across V6, V7, BSD, SVR4, Linux, and modern systems.
 */

#include "abi_versioning.h"
#include "types.h"
#include "defs.h"
#include <string.h>

// =============================================================================
// VERSION DETECTION
// =============================================================================

/**
 * Detect ABI version from ELF header and notes
 */
abi_version_t detect_abi_version(const void *elf_header) {
    // Simplified detection - would parse ELF notes and interpreter
    const uint8_t *magic = (const uint8_t *)elf_header;
    
    // Check ELF magic
    if (magic[0] != 0x7F || magic[1] != 'E' || magic[2] != 'L' || magic[3] != 'F') {
        // Not ELF, might be a.out
        if (magic[0] == 0x07 && magic[1] == 0x01) {
            return ABI_VERSION_V7;  // V7 a.out
        }
        return ABI_VERSION_V6;  // Assume V6
    }
    
    // Would check:
    // - ELF interpreter path
    // - ELF notes (NT_GNU_ABI_TAG, NT_FREEBSD_ABI_TAG)
    // - Dynamic section tags
    // - Symbol versioning
    
    return ABI_VERSION_POSIX24;  // Default to modern POSIX
}

// =============================================================================
// STAT TRANSLATION
// =============================================================================

/**
 * Translate V6 stat to modern
 */
static int stat_v6_to_modern(struct stat_v6 *v6, struct stat *modern) {
    memset(modern, 0, sizeof(*modern));
    modern->dev = v6->st_dev;
    modern->ino = v6->st_ino;
    modern->mode = v6->st_mode;
    modern->nlink = v6->st_nlink;
    modern->size = v6_size_to_modern(v6->st_size0, v6->st_size1);
    // V6 time is in 60Hz ticks
    modern->atime = (v6->st_atime[0] << 16 | v6->st_atime[1]) / 60;
    modern->mtime = (v6->st_mtime[0] << 16 | v6->st_mtime[1]) / 60;
    modern->ctime = modern->mtime;  // V6 has no ctime
    return 0;
}

/**
 * Translate modern stat to V6
 */
static int stat_modern_to_v6(struct stat *modern, struct stat_v6 *v6) {
    memset(v6, 0, sizeof(*v6));
    v6->st_dev = modern->dev & 0xFFFF;
    v6->st_ino = modern->ino & 0xFFFF;
    v6->st_mode = modern->mode & 0xFFFF;
    v6->st_nlink = modern->nlink & 0xFF;
    v6->st_uid = 0;  // Would get from process
    v6->st_gid = 0;
    modern_to_v6_size(modern->size, &v6->st_size0, &v6->st_size1);
    // Convert to 60Hz ticks
    uint32_t atime_ticks = modern->atime * 60;
    v6->st_atime[0] = (atime_ticks >> 16) & 0xFFFF;
    v6->st_atime[1] = atime_ticks & 0xFFFF;
    uint32_t mtime_ticks = modern->mtime * 60;
    v6->st_mtime[0] = (mtime_ticks >> 16) & 0xFFFF;
    v6->st_mtime[1] = mtime_ticks & 0xFFFF;
    return 0;
}

/**
 * Translate V7 stat to modern
 */
static int stat_v7_to_modern(struct stat_v7 *v7, struct stat *modern) {
    memset(modern, 0, sizeof(*modern));
    modern->dev = v7->st_dev;
    modern->ino = v7->st_ino;
    modern->mode = v7->st_mode;
    modern->nlink = v7->st_nlink;
    modern->size = v7->st_size;
    modern->atime = v7->st_atime;
    modern->mtime = v7->st_mtime;
    modern->ctime = v7->st_ctime;
    return 0;
}

/**
 * Translate BSD 4.3 stat to modern
 */
static int stat_bsd43_to_modern(struct stat_bsd43 *bsd, struct stat *modern) {
    memset(modern, 0, sizeof(*modern));
    modern->dev = bsd->st_dev;
    modern->ino = bsd->st_ino;
    modern->mode = bsd->st_mode;
    modern->nlink = bsd->st_nlink;
    modern->size = bsd->st_size;
    modern->atime = bsd->st_atime;
    modern->mtime = bsd->st_mtime;
    modern->ctime = bsd->st_ctime;
    return 0;
}

/**
 * Translate SVR4 stat to modern
 */
static int stat_svr4_to_modern(struct stat_svr4 *svr4, struct stat *modern) {
    memset(modern, 0, sizeof(*modern));
    modern->dev = svr4->st_dev;
    modern->ino = svr4->st_ino;
    modern->mode = svr4->st_mode;
    modern->nlink = svr4->st_nlink;
    modern->size = svr4->st_size;
    modern->atime = svr4->st_atim.tv_sec;
    modern->mtime = svr4->st_mtim.tv_sec;
    modern->ctime = svr4->st_ctim.tv_sec;
    return 0;
}

/**
 * Generic stat translation dispatcher
 */
int translate_stat_version(void *src, abi_version_t src_ver,
                          void *dst, abi_version_t dst_ver) {
    // Convert to modern format first
    struct stat modern_stat;
    
    // Source to modern
    switch (src_ver) {
        case ABI_VERSION_V6:
            stat_v6_to_modern((struct stat_v6 *)src, &modern_stat);
            break;
        case ABI_VERSION_V7:
            stat_v7_to_modern((struct stat_v7 *)src, &modern_stat);
            break;
        case ABI_VERSION_BSD43:
            stat_bsd43_to_modern((struct stat_bsd43 *)src, &modern_stat);
            break;
        case ABI_VERSION_SVR4:
            stat_svr4_to_modern((struct stat_svr4 *)src, &modern_stat);
            break;
        case ABI_VERSION_POSIX24:
        case ABI_VERSION_LINUX6:
            memcpy(&modern_stat, src, sizeof(modern_stat));
            break;
        default:
            return -1;
    }
    
    // Modern to destination
    switch (dst_ver) {
        case ABI_VERSION_V6:
            stat_modern_to_v6(&modern_stat, (struct stat_v6 *)dst);
            break;
        case ABI_VERSION_V7:
            // Would implement modern to V7
            break;
        case ABI_VERSION_POSIX24:
        case ABI_VERSION_LINUX6:
            memcpy(dst, &modern_stat, sizeof(modern_stat));
            break;
        default:
            return -1;
    }
    
    return 0;
}

// =============================================================================
// DIRENT TRANSLATION
// =============================================================================

/**
 * Translate V7 dirent to modern
 */
static int dirent_v7_to_modern(struct dirent_v7 *v7, struct dirent *modern) {
    memset(modern, 0, sizeof(*modern));
    modern->d_ino = v7->d_ino;
    memcpy(modern->d_name, v7->d_name, 14);
    modern->d_name[14] = '\0';
    return 0;
}

/**
 * Translate BSD dirent to modern
 */
static int dirent_bsd_to_modern(struct dirent_bsd *bsd, struct dirent *modern) {
    memset(modern, 0, sizeof(*modern));
    modern->d_ino = bsd->d_fileno;
    modern->d_type = bsd->d_type;
    memcpy(modern->d_name, bsd->d_name, bsd->d_namlen);
    modern->d_name[bsd->d_namlen] = '\0';
    return 0;
}

/**
 * Generic dirent translation dispatcher
 */
int translate_dirent_version(void *src, abi_version_t src_ver,
                            void *dst, abi_version_t dst_ver) {
    struct dirent modern_dirent;
    
    // Source to modern
    switch (src_ver) {
        case ABI_VERSION_V7:
            dirent_v7_to_modern((struct dirent_v7 *)src, &modern_dirent);
            break;
        case ABI_VERSION_BSD43:
        case ABI_VERSION_BSD44:
            dirent_bsd_to_modern((struct dirent_bsd *)src, &modern_dirent);
            break;
        default:
            memcpy(&modern_dirent, src, sizeof(modern_dirent));
            break;
    }
    
    // Modern to destination
    memcpy(dst, &modern_dirent, sizeof(modern_dirent));
    
    return 0;
}

// =============================================================================
// SIGNAL ACTION TRANSLATION
// =============================================================================

/**
 * Translate V7 sigaction to POSIX
 */
static int sigaction_v7_to_posix(struct sigaction_v7 *v7, struct sigaction_posix *posix) {
    memset(posix, 0, sizeof(*posix));
    posix->sa_handler = v7->sa_handler;
    // V7 has simple 32-bit mask
    sigemptyset(&posix->sa_mask);
    for (int i = 0; i < 32; i++) {
        if (v7->sa_mask & (1 << i))
            sigaddset(&posix->sa_mask, i + 1);
    }
    posix->sa_flags = v7->sa_flags;
    return 0;
}

/**
 * Generic sigaction translation
 */
int translate_sigaction_version(void *src, abi_version_t src_ver,
                               void *dst, abi_version_t dst_ver) {
    struct sigaction_posix posix_sa;
    
    // Source to POSIX
    switch (src_ver) {
        case ABI_VERSION_V7:
            sigaction_v7_to_posix((struct sigaction_v7 *)src, &posix_sa);
            break;
        default:
            memcpy(&posix_sa, src, sizeof(posix_sa));
            break;
    }
    
    // POSIX to destination
    memcpy(dst, &posix_sa, sizeof(posix_sa));
    
    return 0;
}

// =============================================================================
// TIME TRANSLATION
// =============================================================================

/**
 * Translate 32-bit time to 64-bit
 */
static int time32_to_time64(struct timeval32 *tv32, struct timeval64 *tv64) {
    tv64->tv_sec = tv32->tv_sec;
    tv64->tv_usec = tv32->tv_usec;
    return 0;
}

/**
 * Translate 64-bit time to 32-bit (with Y2038 check)
 */
static int time64_to_time32(struct timeval64 *tv64, struct timeval32 *tv32) {
    if (tv64->tv_sec > 0x7FFFFFFF) {
        // Y2038 overflow
        tv32->tv_sec = 0x7FFFFFFF;
    } else {
        tv32->tv_sec = tv64->tv_sec;
    }
    tv32->tv_usec = tv64->tv_usec;
    return 0;
}

/**
 * Generic time translation
 */
int translate_time_version(void *src, abi_version_t src_ver,
                          void *dst, abi_version_t dst_ver) {
    // Determine if source is 32-bit or 64-bit time
    if (src_ver <= ABI_VERSION_LINUX4) {
        // 32-bit time
        if (dst_ver >= ABI_VERSION_LINUX5) {
            // Convert to 64-bit
            return time32_to_time64((struct timeval32 *)src, (struct timeval64 *)dst);
        }
    } else {
        // 64-bit time
        if (dst_ver <= ABI_VERSION_LINUX4) {
            // Convert to 32-bit
            return time64_to_time32((struct timeval64 *)src, (struct timeval32 *)dst);
        }
    }
    
    // Same size, direct copy
    memcpy(dst, src, sizeof(struct timeval64));
    return 0;
}

// =============================================================================
// ERRNO TRANSLATION
// =============================================================================

/**
 * Errno translation table
 */
static const struct {
    int v7_errno;
    int posix_errno;
    int linux_errno;
    int bsd_errno;
} errno_map[] = {
    {V7_EPERM,   EPERM,   1,  1},
    {V7_ENOENT,  ENOENT,  2,  2},
    {V7_ESRCH,   ESRCH,   3,  3},
    {V7_EINTR,   EINTR,   4,  4},
    {V7_EIO,     EIO,     5,  5},
    {V7_ENXIO,   ENXIO,   6,  6},
    {V7_E2BIG,   E2BIG,   7,  7},
    {V7_ENOEXEC, ENOEXEC, 8,  8},
    {V7_EBADF,   EBADF,   9,  9},
    {V7_ECHILD,  ECHILD,  10, 10},
    {V7_EAGAIN,  EAGAIN,  11, 35},  // BSD uses EWOULDBLOCK=35
    {V7_ENOMEM,  ENOMEM,  12, 12},
    {V7_EACCES,  EACCES,  13, 13},
    {V7_EFAULT,  EFAULT,  14, 14},
    {V7_EBUSY,   EBUSY,   16, 16},
    {V7_EEXIST,  EEXIST,  17, 17},
    {V7_EXDEV,   EXDEV,   18, 18},
    {V7_ENODEV,  ENODEV,  19, 19},
    {V7_ENOTDIR, ENOTDIR, 20, 20},
    {V7_EISDIR,  EISDIR,  21, 21},
    {V7_EINVAL,  EINVAL,  22, 22},
    {V7_ENFILE,  ENFILE,  23, 23},
    {V7_EMFILE,  EMFILE,  24, 24},
    {V7_ENOTTY,  ENOTTY,  25, 25},
    {V7_EFBIG,   EFBIG,   27, 27},
    {V7_ENOSPC,  ENOSPC,  28, 28},
    {V7_ESPIPE,  ESPIPE,  29, 29},
    {V7_EROFS,   EROFS,   30, 30},
    {V7_EMLINK,  EMLINK,  31, 31},
    {V7_EPIPE,   EPIPE,   32, 32},
    {V7_EDOM,    EDOM,    33, 33},
    {V7_ERANGE,  ERANGE,  34, 34},
};

/**
 * Translate errno between versions
 */
int translate_errno_version(int errno_val, abi_version_t src_ver, abi_version_t dst_ver) {
    // Find errno in source version
    for (int i = 0; i < sizeof(errno_map)/sizeof(errno_map[0]); i++) {
        int src_errno = 0, dst_errno = 0;
        
        // Get source errno value
        switch (src_ver) {
            case ABI_VERSION_V6:
            case ABI_VERSION_V7:
                src_errno = errno_map[i].v7_errno;
                break;
            case ABI_VERSION_POSIX24:
                src_errno = errno_map[i].posix_errno;
                break;
            case ABI_VERSION_LINUX6:
                src_errno = errno_map[i].linux_errno;
                break;
            case ABI_VERSION_BSD44:
            case ABI_VERSION_FBSD14:
                src_errno = errno_map[i].bsd_errno;
                break;
            default:
                src_errno = errno_map[i].posix_errno;
                break;
        }
        
        if (src_errno == errno_val) {
            // Found match, get destination errno
            switch (dst_ver) {
                case ABI_VERSION_V6:
                case ABI_VERSION_V7:
                    dst_errno = errno_map[i].v7_errno;
                    break;
                case ABI_VERSION_POSIX24:
                    dst_errno = errno_map[i].posix_errno;
                    break;
                case ABI_VERSION_LINUX6:
                    dst_errno = errno_map[i].linux_errno;
                    break;
                case ABI_VERSION_BSD44:
                case ABI_VERSION_FBSD14:
                    dst_errno = errno_map[i].bsd_errno;
                    break;
                default:
                    dst_errno = errno_map[i].posix_errno;
                    break;
            }
            
            return dst_errno;
        }
    }
    
    // No translation found, return as-is
    return errno_val;
}

// =============================================================================
// COMPATIBILITY MATRICES
// =============================================================================

/**
 * Stat compatibility matrix
 */
const compat_matrix_entry_t stat_compat_matrix[] = {
    {ABI_VERSION_V6, ABI_VERSION_POSIX24, (void *)stat_v6_to_modern, sizeof(struct stat_v6), sizeof(struct stat)},
    {ABI_VERSION_V7, ABI_VERSION_POSIX24, (void *)stat_v7_to_modern, sizeof(struct stat_v7), sizeof(struct stat)},
    {ABI_VERSION_BSD43, ABI_VERSION_POSIX24, (void *)stat_bsd43_to_modern, sizeof(struct stat_bsd43), sizeof(struct stat)},
    {ABI_VERSION_SVR4, ABI_VERSION_POSIX24, (void *)stat_svr4_to_modern, sizeof(struct stat_svr4), sizeof(struct stat)},
    {0, 0, NULL, 0, 0}  // Terminator
};

/**
 * Find compatible translator
 */
const compat_matrix_entry_t *find_translator(
    const compat_matrix_entry_t *matrix,
    abi_version_t from_ver,
    abi_version_t to_ver) {
    
    for (const compat_matrix_entry_t *entry = matrix; entry->translator; entry++) {
        if (entry->from_version == from_ver && entry->to_version == to_ver) {
            return entry;
        }
    }
    
    return NULL;
}