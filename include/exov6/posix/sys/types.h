/* sys/types.h - POSIX-2024 System Data Types */
#ifndef _SYS_TYPES_H
#define _SYS_TYPES_H

#include <stddef.h>
#include <stdint.h>

#ifdef __cplusplus
extern "C" {
#endif

/* POSIX-2024 required types */

/* Process and thread identifiers */
typedef int             pid_t;      /* Process ID */
typedef unsigned int    uid_t;      /* User ID */
typedef unsigned int    gid_t;      /* Group ID */
typedef pid_t           id_t;       /* Generic ID type */

/* File system types */
typedef unsigned long   dev_t;      /* Device ID */
typedef unsigned long   ino_t;      /* File serial number */
typedef unsigned int    mode_t;     /* File mode */
typedef unsigned int    nlink_t;    /* Link count */
typedef long            off_t;      /* File size/offset */
typedef long            blksize_t;  /* Block size */
typedef long            blkcnt_t;   /* Block count */

/* Time types */
typedef long            time_t;     /* Time in seconds since epoch */
typedef long            clock_t;    /* Clock ticks */
typedef long            suseconds_t; /* Signed number of microseconds */
typedef unsigned long   useconds_t;  /* Unsigned microseconds */

/* I/O types */
typedef long            ssize_t;     /* Signed size type */

/* Socket types */
typedef unsigned int    socklen_t;  /* Socket address length */
typedef uint16_t        sa_family_t; /* Socket address family */
typedef uint16_t        in_port_t;  /* Internet port */
typedef uint32_t        in_addr_t;  /* Internet address */

/* System V IPC types */
typedef int             key_t;      /* IPC key */

/* Thread types - basic definitions */
#ifndef _PTHREAD_TYPES_DEFINED
#define _PTHREAD_TYPES_DEFINED
typedef unsigned long   pthread_t;  /* Thread identifier */
typedef union {
    char __size[40];
    long __align;
} pthread_attr_t;

typedef union {
    char __size[24];
    long __align;
} pthread_mutex_t;

typedef union {
    char __size[4];
    int __align;
} pthread_mutexattr_t;

typedef union {
    char __size[48];
    long __align;
} pthread_cond_t;

typedef union {
    char __size[4];
    int __align;
} pthread_condattr_t;

typedef unsigned int    pthread_key_t;
typedef union {
    int __i[1];
    void *__p[1];
} pthread_once_t;

typedef union {
    char __size[56];
    long __align;
} pthread_rwlock_t;

typedef union {
    char __size[8];
    long __align;
} pthread_rwlockattr_t;
#endif /* _PTHREAD_TYPES_DEFINED */

/* Additional POSIX types */
typedef int             clockid_t;  /* Clock identifier */
typedef void*           timer_t;    /* Timer identifier */

/* Trace types */
typedef int             trace_attr_t;
typedef int             trace_event_id_t;
typedef int             trace_event_set_t;
typedef int             trace_id_t;

/* File descriptor set for select() */
#define FD_SETSIZE      1024

typedef struct {
    unsigned long fds_bits[FD_SETSIZE / (8 * sizeof(unsigned long))];
} fd_set;

/* FD_SET macros */
#define FD_ZERO(set)    do { \
    int __i; \
    for (__i = 0; __i < FD_SETSIZE / (8 * sizeof(unsigned long)); __i++) \
        ((fd_set *)(set))->fds_bits[__i] = 0; \
} while (0)

#define FD_SET(fd, set) \
    ((fd_set *)(set))->fds_bits[(fd) / (8 * sizeof(unsigned long))] |= \
    (1UL << ((fd) % (8 * sizeof(unsigned long))))

#define FD_CLR(fd, set) \
    ((fd_set *)(set))->fds_bits[(fd) / (8 * sizeof(unsigned long))] &= \
    ~(1UL << ((fd) % (8 * sizeof(unsigned long))))

#define FD_ISSET(fd, set) \
    (((fd_set *)(set))->fds_bits[(fd) / (8 * sizeof(unsigned long))] & \
    (1UL << ((fd) % (8 * sizeof(unsigned long)))))

/* I/O vector for readv/writev */
struct iovec {
    void   *iov_base;   /* Base address */
    size_t  iov_len;    /* Number of bytes */
};

/* Time specifications */
struct timespec {
    time_t  tv_sec;     /* Seconds */
    long    tv_nsec;    /* Nanoseconds */
};

struct timeval {
    time_t      tv_sec; /* Seconds */
    suseconds_t tv_usec; /* Microseconds */
};

/* For compatibility with existing code */
typedef unsigned char   u_char;
typedef unsigned short  u_short;
typedef unsigned int    u_int;
typedef unsigned long   u_long;

typedef uint8_t         u_int8_t;
typedef uint16_t        u_int16_t;
typedef uint32_t        u_int32_t;
typedef uint64_t        u_int64_t;

/* Register types */
typedef int             register_t;

/* Byte order definitions */
#define __LITTLE_ENDIAN 1234
#define __BIG_ENDIAN    4321
#define __PDP_ENDIAN    3412

#if defined(__x86_64__) || defined(__i386__) || defined(__aarch64__)
#define __BYTE_ORDER    __LITTLE_ENDIAN
#else
#define __BYTE_ORDER    __BIG_ENDIAN
#endif

/* Legacy BSD types */
typedef unsigned char   uchar;
typedef unsigned short  ushort;
typedef unsigned int    uint;
typedef unsigned long   ulong;

/* caddr_t for legacy compatibility */
typedef char *          caddr_t;

/* Memory types */
typedef unsigned long   fsblkcnt_t; /* File system block count */
typedef unsigned long   fsfilcnt_t; /* File system file count */

#ifdef __cplusplus
}
#endif

#endif /* _SYS_TYPES_H */
