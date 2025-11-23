/**
 * @file linux_io_uring.c
 * @brief Linux io_uring async I/O implementation
 *
 * io_uring is Linux's modern async I/O interface, providing:
 * - Submission queue (SQ) for I/O requests
 * - Completion queue (CQ) for results
 * - Zero-copy operations
 * - Batched syscalls
 * - Kernel-side polling
 *
 * This implementation provides the core io_uring syscalls:
 * - io_uring_setup
 * - io_uring_enter
 * - io_uring_register
 */

#include "linux_syscall.h"
#include <stddef.h>
#include <stdint.h>
#include <stdbool.h>

/* Forward declarations */
extern void *exo_alloc_pages(size_t count);
extern void exo_free_pages(void *addr, size_t count);
extern ssize_t exo_read(int fd, void *buf, size_t count);
extern ssize_t exo_write(int fd, const void *buf, size_t count);
extern off_t exo_seek(int fd, off_t offset, int whence);
extern int exo_thread_yield(void);

/*============================================================================
 * io_uring Constants
 *============================================================================*/

/* Setup flags */
#define IORING_SETUP_IOPOLL         (1U << 0)   /* io_context is polled */
#define IORING_SETUP_SQPOLL         (1U << 1)   /* SQ poll thread */
#define IORING_SETUP_SQ_AFF         (1U << 2)   /* SQ affinity */
#define IORING_SETUP_CQSIZE         (1U << 3)   /* CQ entries count */
#define IORING_SETUP_CLAMP          (1U << 4)   /* Clamp SQ/CQ sizes */
#define IORING_SETUP_ATTACH_WQ      (1U << 5)   /* Attach to existing wq */
#define IORING_SETUP_R_DISABLED     (1U << 6)   /* Start with ring disabled */
#define IORING_SETUP_SUBMIT_ALL     (1U << 7)   /* Continue submit on error */
#define IORING_SETUP_COOP_TASKRUN   (1U << 8)   /* Cooperative task running */
#define IORING_SETUP_TASKRUN_FLAG   (1U << 9)   /* CQRING with taskrun flag */
#define IORING_SETUP_SQE128         (1U << 10)  /* 128-byte SQE */
#define IORING_SETUP_CQE32          (1U << 11)  /* 32-byte CQE */

/* Enter flags */
#define IORING_ENTER_GETEVENTS      (1U << 0)   /* Wait for events */
#define IORING_ENTER_SQ_WAKEUP      (1U << 1)   /* Wake SQ thread */
#define IORING_ENTER_SQ_WAIT        (1U << 2)   /* Wait for SQ space */
#define IORING_ENTER_EXT_ARG        (1U << 3)   /* Extended arguments */
#define IORING_ENTER_REGISTERED_RING (1U << 4)  /* Registered ring */

/* Feature flags */
#define IORING_FEAT_SINGLE_MMAP     (1U << 0)
#define IORING_FEAT_NODROP          (1U << 1)
#define IORING_FEAT_SUBMIT_STABLE   (1U << 2)
#define IORING_FEAT_RW_CUR_POS      (1U << 3)
#define IORING_FEAT_CUR_PERSONALITY (1U << 4)
#define IORING_FEAT_FAST_POLL       (1U << 5)
#define IORING_FEAT_POLL_32BITS     (1U << 6)
#define IORING_FEAT_SQPOLL_NONFIXED (1U << 7)
#define IORING_FEAT_EXT_ARG         (1U << 8)
#define IORING_FEAT_NATIVE_WORKERS  (1U << 9)
#define IORING_FEAT_RSRC_TAGS       (1U << 10)

/* Operation codes */
#define IORING_OP_NOP               0
#define IORING_OP_READV             1
#define IORING_OP_WRITEV            2
#define IORING_OP_FSYNC             3
#define IORING_OP_READ_FIXED        4
#define IORING_OP_WRITE_FIXED       5
#define IORING_OP_POLL_ADD          6
#define IORING_OP_POLL_REMOVE       7
#define IORING_OP_SYNC_FILE_RANGE   8
#define IORING_OP_SENDMSG           9
#define IORING_OP_RECVMSG           10
#define IORING_OP_TIMEOUT           11
#define IORING_OP_TIMEOUT_REMOVE    12
#define IORING_OP_ACCEPT            13
#define IORING_OP_ASYNC_CANCEL      14
#define IORING_OP_LINK_TIMEOUT      15
#define IORING_OP_CONNECT           16
#define IORING_OP_FALLOCATE         17
#define IORING_OP_OPENAT            18
#define IORING_OP_CLOSE             19
#define IORING_OP_FILES_UPDATE      20
#define IORING_OP_STATX             21
#define IORING_OP_READ              22
#define IORING_OP_WRITE             23
#define IORING_OP_FADVISE           24
#define IORING_OP_MADVISE           25
#define IORING_OP_SEND              26
#define IORING_OP_RECV              27
#define IORING_OP_OPENAT2           28
#define IORING_OP_EPOLL_CTL         29
#define IORING_OP_SPLICE            30
#define IORING_OP_PROVIDE_BUFFERS   31
#define IORING_OP_REMOVE_BUFFERS    32
#define IORING_OP_TEE               33
#define IORING_OP_SHUTDOWN          34
#define IORING_OP_RENAMEAT          35
#define IORING_OP_UNLINKAT          36
#define IORING_OP_MKDIRAT           37
#define IORING_OP_SYMLINKAT         38
#define IORING_OP_LINKAT            39
#define IORING_OP_LAST              40

/* SQE flags */
#define IOSQE_FIXED_FILE            (1U << 0)
#define IOSQE_IO_DRAIN              (1U << 1)
#define IOSQE_IO_LINK               (1U << 2)
#define IOSQE_IO_HARDLINK           (1U << 3)
#define IOSQE_ASYNC                 (1U << 4)
#define IOSQE_BUFFER_SELECT         (1U << 5)
#define IOSQE_CQE_SKIP_SUCCESS      (1U << 6)

/* CQE flags */
#define IORING_CQE_F_BUFFER         (1U << 0)
#define IORING_CQE_F_MORE           (1U << 1)
#define IORING_CQE_F_SOCK_NONEMPTY  (1U << 2)
#define IORING_CQE_F_NOTIF          (1U << 3)

/* Register opcodes */
#define IORING_REGISTER_BUFFERS     0
#define IORING_UNREGISTER_BUFFERS   1
#define IORING_REGISTER_FILES       2
#define IORING_UNREGISTER_FILES     3
#define IORING_REGISTER_EVENTFD     4
#define IORING_UNREGISTER_EVENTFD   5
#define IORING_REGISTER_FILES_UPDATE 6
#define IORING_REGISTER_EVENTFD_ASYNC 7
#define IORING_REGISTER_PROBE       8
#define IORING_REGISTER_PERSONALITY 9
#define IORING_UNREGISTER_PERSONALITY 10
#define IORING_REGISTER_RESTRICTIONS 11
#define IORING_REGISTER_ENABLE_RINGS 12

/*============================================================================
 * io_uring Data Structures
 *============================================================================*/

/**
 * Submission Queue Entry (SQE) - 64 bytes
 */
struct io_uring_sqe {
    uint8_t     opcode;         /* Operation code */
    uint8_t     flags;          /* IOSQE_ flags */
    uint16_t    ioprio;         /* I/O priority */
    int32_t     fd;             /* File descriptor */
    union {
        uint64_t off;           /* Offset into file */
        uint64_t addr2;
    };
    union {
        uint64_t addr;          /* Buffer address */
        uint64_t splice_off_in;
    };
    uint32_t    len;            /* Buffer length */
    union {
        uint32_t rw_flags;
        uint32_t fsync_flags;
        uint16_t poll_events;
        uint32_t poll32_events;
        uint32_t sync_range_flags;
        uint32_t msg_flags;
        uint32_t timeout_flags;
        uint32_t accept_flags;
        uint32_t cancel_flags;
        uint32_t open_flags;
        uint32_t statx_flags;
        uint32_t fadvise_advice;
        uint32_t splice_flags;
        uint32_t rename_flags;
        uint32_t unlink_flags;
        uint32_t hardlink_flags;
    };
    uint64_t    user_data;      /* Data passed back at completion */
    union {
        uint16_t buf_index;     /* Index into fixed buffers */
        uint16_t buf_group;     /* Buffer group */
    };
    uint16_t    personality;    /* Personality to use */
    union {
        int32_t splice_fd_in;
        uint32_t file_index;
    };
    uint64_t    __pad2[2];
};

/**
 * Completion Queue Entry (CQE) - 16 bytes
 */
struct io_uring_cqe {
    uint64_t    user_data;      /* sqe->user_data */
    int32_t     res;            /* Result code */
    uint32_t    flags;          /* IORING_CQE_F_* flags */
};

/**
 * Offsets for mmap
 */
struct io_sqring_offsets {
    uint32_t    head;
    uint32_t    tail;
    uint32_t    ring_mask;
    uint32_t    ring_entries;
    uint32_t    flags;
    uint32_t    dropped;
    uint32_t    array;
    uint32_t    resv1;
    uint64_t    resv2;
};

struct io_cqring_offsets {
    uint32_t    head;
    uint32_t    tail;
    uint32_t    ring_mask;
    uint32_t    ring_entries;
    uint32_t    overflow;
    uint32_t    cqes;
    uint32_t    flags;
    uint32_t    resv1;
    uint64_t    resv2;
};

/**
 * io_uring_params - passed to io_uring_setup
 */
struct io_uring_params {
    uint32_t    sq_entries;
    uint32_t    cq_entries;
    uint32_t    flags;
    uint32_t    sq_thread_cpu;
    uint32_t    sq_thread_idle;
    uint32_t    features;
    uint32_t    wq_fd;
    uint32_t    resv[3];
    struct io_sqring_offsets sq_off;
    struct io_cqring_offsets cq_off;
};

/*============================================================================
 * io_uring Ring State
 *============================================================================*/

/**
 * Internal ring state
 */
struct io_ring {
    int fd;                         /* Ring file descriptor */
    uint32_t flags;                 /* Setup flags */

    /* Submission queue */
    uint32_t sq_entries;            /* Number of SQ entries */
    uint32_t sq_mask;               /* SQ entry mask */
    volatile uint32_t *sq_head;     /* Consumer head */
    volatile uint32_t *sq_tail;     /* Producer tail */
    volatile uint32_t *sq_flags;    /* Flags */
    volatile uint32_t *sq_dropped;  /* Dropped entries */
    uint32_t *sq_array;             /* Index array */
    struct io_uring_sqe *sqes;      /* SQE array */

    /* Completion queue */
    uint32_t cq_entries;            /* Number of CQ entries */
    uint32_t cq_mask;               /* CQ entry mask */
    volatile uint32_t *cq_head;     /* Consumer head */
    volatile uint32_t *cq_tail;     /* Producer tail */
    volatile uint32_t *cq_overflow; /* Overflow count */
    volatile uint32_t *cq_flags;    /* Flags */
    struct io_uring_cqe *cqes;      /* CQE array */

    /* Registered resources */
    struct linux_iovec *buffers;    /* Fixed buffers */
    int buffer_count;
    int *files;                     /* Fixed files */
    int file_count;

    /* Memory regions */
    void *sq_ring;                  /* SQ ring mmap */
    void *cq_ring;                  /* CQ ring mmap (may be same as sq_ring) */
    void *sqe_ring;                 /* SQE mmap */
    size_t sq_ring_size;
    size_t cq_ring_size;
    size_t sqe_size;

    bool active;
};

/* Ring table */
#define IO_RING_MAX 64
static struct io_ring rings[IO_RING_MAX];
static int ring_next_fd = 100;  /* Start above regular fds */

/*============================================================================
 * Helper Functions
 *============================================================================*/

/**
 * Find ring by fd
 */
static struct io_ring *find_ring(int fd)
{
    for (int i = 0; i < IO_RING_MAX; i++) {
        if (rings[i].active && rings[i].fd == fd) {
            return &rings[i];
        }
    }
    return NULL;
}

/**
 * Allocate a new ring
 */
static struct io_ring *alloc_ring(void)
{
    for (int i = 0; i < IO_RING_MAX; i++) {
        if (!rings[i].active) {
            rings[i].active = true;
            rings[i].fd = ring_next_fd++;
            return &rings[i];
        }
    }
    return NULL;
}

/**
 * Round up to power of 2
 */
static uint32_t roundup_pow2(uint32_t x)
{
    x--;
    x |= x >> 1;
    x |= x >> 2;
    x |= x >> 4;
    x |= x >> 8;
    x |= x >> 16;
    x++;
    return x;
}

/*============================================================================
 * io_uring_setup
 *============================================================================*/

/**
 * Setup an io_uring instance
 */
long linux_sys_io_uring_setup(uint32_t entries, struct io_uring_params *p)
{
    if (!p) {
        return -LINUX_EFAULT;
    }

    if (entries == 0 || entries > 32768) {
        return -LINUX_EINVAL;
    }

    /* Round entries to power of 2 */
    entries = roundup_pow2(entries);

    /* Allocate ring */
    struct io_ring *ring = alloc_ring();
    if (!ring) {
        return -LINUX_ENOMEM;
    }

    ring->flags = p->flags;
    ring->sq_entries = entries;
    ring->sq_mask = entries - 1;

    /* CQ is at least 2x SQ size */
    uint32_t cq_entries = entries * 2;
    if (p->flags & IORING_SETUP_CQSIZE) {
        if (p->cq_entries > cq_entries) {
            cq_entries = roundup_pow2(p->cq_entries);
        }
    }
    ring->cq_entries = cq_entries;
    ring->cq_mask = cq_entries - 1;

    /* Allocate SQ ring */
    size_t sq_ring_size = sizeof(uint32_t) * 8 + sizeof(uint32_t) * entries;
    ring->sq_ring_size = (sq_ring_size + 4095) & ~4095;
    ring->sq_ring = exo_alloc_pages(ring->sq_ring_size / 4096);
    if (!ring->sq_ring) {
        ring->active = false;
        return -LINUX_ENOMEM;
    }

    /* Setup SQ ring pointers */
    uint32_t *sq = (uint32_t *)ring->sq_ring;
    ring->sq_head = &sq[0];
    ring->sq_tail = &sq[1];
    ring->sq_flags = &sq[4];
    ring->sq_dropped = &sq[5];
    ring->sq_array = &sq[8];
    *ring->sq_head = 0;
    *ring->sq_tail = 0;
    *ring->sq_flags = 0;
    *ring->sq_dropped = 0;

    /* Allocate SQE array */
    ring->sqe_size = sizeof(struct io_uring_sqe) * entries;
    ring->sqe_size = (ring->sqe_size + 4095) & ~4095;
    ring->sqe_ring = exo_alloc_pages(ring->sqe_size / 4096);
    if (!ring->sqe_ring) {
        exo_free_pages(ring->sq_ring, ring->sq_ring_size / 4096);
        ring->active = false;
        return -LINUX_ENOMEM;
    }
    ring->sqes = (struct io_uring_sqe *)ring->sqe_ring;

    /* Allocate CQ ring */
    size_t cq_ring_size = sizeof(uint32_t) * 8 + sizeof(struct io_uring_cqe) * cq_entries;
    ring->cq_ring_size = (cq_ring_size + 4095) & ~4095;
    ring->cq_ring = exo_alloc_pages(ring->cq_ring_size / 4096);
    if (!ring->cq_ring) {
        exo_free_pages(ring->sq_ring, ring->sq_ring_size / 4096);
        exo_free_pages(ring->sqe_ring, ring->sqe_size / 4096);
        ring->active = false;
        return -LINUX_ENOMEM;
    }

    /* Setup CQ ring pointers */
    uint32_t *cq = (uint32_t *)ring->cq_ring;
    ring->cq_head = &cq[0];
    ring->cq_tail = &cq[1];
    ring->cq_overflow = &cq[4];
    ring->cq_flags = &cq[5];
    ring->cqes = (struct io_uring_cqe *)&cq[8];
    *ring->cq_head = 0;
    *ring->cq_tail = 0;
    *ring->cq_overflow = 0;
    *ring->cq_flags = 0;

    /* Fill in params */
    p->sq_entries = ring->sq_entries;
    p->cq_entries = ring->cq_entries;
    p->features = IORING_FEAT_SINGLE_MMAP | IORING_FEAT_NODROP |
                  IORING_FEAT_SUBMIT_STABLE | IORING_FEAT_RW_CUR_POS;

    /* SQ offsets */
    p->sq_off.head = 0;
    p->sq_off.tail = sizeof(uint32_t);
    p->sq_off.ring_mask = sizeof(uint32_t) * 2;
    p->sq_off.ring_entries = sizeof(uint32_t) * 3;
    p->sq_off.flags = sizeof(uint32_t) * 4;
    p->sq_off.dropped = sizeof(uint32_t) * 5;
    p->sq_off.array = sizeof(uint32_t) * 8;

    /* CQ offsets */
    p->cq_off.head = 0;
    p->cq_off.tail = sizeof(uint32_t);
    p->cq_off.ring_mask = sizeof(uint32_t) * 2;
    p->cq_off.ring_entries = sizeof(uint32_t) * 3;
    p->cq_off.overflow = sizeof(uint32_t) * 4;
    p->cq_off.flags = sizeof(uint32_t) * 5;
    p->cq_off.cqes = sizeof(uint32_t) * 8;

    /* Write ring_mask and ring_entries */
    sq[2] = ring->sq_mask;
    sq[3] = ring->sq_entries;
    cq[2] = ring->cq_mask;
    cq[3] = ring->cq_entries;

    return ring->fd;
}

/*============================================================================
 * io_uring_enter
 *============================================================================*/

/**
 * Process a single SQE
 */
static int process_sqe(struct io_ring *ring, struct io_uring_sqe *sqe,
                       struct io_uring_cqe *cqe)
{
    cqe->user_data = sqe->user_data;
    cqe->flags = 0;

    switch (sqe->opcode) {
    case IORING_OP_NOP:
        cqe->res = 0;
        break;

    case IORING_OP_READ:
        {
            int fd = sqe->fd;
            void *buf = (void *)(uintptr_t)sqe->addr;
            uint32_t len = sqe->len;
            off_t off = (off_t)sqe->off;

            if (off != (uint64_t)-1) {
                exo_seek(fd, off, 0);
            }
            cqe->res = exo_read(fd, buf, len);
        }
        break;

    case IORING_OP_WRITE:
        {
            int fd = sqe->fd;
            const void *buf = (const void *)(uintptr_t)sqe->addr;
            uint32_t len = sqe->len;
            off_t off = (off_t)sqe->off;

            if (off != (uint64_t)-1) {
                exo_seek(fd, off, 0);
            }
            cqe->res = exo_write(fd, buf, len);
        }
        break;

    case IORING_OP_READV:
        {
            int fd = sqe->fd;
            struct linux_iovec *iov = (struct linux_iovec *)(uintptr_t)sqe->addr;
            uint32_t iovcnt = sqe->len;
            off_t off = (off_t)sqe->off;

            if (off != (uint64_t)-1) {
                exo_seek(fd, off, 0);
            }

            ssize_t total = 0;
            for (uint32_t i = 0; i < iovcnt; i++) {
                ssize_t n = exo_read(fd, iov[i].iov_base, iov[i].iov_len);
                if (n < 0) {
                    cqe->res = (total > 0) ? total : n;
                    return 0;
                }
                total += n;
                if ((size_t)n < iov[i].iov_len) break;
            }
            cqe->res = total;
        }
        break;

    case IORING_OP_WRITEV:
        {
            int fd = sqe->fd;
            struct linux_iovec *iov = (struct linux_iovec *)(uintptr_t)sqe->addr;
            uint32_t iovcnt = sqe->len;
            off_t off = (off_t)sqe->off;

            if (off != (uint64_t)-1) {
                exo_seek(fd, off, 0);
            }

            ssize_t total = 0;
            for (uint32_t i = 0; i < iovcnt; i++) {
                ssize_t n = exo_write(fd, iov[i].iov_base, iov[i].iov_len);
                if (n < 0) {
                    cqe->res = (total > 0) ? total : n;
                    return 0;
                }
                total += n;
                if ((size_t)n < iov[i].iov_len) break;
            }
            cqe->res = total;
        }
        break;

    case IORING_OP_FSYNC:
        /* TODO: Implement fsync */
        cqe->res = 0;
        break;

    case IORING_OP_POLL_ADD:
    case IORING_OP_POLL_REMOVE:
        /* TODO: Implement poll operations */
        cqe->res = -LINUX_ENOSYS;
        break;

    case IORING_OP_TIMEOUT:
        {
            struct linux_timespec *ts = (struct linux_timespec *)(uintptr_t)sqe->addr;
            uint64_t timeout_ns = ts->tv_sec * 1000000000ULL + ts->tv_nsec;
            /* TODO: Implement actual timeout */
            (void)timeout_ns;
            cqe->res = -LINUX_ETIME;
        }
        break;

    case IORING_OP_CLOSE:
        {
            extern long linux_sys_close(int fd);
            cqe->res = linux_sys_close(sqe->fd);
        }
        break;

    case IORING_OP_OPENAT:
        {
            extern long linux_sys_openat(int dirfd, const char *pathname,
                                         int flags, int mode);
            int dirfd = sqe->fd;
            const char *path = (const char *)(uintptr_t)sqe->addr;
            int flags = sqe->open_flags;
            int mode = sqe->len;
            cqe->res = linux_sys_openat(dirfd, path, flags, mode);
        }
        break;

    case IORING_OP_READ_FIXED:
    case IORING_OP_WRITE_FIXED:
        {
            /* Use registered buffers */
            uint16_t buf_index = sqe->buf_index;
            if (!ring->buffers || buf_index >= ring->buffer_count) {
                cqe->res = -LINUX_EFAULT;
                break;
            }
            struct linux_iovec *iov = &ring->buffers[buf_index];

            if (sqe->opcode == IORING_OP_READ_FIXED) {
                cqe->res = exo_read(sqe->fd, iov->iov_base, sqe->len);
            } else {
                cqe->res = exo_write(sqe->fd, iov->iov_base, sqe->len);
            }
        }
        break;

    default:
        cqe->res = -LINUX_EINVAL;
        break;
    }

    return 0;
}

/**
 * Submit I/O requests and/or wait for completions
 */
long linux_sys_io_uring_enter(int fd, uint32_t to_submit, uint32_t min_complete,
                              uint32_t flags, const void *arg, size_t argsz)
{
    struct io_ring *ring = find_ring(fd);
    if (!ring) {
        return -LINUX_EBADF;
    }

    (void)arg;
    (void)argsz;

    uint32_t submitted = 0;

    /* Process submissions */
    if (to_submit > 0) {
        uint32_t sq_head = *ring->sq_head;
        uint32_t sq_tail = *ring->sq_tail;

        while (submitted < to_submit && sq_head != sq_tail) {
            uint32_t index = ring->sq_array[sq_head & ring->sq_mask];
            struct io_uring_sqe *sqe = &ring->sqes[index];

            /* Get CQE slot */
            uint32_t cq_tail = *ring->cq_tail;
            uint32_t cq_head = *ring->cq_head;

            if (cq_tail - cq_head >= ring->cq_entries) {
                /* CQ full */
                (*ring->cq_overflow)++;
                break;
            }

            struct io_uring_cqe *cqe = &ring->cqes[cq_tail & ring->cq_mask];

            /* Process the SQE */
            process_sqe(ring, sqe, cqe);

            /* Advance CQ tail */
            __atomic_store_n(ring->cq_tail, cq_tail + 1, __ATOMIC_RELEASE);

            sq_head++;
            submitted++;
        }

        /* Update SQ head */
        __atomic_store_n(ring->sq_head, sq_head, __ATOMIC_RELEASE);
    }

    /* Wait for completions if requested */
    if (flags & IORING_ENTER_GETEVENTS) {
        while (1) {
            uint32_t cq_head = *ring->cq_head;
            uint32_t cq_tail = *ring->cq_tail;
            uint32_t available = cq_tail - cq_head;

            if (available >= min_complete) {
                break;
            }

            /* Would need to wait - for now just yield */
            exo_thread_yield();

            /* In real implementation, would block here */
            break;
        }
    }

    return submitted;
}

/*============================================================================
 * io_uring_register
 *============================================================================*/

/**
 * Register buffers/files with io_uring
 */
long linux_sys_io_uring_register(int fd, unsigned int opcode,
                                 void *arg, unsigned int nr_args)
{
    struct io_ring *ring = find_ring(fd);
    if (!ring) {
        return -LINUX_EBADF;
    }

    switch (opcode) {
    case IORING_REGISTER_BUFFERS:
        {
            struct linux_iovec *iovs = (struct linux_iovec *)arg;
            if (!iovs || nr_args == 0) {
                return -LINUX_EINVAL;
            }

            /* Free existing buffers */
            if (ring->buffers) {
                exo_free_pages(ring->buffers,
                              (ring->buffer_count * sizeof(struct linux_iovec) + 4095) / 4096);
            }

            /* Allocate and copy buffer descriptors */
            size_t size = nr_args * sizeof(struct linux_iovec);
            ring->buffers = (struct linux_iovec *)exo_alloc_pages((size + 4095) / 4096);
            if (!ring->buffers) {
                return -LINUX_ENOMEM;
            }

            for (unsigned int i = 0; i < nr_args; i++) {
                ring->buffers[i] = iovs[i];
            }
            ring->buffer_count = nr_args;
            return 0;
        }

    case IORING_UNREGISTER_BUFFERS:
        if (ring->buffers) {
            exo_free_pages(ring->buffers,
                          (ring->buffer_count * sizeof(struct linux_iovec) + 4095) / 4096);
            ring->buffers = NULL;
            ring->buffer_count = 0;
        }
        return 0;

    case IORING_REGISTER_FILES:
        {
            int *fds = (int *)arg;
            if (!fds || nr_args == 0) {
                return -LINUX_EINVAL;
            }

            if (ring->files) {
                exo_free_pages(ring->files,
                              (ring->file_count * sizeof(int) + 4095) / 4096);
            }

            size_t size = nr_args * sizeof(int);
            ring->files = (int *)exo_alloc_pages((size + 4095) / 4096);
            if (!ring->files) {
                return -LINUX_ENOMEM;
            }

            for (unsigned int i = 0; i < nr_args; i++) {
                ring->files[i] = fds[i];
            }
            ring->file_count = nr_args;
            return 0;
        }

    case IORING_UNREGISTER_FILES:
        if (ring->files) {
            exo_free_pages(ring->files,
                          (ring->file_count * sizeof(int) + 4095) / 4096);
            ring->files = NULL;
            ring->file_count = 0;
        }
        return 0;

    case IORING_REGISTER_PROBE:
        {
            /* Return supported operations */
            struct io_uring_probe {
                uint8_t last_op;
                uint8_t ops_len;
                uint16_t resv;
                uint32_t resv2[3];
                struct {
                    uint8_t op;
                    uint8_t resv;
                    uint16_t flags;
                    uint32_t resv2;
                } ops[];
            } *probe = (struct io_uring_probe *)arg;

            if (!probe || nr_args < sizeof(struct io_uring_probe)) {
                return -LINUX_EINVAL;
            }

            probe->last_op = IORING_OP_LAST - 1;
            probe->ops_len = 0;
            return 0;
        }

    case IORING_REGISTER_ENABLE_RINGS:
        /* Enable the ring */
        return 0;

    default:
        return -LINUX_EINVAL;
    }
}

/*============================================================================
 * Cleanup
 *============================================================================*/

/**
 * Close an io_uring instance
 */
long linux_sys_io_uring_close(int fd)
{
    struct io_ring *ring = find_ring(fd);
    if (!ring) {
        return -LINUX_EBADF;
    }

    /* Free resources */
    if (ring->sq_ring) {
        exo_free_pages(ring->sq_ring, ring->sq_ring_size / 4096);
    }
    if (ring->cq_ring) {
        exo_free_pages(ring->cq_ring, ring->cq_ring_size / 4096);
    }
    if (ring->sqe_ring) {
        exo_free_pages(ring->sqe_ring, ring->sqe_size / 4096);
    }
    if (ring->buffers) {
        exo_free_pages(ring->buffers,
                      (ring->buffer_count * sizeof(struct linux_iovec) + 4095) / 4096);
    }
    if (ring->files) {
        exo_free_pages(ring->files,
                      (ring->file_count * sizeof(int) + 4095) / 4096);
    }

    ring->active = false;
    return 0;
}

/*============================================================================
 * Debugging Interface
 *============================================================================*/

/**
 * Get io_uring statistics
 */
int linux_get_io_uring_stats(int *active_rings, int *pending_sqes,
                             int *completed_cqes)
{
    int rings_count = 0;
    int pending = 0;
    int completed = 0;

    for (int i = 0; i < IO_RING_MAX; i++) {
        if (rings[i].active) {
            rings_count++;
            uint32_t sq_head = *rings[i].sq_head;
            uint32_t sq_tail = *rings[i].sq_tail;
            pending += (sq_tail - sq_head);

            uint32_t cq_head = *rings[i].cq_head;
            uint32_t cq_tail = *rings[i].cq_tail;
            completed += (cq_tail - cq_head);
        }
    }

    if (active_rings) *active_rings = rings_count;
    if (pending_sqes) *pending_sqes = pending;
    if (completed_cqes) *completed_cqes = completed;

    return 0;
}
