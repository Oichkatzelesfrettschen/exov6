/**
 * @file epoll.h
 * @brief Linux-compatible epoll Interface
 *
 * Cleanroom implementation of epoll for FeuerBird exokernel.
 * Uses the unified Event Core for actual event management.
 *
 * epoll provides:
 * - Edge-triggered (EPOLLET) and level-triggered modes
 * - One-shot mode (EPOLLONESHOT)
 * - Exclusive wakeup (EPOLLEXCLUSIVE)
 * - File descriptor monitoring (read, write, error, hangup)
 */
#pragma once

#include <stdint.h>

/**
 * epoll events (compatible with Linux ABI)
 */
#define EPOLLIN         0x001   /* Readable */
#define EPOLLPRI        0x002   /* Priority data (OOB) */
#define EPOLLOUT        0x004   /* Writable */
#define EPOLLERR        0x008   /* Error condition */
#define EPOLLHUP        0x010   /* Hangup */
#define EPOLLNVAL       0x020   /* Invalid fd (not in Linux but useful) */
#define EPOLLRDNORM     0x040   /* Normal read data */
#define EPOLLRDBAND     0x080   /* Priority band read data */
#define EPOLLWRNORM     0x100   /* Normal write data */
#define EPOLLWRBAND     0x200   /* Priority band write data */
#define EPOLLMSG        0x400   /* Message available */
#define EPOLLRDHUP      0x2000  /* Peer closed connection */

/**
 * epoll control flags
 */
#define EPOLLET         (1 << 31)   /* Edge-triggered */
#define EPOLLONESHOT    (1 << 30)   /* One-shot mode */
#define EPOLLWAKEUP     (1 << 29)   /* Wakeup hint */
#define EPOLLEXCLUSIVE  (1 << 28)   /* Exclusive wakeup */

/**
 * epoll_ctl operations
 */
#define EPOLL_CTL_ADD   1   /* Add fd to epoll instance */
#define EPOLL_CTL_DEL   2   /* Remove fd from epoll instance */
#define EPOLL_CTL_MOD   3   /* Modify events for fd */

/**
 * epoll_create1 flags
 */
#define EPOLL_CLOEXEC   02000000    /* Set close-on-exec flag */

/**
 * epoll_event structure (Linux-compatible layout)
 * Note: The union is needed for Linux ABI compatibility
 */
struct epoll_event {
    uint32_t events;        /* Requested/returned events */
    union {
        void *ptr;          /* User pointer */
        int fd;             /* File descriptor */
        uint32_t u32;       /* 32-bit value */
        uint64_t u64;       /* 64-bit value */
    } data;
} __attribute__((packed));

/**
 * Create an epoll instance
 *
 * @param size      Hint for number of fds (ignored, kept for compat)
 * @return          epoll fd on success, -errno on failure
 */
int sys_epoll_create(int size);

/**
 * Create an epoll instance with flags
 *
 * @param flags     EPOLL_CLOEXEC or 0
 * @return          epoll fd on success, -errno on failure
 */
int sys_epoll_create1(int flags);

/**
 * Control an epoll instance
 *
 * @param epfd      epoll file descriptor
 * @param op        Operation (EPOLL_CTL_ADD/DEL/MOD)
 * @param fd        Target file descriptor
 * @param event     Event specification (for ADD/MOD)
 * @return          0 on success, -errno on failure
 */
int sys_epoll_ctl(int epfd, int op, int fd, struct epoll_event *event);

/**
 * Wait for events on an epoll instance
 *
 * @param epfd      epoll file descriptor
 * @param events    Output array for events
 * @param maxevents Maximum events to return
 * @param timeout   Timeout in milliseconds (-1 = infinite)
 * @return          Number of events, or -errno on failure
 */
int sys_epoll_wait(int epfd, struct epoll_event *events,
                   int maxevents, int timeout);

/**
 * Wait for events with signal mask
 *
 * @param epfd      epoll file descriptor
 * @param events    Output array for events
 * @param maxevents Maximum events to return
 * @param timeout   Timeout in milliseconds (-1 = infinite)
 * @param sigmask   Signal mask to apply during wait
 * @param sigsetsize Size of signal mask
 * @return          Number of events, or -errno on failure
 */
int sys_epoll_pwait(int epfd, struct epoll_event *events,
                    int maxevents, int timeout,
                    const void *sigmask, unsigned long sigsetsize);

/**
 * Wait for events with signal mask and timeout structure
 * (epoll_pwait2 - Linux 5.11+)
 *
 * @param epfd      epoll file descriptor
 * @param events    Output array for events
 * @param maxevents Maximum events to return
 * @param timeout   Timeout as timespec (NULL = infinite)
 * @param sigmask   Signal mask to apply during wait
 * @param sigsetsize Size of signal mask
 * @return          Number of events, or -errno on failure
 */
struct timespec;
int sys_epoll_pwait2(int epfd, struct epoll_event *events,
                     int maxevents, const struct timespec *timeout,
                     const void *sigmask, unsigned long sigsetsize);

/**
 * Initialize epoll subsystem
 * Called once at boot after evcore_init()
 */
void epoll_init(void);

