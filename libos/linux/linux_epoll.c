/**
 * @file linux_epoll.c
 * @brief Linux Epoll Event Notification
 *
 * Implements the epoll family of syscalls for scalable I/O event notification.
 * Epoll provides O(1) event notification for large numbers of file descriptors.
 *
 * Key design:
 * - Red-black tree for registered FDs (O(log n) add/remove)
 * - Ready list for events (O(1) notification)
 * - Level-triggered (default) and edge-triggered modes
 *
 * References:
 * - https://man7.org/linux/man-pages/man7/epoll.7.html
 * - https://copyconstruct.medium.com/the-method-to-epolls-madness-d9d2d6378642
 */

#include "linux_syscall.h"
#include <errno.h>
#include <stdlib.h>
#include <string.h>
#include <stdatomic.h>

/*
 * ============================================================================
 * Epoll Data Structures
 * ============================================================================
 */

#define EPOLL_MAX_INSTANCES     256
#define EPOLL_MAX_ITEMS         4096

/* Epoll item - represents one monitored file descriptor */
struct epitem {
    int                     fd;         /* Monitored file descriptor */
    uint32_t                events;     /* Monitored events */
    uint64_t                data;       /* User data */

    /* Tree linkage (simplified - would use RB-tree) */
    struct epitem          *left;
    struct epitem          *right;
    struct epitem          *parent;

    /* Ready list linkage */
    struct epitem          *ready_next;
    int                     on_ready_list;
};

/* Epoll instance */
struct eventpoll {
    int                     epfd;       /* Epoll file descriptor */
    _Atomic(int)            refcount;

    /* Registered items (simplified tree) */
    struct epitem          *items;      /* Array for simplicity */
    int                     item_count;
    int                     item_capacity;

    /* Ready list */
    struct epitem          *ready_list;
    _Atomic(int)            ready_count;

    /* Synchronization */
    _Atomic(int)            lock;

    /* Wait queue */
    _Atomic(int)            waiters;
};

/* Epoll instance table */
static struct eventpoll *epoll_table[EPOLL_MAX_INSTANCES];
static _Atomic(int) next_epfd = 1000;  /* Start above normal FDs */
static _Atomic(int) epoll_lock = 0;

static void lock_epoll_table(void) {
    int expected = 0;
    while (!atomic_compare_exchange_weak(&epoll_lock, &expected, 1))
        expected = 0;
}

static void unlock_epoll_table(void) {
    atomic_store(&epoll_lock, 0);
}

static void lock_ep(struct eventpoll *ep) {
    int expected = 0;
    while (!atomic_compare_exchange_weak(&ep->lock, &expected, 1))
        expected = 0;
}

static void unlock_ep(struct eventpoll *ep) {
    atomic_store(&ep->lock, 0);
}

/*
 * ============================================================================
 * Epoll Instance Management
 * ============================================================================
 */

static struct eventpoll *alloc_eventpoll(void)
{
    struct eventpoll *ep = calloc(1, sizeof(*ep));
    if (ep == NULL)
        return NULL;

    ep->epfd = atomic_fetch_add(&next_epfd, 1);
    atomic_store(&ep->refcount, 1);
    ep->item_capacity = 64;
    ep->items = calloc(ep->item_capacity, sizeof(struct epitem));
    if (ep->items == NULL) {
        free(ep);
        return NULL;
    }

    /* Add to table */
    lock_epoll_table();
    int idx = ep->epfd % EPOLL_MAX_INSTANCES;
    epoll_table[idx] = ep;
    unlock_epoll_table();

    return ep;
}

static struct eventpoll *get_eventpoll(int epfd)
{
    lock_epoll_table();
    int idx = epfd % EPOLL_MAX_INSTANCES;
    struct eventpoll *ep = epoll_table[idx];
    if (ep && ep->epfd == epfd) {
        atomic_fetch_add(&ep->refcount, 1);
    } else {
        ep = NULL;
    }
    unlock_epoll_table();
    return ep;
}

static void put_eventpoll(struct eventpoll *ep)
{
    if (ep == NULL)
        return;

    if (atomic_fetch_sub(&ep->refcount, 1) == 1) {
        /* Last reference - free */
        lock_epoll_table();
        int idx = ep->epfd % EPOLL_MAX_INSTANCES;
        if (epoll_table[idx] == ep)
            epoll_table[idx] = NULL;
        unlock_epoll_table();

        free(ep->items);
        free(ep);
    }
}

/*
 * ============================================================================
 * Epoll Item Management
 * ============================================================================
 */

static struct epitem *find_epitem(struct eventpoll *ep, int fd)
{
    for (int i = 0; i < ep->item_count; i++) {
        if (ep->items[i].fd == fd)
            return &ep->items[i];
    }
    return NULL;
}

static int add_epitem(struct eventpoll *ep, int fd, uint32_t events, uint64_t data)
{
    /* Check if already exists */
    if (find_epitem(ep, fd) != NULL)
        return -EEXIST;

    /* Expand array if needed */
    if (ep->item_count >= ep->item_capacity) {
        int new_cap = ep->item_capacity * 2;
        struct epitem *new_items = realloc(ep->items, new_cap * sizeof(struct epitem));
        if (new_items == NULL)
            return -ENOMEM;
        ep->items = new_items;
        ep->item_capacity = new_cap;
    }

    /* Add new item */
    struct epitem *item = &ep->items[ep->item_count++];
    memset(item, 0, sizeof(*item));
    item->fd = fd;
    item->events = events;
    item->data = data;

    return 0;
}

static int remove_epitem(struct eventpoll *ep, int fd)
{
    for (int i = 0; i < ep->item_count; i++) {
        if (ep->items[i].fd == fd) {
            /* Remove from ready list if present */
            if (ep->items[i].on_ready_list) {
                /* Would remove from ready list */
                atomic_fetch_sub(&ep->ready_count, 1);
            }

            /* Swap with last and shrink */
            if (i < ep->item_count - 1) {
                ep->items[i] = ep->items[ep->item_count - 1];
            }
            ep->item_count--;
            return 0;
        }
    }
    return -ENOENT;
}

/*
 * ============================================================================
 * Epoll Syscalls
 * ============================================================================
 */

/**
 * linux_sys_epoll_create - Create an epoll instance
 * @size: Ignored (kept for compatibility)
 *
 * Returns epoll file descriptor on success.
 */
long linux_sys_epoll_create(int size)
{
    if (size <= 0)
        return -EINVAL;

    struct eventpoll *ep = alloc_eventpoll();
    if (ep == NULL)
        return -ENOMEM;

    return ep->epfd;
}

/**
 * linux_sys_epoll_create1 - Create an epoll instance with flags
 * @flags: EPOLL_CLOEXEC
 */
long linux_sys_epoll_create1(int flags)
{
    if (flags & ~EPOLL_CLOEXEC)
        return -EINVAL;

    struct eventpoll *ep = alloc_eventpoll();
    if (ep == NULL)
        return -ENOMEM;

    /* Would set CLOEXEC flag on fd if requested */

    return ep->epfd;
}

/**
 * linux_sys_epoll_ctl - Control an epoll instance
 * @epfd: Epoll file descriptor
 * @op: Operation (EPOLL_CTL_ADD, EPOLL_CTL_MOD, EPOLL_CTL_DEL)
 * @fd: Target file descriptor
 * @event: Event configuration
 */
long linux_sys_epoll_ctl(int epfd, int op, int fd, struct linux_epoll_event *event)
{
    struct eventpoll *ep = get_eventpoll(epfd);
    int error = 0;

    if (ep == NULL)
        return -EBADF;

    /* Can't add epoll to itself */
    if (fd == epfd) {
        put_eventpoll(ep);
        return -EINVAL;
    }

    lock_ep(ep);

    switch (op) {
    case EPOLL_CTL_ADD:
        if (event == NULL) {
            error = -EFAULT;
            break;
        }
        error = add_epitem(ep, fd, event->events, event->data);
        break;

    case EPOLL_CTL_MOD:
        if (event == NULL) {
            error = -EFAULT;
            break;
        }
        {
            struct epitem *item = find_epitem(ep, fd);
            if (item == NULL) {
                error = -ENOENT;
            } else {
                item->events = event->events;
                item->data = event->data;
            }
        }
        break;

    case EPOLL_CTL_DEL:
        error = remove_epitem(ep, fd);
        break;

    default:
        error = -EINVAL;
        break;
    }

    unlock_ep(ep);
    put_eventpoll(ep);

    return error;
}

/**
 * check_fd_events - Check if a file descriptor has pending events
 *
 * In a real implementation, this would check the actual FD state.
 * Here we simulate it based on FD type.
 */
static uint32_t check_fd_events(int fd, uint32_t requested)
{
    /* Simulate: always readable/writable for now */
    uint32_t available = EPOLLIN | EPOLLOUT;

    /* Filter by requested events */
    return available & requested;
}

/**
 * linux_sys_epoll_wait - Wait for events on an epoll instance
 * @epfd: Epoll file descriptor
 * @events: Buffer for returned events
 * @maxevents: Maximum events to return
 * @timeout: Timeout in milliseconds (-1 = infinite, 0 = immediate)
 */
long linux_sys_epoll_wait(int epfd, struct linux_epoll_event *events,
                          int maxevents, int timeout)
{
    struct eventpoll *ep;
    int ready = 0;

    if (maxevents <= 0 || events == NULL)
        return -EINVAL;

    ep = get_eventpoll(epfd);
    if (ep == NULL)
        return -EBADF;

    lock_ep(ep);

    /* Check all monitored FDs for events */
    for (int i = 0; i < ep->item_count && ready < maxevents; i++) {
        struct epitem *item = &ep->items[i];
        uint32_t revents = check_fd_events(item->fd, item->events);

        if (revents) {
            events[ready].events = revents;
            events[ready].data = item->data;
            ready++;

            /* For edge-triggered, would mark as not ready until new event */
            if (item->events & EPOLLET) {
                /* Would need actual FD state tracking */
            }

            /* For EPOLLONESHOT, disable monitoring */
            if (item->events & EPOLLONESHOT) {
                item->events = 0;
            }
        }
    }

    unlock_ep(ep);

    /* If no events and timeout != 0, would sleep here */
    if (ready == 0 && timeout != 0) {
        atomic_fetch_add(&ep->waiters, 1);
        /* Would sleep until:
         * 1. Events become available
         * 2. Timeout expires
         * 3. Signal interrupts
         */
        atomic_fetch_sub(&ep->waiters, 1);

        /* Check again after "sleep" */
        lock_ep(ep);
        for (int i = 0; i < ep->item_count && ready < maxevents; i++) {
            struct epitem *item = &ep->items[i];
            uint32_t revents = check_fd_events(item->fd, item->events);
            if (revents) {
                events[ready].events = revents;
                events[ready].data = item->data;
                ready++;
            }
        }
        unlock_ep(ep);
    }

    put_eventpoll(ep);
    return ready;
}

/**
 * linux_sys_epoll_pwait - Wait for events with signal mask
 */
long linux_sys_epoll_pwait(int epfd, struct linux_epoll_event *events,
                           int maxevents, int timeout,
                           const uint64_t *sigmask, size_t sigsetsize)
{
    /* Would apply signal mask during wait */
    (void)sigmask;
    (void)sigsetsize;

    return linux_sys_epoll_wait(epfd, events, maxevents, timeout);
}

/**
 * linux_sys_epoll_pwait2 - Wait with timespec timeout
 */
long linux_sys_epoll_pwait2(int epfd, struct linux_epoll_event *events,
                            int maxevents, const struct linux_timespec *timeout,
                            const uint64_t *sigmask, size_t sigsetsize)
{
    int timeout_ms = -1;

    if (timeout) {
        timeout_ms = timeout->tv_sec * 1000 + timeout->tv_nsec / 1000000;
    }

    return linux_sys_epoll_pwait(epfd, events, maxevents, timeout_ms,
                                 sigmask, sigsetsize);
}

/*
 * ============================================================================
 * Select/Poll Implementation
 * ============================================================================
 */

/**
 * linux_sys_select - Synchronous I/O multiplexing
 */
long linux_sys_select(int nfds, void *readfds, void *writefds,
                      void *exceptfds, struct linux_timeval *timeout)
{
    int ready = 0;
    uint64_t *rfds = readfds;
    uint64_t *wfds = writefds;
    uint64_t *efds = exceptfds;

    if (nfds < 0 || nfds > 1024)
        return -EINVAL;

    /* Check each file descriptor */
    for (int fd = 0; fd < nfds; fd++) {
        int word = fd / 64;
        uint64_t bit = 1ULL << (fd % 64);

        /* Check read */
        if (rfds && (rfds[word] & bit)) {
            /* Would check if fd is readable */
            /* For now, assume ready */
            ready++;
        }

        /* Check write */
        if (wfds && (wfds[word] & bit)) {
            ready++;
        }

        /* Check exception */
        if (efds && (efds[word] & bit)) {
            /* Clear - no exceptions */
            efds[word] &= ~bit;
        }
    }

    return ready;
}

/**
 * linux_sys_pselect6 - Select with timespec and signal mask
 */
long linux_sys_pselect6(int nfds, void *readfds, void *writefds,
                        void *exceptfds, const struct linux_timespec *timeout,
                        const void *sigmask)
{
    struct linux_timeval tv;
    struct linux_timeval *tvp = NULL;

    if (timeout) {
        tv.tv_sec = timeout->tv_sec;
        tv.tv_usec = timeout->tv_nsec / 1000;
        tvp = &tv;
    }

    /* Would apply signal mask */
    (void)sigmask;

    return linux_sys_select(nfds, readfds, writefds, exceptfds, tvp);
}

/* Poll fd structure */
struct linux_pollfd {
    int     fd;
    short   events;
    short   revents;
};

/**
 * linux_sys_poll - Wait for events on file descriptors
 */
long linux_sys_poll(void *fds, unsigned int nfds, int timeout)
{
    struct linux_pollfd *pfds = fds;
    int ready = 0;

    if (pfds == NULL && nfds > 0)
        return -EFAULT;

    for (unsigned int i = 0; i < nfds; i++) {
        pfds[i].revents = 0;

        /* Check for requested events */
        if (pfds[i].events & EPOLLIN) {
            /* Would check if readable */
            pfds[i].revents |= EPOLLIN;
        }
        if (pfds[i].events & EPOLLOUT) {
            pfds[i].revents |= EPOLLOUT;
        }

        if (pfds[i].revents)
            ready++;
    }

    /* Would sleep if no events and timeout != 0 */

    return ready;
}

/**
 * linux_sys_ppoll - Poll with timespec and signal mask
 */
long linux_sys_ppoll(void *fds, unsigned int nfds,
                     const struct linux_timespec *tmo,
                     const uint64_t *sigmask, size_t sigsetsize)
{
    int timeout_ms = -1;

    if (tmo) {
        timeout_ms = tmo->tv_sec * 1000 + tmo->tv_nsec / 1000000;
    }

    (void)sigmask;
    (void)sigsetsize;

    return linux_sys_poll(fds, nfds, timeout_ms);
}

/*
 * ============================================================================
 * Timer/Event FDs (Stubs)
 * ============================================================================
 */

long linux_sys_timerfd_create(int clockid, int flags)
{
    (void)clockid;
    (void)flags;
    return -ENOSYS;  /* TODO */
}

long linux_sys_timerfd_settime(int fd, int flags, const void *new_value, void *old_value)
{
    (void)fd;
    (void)flags;
    (void)new_value;
    (void)old_value;
    return -ENOSYS;
}

long linux_sys_timerfd_gettime(int fd, void *curr_value)
{
    (void)fd;
    (void)curr_value;
    return -ENOSYS;
}

long linux_sys_eventfd(unsigned int initval)
{
    (void)initval;
    return -ENOSYS;  /* TODO */
}

long linux_sys_eventfd2(unsigned int initval, int flags)
{
    (void)initval;
    (void)flags;
    return -ENOSYS;
}

long linux_sys_signalfd(int fd, const uint64_t *mask, size_t sizemask)
{
    (void)fd;
    (void)mask;
    (void)sizemask;
    return -ENOSYS;
}

long linux_sys_signalfd4(int fd, const uint64_t *mask, size_t sizemask, int flags)
{
    (void)fd;
    (void)mask;
    (void)sizemask;
    (void)flags;
    return -ENOSYS;
}

/*
 * ============================================================================
 * Inotify (Stubs)
 * ============================================================================
 */

long linux_sys_inotify_init(void)
{
    return -ENOSYS;  /* TODO */
}

long linux_sys_inotify_init1(int flags)
{
    (void)flags;
    return -ENOSYS;
}

long linux_sys_inotify_add_watch(int fd, const char *pathname, uint32_t mask)
{
    (void)fd;
    (void)pathname;
    (void)mask;
    return -ENOSYS;
}

long linux_sys_inotify_rm_watch(int fd, int wd)
{
    (void)fd;
    (void)wd;
    return -ENOSYS;
}
