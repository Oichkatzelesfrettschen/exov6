/**
 * @file epoll.c
 * @brief Linux-compatible epoll Implementation
 *
 * Cleanroom epoll implementation for FeuerBird exokernel.
 * Uses the unified Event Core for actual event management.
 *
 * Key design decisions:
 * 1. Thin wrapper around evcore - translates epoll semantics
 * 2. epoll instance is stored in file table entry
 * 3. Event translation: EPOLL* flags -> EV_TYPE_* flags
 */

#include "epoll.h"
#include "../event/evcore.h"
#include "../defs.h"
#include "../proc.h"

/* Errno values */
#ifndef EINVAL
#define EINVAL 22
#endif
#ifndef ENOMEM
#define ENOMEM 12
#endif
#ifndef EBADF
#define EBADF 9
#endif
#ifndef EEXIST
#define EEXIST 17
#endif
#ifndef ENOENT
#define ENOENT 2
#endif
#ifndef EINTR
#define EINTR 4
#endif
#ifndef ENFILE
#define ENFILE 23
#endif
#ifndef EPERM
#define EPERM 1
#endif

/**
 * epoll instance structure
 * One per epoll file descriptor
 */
struct epoll_instance {
    struct ev_queue *eq;    /* Underlying event queue */
    int flags;              /* Creation flags */
};

/**
 * Maximum epoll instances per process
 */
#define MAX_EPOLL_INSTANCES 64

/**
 * Simple epoll instance registry
 * In a full implementation, this would be per-file-descriptor
 */
static struct {
    struct spinlock lock;
    struct epoll_instance *instances[MAX_EPOLL_INSTANCES];
    int count;
} epoll_registry;

/**
 * Translate epoll events to evcore types
 */
static uint16_t epoll_to_ev_types(uint32_t events) {
    uint16_t types = 0;

    if (events & (EPOLLIN | EPOLLRDNORM | EPOLLRDBAND)) {
        types |= EV_TYPE_READ;
    }
    if (events & (EPOLLOUT | EPOLLWRNORM | EPOLLWRBAND)) {
        types |= EV_TYPE_WRITE;
    }
    if (events & EPOLLERR) {
        types |= EV_TYPE_ERROR;
    }
    if (events & (EPOLLHUP | EPOLLRDHUP)) {
        types |= EV_TYPE_HUP;
    }
    if (events & EPOLLPRI) {
        types |= EV_TYPE_EXCEPT;
    }

    return types;
}

/**
 * Translate evcore types back to epoll events
 */
static uint32_t ev_types_to_epoll(uint16_t types) {
    uint32_t events = 0;

    if (types & EV_TYPE_READ) {
        events |= EPOLLIN | EPOLLRDNORM;
    }
    if (types & EV_TYPE_WRITE) {
        events |= EPOLLOUT | EPOLLWRNORM;
    }
    if (types & EV_TYPE_ERROR) {
        events |= EPOLLERR;
    }
    if (types & EV_TYPE_HUP) {
        events |= EPOLLHUP;
    }
    if (types & EV_TYPE_EXCEPT) {
        events |= EPOLLPRI;
    }

    return events;
}

/**
 * Translate epoll flags to evcore flags
 */
static uint16_t epoll_to_ev_flags(uint32_t events, int op) {
    uint16_t flags = 0;

    switch (op) {
        case EPOLL_CTL_ADD:
            flags |= EV_FLAG_ADD;
            break;
        case EPOLL_CTL_DEL:
            flags |= EV_FLAG_DELETE;
            break;
        case EPOLL_CTL_MOD:
            flags |= EV_FLAG_ADD;  /* Modify is add with replace */
            break;
    }

    if (events & EPOLLET) {
        flags |= EV_FLAG_EDGE;
    } else {
        flags |= EV_FLAG_LEVEL;
    }

    if (events & EPOLLONESHOT) {
        flags |= EV_FLAG_ONESHOT;
    }

    return flags;
}

/**
 * Allocate epoll instance
 */
static struct epoll_instance *epoll_alloc(void) {
    char *p = kalloc();
    if (!p) {
        return 0;
    }
    for (unsigned long i = 0; i < sizeof(struct epoll_instance); i++) {
        p[i] = 0;
    }
    return (struct epoll_instance *)p;
}

/**
 * Free epoll instance
 */
static void epoll_free(struct epoll_instance *ep) {
    if (ep) {
        if (ep->eq) {
            evcore_destroy(ep->eq);
        }
        kfree((char *)ep);
    }
}

/**
 * Register epoll instance and return pseudo-fd
 */
static int epoll_register(struct epoll_instance *ep) {
    acquire(&epoll_registry.lock);

    if (epoll_registry.count >= MAX_EPOLL_INSTANCES) {
        release(&epoll_registry.lock);
        return -ENFILE;
    }

    /* Find free slot, use index as pseudo-fd (offset by 1000 to avoid conflicts) */
    for (int i = 0; i < MAX_EPOLL_INSTANCES; i++) {
        if (epoll_registry.instances[i] == 0) {
            epoll_registry.instances[i] = ep;
            epoll_registry.count++;
            release(&epoll_registry.lock);
            return 1000 + i;  /* Pseudo-fd */
        }
    }

    release(&epoll_registry.lock);
    return -ENFILE;
}

/**
 * Lookup epoll instance by fd
 */
static struct epoll_instance *epoll_lookup(int epfd) {
    int idx = epfd - 1000;
    if (idx < 0 || idx >= MAX_EPOLL_INSTANCES) {
        return 0;
    }

    acquire(&epoll_registry.lock);
    struct epoll_instance *ep = epoll_registry.instances[idx];
    release(&epoll_registry.lock);

    return ep;
}

/**
 * Unregister and free epoll instance
 */
static void epoll_unregister(int epfd) {
    int idx = epfd - 1000;
    if (idx < 0 || idx >= MAX_EPOLL_INSTANCES) {
        return;
    }

    acquire(&epoll_registry.lock);
    struct epoll_instance *ep = epoll_registry.instances[idx];
    if (ep) {
        epoll_registry.instances[idx] = 0;
        epoll_registry.count--;
    }
    release(&epoll_registry.lock);

    if (ep) {
        epoll_free(ep);
    }
}

/**
 * Initialize epoll subsystem
 */
void epoll_init(void) {
    initlock(&epoll_registry.lock, "epoll_registry");
    for (int i = 0; i < MAX_EPOLL_INSTANCES; i++) {
        epoll_registry.instances[i] = 0;
    }
    epoll_registry.count = 0;
}

/**
 * Create an epoll instance
 */
int sys_epoll_create(int size) {
    /* size is ignored but must be positive for Linux compat */
    if (size <= 0) {
        return -EINVAL;
    }

    return sys_epoll_create1(0);
}

/**
 * Create an epoll instance with flags
 */
int sys_epoll_create1(int flags) {
    /* Only EPOLL_CLOEXEC is valid */
    if (flags & ~EPOLL_CLOEXEC) {
        return -EINVAL;
    }

    struct epoll_instance *ep = epoll_alloc();
    if (!ep) {
        return -ENOMEM;
    }

    ep->eq = evcore_create();
    if (!ep->eq) {
        epoll_free(ep);
        return -ENOMEM;
    }

    ep->flags = flags;

    int fd = epoll_register(ep);
    if (fd < 0) {
        epoll_free(ep);
        return fd;
    }

    return fd;
}

/**
 * Control an epoll instance
 */
int sys_epoll_ctl(int epfd, int op, int fd, struct epoll_event *event) {
    struct epoll_instance *ep = epoll_lookup(epfd);
    if (!ep) {
        return -EBADF;
    }

    /* Validate operation */
    if (op != EPOLL_CTL_ADD && op != EPOLL_CTL_DEL && op != EPOLL_CTL_MOD) {
        return -EINVAL;
    }

    /* DEL doesn't need event, ADD/MOD do */
    if (op != EPOLL_CTL_DEL && !event) {
        return -EINVAL;
    }

    /* Cannot add epoll fd to itself */
    if (fd == epfd) {
        return -EINVAL;
    }

    uint16_t types = 0;
    uint16_t flags = 0;
    void *udata = 0;

    if (event) {
        types = epoll_to_ev_types(event->events);
        flags = epoll_to_ev_flags(event->events, op);
        udata = event->data.ptr;
    } else {
        flags = EV_FLAG_DELETE;
    }

    return evcore_ctl(ep->eq, (uintptr_t)fd, EV_SRC_FD,
                      types, flags, 0, 0, udata);
}

/**
 * Wait for events on an epoll instance
 */
int sys_epoll_wait(int epfd, struct epoll_event *events,
                   int maxevents, int timeout) {
    struct epoll_instance *ep = epoll_lookup(epfd);
    if (!ep) {
        return -EBADF;
    }

    if (!events || maxevents <= 0) {
        return -EINVAL;
    }

    /* Convert timeout to nanoseconds (-1 = infinite) */
    int64_t timeout_ns;
    if (timeout < 0) {
        timeout_ns = -1;  /* Infinite */
    } else if (timeout == 0) {
        timeout_ns = 0;   /* Non-blocking poll */
    } else {
        timeout_ns = (int64_t)timeout * 1000000LL;  /* ms to ns */
    }

    /* Allocate temporary buffer for evcore results */
    struct ev_result *results = (struct ev_result *)kalloc();
    if (!results) {
        return -ENOMEM;
    }

    /* Limit to what fits in a page */
    int max_results = 4096 / sizeof(struct ev_result);
    if (maxevents > max_results) {
        maxevents = max_results;
    }

    int count = evcore_wait(ep->eq, results, maxevents, timeout_ns);

    if (count > 0) {
        /* Translate results to epoll format */
        for (int i = 0; i < count; i++) {
            events[i].events = ev_types_to_epoll(results[i].events);
            events[i].data.ptr = results[i].udata;
        }
    }

    kfree((char *)results);

    return count;
}

/**
 * Wait for events with signal mask
 */
int sys_epoll_pwait(int epfd, struct epoll_event *events,
                    int maxevents, int timeout,
                    const void *sigmask, unsigned long sigsetsize) {
    /* TODO: Apply signal mask during wait */
    (void)sigmask;
    (void)sigsetsize;

    return sys_epoll_wait(epfd, events, maxevents, timeout);
}

/**
 * Wait for events with timespec timeout
 */
int sys_epoll_pwait2(int epfd, struct epoll_event *events,
                     int maxevents, const struct timespec *timeout,
                     const void *sigmask, unsigned long sigsetsize) {
    int timeout_ms;

    if (!timeout) {
        timeout_ms = -1;  /* Infinite */
    } else {
        /* Convert timespec to milliseconds */
        /* Note: Would need to read from userspace properly */
        timeout_ms = 0;  /* Placeholder */
    }

    return sys_epoll_pwait(epfd, events, maxevents, timeout_ms,
                           sigmask, sigsetsize);
}

