/**
 * @file kqueue.c
 * @brief BSD-compatible kqueue Implementation
 *
 * Cleanroom kqueue implementation for FeuerBird exokernel.
 * Uses the unified Event Core for actual event management.
 *
 * Key design decisions:
 * 1. Thin wrapper around evcore - translates kqueue semantics
 * 2. Filter types map to evcore source types
 * 3. kevent flags map to evcore flags
 */

#include "kqueue.h"
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
#ifndef ENOENT
#define ENOENT 2
#endif
#ifndef EINTR
#define EINTR 4
#endif
#ifndef ENFILE
#define ENFILE 23
#endif
#ifndef ESRCH
#define ESRCH 3
#endif

/**
 * kqueue instance structure
 */
struct kqueue_instance {
    struct ev_queue *eq;    /* Underlying event queue */
    int flags;              /* Creation flags */
};

/**
 * Maximum kqueue instances per process
 */
#define MAX_KQUEUE_INSTANCES 64

/**
 * Simple kqueue instance registry
 */
static struct {
    struct spinlock lock;
    struct kqueue_instance *instances[MAX_KQUEUE_INSTANCES];
    int count;
} kqueue_registry;

/**
 * Translate kqueue filter to evcore source type
 */
static int filter_to_src_type(int16_t filter) {
    switch (filter) {
        case EVFILT_READ:
        case EVFILT_WRITE:
            return EV_SRC_FD;
        case EVFILT_SIGNAL:
            return EV_SRC_SIGNAL;
        case EVFILT_TIMER:
            return EV_SRC_TIMER;
        case EVFILT_PROC:
            return EV_SRC_PROC;
        case EVFILT_VNODE:
            return EV_SRC_VNODE;
        case EVFILT_USER:
            return EV_SRC_USER;
        default:
            return -1;
    }
}

/**
 * Translate kqueue filter to evcore event types
 */
static uint16_t filter_to_ev_types(int16_t filter, uint32_t fflags) {
    switch (filter) {
        case EVFILT_READ:
            return EV_TYPE_READ;
        case EVFILT_WRITE:
            return EV_TYPE_WRITE;
        case EVFILT_SIGNAL:
            return EV_TYPE_SIGNAL;
        case EVFILT_TIMER:
            return EV_TYPE_TIMER;
        case EVFILT_PROC:
            return EV_TYPE_PROC;
        case EVFILT_VNODE:
            return EV_TYPE_VNODE;
        case EVFILT_USER:
            return EV_TYPE_USER;
        default:
            return 0;
    }
    (void)fflags;  /* Could use fflags to fine-tune types */
}

/**
 * Translate evcore types back to kqueue data
 */
static intptr_t ev_to_kqueue_data(int16_t filter, uint16_t events, int64_t data) {
    (void)events;
    /* For most filters, just return the data field */
    switch (filter) {
        case EVFILT_READ:
        case EVFILT_WRITE:
            return (intptr_t)data;  /* Number of bytes available */
        case EVFILT_TIMER:
            return (intptr_t)data;  /* Number of expirations */
        case EVFILT_PROC:
            return (intptr_t)data;  /* Exit status or child PID */
        default:
            return (intptr_t)data;
    }
}

/**
 * Translate kevent flags to evcore flags
 */
static uint16_t kqueue_to_ev_flags(uint16_t flags) {
    uint16_t ev_flags = 0;

    if (flags & EV_ADD) {
        ev_flags |= EV_FLAG_ADD;
    }
    if (flags & EV_DELETE) {
        ev_flags |= EV_FLAG_DELETE;
    }
    if (flags & EV_ENABLE) {
        ev_flags |= EV_FLAG_ENABLE;
    }
    if (flags & EV_DISABLE) {
        ev_flags |= EV_FLAG_DISABLE;
    }
    if (flags & EV_ONESHOT) {
        ev_flags |= EV_FLAG_ONESHOT;
    }
    if (flags & EV_CLEAR) {
        ev_flags |= EV_FLAG_CLEAR;
    }
    if (flags & EV_DISPATCH) {
        ev_flags |= EV_FLAG_DISPATCH;
    }

    return ev_flags;
}

/**
 * Allocate kqueue instance
 */
static struct kqueue_instance *kqueue_alloc(void) {
    char *p = kalloc();
    if (!p) {
        return 0;
    }
    for (unsigned long i = 0; i < sizeof(struct kqueue_instance); i++) {
        p[i] = 0;
    }
    return (struct kqueue_instance *)p;
}

/**
 * Free kqueue instance
 */
static void kqueue_free(struct kqueue_instance *kq) {
    if (kq) {
        if (kq->eq) {
            evcore_destroy(kq->eq);
        }
        kfree((char *)kq);
    }
}

/**
 * Register kqueue instance and return pseudo-fd
 */
static int kqueue_register(struct kqueue_instance *kq) {
    acquire(&kqueue_registry.lock);

    if (kqueue_registry.count >= MAX_KQUEUE_INSTANCES) {
        release(&kqueue_registry.lock);
        return -ENFILE;
    }

    /* Use offset of 2000 for kqueue fds (epoll uses 1000) */
    for (int i = 0; i < MAX_KQUEUE_INSTANCES; i++) {
        if (kqueue_registry.instances[i] == 0) {
            kqueue_registry.instances[i] = kq;
            kqueue_registry.count++;
            release(&kqueue_registry.lock);
            return 2000 + i;
        }
    }

    release(&kqueue_registry.lock);
    return -ENFILE;
}

/**
 * Lookup kqueue instance by fd
 */
static struct kqueue_instance *kqueue_lookup(int kqfd) {
    int idx = kqfd - 2000;
    if (idx < 0 || idx >= MAX_KQUEUE_INSTANCES) {
        return 0;
    }

    acquire(&kqueue_registry.lock);
    struct kqueue_instance *kq = kqueue_registry.instances[idx];
    release(&kqueue_registry.lock);

    return kq;
}

/**
 * Initialize kqueue subsystem
 */
void kqueue_init(void) {
    initlock(&kqueue_registry.lock, "kqueue_registry");
    for (int i = 0; i < MAX_KQUEUE_INSTANCES; i++) {
        kqueue_registry.instances[i] = 0;
    }
    kqueue_registry.count = 0;
}

/**
 * Create a new kqueue
 */
int sys_kqueue(void) {
    return sys_kqueue1(0);
}

/**
 * Create kqueue with flags
 */
int sys_kqueue1(int flags) {
    /* Only O_CLOEXEC (0x80000) is valid */
    (void)flags;  /* Accept any flags for now */

    struct kqueue_instance *kq = kqueue_alloc();
    if (!kq) {
        return -ENOMEM;
    }

    kq->eq = evcore_create();
    if (!kq->eq) {
        kqueue_free(kq);
        return -ENOMEM;
    }

    kq->flags = flags;

    int fd = kqueue_register(kq);
    if (fd < 0) {
        kqueue_free(kq);
        return fd;
    }

    return fd;
}

/**
 * Process a single kevent change
 */
static int process_kevent_change(struct kqueue_instance *kq,
                                 const struct kevent *kev) {
    int src_type = filter_to_src_type(kev->filter);
    if (src_type < 0) {
        return -EINVAL;
    }

    uint16_t types = filter_to_ev_types(kev->filter, kev->fflags);
    uint16_t flags = kqueue_to_ev_flags(kev->flags);

    return evcore_ctl(kq->eq, kev->ident, src_type,
                      types, flags, (uint16_t)kev->fflags,
                      (int64_t)kev->data, kev->udata);
}

/**
 * Register/modify/retrieve events
 */
int sys_kevent(int kqfd, const struct kevent *changelist, int nchanges,
               struct kevent *eventlist, int nevents,
               const struct kqueue_timespec *timeout) {
    struct kqueue_instance *kq = kqueue_lookup(kqfd);
    if (!kq) {
        return -EBADF;
    }

    /* Process changes first */
    if (changelist && nchanges > 0) {
        for (int i = 0; i < nchanges; i++) {
            int err = process_kevent_change(kq, &changelist[i]);
            if (err < 0) {
                /* If EV_RECEIPT is set, store error and continue */
                if (eventlist && nevents > 0 &&
                    (changelist[i].flags & EV_RECEIPT)) {
                    eventlist[0].ident = changelist[i].ident;
                    eventlist[0].filter = changelist[i].filter;
                    eventlist[0].flags = EV_ERROR;
                    eventlist[0].fflags = 0;
                    eventlist[0].data = -err;
                    eventlist[0].udata = changelist[i].udata;
                    return 1;
                }
                return err;
            }
        }
    }

    /* If no events requested, just return */
    if (!eventlist || nevents <= 0) {
        return 0;
    }

    /* Calculate timeout */
    int64_t timeout_ns;
    if (!timeout) {
        timeout_ns = -1;  /* Infinite */
    } else if (timeout->tv_sec == 0 && timeout->tv_nsec == 0) {
        timeout_ns = 0;   /* Non-blocking poll */
    } else {
        timeout_ns = timeout->tv_sec * 1000000000LL + timeout->tv_nsec;
    }

    /* Allocate temporary buffer for evcore results */
    struct ev_result *results = (struct ev_result *)kalloc();
    if (!results) {
        return -ENOMEM;
    }

    /* Limit to what fits in a page */
    int max_results = 4096 / sizeof(struct ev_result);
    if (nevents > max_results) {
        nevents = max_results;
    }

    int count = evcore_wait(kq->eq, results, nevents, timeout_ns);

    if (count > 0) {
        /* Translate results to kevent format */
        for (int i = 0; i < count; i++) {
            eventlist[i].ident = results[i].ident;

            /* Map source type back to filter */
            switch (results[i].src_type) {
                case EV_SRC_FD:
                    if (results[i].events & EV_TYPE_READ) {
                        eventlist[i].filter = EVFILT_READ;
                    } else {
                        eventlist[i].filter = EVFILT_WRITE;
                    }
                    break;
                case EV_SRC_SIGNAL:
                    eventlist[i].filter = EVFILT_SIGNAL;
                    break;
                case EV_SRC_TIMER:
                    eventlist[i].filter = EVFILT_TIMER;
                    break;
                case EV_SRC_PROC:
                    eventlist[i].filter = EVFILT_PROC;
                    break;
                case EV_SRC_VNODE:
                    eventlist[i].filter = EVFILT_VNODE;
                    break;
                case EV_SRC_USER:
                    eventlist[i].filter = EVFILT_USER;
                    break;
                default:
                    eventlist[i].filter = EVFILT_READ;
            }

            eventlist[i].flags = 0;
            if (results[i].flags & EV_FLAG_EOF) {
                eventlist[i].flags |= EV_EOF;
            }
            if (results[i].flags & EV_FLAG_ERROR) {
                eventlist[i].flags |= EV_ERROR;
            }

            eventlist[i].fflags = 0;
            eventlist[i].data = ev_to_kqueue_data(eventlist[i].filter,
                                                   results[i].events,
                                                   results[i].data);
            eventlist[i].udata = results[i].udata;
        }
    }

    kfree((char *)results);

    return count;
}

