/**
 * @file kqueue.h
 * @brief BSD-compatible kqueue Interface
 *
 * Cleanroom implementation of kqueue for FeuerBird exokernel.
 * Uses the unified Event Core for actual event management.
 *
 * kqueue provides:
 * - Multiple event types (fd, signal, timer, process, vnode, user)
 * - Edge and level triggered modes
 * - One-shot mode
 * - Arbitrary user data attachment
 */
#pragma once

#include <stdint.h>

/**
 * kevent structure (BSD-compatible layout)
 */
struct kevent {
    uintptr_t ident;        /* Identifier for event (fd, pid, signal, etc.) */
    int16_t filter;         /* Filter for event */
    uint16_t flags;         /* Action flags */
    uint32_t fflags;        /* Filter-specific flags */
    intptr_t data;          /* Filter-specific data */
    void *udata;            /* User data - opaque */
};

/**
 * Filter types (what kind of event)
 */
#define EVFILT_READ     (-1)    /* Readable */
#define EVFILT_WRITE    (-2)    /* Writable */
#define EVFILT_AIO      (-3)    /* AIO completion (not implemented) */
#define EVFILT_VNODE    (-4)    /* Vnode changes */
#define EVFILT_PROC     (-5)    /* Process events */
#define EVFILT_SIGNAL   (-6)    /* Signal delivery */
#define EVFILT_TIMER    (-7)    /* Timer events */
#define EVFILT_PROCDESC (-8)    /* Process descriptor (FreeBSD) */
#define EVFILT_FS       (-9)    /* Filesystem events (FreeBSD) */
#define EVFILT_LIO      (-10)   /* LIO completion (not implemented) */
#define EVFILT_USER     (-11)   /* User-triggered events */
#define EVFILT_SENDFILE (-12)   /* Sendfile events (FreeBSD) */
#define EVFILT_EMPTY    (-13)   /* Empty filter (FreeBSD) */
#define EVFILT_SYSCOUNT 13      /* Number of filters */

/**
 * Action flags
 */
#define EV_ADD          0x0001  /* Add event to kqueue */
#define EV_DELETE       0x0002  /* Remove event from kqueue */
#define EV_ENABLE       0x0004  /* Enable event */
#define EV_DISABLE      0x0008  /* Disable event */
#define EV_ONESHOT      0x0010  /* One-shot event */
#define EV_CLEAR        0x0020  /* Clear state after retrieval */
#define EV_RECEIPT      0x0040  /* Return receipt (EV_ERROR only) */
#define EV_DISPATCH     0x0080  /* Disable after delivery */
#define EV_DISPATCH2    (EV_DISPATCH | 0x0100)  /* Extended dispatch */
#define EV_UDATA_SPECIFIC 0x0100 /* Per-event udata tracking */

/**
 * Return flags (set by kernel)
 */
#define EV_EOF          0x8000  /* EOF condition */
#define EV_ERROR        0x4000  /* Error, data=errno */

/**
 * EVFILT_VNODE fflags
 */
#define NOTE_DELETE     0x0001  /* File was deleted */
#define NOTE_WRITE      0x0002  /* File was written */
#define NOTE_EXTEND     0x0004  /* File was extended */
#define NOTE_ATTRIB     0x0008  /* Attributes changed */
#define NOTE_LINK       0x0010  /* Link count changed */
#define NOTE_RENAME     0x0020  /* File was renamed */
#define NOTE_REVOKE     0x0040  /* Access revoked */
#define NOTE_OPEN       0x0080  /* File was opened */
#define NOTE_CLOSE      0x0100  /* File was closed */
#define NOTE_CLOSE_WRITE 0x0200 /* File closed after write */
#define NOTE_READ       0x0400  /* File was read */

/**
 * EVFILT_PROC fflags
 */
#define NOTE_EXIT       0x80000000  /* Process exited */
#define NOTE_FORK       0x40000000  /* Process forked */
#define NOTE_EXEC       0x20000000  /* Process exec'd */
#define NOTE_TRACK      0x00000001  /* Track across fork */
#define NOTE_TRACKERR   0x00000002  /* Track error */
#define NOTE_CHILD      0x00000004  /* Child created */

/**
 * EVFILT_TIMER fflags
 */
#define NOTE_SECONDS    0x00000001  /* Timer units: seconds */
#define NOTE_MSECONDS   0x00000002  /* Timer units: milliseconds */
#define NOTE_USECONDS   0x00000004  /* Timer units: microseconds */
#define NOTE_NSECONDS   0x00000008  /* Timer units: nanoseconds */
#define NOTE_ABSOLUTE   0x00000010  /* Absolute timer */

/**
 * EVFILT_USER fflags
 */
#define NOTE_TRIGGER    0x01000000  /* Trigger event */
#define NOTE_FFNOP      0x00000000  /* Ignore fflags */
#define NOTE_FFAND      0x40000000  /* AND fflags */
#define NOTE_FFOR       0x80000000  /* OR fflags */
#define NOTE_FFCOPY     0xc0000000  /* Copy fflags */
#define NOTE_FFCTRLMASK 0xc0000000  /* Control mask */
#define NOTE_FFLAGSMASK 0x00ffffff  /* User flags mask */

/**
 * EV_SET macro - initialize a kevent structure
 */
#define EV_SET(kevp, a, b, c, d, e, f) do { \
    struct kevent *__kevp = (kevp);         \
    __kevp->ident = (a);                    \
    __kevp->filter = (b);                   \
    __kevp->flags = (c);                    \
    __kevp->fflags = (d);                   \
    __kevp->data = (e);                     \
    __kevp->udata = (f);                    \
} while(0)

/**
 * timespec structure for kevent timeout
 */
struct kqueue_timespec {
    int64_t tv_sec;
    int64_t tv_nsec;
};

/**
 * Create a new kqueue
 *
 * @return          kqueue fd on success, -errno on failure
 */
int sys_kqueue(void);

/**
 * Create kqueue with flags (kqueue1 - FreeBSD extension)
 *
 * @param flags     Flags (O_CLOEXEC supported)
 * @return          kqueue fd on success, -errno on failure
 */
int sys_kqueue1(int flags);

/**
 * Register/modify/retrieve events
 *
 * @param kq        kqueue file descriptor
 * @param changelist Array of changes to apply (can be NULL)
 * @param nchanges  Number of changes
 * @param eventlist Output array for events (can be NULL)
 * @param nevents   Maximum events to return
 * @param timeout   Timeout (NULL = infinite, 0,0 = poll)
 * @return          Number of events, or -errno on failure
 */
int sys_kevent(int kq, const struct kevent *changelist, int nchanges,
               struct kevent *eventlist, int nevents,
               const struct kqueue_timespec *timeout);

/**
 * Initialize kqueue subsystem
 * Called once at boot after evcore_init()
 */
void kqueue_init(void);

