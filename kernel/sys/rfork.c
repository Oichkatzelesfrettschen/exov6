/**
 * @file rfork.c
 * @brief BSD/Plan 9-compatible rfork Implementation
 *
 * Cleanroom rfork implementation for FeuerBird exokernel.
 * Translates rfork semantics to unified clone infrastructure.
 *
 * Key design decisions:
 * 1. rfork flags map to clone flags internally
 * 2. Process descriptors use fd-based handle system
 * 3. Supports both Plan 9 and FreeBSD semantics
 */

#include "rfork.h"
#include "clone.h"
#include "../defs.h"
#include "../proc.h"
#include <spinlock.h>

/* Errno values */
#ifndef EINVAL
#define EINVAL 22
#endif
#ifndef ENOMEM
#define ENOMEM 12
#endif
#ifndef EPERM
#define EPERM 1
#endif
#ifndef ENOSYS
#define ENOSYS 38
#endif
#ifndef EAGAIN
#define EAGAIN 11
#endif
#ifndef EBADF
#define EBADF 9
#endif

/**
 * Maximum process descriptors
 */
#define MAX_PROC_DESCS 256

/**
 * Process descriptor entry
 */
struct proc_desc {
    int pid;                /* Process ID */
    int flags;              /* PD_* flags */
    int refcount;           /* Reference count */
};

/**
 * Process descriptor registry
 */
static struct {
    struct spinlock lock;
    struct proc_desc descs[MAX_PROC_DESCS];
    int count;
} pd_registry;

/**
 * Translate rfork flags to clone flags
 */
uint64_t rfork_to_clone_flags(int rfork_flags) {
    uint64_t clone_flags = 0;

    /* Memory sharing */
    if (rfork_flags & RFMEM) {
        clone_flags |= CLONE_VM;
    }

    /* File descriptor handling */
    if (!(rfork_flags & RFFDG)) {
        /* RFFDG means copy, so without it we share */
        clone_flags |= CLONE_FILES;
    }

    /* Signal handler sharing */
    if (rfork_flags & RFSIGSHARE) {
        clone_flags |= CLONE_SIGHAND;
    }

    /* Thread creation */
    if (rfork_flags & RFTHREAD) {
        clone_flags |= CLONE_THREAD | CLONE_VM | CLONE_SIGHAND;
    }

    /* RFPROC with no sharing is like a normal fork */
    if ((rfork_flags & RFPROC) && !(rfork_flags & RFMEM)) {
        /* Just create new process, no special sharing */
    }

    /* RFNOWAIT - child is dissociated */
    if (rfork_flags & RFNOWAIT) {
        /* No direct clone equivalent - handle in process table */
    }

    /* RFCFDG - close all file descriptors */
    if (rfork_flags & RFCFDG) {
        /* Would close all fds after fork */
    }

    /* Linux thread notification (for pthreads compat) */
    if (rfork_flags & RFLINUXTHPN) {
        clone_flags |= CLONE_CHILD_CLEARTID;
    }

    /* Default exit signal is SIGCHLD (17) */
    clone_flags |= 17;

    return clone_flags;
}

/**
 * Allocate process descriptor
 */
static int pd_alloc(int pid, int flags) {
    acquire(&pd_registry.lock);

    if (pd_registry.count >= MAX_PROC_DESCS) {
        release(&pd_registry.lock);
        return -EAGAIN;
    }

    /* Use offset of 4000 for process descriptor fds */
    for (int i = 0; i < MAX_PROC_DESCS; i++) {
        if (pd_registry.descs[i].pid == 0) {
            pd_registry.descs[i].pid = pid;
            pd_registry.descs[i].flags = flags;
            pd_registry.descs[i].refcount = 1;
            pd_registry.count++;
            release(&pd_registry.lock);
            return 4000 + i;
        }
    }

    release(&pd_registry.lock);
    return -EAGAIN;
}

/**
 * Lookup process descriptor
 */
static struct proc_desc *pd_lookup(int fd) {
    int idx = fd - 4000;
    if (idx < 0 || idx >= MAX_PROC_DESCS) {
        return 0;
    }

    acquire(&pd_registry.lock);
    struct proc_desc *pd = &pd_registry.descs[idx];
    if (pd->pid == 0) {
        release(&pd_registry.lock);
        return 0;
    }
    release(&pd_registry.lock);

    return pd;
}

/**
 * Initialize rfork subsystem
 */
void rfork_init(void) {
    initlock(&pd_registry.lock, "pd_registry");
    for (int i = 0; i < MAX_PROC_DESCS; i++) {
        pd_registry.descs[i].pid = 0;
        pd_registry.descs[i].flags = 0;
        pd_registry.descs[i].refcount = 0;
    }
    pd_registry.count = 0;
}

/**
 * Create a new process/thread with configurable sharing
 */
int sys_rfork(int flags) {
    /* Validate flags */
    if (flags == 0) {
        return -EINVAL;
    }

    /* Without RFPROC, we're modifying current process (like unshare) */
    if (!(flags & RFPROC)) {
        uint64_t clone_flags = 0;

        /* RFNAMEG - new name group (namespace-like) */
        if (flags & RFNAMEG) {
            clone_flags |= CLONE_NEWNS;
        }

        /* RFCNAMEG - zero name group */
        if (flags & RFCNAMEG) {
            clone_flags |= CLONE_NEWNS;
        }

        /* RFENVG - new environment group */
        if (flags & RFENVG) {
            /* No direct equivalent - would clear environment */
        }

        /* RFNOTEG - new note group (signal group) */
        if (flags & RFNOTEG) {
            /* Would create new signal handling context */
        }

        if (clone_flags) {
            return sys_unshare(clone_flags);
        }

        return 0;
    }

    /* RFPROC set - create new process or thread */
    uint64_t clone_flags = rfork_to_clone_flags(flags);

    return sys_clone(clone_flags, 0, 0, 0, 0);
}

/**
 * Create process with process descriptor (FreeBSD)
 */
int sys_pdfork(int *fdp, int flags) {
    if (!fdp) {
        return -EINVAL;
    }

    /* Validate flags */
    if (flags & ~(PD_DAEMON | PD_CLOEXEC)) {
        return -EINVAL;
    }

    /* Fork the process */
    int pid = sys_rfork(RFPROC | RFFDG);
    if (pid < 0) {
        return pid;
    }

    if (pid == 0) {
        /* Child */
        if (flags & PD_DAEMON) {
            /* Would setsid() and redirect stdin/stdout/stderr */
        }
        return 0;
    }

    /* Parent - create process descriptor */
    int fd = pd_alloc(pid, flags);
    if (fd < 0) {
        /* Would need to clean up child - for now just fail */
        return fd;
    }

    *fdp = fd;
    return pid;
}

/**
 * Get PID from process descriptor
 */
int sys_pdgetpid(int fd, int *pidp) {
    if (!pidp) {
        return -EINVAL;
    }

    struct proc_desc *pd = pd_lookup(fd);
    if (!pd) {
        return -EBADF;
    }

    *pidp = pd->pid;
    return 0;
}

/**
 * Kill process via descriptor
 */
int sys_pdkill(int fd, int signum) {
    struct proc_desc *pd = pd_lookup(fd);
    if (!pd) {
        return -EBADF;
    }

    /* Would send signal to pd->pid */
    /* For now, just validate we have a valid descriptor */
    (void)signum;

    return -ENOSYS;
}

