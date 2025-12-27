/**
 * @file capsicum.c
 * @brief FreeBSD-compatible Capsicum Implementation
 *
 * Cleanroom Capsicum implementation for FeuerBird exokernel.
 * Uses isolation domains for capability mode enforcement.
 *
 * Key design decisions:
 * 1. Capability mode uses isodomain with ISO_AXIS_CAPABILITY
 * 2. Per-fd rights stored in capability wrapper table
 * 3. Rights can only be reduced, never expanded
 * 4. Once in capability mode, cannot exit
 */

#include "capsicum.h"
#include "../isolation/isodomain.h"
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
#ifndef EBADF
#define EBADF 9
#endif
#ifndef ENOTCAPABLE
#define ENOTCAPABLE 93  /* FreeBSD capability error */
#endif
#ifndef ECAPMODE
#define ECAPMODE 94     /* Not permitted in capability mode */
#endif

/**
 * Maximum file descriptors per process
 */
#define MAX_FDS 256

/**
 * Maximum processes tracked
 */
#define MAX_PROCS 64

/**
 * Capability wrapper for a file descriptor
 */
struct cap_fd {
    int fd;                     /* Underlying fd */
    cap_rights_t rights;        /* Allowed rights */
    int valid;                  /* Entry in use */
};

/**
 * Per-process capability state
 */
struct cap_proc {
    int pid;                            /* Process ID */
    int in_capability_mode;             /* In capability mode */
    struct isodomain *cap_domain;       /* Capability isolation domain */
    struct cap_fd fds[MAX_FDS];         /* Per-fd capabilities */
    int refcount;                       /* Reference count */
};

/**
 * Capsicum registry
 */
static struct {
    struct spinlock lock;
    struct cap_proc procs[MAX_PROCS];
    int initialized;
} cap_registry;

/**
 * Get or create capability state for current process
 */
static struct cap_proc *cap_get_proc(int create) {
    /* Would get current process PID */
    int pid = 1;  /* Placeholder - would use myproc()->pid */

    acquire(&cap_registry.lock);

    /* Look for existing entry */
    for (int i = 0; i < MAX_PROCS; i++) {
        if (cap_registry.procs[i].pid == pid && cap_registry.procs[i].refcount > 0) {
            struct cap_proc *cp = &cap_registry.procs[i];
            release(&cap_registry.lock);
            return cp;
        }
    }

    if (!create) {
        release(&cap_registry.lock);
        return 0;
    }

    /* Create new entry */
    for (int i = 0; i < MAX_PROCS; i++) {
        if (cap_registry.procs[i].refcount == 0) {
            struct cap_proc *cp = &cap_registry.procs[i];
            cp->pid = pid;
            cp->in_capability_mode = 0;
            cp->cap_domain = 0;
            cp->refcount = 1;

            /* Initialize all fds with full rights */
            for (int j = 0; j < MAX_FDS; j++) {
                cp->fds[j].fd = -1;
                cp->fds[j].rights = CAP_ALL;
                cp->fds[j].valid = 0;
            }

            release(&cap_registry.lock);
            return cp;
        }
    }

    release(&cap_registry.lock);
    return 0;
}

/**
 * Get capability entry for fd
 */
static struct cap_fd *cap_get_fd(struct cap_proc *cp, int fd) {
    if (!cp || fd < 0 || fd >= MAX_FDS) {
        return 0;
    }

    if (cp->fds[fd].valid) {
        return &cp->fds[fd];
    }

    return 0;
}

/**
 * Create or update capability entry for fd
 */
static struct cap_fd *cap_set_fd(struct cap_proc *cp, int fd, cap_rights_t rights) {
    if (!cp || fd < 0 || fd >= MAX_FDS) {
        return 0;
    }

    cp->fds[fd].fd = fd;
    cp->fds[fd].rights = rights;
    cp->fds[fd].valid = 1;

    return &cp->fds[fd];
}

/**
 * Initialize capsicum subsystem
 */
void capsicum_init(void) {
    if (cap_registry.initialized) {
        return;
    }

    initlock(&cap_registry.lock, "capsicum");

    for (int i = 0; i < MAX_PROCS; i++) {
        cap_registry.procs[i].pid = 0;
        cap_registry.procs[i].in_capability_mode = 0;
        cap_registry.procs[i].cap_domain = 0;
        cap_registry.procs[i].refcount = 0;
    }

    cap_registry.initialized = 1;
}

/**
 * Enter capability mode
 *
 * After this call, the process cannot access global namespaces.
 * Only file descriptors with appropriate rights can be used.
 * This is a one-way operation - cannot exit capability mode.
 */
int sys_cap_enter(void) {
    struct cap_proc *cp = cap_get_proc(1);
    if (!cp) {
        return -ENOMEM;
    }

    if (cp->in_capability_mode) {
        /* Already in capability mode - success */
        return 0;
    }

    /* Create isolation domain with capability axis */
    cp->cap_domain = isodomain_create("capsicum", 0, ISO_AXIS_CAPABILITY, 0);
    if (!cp->cap_domain) {
        return -ENOMEM;
    }

    /* Enter the isolation domain */
    int err = isodomain_enter(0, cp->cap_domain);
    if (err < 0) {
        isodomain_destroy(cp->cap_domain);
        cp->cap_domain = 0;
        return err;
    }

    /* Mark as in capability mode - no going back */
    cp->in_capability_mode = 1;

    return 0;
}

/**
 * Check if in capability mode
 */
int sys_cap_getmode(int *in_capability_mode) {
    if (!in_capability_mode) {
        return -EINVAL;
    }

    struct cap_proc *cp = cap_get_proc(0);
    if (!cp) {
        *in_capability_mode = 0;
    } else {
        *in_capability_mode = cp->in_capability_mode;
    }

    return 0;
}

/**
 * Limit capability rights on a file descriptor
 *
 * Rights can only be reduced, never expanded.
 * This is the core Capsicum security guarantee.
 */
int sys_cap_rights_limit(int fd, const cap_rights_t *rights) {
    if (!rights || fd < 0 || fd >= MAX_FDS) {
        return -EINVAL;
    }

    struct cap_proc *cp = cap_get_proc(1);
    if (!cp) {
        return -ENOMEM;
    }

    cap_rights_t new_rights = *rights;

    /* Check if fd already has capability wrapper */
    struct cap_fd *cf = cap_get_fd(cp, fd);
    if (cf) {
        /* Can only reduce rights, never expand */
        new_rights &= cf->rights;
    }

    /* Create or update capability wrapper */
    cf = cap_set_fd(cp, fd, new_rights);
    if (!cf) {
        return -ENOMEM;
    }

    return 0;
}

/**
 * Get capability rights on a file descriptor
 */
int sys_cap_rights_get(int fd, cap_rights_t *rights) {
    if (!rights || fd < 0 || fd >= MAX_FDS) {
        return -EINVAL;
    }

    struct cap_proc *cp = cap_get_proc(0);
    if (!cp) {
        /* No capability state - fd has all rights */
        *rights = CAP_ALL;
        return 0;
    }

    struct cap_fd *cf = cap_get_fd(cp, fd);
    if (!cf) {
        /* No wrapper - fd has all rights */
        *rights = CAP_ALL;
    } else {
        *rights = cf->rights;
    }

    return 0;
}

/**
 * Create a capability from an existing file descriptor
 *
 * Returns a new fd that is a capability-wrapped version of the original.
 * The new fd can only be used with the specified rights.
 */
int sys_cap_new(int fd, cap_rights_t rights) {
    if (fd < 0 || fd >= MAX_FDS) {
        return -EBADF;
    }

    struct cap_proc *cp = cap_get_proc(1);
    if (!cp) {
        return -ENOMEM;
    }

    /* Check if source fd has a capability wrapper */
    struct cap_fd *cf = cap_get_fd(cp, fd);
    cap_rights_t source_rights = cf ? cf->rights : CAP_ALL;

    /* New rights cannot exceed source rights */
    cap_rights_t new_rights = rights & source_rights;

    /* Find a free fd slot for the new capability */
    /* In a real implementation, this would dup the fd */
    int new_fd = -1;
    for (int i = fd + 1; i < MAX_FDS; i++) {
        if (!cp->fds[i].valid) {
            new_fd = i;
            break;
        }
    }

    if (new_fd < 0) {
        return -ENOMEM;
    }

    /* Create capability wrapper for new fd */
    cap_set_fd(cp, new_fd, new_rights);

    return new_fd;
}

/**
 * Check if fd has specific rights
 *
 * Used internally before syscall operations to verify
 * that the operation is permitted on this fd.
 */
int sys_cap_rights_check(int fd, cap_rights_t rights) {
    if (fd < 0 || fd >= MAX_FDS) {
        return -EBADF;
    }

    struct cap_proc *cp = cap_get_proc(0);
    if (!cp) {
        /* No capability state - all rights permitted */
        return 0;
    }

    struct cap_fd *cf = cap_get_fd(cp, fd);
    if (!cf) {
        /* No wrapper - all rights permitted */
        return 0;
    }

    /* Check if all requested rights are present */
    if ((cf->rights & rights) == rights) {
        return 0;
    }

    return -ENOTCAPABLE;
}

/**
 * Initialize rights structure (variadic)
 */
void cap_rights_init(cap_rights_t *rights, ...) {
    if (!rights) {
        return;
    }

    *rights = 0;

    /* In a real implementation, would process varargs */
    /* For now, just initialize to zero */
}

/**
 * Set rights in structure (variadic)
 */
void cap_rights_set(cap_rights_t *rights, ...) {
    if (!rights) {
        return;
    }

    /* In a real implementation, would process varargs */
    /* For now, no-op - caller should use bitwise OR directly */
}

/**
 * Clear rights in structure (variadic)
 */
void cap_rights_clear(cap_rights_t *rights, ...) {
    if (!rights) {
        return;
    }

    /* In a real implementation, would process varargs */
    /* For now, no-op - caller should use bitwise AND with complement */
}

/**
 * Check if rights are set (variadic)
 */
int cap_rights_is_set(const cap_rights_t *rights, ...) {
    if (!rights) {
        return 0;
    }

    /* In a real implementation, would process varargs */
    /* For now, return non-zero if any rights are set */
    return *rights != 0;
}

/**
 * Check if operation is allowed in capability mode
 *
 * Called by syscall handlers to block operations that
 * would access global namespaces (open, chdir, etc.)
 */
int cap_check_mode(void) {
    struct cap_proc *cp = cap_get_proc(0);
    if (!cp || !cp->in_capability_mode) {
        return 0;  /* Not in capability mode - allowed */
    }

    return -ECAPMODE;  /* In capability mode - denied */
}

/**
 * Inherit capability state to child process
 * Called during fork/clone
 */
int cap_fork_inherit(int parent_pid, int child_pid) {
    acquire(&cap_registry.lock);

    struct cap_proc *parent = 0;
    for (int i = 0; i < MAX_PROCS; i++) {
        if (cap_registry.procs[i].pid == parent_pid &&
            cap_registry.procs[i].refcount > 0) {
            parent = &cap_registry.procs[i];
            break;
        }
    }

    if (!parent) {
        release(&cap_registry.lock);
        return 0;  /* Parent has no capability state */
    }

    /* Find slot for child */
    struct cap_proc *child = 0;
    for (int i = 0; i < MAX_PROCS; i++) {
        if (cap_registry.procs[i].refcount == 0) {
            child = &cap_registry.procs[i];
            break;
        }
    }

    if (!child) {
        release(&cap_registry.lock);
        return -ENOMEM;
    }

    /* Copy capability state */
    child->pid = child_pid;
    child->in_capability_mode = parent->in_capability_mode;
    child->cap_domain = parent->cap_domain;  /* Share domain ref */
    child->refcount = 1;

    /* Copy fd rights */
    for (int i = 0; i < MAX_FDS; i++) {
        child->fds[i] = parent->fds[i];
    }

    release(&cap_registry.lock);
    return 0;
}
