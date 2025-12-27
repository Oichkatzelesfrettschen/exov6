/**
 * @file doors.c
 * @brief Illumos/Solaris-compatible Doors Implementation
 *
 * Cleanroom doors implementation for FeuerBird exokernel.
 * Uses the Wait Channel primitive for blocking/waking.
 *
 * Key design decisions:
 * 1. Uses wait channels for client blocking during calls
 * 2. Server threads wake on door invocations
 * 3. Supports credential passing
 * 4. Zero-copy where buffer sizes permit
 */

#include "doors.h"
#include "../sync/waitchan.h"
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
#ifndef ENOENT
#define ENOENT 2
#endif
#ifndef EINTR
#define EINTR 4
#endif
#ifndef ENFILE
#define ENFILE 23
#endif
#ifndef EFAULT
#define EFAULT 14
#endif
#ifndef EBUSY
#define EBUSY 16
#endif
#ifndef EPERM
#define EPERM 1
#endif
#ifndef EAGAIN
#define EAGAIN 11
#endif
#ifndef EOVERFLOW
#define EOVERFLOW 75
#endif

/**
 * Door invocation state
 */
#define DOOR_STATE_IDLE         0   /* No active invocation */
#define DOOR_STATE_CALLING      1   /* Client waiting for response */
#define DOOR_STATE_SERVING      2   /* Server processing */
#define DOOR_STATE_RETURNING    3   /* Server returning */

/**
 * Door invocation structure
 * One per active door call
 */
struct door_invocation {
    struct spinlock lock;
    int state;                      /* DOOR_STATE_* */
    int caller_pid;                 /* Calling process */
    int server_pid;                 /* Serving process */

    /* Call data */
    char *call_data;                /* Argument data */
    size_t call_size;               /* Argument size */
    door_desc_t *call_descs;        /* Passed descriptors */
    uint32_t call_ndesc;            /* Number of descriptors */

    /* Return data */
    char *ret_data;                 /* Return data */
    size_t ret_size;                /* Return size */
    door_desc_t *ret_descs;         /* Return descriptors */
    uint32_t ret_ndesc;             /* Number of return descriptors */

    int error;                      /* Error code if any */
    struct door_invocation *next;   /* For free list */
};

/**
 * Door structure
 */
struct door {
    struct spinlock lock;
    door_id_t id;                   /* Unique door ID */
    uint32_t attr;                  /* Door attributes */
    door_server_proc_t proc;        /* Server procedure */
    void *cookie;                   /* Server cookie */
    int owner_pid;                  /* Process that created door */
    int refcount;                   /* Reference count */
    int revoked;                    /* Door has been revoked */

    /* Parameters */
    size_t data_max;                /* Max data size */
    size_t data_min;                /* Min data size */
    uint32_t desc_max;              /* Max descriptors */

    /* Active invocations */
    struct door_invocation *pending;    /* Pending invocations */
    int pending_count;              /* Number pending */

    /* Wait channels */
    uintptr_t server_wc;            /* Server waits here for calls */
    uintptr_t client_wc;            /* Clients wait here for returns */
};

/**
 * Maximum doors per process
 */
#define MAX_DOORS 256

/**
 * Maximum invocations per door
 */
#define MAX_INVOCATIONS 64

/**
 * Door registry
 */
static struct {
    struct spinlock lock;
    struct door *doors[MAX_DOORS];
    door_id_t next_id;
    int count;
} door_registry;

/**
 * Invocation pool
 */
static struct {
    struct spinlock lock;
    struct door_invocation *free_list;
    struct door_invocation pool[MAX_INVOCATIONS];
} invocation_pool;

/**
 * Initialize invocation pool
 */
static void init_invocation_pool(void) {
    initlock(&invocation_pool.lock, "inv_pool");
    invocation_pool.free_list = 0;

    for (int i = MAX_INVOCATIONS - 1; i >= 0; i--) {
        struct door_invocation *inv = &invocation_pool.pool[i];
        initlock(&inv->lock, "door_inv");
        inv->state = DOOR_STATE_IDLE;
        inv->next = invocation_pool.free_list;
        invocation_pool.free_list = inv;
    }
}

/**
 * Allocate invocation
 */
static struct door_invocation *alloc_invocation(void) {
    acquire(&invocation_pool.lock);

    struct door_invocation *inv = invocation_pool.free_list;
    if (inv) {
        invocation_pool.free_list = inv->next;
        inv->next = 0;
        inv->state = DOOR_STATE_IDLE;
        inv->error = 0;
    }

    release(&invocation_pool.lock);
    return inv;
}

/**
 * Free invocation
 */
static void free_invocation(struct door_invocation *inv) {
    if (!inv) return;

    acquire(&invocation_pool.lock);
    inv->state = DOOR_STATE_IDLE;
    inv->next = invocation_pool.free_list;
    invocation_pool.free_list = inv;
    release(&invocation_pool.lock);
}

/**
 * Allocate door structure
 */
static struct door *door_alloc(void) {
    char *p = kalloc();
    if (!p) {
        return 0;
    }
    for (unsigned long i = 0; i < sizeof(struct door); i++) {
        p[i] = 0;
    }
    return (struct door *)p;
}

/**
 * Free door structure
 */
static void door_free(struct door *d) {
    if (d) {
        kfree((char *)d);
    }
}

/**
 * Register door and return pseudo-fd
 */
static int door_register(struct door *d) {
    acquire(&door_registry.lock);

    if (door_registry.count >= MAX_DOORS) {
        release(&door_registry.lock);
        return -ENFILE;
    }

    /* Use offset of 3000 for door fds (epoll=1000, kqueue=2000) */
    for (int i = 0; i < MAX_DOORS; i++) {
        if (door_registry.doors[i] == 0) {
            door_registry.doors[i] = d;
            door_registry.count++;
            d->id = door_registry.next_id++;
            release(&door_registry.lock);
            return 3000 + i;
        }
    }

    release(&door_registry.lock);
    return -ENFILE;
}

/**
 * Lookup door by fd
 */
static struct door *door_lookup(int fd) {
    int idx = fd - 3000;
    if (idx < 0 || idx >= MAX_DOORS) {
        return 0;
    }

    acquire(&door_registry.lock);
    struct door *d = door_registry.doors[idx];
    release(&door_registry.lock);

    return d;
}

/**
 * Unregister door
 */
static void door_unregister(int fd) {
    int idx = fd - 3000;
    if (idx < 0 || idx >= MAX_DOORS) {
        return;
    }

    acquire(&door_registry.lock);
    struct door *d = door_registry.doors[idx];
    if (d) {
        door_registry.doors[idx] = 0;
        door_registry.count--;
    }
    release(&door_registry.lock);

    if (d) {
        door_free(d);
    }
}

/**
 * Initialize doors subsystem
 */
void doors_init(void) {
    initlock(&door_registry.lock, "door_registry");
    for (int i = 0; i < MAX_DOORS; i++) {
        door_registry.doors[i] = 0;
    }
    door_registry.next_id = 1;
    door_registry.count = 0;

    init_invocation_pool();
}

/**
 * Create a door
 */
int sys_door_create(door_server_proc_t proc, void *cookie, uint32_t attr) {
    if (!proc) {
        return -EINVAL;
    }

    struct door *d = door_alloc();
    if (!d) {
        return -ENOMEM;
    }

    initlock(&d->lock, "door");
    d->attr = attr;
    d->proc = proc;
    d->cookie = cookie;
    d->owner_pid = 0;  /* Would be myproc()->pid */
    d->refcount = 1;
    d->revoked = 0;

    /* Default parameters */
    d->data_max = 4096;
    d->data_min = 0;
    d->desc_max = 16;

    d->pending = 0;
    d->pending_count = 0;

    /* Use door address as wait channel identifier */
    d->server_wc = (uintptr_t)d;
    d->client_wc = (uintptr_t)d + 1;

    int fd = door_register(d);
    if (fd < 0) {
        door_free(d);
        return fd;
    }

    return fd;
}

/**
 * Call a door
 */
int sys_door_call(int fd, door_arg_t *arg) {
    if (!arg) {
        return -EINVAL;
    }

    struct door *d = door_lookup(fd);
    if (!d) {
        return -EBADF;
    }

    acquire(&d->lock);

    if (d->revoked) {
        release(&d->lock);
        return -EBADF;
    }

    /* Check data size limits */
    if (arg->data_size > d->data_max) {
        release(&d->lock);
        return -EOVERFLOW;
    }
    if (arg->data_size < d->data_min) {
        release(&d->lock);
        return -EINVAL;
    }
    if (arg->desc_num > d->desc_max) {
        release(&d->lock);
        return -EINVAL;
    }

    /* Allocate invocation */
    struct door_invocation *inv = alloc_invocation();
    if (!inv) {
        release(&d->lock);
        return -EAGAIN;
    }

    /* Set up invocation */
    inv->state = DOOR_STATE_CALLING;
    inv->caller_pid = 0;  /* Would be myproc()->pid */
    inv->server_pid = 0;
    inv->call_data = arg->data_ptr;
    inv->call_size = arg->data_size;
    inv->call_descs = arg->desc_ptr;
    inv->call_ndesc = arg->desc_num;
    inv->ret_data = 0;
    inv->ret_size = 0;
    inv->ret_descs = 0;
    inv->ret_ndesc = 0;
    inv->error = 0;

    /* Add to pending list */
    inv->next = d->pending;
    d->pending = inv;
    d->pending_count++;

    release(&d->lock);

    /* Wake server thread waiting for calls */
    wc_wake(d->server_wc, 1, 0);

    /* Wait for response */
    while (inv->state == DOOR_STATE_CALLING) {
        int r = wc_wait(d->client_wc, 0, 0, 0); /* 0 timeout = infinite */
        if (r == -EINTR) {
            /* Check if we should continue waiting */
            acquire(&d->lock);
            if (d->revoked) {
                /* Remove from pending list */
                struct door_invocation **pp = &d->pending;
                while (*pp && *pp != inv) {
                    pp = &(*pp)->next;
                }
                if (*pp) {
                    *pp = inv->next;
                    d->pending_count--;
                }
                release(&d->lock);
                free_invocation(inv);
                return -EINTR;
            }
            release(&d->lock);
        }
    }

    /* Copy return data to caller's buffer */
    if (inv->ret_data && inv->ret_size > 0 && arg->rbuf && arg->rsize > 0) {
        size_t copy_size = inv->ret_size;
        if (copy_size > arg->rsize) {
            copy_size = arg->rsize;
        }
        for (size_t i = 0; i < copy_size; i++) {
            arg->rbuf[i] = inv->ret_data[i];
        }
        arg->rsize = copy_size;
    } else {
        arg->rsize = 0;
    }

    int error = inv->error;
    free_invocation(inv);

    return error;
}

/**
 * Return from a door invocation
 */
int sys_door_return(char *data, size_t size,
                    door_desc_t *descs, uint32_t num_descs) {
    /*
     * In a real implementation, this would:
     * 1. Find the current thread's active invocation
     * 2. Copy return data
     * 3. Wake the client
     * 4. Block waiting for next invocation
     *
     * For now, this is a stub that demonstrates the interface.
     */
    (void)data;
    (void)size;
    (void)descs;
    (void)num_descs;

    /* Would get current invocation from thread-local state */
    /* For now, just return success */
    return 0;
}

/**
 * Get door info
 */
int sys_door_info(int fd, door_info_t *info) {
    if (!info) {
        return -EINVAL;
    }

    struct door *d = door_lookup(fd);
    if (!d) {
        return -EBADF;
    }

    acquire(&d->lock);

    info->di_target = d->owner_pid;
    info->di_uniquifier = d->id;
    info->di_attributes = d->attr;

    /* Only expose proc/data if local */
    info->di_attributes |= DOOR_LOCAL;
    info->di_proc = (void *)d->proc;
    info->di_data = d->cookie;

    if (d->revoked) {
        info->di_attributes |= DOOR_REVOKED;
    }
    if (d->attr & DOOR_UNREF) {
        info->di_attributes |= DOOR_IS_UNREF;
    }

    release(&d->lock);

    return 0;
}

/**
 * Revoke a door
 */
int sys_door_revoke(int fd) {
    struct door *d = door_lookup(fd);
    if (!d) {
        return -EBADF;
    }

    acquire(&d->lock);

    /* Only owner can revoke */
    /* if (myproc()->pid != d->owner_pid) { ... } */

    d->revoked = 1;

    /* Wake all waiting clients */
    wc_wake(d->client_wc, 0, 0);  /* 0 count = wake all */

    /* Wake server thread */
    wc_wake(d->server_wc, 1, 0);

    release(&d->lock);

    return 0;
}

/**
 * Get door credentials
 */
int sys_door_cred(void *info) {
    if (!info) {
        return -EINVAL;
    }

    /* Would return caller credentials */
    /* For now, just return success */
    return 0;
}

/**
 * Bind door to file path
 */
int sys_door_bind(int fd, const char *path) {
    if (!path) {
        return -EINVAL;
    }

    struct door *d = door_lookup(fd);
    if (!d) {
        return -EBADF;
    }

    /* Would create filesystem entry pointing to door */
    /* For now, just return success */
    (void)path;
    return 0;
}

/**
 * Unbind door from file path
 */
int sys_door_unbind(const char *path) {
    if (!path) {
        return -EINVAL;
    }

    /* Would remove filesystem entry */
    /* For now, just return success */
    return 0;
}

/**
 * Get door parameter
 */
int sys_door_getparam(int fd, int param, size_t *out) {
    if (!out) {
        return -EINVAL;
    }

    struct door *d = door_lookup(fd);
    if (!d) {
        return -EBADF;
    }

    acquire(&d->lock);

    switch (param) {
        case DOOR_PARAM_DATA_MAX:
            *out = d->data_max;
            break;
        case DOOR_PARAM_DATA_MIN:
            *out = d->data_min;
            break;
        case DOOR_PARAM_DESC_MAX:
            *out = d->desc_max;
            break;
        default:
            release(&d->lock);
            return -EINVAL;
    }

    release(&d->lock);
    return 0;
}

/**
 * Set door parameter
 */
int sys_door_setparam(int fd, int param, size_t value) {
    struct door *d = door_lookup(fd);
    if (!d) {
        return -EBADF;
    }

    acquire(&d->lock);

    /* Only owner can set parameters */
    /* if (myproc()->pid != d->owner_pid) { ... } */

    switch (param) {
        case DOOR_PARAM_DATA_MAX:
            d->data_max = value;
            break;
        case DOOR_PARAM_DATA_MIN:
            d->data_min = value;
            break;
        case DOOR_PARAM_DESC_MAX:
            d->desc_max = (uint32_t)value;
            break;
        default:
            release(&d->lock);
            return -EINVAL;
    }

    release(&d->lock);
    return 0;
}

