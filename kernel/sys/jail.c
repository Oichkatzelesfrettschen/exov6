/**
 * @file jail.c
 * @brief FreeBSD-compatible Jail Implementation
 *
 * Cleanroom jail implementation for FeuerBird exokernel.
 * Translates jail semantics to isolation domain primitives.
 *
 * Key design decisions:
 * 1. Each jail maps to an isolation domain
 * 2. Jail parameters stored in domain metadata
 * 3. Filesystem root enforced via domain's iso_fs
 * 4. Network isolation via domain's iso_net
 */

#include "jail.h"
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
#ifndef EPERM
#define EPERM 1
#endif
#ifndef ENOSYS
#define ENOSYS 38
#endif
#ifndef EAGAIN
#define EAGAIN 11
#endif
#ifndef ENOENT
#define ENOENT 2
#endif
#ifndef EEXIST
#define EEXIST 17
#endif

/**
 * Maximum jails in system
 */
#define MAX_JAILS 256

/**
 * Maximum jail name length
 */
#define JAIL_NAME_MAX 64

/**
 * Maximum path length
 */
#define JAIL_PATH_MAX 256

/**
 * Maximum hostname length
 */
#define JAIL_HOST_MAX 256

/**
 * Jail entry structure
 */
struct jail_entry {
    jail_id_t jid;              /* Jail ID */
    struct isodomain *domain;   /* Underlying isolation domain */
    char name[JAIL_NAME_MAX];   /* Jail name */
    char path[JAIL_PATH_MAX];   /* Root path */
    char hostname[JAIL_HOST_MAX]; /* Hostname */
    uint32_t ip4_count;         /* Number of IPv4 addresses */
    uint32_t ip6_count;         /* Number of IPv6 addresses */
    int securelevel;            /* Securelevel */
    int devfs_ruleset;          /* devfs ruleset */
    int children_max;           /* Max child jails */
    int children_cur;           /* Current child count */
    int persist;                /* Persist flag */
    int dying;                  /* Jail is being removed */
    int refcount;               /* Reference count */
};

/**
 * Jail registry
 */
static struct {
    struct spinlock lock;
    struct jail_entry jails[MAX_JAILS];
    jail_id_t next_jid;
    int count;
} jail_registry;

/**
 * String copy helper
 */
static void jail_strcpy(char *dst, const char *src, size_t max) {
    size_t i;
    for (i = 0; i < max - 1 && src && src[i]; i++) {
        dst[i] = src[i];
    }
    dst[i] = '\0';
}

/**
 * String length helper
 */
static size_t jail_strlen(const char *s) {
    size_t len = 0;
    if (s) {
        while (s[len]) len++;
    }
    return len;
}

/**
 * Allocate jail entry
 */
static struct jail_entry *jail_alloc(void) {
    acquire(&jail_registry.lock);

    if (jail_registry.count >= MAX_JAILS) {
        release(&jail_registry.lock);
        return 0;
    }

    for (int i = 0; i < MAX_JAILS; i++) {
        if (jail_registry.jails[i].jid == 0) {
            struct jail_entry *je = &jail_registry.jails[i];
            je->jid = jail_registry.next_jid++;
            je->refcount = 1;
            jail_registry.count++;
            release(&jail_registry.lock);
            return je;
        }
    }

    release(&jail_registry.lock);
    return 0;
}

/**
 * Lookup jail by ID
 */
static struct jail_entry *jail_lookup(jail_id_t jid) {
    if (jid <= 0) {
        return 0;
    }

    acquire(&jail_registry.lock);

    for (int i = 0; i < MAX_JAILS; i++) {
        if (jail_registry.jails[i].jid == jid) {
            struct jail_entry *je = &jail_registry.jails[i];
            release(&jail_registry.lock);
            return je;
        }
    }

    release(&jail_registry.lock);
    return 0;
}

/**
 * Lookup jail by name
 */
static struct jail_entry *jail_lookup_name(const char *name) {
    if (!name) {
        return 0;
    }

    acquire(&jail_registry.lock);

    for (int i = 0; i < MAX_JAILS; i++) {
        struct jail_entry *je = &jail_registry.jails[i];
        if (je->jid != 0) {
            /* Simple string compare */
            const char *a = je->name;
            const char *b = name;
            int match = 1;
            while (*a && *b) {
                if (*a++ != *b++) {
                    match = 0;
                    break;
                }
            }
            if (match && *a == '\0' && *b == '\0') {
                release(&jail_registry.lock);
                return je;
            }
        }
    }

    release(&jail_registry.lock);
    return 0;
}

/**
 * Free jail entry
 */
static void jail_free(struct jail_entry *je) {
    if (!je) return;

    acquire(&jail_registry.lock);

    if (--je->refcount == 0) {
        if (je->domain) {
            isodomain_destroy(je->domain);
        }
        je->jid = 0;
        je->domain = 0;
        je->name[0] = '\0';
        je->path[0] = '\0';
        je->hostname[0] = '\0';
        jail_registry.count--;
    }

    release(&jail_registry.lock);
}

/**
 * Initialize jail subsystem
 */
void jail_init(void) {
    initlock(&jail_registry.lock, "jail_registry");
    for (int i = 0; i < MAX_JAILS; i++) {
        jail_registry.jails[i].jid = 0;
        jail_registry.jails[i].domain = 0;
        jail_registry.jails[i].refcount = 0;
    }
    jail_registry.next_jid = 1;
    jail_registry.count = 0;
}

/**
 * Create and attach to a jail (legacy interface)
 */
int sys_jail(struct jail *jail) {
    if (!jail) {
        return -EINVAL;
    }

    if (jail->version != JAIL_API_VERSION) {
        return -EINVAL;
    }

    if (!jail->path) {
        return -EINVAL;
    }

    /* Allocate jail entry */
    struct jail_entry *je = jail_alloc();
    if (!je) {
        return -EAGAIN;
    }

    /* Create isolation domain with filesystem, network, and process isolation */
    uint16_t axes = ISO_AXIS_FILESYSTEM | ISO_AXIS_NETWORK | ISO_AXIS_PROCESS;
    je->domain = isodomain_create("jail", 0, axes, 0);
    if (!je->domain) {
        jail_free(je);
        return -ENOMEM;
    }

    /* Copy jail parameters */
    jail_strcpy(je->path, jail->path, JAIL_PATH_MAX);
    if (jail->hostname) {
        jail_strcpy(je->hostname, jail->hostname, JAIL_HOST_MAX);
    }
    if (jail->jailname) {
        jail_strcpy(je->name, jail->jailname, JAIL_NAME_MAX);
    }
    je->ip4_count = jail->ip4s;
    je->ip6_count = jail->ip6s;
    je->securelevel = -1;  /* Default */
    je->devfs_ruleset = 0;
    je->children_max = 0;
    je->children_cur = 0;
    je->persist = 0;
    je->dying = 0;

    /* Enter the isolation domain (NULL proc = current process) */
    int err = isodomain_enter(0, je->domain);
    if (err < 0) {
        jail_free(je);
        return err;
    }

    return je->jid;
}

/**
 * Attach to an existing jail
 */
int sys_jail_attach(jail_id_t jid) {
    struct jail_entry *je = jail_lookup(jid);
    if (!je) {
        return -ENOENT;
    }

    if (je->dying) {
        return -ENOENT;
    }

    /* Enter the isolation domain (NULL proc = current process) */
    int err = isodomain_enter(0, je->domain);
    if (err < 0) {
        return err;
    }

    je->refcount++;
    return 0;
}

/**
 * Remove a jail
 */
int sys_jail_remove(jail_id_t jid) {
    struct jail_entry *je = jail_lookup(jid);
    if (!je) {
        return -ENOENT;
    }

    /* Mark as dying */
    je->dying = 1;

    /* Would need to kill all processes in jail */
    /* For now, just mark and return */

    jail_free(je);
    return 0;
}

/**
 * Set jail parameters (modern interface)
 */
int sys_jail_set(struct iovec *iov, unsigned int niov, int flags) {
    if (!iov || niov == 0 || (niov & 1)) {
        return -EINVAL;
    }

    if (flags & ~JAIL_SET_MASK) {
        return -EINVAL;
    }

    struct jail_entry *je = 0;
    jail_id_t jid = 0;
    const char *name = 0;
    const char *path = 0;
    const char *hostname = 0;

    /* Parse parameters */
    for (unsigned int i = 0; i < niov; i += 2) {
        const char *param = (const char *)iov[i].iov_base;
        void *value = iov[i + 1].iov_base;
        size_t len = iov[i + 1].iov_len;

        /* Simple parameter matching */
        if (param && value) {
            /* Check for "jid" */
            if (param[0] == 'j' && param[1] == 'i' && param[2] == 'd' && param[3] == '\0') {
                if (len >= sizeof(jail_id_t)) {
                    jid = *(jail_id_t *)value;
                }
            }
            /* Check for "name" */
            else if (param[0] == 'n' && param[1] == 'a' && param[2] == 'm' && param[3] == 'e' && param[4] == '\0') {
                name = (const char *)value;
            }
            /* Check for "path" */
            else if (param[0] == 'p' && param[1] == 'a' && param[2] == 't' && param[3] == 'h' && param[4] == '\0') {
                path = (const char *)value;
            }
            /* Check for "host.hostname" */
            else if (param[0] == 'h' && param[1] == 'o' && param[2] == 's' && param[3] == 't') {
                hostname = (const char *)value;
            }
        }
    }

    /* Create or update */
    if (flags & JAIL_CREATE) {
        if (!path) {
            return -EINVAL;
        }

        je = jail_alloc();
        if (!je) {
            return -EAGAIN;
        }

        uint16_t axes = ISO_AXIS_FILESYSTEM | ISO_AXIS_NETWORK | ISO_AXIS_PROCESS;
        je->domain = isodomain_create("jail", 0, axes, 0);
        if (!je->domain) {
            jail_free(je);
            return -ENOMEM;
        }

        jail_strcpy(je->path, path, JAIL_PATH_MAX);
        if (name) {
            jail_strcpy(je->name, name, JAIL_NAME_MAX);
        }
        if (hostname) {
            jail_strcpy(je->hostname, hostname, JAIL_HOST_MAX);
        }

        jid = je->jid;
    } else if (flags & JAIL_UPDATE) {
        if (jid > 0) {
            je = jail_lookup(jid);
        } else if (name) {
            je = jail_lookup_name(name);
        }

        if (!je) {
            return -ENOENT;
        }

        /* Update parameters */
        if (path) {
            jail_strcpy(je->path, path, JAIL_PATH_MAX);
        }
        if (hostname) {
            jail_strcpy(je->hostname, hostname, JAIL_HOST_MAX);
        }

        jid = je->jid;
    }

    /* Attach if requested */
    if ((flags & JAIL_ATTACH) && je) {
        int err = isodomain_enter(0, je->domain);
        if (err < 0) {
            if (flags & JAIL_CREATE) {
                jail_free(je);
            }
            return err;
        }
    }

    return jid;
}

/**
 * Get jail parameters
 */
int sys_jail_get(struct iovec *iov, unsigned int niov, int flags) {
    if (!iov || niov == 0 || (niov & 1)) {
        return -EINVAL;
    }

    jail_id_t jid = 0;
    const char *name = 0;

    /* Find jail identifier in parameters */
    for (unsigned int i = 0; i < niov; i += 2) {
        const char *param = (const char *)iov[i].iov_base;
        void *value = iov[i + 1].iov_base;
        size_t len = iov[i + 1].iov_len;

        if (param && value) {
            if (param[0] == 'j' && param[1] == 'i' && param[2] == 'd' && param[3] == '\0') {
                if (len >= sizeof(jail_id_t)) {
                    jid = *(jail_id_t *)value;
                }
            } else if (param[0] == 'n' && param[1] == 'a' && param[2] == 'm' && param[3] == 'e' && param[4] == '\0') {
                name = (const char *)value;
            }
        }
    }

    /* Lookup jail */
    struct jail_entry *je = 0;
    if (jid > 0) {
        je = jail_lookup(jid);
    } else if (name) {
        je = jail_lookup_name(name);
    }

    if (!je) {
        return -ENOENT;
    }

    if ((flags & JAIL_DYING) && !je->dying) {
        return -ENOENT;
    }

    /* Fill in requested parameters */
    for (unsigned int i = 0; i < niov; i += 2) {
        const char *param = (const char *)iov[i].iov_base;
        void *value = iov[i + 1].iov_base;
        size_t len = iov[i + 1].iov_len;

        if (param && value && len > 0) {
            if (param[0] == 'j' && param[1] == 'i' && param[2] == 'd' && param[3] == '\0') {
                if (len >= sizeof(jail_id_t)) {
                    *(jail_id_t *)value = je->jid;
                }
            } else if (param[0] == 'p' && param[1] == 'a' && param[2] == 't' && param[3] == 'h' && param[4] == '\0') {
                jail_strcpy((char *)value, je->path, len);
            } else if (param[0] == 'h' && param[1] == 'o' && param[2] == 's' && param[3] == 't') {
                jail_strcpy((char *)value, je->hostname, len);
            }
        }
    }

    return je->jid;
}

/**
 * Get current jail ID
 */
jail_id_t sys_jail_getid(void) {
    /* Would check current process's jail */
    /* For now, return 0 (not jailed) */
    return 0;
}

/**
 * Get jail name from ID
 */
int sys_jail_getname(jail_id_t jid, char *name, size_t len) {
    if (!name || len == 0) {
        return -EINVAL;
    }

    struct jail_entry *je = jail_lookup(jid);
    if (!je) {
        return -ENOENT;
    }

    jail_strcpy(name, je->name, len);
    return 0;
}

