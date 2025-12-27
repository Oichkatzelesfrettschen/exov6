/**
 * @file zones.c
 * @brief Illumos/Solaris-compatible Zone Implementation
 *
 * Cleanroom zone implementation for FeuerBird exokernel.
 * Translates zone semantics to isolation domain primitives.
 *
 * Key design decisions:
 * 1. Each zone maps to an isolation domain with all axes
 * 2. Global zone (ID 0) is always present
 * 3. Zone brands stored as domain metadata
 * 4. Resource controls via domain limits
 */

#include "zone.h"
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
#ifndef ENOENT
#define ENOENT 2
#endif
#ifndef EEXIST
#define EEXIST 17
#endif
#ifndef EBUSY
#define EBUSY 16
#endif
#ifndef ESRCH
#define ESRCH 3
#endif

/**
 * Maximum zones in system
 */
#define MAX_ZONES 256

/**
 * Zone entry structure
 */
struct zone_entry {
    zoneid_t id;                            /* Zone ID */
    struct isodomain *domain;               /* Underlying isolation domain */
    char name[ZONENAME_MAX];                /* Zone name */
    char root[ZONE_ROOTPATHMAX];            /* Root path */
    zone_state_t state;                     /* Zone state */
    uint64_t uniqid;                        /* Unique ID */
    int init_pid;                           /* Init process PID */
    uint32_t flags;                         /* Zone flags */
    char brand[ZONENAME_MAX];               /* Brand name */
    int refcount;                           /* Reference count */
};

/**
 * Zone registry
 */
static struct {
    struct spinlock lock;
    struct zone_entry zones[MAX_ZONES];
    zoneid_t next_id;
    uint64_t next_uniqid;
    int count;
} zone_registry;

/**
 * String copy helper
 */
static void zone_strcpy(char *dst, const char *src, size_t max) {
    size_t i;
    for (i = 0; i < max - 1 && src && src[i]; i++) {
        dst[i] = src[i];
    }
    dst[i] = '\0';
}

/**
 * String compare helper
 */
static int zone_strcmp(const char *a, const char *b) {
    while (*a && *b && *a == *b) {
        a++;
        b++;
    }
    return *a - *b;
}

/**
 * Lookup zone by ID
 */
static struct zone_entry *zone_lookup(zoneid_t id) {
    if (id < 0) {
        return 0;
    }

    acquire(&zone_registry.lock);

    for (int i = 0; i < MAX_ZONES; i++) {
        if (zone_registry.zones[i].id == id &&
            zone_registry.zones[i].state != ZONE_IS_DEAD) {
            struct zone_entry *ze = &zone_registry.zones[i];
            release(&zone_registry.lock);
            return ze;
        }
    }

    release(&zone_registry.lock);
    return 0;
}

/**
 * Lookup zone by name
 */
static struct zone_entry *zone_lookup_name(const char *name) {
    if (!name) {
        return 0;
    }

    acquire(&zone_registry.lock);

    for (int i = 0; i < MAX_ZONES; i++) {
        struct zone_entry *ze = &zone_registry.zones[i];
        if (ze->state != ZONE_IS_DEAD && zone_strcmp(ze->name, name) == 0) {
            release(&zone_registry.lock);
            return ze;
        }
    }

    release(&zone_registry.lock);
    return 0;
}

/**
 * Initialize zone subsystem
 */
void zones_init(void) {
    initlock(&zone_registry.lock, "zone_registry");

    /* Initialize all slots */
    for (int i = 0; i < MAX_ZONES; i++) {
        zone_registry.zones[i].id = -1;
        zone_registry.zones[i].domain = 0;
        zone_registry.zones[i].state = ZONE_IS_DEAD;
        zone_registry.zones[i].refcount = 0;
    }

    zone_registry.next_id = 1;  /* 0 is reserved for global zone */
    zone_registry.next_uniqid = 1;
    zone_registry.count = 0;

    /* Create global zone (always present) */
    struct zone_entry *gz = &zone_registry.zones[0];
    gz->id = GLOBAL_ZONEID;
    gz->domain = 0;  /* Global zone has no isolation domain */
    zone_strcpy(gz->name, "global", ZONENAME_MAX);
    zone_strcpy(gz->root, "/", ZONE_ROOTPATHMAX);
    gz->state = ZONE_IS_RUNNING;
    gz->uniqid = 0;
    gz->init_pid = 1;
    gz->flags = 0;
    zone_strcpy(gz->brand, "native", ZONENAME_MAX);
    gz->refcount = 1;
    zone_registry.count = 1;
}

/**
 * Get current zone ID
 */
zoneid_t sys_getzoneid(void) {
    /* Would check current process's zone */
    /* For now, return global zone */
    return GLOBAL_ZONEID;
}

/**
 * Get zone ID by name
 */
zoneid_t sys_getzoneidbyname(const char *name) {
    if (!name) {
        return -EINVAL;
    }

    struct zone_entry *ze = zone_lookup_name(name);
    if (!ze) {
        return -ESRCH;
    }

    return ze->id;
}

/**
 * Get zone name by ID
 */
int sys_getzonenamebyid(zoneid_t id, char *buf, size_t buflen) {
    if (!buf || buflen == 0) {
        return -EINVAL;
    }

    struct zone_entry *ze = zone_lookup(id);
    if (!ze) {
        return -ESRCH;
    }

    zone_strcpy(buf, ze->name, buflen);

    /* Return length of name */
    size_t len = 0;
    while (ze->name[len]) len++;
    return (int)len;
}

/**
 * List all zone IDs
 */
int sys_zone_list(zoneid_t *ids, uint32_t *nids) {
    if (!nids) {
        return -EINVAL;
    }

    acquire(&zone_registry.lock);

    uint32_t max = ids ? *nids : 0;
    uint32_t count = 0;

    for (int i = 0; i < MAX_ZONES && (!ids || count < max); i++) {
        if (zone_registry.zones[i].state != ZONE_IS_DEAD) {
            if (ids) {
                ids[count] = zone_registry.zones[i].id;
            }
            count++;
        }
    }

    *nids = zone_registry.count;
    release(&zone_registry.lock);

    return 0;
}

/**
 * Create a new zone
 */
zoneid_t sys_zone_create(const char *name, const char *root, uint32_t flags) {
    if (!name || !root) {
        return -EINVAL;
    }

    /* Check if zone already exists */
    if (zone_lookup_name(name)) {
        return -EEXIST;
    }

    acquire(&zone_registry.lock);

    /* Find free slot */
    struct zone_entry *ze = 0;
    for (int i = 1; i < MAX_ZONES; i++) {  /* Start at 1, 0 is global */
        if (zone_registry.zones[i].state == ZONE_IS_DEAD) {
            ze = &zone_registry.zones[i];
            break;
        }
    }

    if (!ze) {
        release(&zone_registry.lock);
        return -ENOMEM;
    }

    /* Create isolation domain with all isolation axes */
    uint16_t axes = ISO_AXIS_FILESYSTEM | ISO_AXIS_NETWORK |
                    ISO_AXIS_PROCESS | ISO_AXIS_USER |
                    ISO_AXIS_IPC | ISO_AXIS_RESOURCE;

    release(&zone_registry.lock);

    struct isodomain *dom = isodomain_create(name, 0, axes, 0);
    if (!dom) {
        return -ENOMEM;
    }

    acquire(&zone_registry.lock);

    /* Initialize zone entry */
    ze->id = zone_registry.next_id++;
    ze->domain = dom;
    zone_strcpy(ze->name, name, ZONENAME_MAX);
    zone_strcpy(ze->root, root, ZONE_ROOTPATHMAX);
    ze->state = ZONE_IS_INITIALIZED;
    ze->uniqid = zone_registry.next_uniqid++;
    ze->init_pid = 0;
    ze->flags = flags;
    zone_strcpy(ze->brand, "native", ZONENAME_MAX);  /* Default brand */
    ze->refcount = 1;
    zone_registry.count++;

    zoneid_t id = ze->id;
    release(&zone_registry.lock);

    return id;
}

/**
 * Enter a zone
 */
int sys_zone_enter(zoneid_t id) {
    if (id == GLOBAL_ZONEID) {
        return -EINVAL;  /* Cannot explicitly enter global zone */
    }

    struct zone_entry *ze = zone_lookup(id);
    if (!ze) {
        return -ESRCH;
    }

    if (ze->state != ZONE_IS_RUNNING) {
        return -EINVAL;
    }

    /* Enter the isolation domain */
    int err = isodomain_enter(0, ze->domain);
    if (err < 0) {
        return err;
    }

    ze->refcount++;
    return 0;
}

/**
 * Destroy a zone
 */
int sys_zone_destroy(zoneid_t id) {
    if (id == GLOBAL_ZONEID) {
        return -EPERM;  /* Cannot destroy global zone */
    }

    struct zone_entry *ze = zone_lookup(id);
    if (!ze) {
        return -ESRCH;
    }

    if (ze->state == ZONE_IS_RUNNING) {
        return -EBUSY;  /* Must shutdown first */
    }

    acquire(&zone_registry.lock);

    /* Mark as dying/dead */
    ze->state = ZONE_IS_DEAD;

    if (ze->domain) {
        isodomain_destroy(ze->domain);
        ze->domain = 0;
    }

    ze->refcount = 0;
    zone_registry.count--;

    release(&zone_registry.lock);

    return 0;
}

/**
 * Get zone attribute
 */
int sys_zone_getattr(zoneid_t id, int attr, void *buf, size_t bufsize) {
    if (!buf || bufsize == 0) {
        return -EINVAL;
    }

    struct zone_entry *ze = zone_lookup(id);
    if (!ze) {
        return -ESRCH;
    }

    switch (attr) {
        case ZONE_ATTR_NAME:
            zone_strcpy((char *)buf, ze->name, bufsize);
            break;
        case ZONE_ATTR_ROOT:
            zone_strcpy((char *)buf, ze->root, bufsize);
            break;
        case ZONE_ATTR_STATUS:
            if (bufsize >= sizeof(zone_state_t)) {
                *(zone_state_t *)buf = ze->state;
            }
            break;
        case ZONE_ATTR_UNIQID:
            if (bufsize >= sizeof(uint64_t)) {
                *(uint64_t *)buf = ze->uniqid;
            }
            break;
        case ZONE_ATTR_INITPID:
            if (bufsize >= sizeof(int)) {
                *(int *)buf = ze->init_pid;
            }
            break;
        case ZONE_ATTR_FLAGS:
            if (bufsize >= sizeof(uint32_t)) {
                *(uint32_t *)buf = ze->flags;
            }
            break;
        case ZONE_ATTR_BRAND:
            zone_strcpy((char *)buf, ze->brand, bufsize);
            break;
        default:
            return -EINVAL;
    }

    return 0;
}

/**
 * Set zone attribute
 */
int sys_zone_setattr(zoneid_t id, int attr, void *buf, size_t bufsize) {
    if (!buf || bufsize == 0) {
        return -EINVAL;
    }

    struct zone_entry *ze = zone_lookup(id);
    if (!ze) {
        return -ESRCH;
    }

    switch (attr) {
        case ZONE_ATTR_BRAND:
            zone_strcpy(ze->brand, (const char *)buf, ZONENAME_MAX);
            break;
        case ZONE_ATTR_FLAGS:
            if (bufsize >= sizeof(uint32_t)) {
                ze->flags = *(uint32_t *)buf;
            }
            break;
        case ZONE_ATTR_INITPID:
            if (bufsize >= sizeof(int)) {
                ze->init_pid = *(int *)buf;
            }
            break;
        default:
            return -EINVAL;
    }

    return 0;
}

/**
 * Boot a zone
 */
int sys_zone_boot(zoneid_t id) {
    struct zone_entry *ze = zone_lookup(id);
    if (!ze) {
        return -ESRCH;
    }

    if (ze->state != ZONE_IS_INITIALIZED && ze->state != ZONE_IS_READY) {
        return -EINVAL;
    }

    ze->state = ZONE_IS_BOOTING;
    /* Would start zone's init process here */
    ze->state = ZONE_IS_RUNNING;

    return 0;
}

/**
 * Shutdown a zone
 */
int sys_zone_shutdown(zoneid_t id) {
    if (id == GLOBAL_ZONEID) {
        return -EPERM;
    }

    struct zone_entry *ze = zone_lookup(id);
    if (!ze) {
        return -ESRCH;
    }

    if (ze->state != ZONE_IS_RUNNING) {
        return -EINVAL;
    }

    ze->state = ZONE_IS_SHUTTING_DOWN;
    /* Would signal zone's processes to terminate */
    ze->state = ZONE_IS_DOWN;

    return 0;
}

