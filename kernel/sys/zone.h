/**
 * @file zone.h
 * @brief Illumos/Solaris-compatible Zone Interface
 *
 * Cleanroom implementation of zones for FeuerBird exokernel.
 * Uses isolation domains for actual isolation enforcement.
 *
 * Zones provide:
 * - Comprehensive OS virtualization
 * - Resource management (CPU, memory, network)
 * - Brand support (personality emulation)
 * - Network virtualization (exclusive IP)
 * - Delegated administration
 */
#pragma once

#include <stdint.h>

/* size_t for kernel context */
#ifndef _SIZE_T_DEFINED
#define _SIZE_T_DEFINED
typedef unsigned long size_t;
#endif

/**
 * Zone ID type
 */
typedef int32_t zoneid_t;

/**
 * Global zone ID (always 0)
 */
#define GLOBAL_ZONEID   0

/**
 * Zone states
 */
typedef enum {
    ZONE_IS_UNINITIALIZED = 0,
    ZONE_IS_INITIALIZED,
    ZONE_IS_READY,
    ZONE_IS_BOOTING,
    ZONE_IS_RUNNING,
    ZONE_IS_SHUTTING_DOWN,
    ZONE_IS_EMPTY,
    ZONE_IS_DOWN,
    ZONE_IS_DYING,
    ZONE_IS_DEAD
} zone_state_t;

/**
 * Zone attributes
 */
#define ZONE_ATTR_NAME          1
#define ZONE_ATTR_ROOT          2
#define ZONE_ATTR_STATUS        3
#define ZONE_ATTR_PRIVSET       4
#define ZONE_ATTR_UNIQID        5
#define ZONE_ATTR_POOLID        6
#define ZONE_ATTR_INITPID       7
#define ZONE_ATTR_BRAND         8
#define ZONE_ATTR_FLAGS         9
#define ZONE_ATTR_HOSTID        10
#define ZONE_ATTR_FS_ALLOWED    11
#define ZONE_ATTR_NETWORK       12
#define ZONE_ATTR_INITNAME      13
#define ZONE_ATTR_BOOTARGS      14
#define ZONE_ATTR_SCHED_CLASS   15

/**
 * Zone creation flags
 */
#define ZCF_NET_EXCL        0x0001  /* Exclusive IP stack */
#define ZCF_ENABLE_SHMEM    0x0002  /* Enable shared memory */

/**
 * Maximum zone name length
 */
#define ZONENAME_MAX        64

/**
 * Maximum zone path length
 */
#define ZONE_ROOTPATHMAX    256

/**
 * Zone information structure
 */
struct zoneinfo {
    zoneid_t zi_id;                     /* Zone ID */
    char zi_name[ZONENAME_MAX];         /* Zone name */
    char zi_root[ZONE_ROOTPATHMAX];     /* Zone root path */
    zone_state_t zi_status;             /* Zone state */
    uint64_t zi_uniqid;                 /* Unique ID */
    int zi_boot_pid;                    /* Boot process PID */
    uint32_t zi_flags;                  /* Zone flags */
    char zi_brand[ZONENAME_MAX];        /* Brand name */
};

/**
 * Get current zone ID
 *
 * @return          Zone ID of calling process
 */
zoneid_t sys_getzoneid(void);

/**
 * Get zone ID by name
 *
 * @param name      Zone name
 * @return          Zone ID, or -errno on failure
 */
zoneid_t sys_getzoneidbyname(const char *name);

/**
 * Get zone name by ID
 *
 * @param id        Zone ID
 * @param buf       Buffer for name
 * @param buflen    Buffer length
 * @return          Length of name, or -errno on failure
 */
int sys_getzonenamebyid(zoneid_t id, char *buf, size_t buflen);

/**
 * List all zone IDs
 *
 * @param ids       Buffer for zone IDs
 * @param nids      Number of IDs buffer can hold
 * @return          Number of zones, or -errno on failure
 */
int sys_zone_list(zoneid_t *ids, uint32_t *nids);

/**
 * Create a new zone
 *
 * @param name      Zone name
 * @param root      Zone root path
 * @param flags     Creation flags (ZCF_*)
 * @return          Zone ID, or -errno on failure
 */
zoneid_t sys_zone_create(const char *name, const char *root, uint32_t flags);

/**
 * Enter a zone
 *
 * @param id        Zone ID to enter
 * @return          0 on success, -errno on failure
 */
int sys_zone_enter(zoneid_t id);

/**
 * Destroy a zone
 *
 * @param id        Zone ID
 * @return          0 on success, -errno on failure
 */
int sys_zone_destroy(zoneid_t id);

/**
 * Get zone attribute
 *
 * @param id        Zone ID
 * @param attr      Attribute (ZONE_ATTR_*)
 * @param buf       Buffer for attribute value
 * @param bufsize   Buffer size
 * @return          Attribute size, or -errno on failure
 */
int sys_zone_getattr(zoneid_t id, int attr, void *buf, size_t bufsize);

/**
 * Set zone attribute
 *
 * @param id        Zone ID
 * @param attr      Attribute (ZONE_ATTR_*)
 * @param buf       Attribute value
 * @param bufsize   Value size
 * @return          0 on success, -errno on failure
 */
int sys_zone_setattr(zoneid_t id, int attr, void *buf, size_t bufsize);

/**
 * Boot a zone
 *
 * @param id        Zone ID
 * @return          0 on success, -errno on failure
 */
int sys_zone_boot(zoneid_t id);

/**
 * Shutdown a zone
 *
 * @param id        Zone ID
 * @return          0 on success, -errno on failure
 */
int sys_zone_shutdown(zoneid_t id);

/**
 * Initialize zone subsystem
 */
void zone_init(void);

